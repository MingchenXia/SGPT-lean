import SGPT.Siu.PrimeDivisorCurrent
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance

/-!
# Modified nef classes

Source: `def:mnclass` of the book (chapter *Plurisubharmonic functions*, section *The space of
currents*): after fixing a Kähler form `ω`, a class `α ∈ H^{1,1}(X, ℝ)` is *modified nef* if for
every `ε > 0` there is a closed `(1,1)`-current `T ∈ α` with `T + εω ≥ 0` and
`ν(T + εω, D) = 0` for every prime divisor `D`; this does not depend on `ω`.

As in the existing potential-based class API (`ClassPseudoeffectiveViaPotentials`,
`ClassNefWithRespectTo`), a class is a real Bott–Chern class `RealBottChern` and the currents
`T ∈ α` with `T + εω ≥ 0` are written `T = θ + ddᶜφ` with `θ ∈ α` smooth and
`φ ∈ PSH(X, θ + εω)`, so that `T + εω = (θ + εω) + ddᶜφ` and `ν(T + εω, D) = ν(φ, D)`
(`currentGenericLelong_eq_primeGenericLelong`).  The definition descends to Bott–Chern classes
(`modifiedNefWithRespectTo_of_bottChernRel`) and is independent of the Kähler background
(`modifiedNefWithRespectTo_iff`, `classModifiedNefWithRespectTo_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Siu

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open NaturalThetaPshGeometricCurrent SquaredLogLelongSourceNormalization
open ClosedRealOneOneForm

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The generic Lelong number `ν(φ, D) = inf_{x ∈ D} ν(φ, x)` of a potential along a prime
divisor (book normalization). -/
def primeGenericLelong (φ : M → EReal) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) : ℝ≥0∞ :=
  ⨅ x ∈ D.val, squaredLogLelongNumber (n := m + 1) φ x

/-- For `T = θ + ddᶜφ`, `ν(T, D) = ν(φ, D)`. -/
theorem currentGenericLelong_eq_primeGenericLelong
    {T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))} (hT : IsClosedPositiveCurrent T)
    {θ : SmoothRealForm (m + 1) M 2} {φ : M → EReal} {hφ : IsThetaPshPotential θ φ}
    (heq : T = thetaPotentialCurrent θ φ hφ) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    currentGenericLelong T hT D = primeGenericLelong φ D := by
  simp only [currentGenericLelong, primeGenericLelong,
    currentLelong_eq_of_eq_thetaPotentialCurrent hT heq]

/-- Subtracting a chart-smooth function does not change generic Lelong numbers. -/
theorem primeGenericLelong_sub_smooth (φ : M → EReal) {f : M → ℝ}
    (hf : ChartSmooth (n := m + 1) f) (D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M) :
    primeGenericLelong (fun x => φ x - (f x : EReal)) D = primeGenericLelong φ D := by
  unfold primeGenericLelong
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  have hfc : ContinuousAt (fun y => -f y) x := by
    let e := complexChartAt (n := m + 1) x
    have hx : x ∈ e.val.source := mem_complexChartAt_source x
    have h1 : ContinuousAt (fun z => f (e.val.symm z)) (e.val x) :=
      ((hf e).continuousOn _ (e.val.map_source hx)).continuousAt
        (e.val.open_target.mem_nhds (e.val.map_source hx))
    have h2 : ContinuousAt (fun y => f (e.val.symm (e.val y))) x := h1.comp (e.val.continuousAt hx)
    have h3 : (fun y => f (e.val.symm (e.val y))) =ᶠ[𝓝 x] f := by
      filter_upwards [e.val.open_source.mem_nhds hx] with y hy
      rw [e.val.left_inv hy]
    exact (h2.congr h3).neg
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
    ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  have h := LelongChartReaderInvariance.lelongNumber_add_continuous_eq (n := m + 1) (u := φ) hfc
  have hfun : (fun y => φ y + ((-f y : ℝ) : EReal)) = fun y => φ y - (f y : EReal) := by
    funext y
    rw [EReal.coe_neg, sub_eq_add_neg]
  rw [hfun] at h
  exact h

/-- **Modified nef representatives** (`def:mnclass`, on a smooth representative `θ` of the class):
for every `ε > 0` there is `φ ∈ PSH(X, θ + εω)` (i.e. a closed current `T = θ + ddᶜφ` in the
class with `T + εω ≥ 0`) whose generic Lelong number vanishes along every prime divisor. -/
def ModifiedNefWithRespectTo (ω : KahlerBackground (m + 1) M)
    (θ : ClosedRealOneOneForm (m + 1) M) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ φ : M → EReal, IsThetaPshPotential (θ + ε • ω.form).val φ ∧
    ∀ D : SGPT.PSH.GeometricPrimeCarrier (m + 1) M, primeGenericLelong φ D = 0

/-- The condition only depends on the Bott–Chern class of the representative. -/
theorem modifiedNefWithRespectTo_of_bottChernRel (ω : KahlerBackground (m + 1) M)
    {θ η : ClosedRealOneOneForm (m + 1) M} (hθη : BottChernRel θ η)
    (hθ : ModifiedNefWithRespectTo ω θ) : ModifiedNefWithRespectTo ω η := by
  intro ε hε
  obtain ⟨φ, hφ, hD⟩ := hθ ε hε
  obtain ⟨f, hf, heq⟩ := hθη.add (BottChernRel.refl (ε • ω.form))
  refine ⟨fun x => φ x - (f x : EReal), thetaPshPotential_sub_smooth hf heq hφ, fun D => ?_⟩
  rw [primeGenericLelong_sub_smooth φ hf D, hD D]

/-- **Modified nef classes** (`def:mnclass`) on the real Bott–Chern quotient. -/
def ClassModifiedNefWithRespectTo (ω : KahlerBackground (m + 1) M)
    (α : RealBottChern (m + 1) M) : Prop :=
  Quotient.lift (s := bottChernSetoid) (ModifiedNefWithRespectTo ω)
    (fun _ _ h => propext ⟨modifiedNefWithRespectTo_of_bottChernRel ω h,
      modifiedNefWithRespectTo_of_bottChernRel ω (BottChernRel.symm h)⟩) α

@[simp] theorem classModifiedNefWithRespectTo_ofRepresentative (ω : KahlerBackground (m + 1) M)
    (θ : ClosedRealOneOneForm (m + 1) M) :
    ClassModifiedNefWithRespectTo ω (RealBottChern.ofRepresentative θ) ↔
      ModifiedNefWithRespectTo ω θ := Iff.rfl

/-- One direction of the independence of the Kähler form. -/
theorem ModifiedNefWithRespectTo.of_kahler [CompactSpace M] {ω : KahlerBackground (m + 1) M}
    (ω' : KahlerBackground (m + 1) M) {θ : ClosedRealOneOneForm (m + 1) M}
    (hθ : ModifiedNefWithRespectTo ω θ) : ModifiedNefWithRespectTo ω' θ := by
  intro ε hε
  -- `ω ≤ A ω'`
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω' (-ω.form)
  obtain ⟨φ, hφ, hD⟩ := hθ (ε / A) (div_pos hε hA)
  refine ⟨φ, ?_, hD⟩
  -- `θ + εω' = (θ + (ε/A) ω) + (ε/A) (-ω + A ω')`
  have hsemi' : ((ε / A) • (-ω.form + A • ω'.form)).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul hsemi (div_pos hε hA).le
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hφ hsemi'
  have heq : θ + (ε / A) • ω.form + (ε / A) • (-ω.form + A • ω'.form) = θ + ε • ω'.form := by
    rw [smul_add, smul_neg, smul_smul, div_mul_cancel₀ ε hA.ne']
    abel
  rwa [heq] at h

/-- **The definition of modified nef classes does not depend on the Kähler form** (the claim of
`def:mnclass`). -/
theorem modifiedNefWithRespectTo_iff [CompactSpace M] (ω ω' : KahlerBackground (m + 1) M)
    (θ : ClosedRealOneOneForm (m + 1) M) :
    ModifiedNefWithRespectTo ω θ ↔ ModifiedNefWithRespectTo ω' θ :=
  ⟨fun h => h.of_kahler ω', fun h => h.of_kahler ω⟩

theorem classModifiedNefWithRespectTo_iff [CompactSpace M] (ω ω' : KahlerBackground (m + 1) M)
    (α : RealBottChern (m + 1) M) :
    ClassModifiedNefWithRespectTo ω α ↔ ClassModifiedNefWithRespectTo ω' α := by
  induction α using Quotient.inductionOn with
  | h θ => exact modifiedNefWithRespectTo_iff ω ω' θ

end SGPT.Siu
