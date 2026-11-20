import SGPT.Okounkov.ValuativeKahlerSlice
import SGPT.Trace.SmoothTarget
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.GlobalPMultiplierOrder

/-!
# The slice formula `lma:slicepob` for currents with bounded potentials

Source: the book's `lma:slicepob` (chapter *The theory of Okounkov bodies*, subsection *The
valuative characterization*, lines 1728--1790), second ("more generally") assertion, for
currents with bounded potentials; blueprint chapter `claude-okoun-val`.

Let `X` be a connected compact Kähler manifold of dimension `n = m + 2 ≥ 2` with a smooth flag
`Y•`, `α = {θ}` a big class and `T = θ + dd^c φ ∈ 𝒵₊(X, α)` with **bounded** potential `φ` (so
`ν(T, Y₁) = 0`). For every trace operator `τ` of `φ` along `Y₁` (`def:traceop`, the source
predicate `IsNaturalSourceTraceRepresentative`, the trace used in the flag valuation
`def:valcurr`) and every representative `Tr^{α|_{Y₁}}_{Y₁}(T) = θ|_{Y₁} + dd^c τ'` of `Tr_{Y₁}(T)`
in the class `α|_{Y₁}` (`rmk:tracecurrent`: `τ'` is `θ|_{Y₁}`-psh and `P`-equivalent to `τ`),

`{y ∈ ℝ^{n-1} : (0, y) ∈ Δ_{Y•}(T)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(Tr^{α|_{Y₁}}_{Y₁}(T))`

(`slice_zero_generalPartialBody_eq_of_bounded`). This is the case `D = 0`, `π = id` of Step 1 of
the book's proof: `Δ_{Y•}(T) = Δ_{Y•}(α)` (`thm:pobmain` (3)), `α` is nef (`T` has bounded
potential), the slice of `Δ_{Y•}(α)` is `⋂_{ε > 0} Δ_{Y₁ ⊇ ⋯}((α + ε{ω})|_{Y₁})`
(`lma:Kahlerclassokounrest`, `slice_zero_eq_iInter_of_nef`), and this is `Δ_{Y₁ ⊇ ⋯}(T|_{Y₁})` for
the bounded restriction `T|_{Y₁}` (`iInter_tradOkounkovBody_eq_generalPartialBody_of_bounded`);
finally `T|_{Y₁} ⪯_P Tr_{Y₁}(T) ∼_P Tr^{α|_{Y₁}}_{Y₁}(T)` (`prop:Trdominarest`) and
`thm:pobmain` (2).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.Valuative

open Set Filter
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.NaturalSubmanifoldSourceTraceDefinition
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.PSH SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalSlice
open SGPT.Okounkov.PartialBody

section General

variable {m : ℕ} {G : OriginalFlagGeometry.{u} (m + 1)}

/-- `Δ(T) ⊆ ⋂_{ε > 0} Δ(γ + ε{ω})` for `T ∈ 𝒵₊(X, γ)` (no bigness). -/
theorem generalPartialBody_subset_iInter_tradOkounkovBody
    {σ : ClosedRealOneOneForm (m + 1) G.carrier} {φ : G.carrier → EReal}
    (hφ : IsThetaPshPotential σ.val φ) (ω : KahlerBackground (m + 1) G.carrier) :
    generalPartialBody G σ φ ⊆ ⋂ (ε : ℝ) (_ : 0 < ε), tradOkounkovBody G (σ + ε • ω.form) := by
  rw [generalPartialBody_eq_of_kahler hφ ω]
  refine subset_iInter₂ fun ε hε => ?_
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  have hj' : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  have hK := isKahlerCurrentPotential_add_smul hφ ω hj'
  refine (iInter_subset _ j).trans ((kahlerPartialBody_subset_of_iOrder hK hK
    (iOrderOnManifold_refl φ)).2.trans (PartialBody.tradOkounkovBody_subset_of_le ?_))
  have heq : σ + ε • ω.form - (σ + ((j : ℝ) + 1)⁻¹ • ω.form) =
      (ε - ((j : ℝ) + 1)⁻¹) • ω.form := by module
  rw [heq]
  refine KahlerDomination.isSemipositive_smul ω.isSemipositive ?_
  rw [inv_eq_one_div]
  linarith

/-- `thm:pobmain` (2) without bigness: `T ⪯_𝓘 S` gives `Δ(T) ⊆ Δ(S)`. -/
theorem generalPartialBody_mono_of_iOrder {σ : ClosedRealOneOneForm (m + 1) G.carrier}
    {φ ψ : G.carrier → EReal} (hφ : IsThetaPshPotential σ.val φ)
    (hψ : IsThetaPshPotential σ.val ψ) (hI : IOrderOnManifold (n := m + 1) φ ψ) :
    generalPartialBody G σ φ ⊆ generalPartialBody G σ ψ := by
  refine iInter_mono fun j => ?_
  have ht : (0 : ℝ) < ((j : ℝ) + 1)⁻¹ := by positivity
  exact (kahlerPartialBody_subset_of_iOrder (isKahlerCurrentPotential_add_smul hφ G.omega ht)
    (isKahlerCurrentPotential_add_smul hψ G.omega ht) hI).1

end General

section Bounded

variable {m : ℕ} {F : OriginalFlagGeometry.{u} (m + 2)}

/-- The restriction to `Y₁` of a `θ`-psh potential which is finite somewhere on `Y₁` is
`θ|_{Y₁}`-psh. -/
theorem isThetaPshPotential_restrict_firstFlag {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hne : ∃ y : F.tail.carrier, φ y.val ≠ ⊥) :
    IsThetaPshPotential (TranscendentalMain.firstFlagRestriction F θ).val
      (fun y : F.tail.carrier => φ y.val) := by
  have hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (m + 1)) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ (m + 1)) F.firstDivisor.2.2
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ (m + 1))
    F.firstDivisor.2.2
  let : ConnectedSpace (F.flag (1 : Fin (m + 3))) := F.tail.connected
  have hpsh := GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hφ.1
  have hne' : ∃ y : F.flag (1 : Fin (m + 3)), φ y.val ≠ ⊥ := hne
  have hnd := ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot hpsh hne'
  exact ⟨hpsh, hnd⟩

/-- **`lma:slicepob` for currents with bounded potentials**: let `α = {θ}` be big,
`T = θ + dd^c φ` with `φ` bounded, `τ` a trace operator of `φ` along `Y₁` and
`Tr^{α|_{Y₁}}_{Y₁}(T) = θ|_{Y₁} + dd^c τ'` a representative of `Tr_{Y₁}(T)` in `α|_{Y₁}`
(`τ'` is `θ|_{Y₁}`-psh and `τ' ∼_P τ`). Then
`{y : (0, y) ∈ Δ_{Y•}(T)} = Δ_{Y₁ ⊇ ⋯ ⊇ Yₙ}(Tr^{α|_{Y₁}}_{Y₁}(T))`. -/
theorem slice_zero_generalPartialBody_eq_of_bounded {θ : ClosedRealOneOneForm (m + 2) F.carrier}
    (hbig : SGPT.PSH.BookCurrent.IsBig (RealBottChern.ofRepresentative θ))
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hb : BoundedGlobalProduct.IsBoundedPotential φ)
    {τ : F.tail.carrier → EReal} (hτ : IsNaturalSourceTraceRepresentative F.omega F.firstDivisor φ τ)
    {τ' : F.tail.carrier → EReal}
    (hτ' : IsThetaPshPotential (TranscendentalMain.firstFlagRestriction F θ).val τ')
    (hP : letI : MeasurableSpace F.tail.carrier := borel F.tail.carrier
      haveI : BorelSpace F.tail.carrier := ⟨rfl⟩
      SourcePEquivalent (n := m + 1) τ' τ) :
    TranscendentalMain.firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (TranscendentalMain.firstFlagRestriction F θ) τ' := by
  obtain ⟨a, b, hab⟩ := hb
  have hnef := DominationIntersectionNumbers.nefWithRespectTo_of_isBoundedPotential F.omega hφ.1
    ⟨a, b, hab⟩
  -- `Δ(T) = Δ(α)`
  have hmin : ∀ ψ : F.carrier → EReal, IsThetaPshPotential θ.val ψ → SingularityLE ψ φ := by
    intro ψ hψ
    obtain ⟨A, hA⟩ := RelativePreceqClasses.exists_le_coe_of_isThetaPshPotential hψ
    refine ⟨A - a, fun x _ => ?_⟩
    calc ψ x ≤ (A : EReal) := hA x
      _ = ((A - a : ℝ) : EReal) + (a : EReal) := by rw [← EReal.coe_add, sub_add_cancel]
      _ ≤ ((A - a : ℝ) : EReal) + φ x := add_le_add le_rfl (hab x).1
      _ = φ x + ((A - a : ℝ) : EReal) := add_comm _ _
  rw [generalPartialBody_eq_tradOkounkovBody_of_minimal hbig hφ hmin,
    slice_zero_eq_iInter_of_nef hbig hnef]
  simp_rw [firstFlagRestriction_add_smul]
  set ωY : KahlerBackground (m + 1) F.tail.carrier := restrictedKahlerForm F.omega with hωY
  have hωYf : ωY.form = TranscendentalMain.firstFlagRestriction F F.omega.form := rfl
  rw [← hωYf]
  -- the restriction `T|_{Y₁}`
  have hne : ∃ y : F.tail.carrier, φ y.val ≠ ⊥ := by
    obtain ⟨x₀, hx₀⟩ := F.firstDivisor.2.1.nonempty
    exact ⟨⟨x₀, hx₀⟩, ne_bot_of_le_ne_bot (EReal.coe_ne_bot a) (hab x₀).1⟩
  have hres := isThetaPshPotential_restrict_firstFlag hφ hne
  have hbridge := iInter_tradOkounkovBody_eq_generalPartialBody_of_bounded hres ωY
    (C := a) (fun y => (hab y.val).1)
  -- `T|_{Y₁} ⪯_𝓘 Tr_{Y₁}(T) ⪯_𝓘 Tr^{α|_{Y₁}}_{Y₁}(T)`
  have hI₁ : IOrderOnManifold (n := m + 1) (fun y : F.tail.carrier => φ y.val) τ := by
    let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
    have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
    have htr : IsSourceTraceRepresentativeAlong F.omega F.tail.omega
        (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (m + 1)) F.firstDivisor.2.2) φ τ := hτ
    exact GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder
      (SGPT.Trace.sourcePOrder_restriction_trace (Nat.le_succ (m + 1)) F.tail.omega _ htr hne)
  have hI₂ : IOrderOnManifold (n := m + 1) τ τ' := by
    let _ : MeasurableSpace F.tail.carrier := borel F.tail.carrier
    have _ : BorelSpace F.tail.carrier := ⟨rfl⟩
    exact GlobalPMultiplierOrder.iOrderOnManifold_of_sourcePOrder hP.2
  apply Subset.antisymm
  · rw [← hbridge]
    exact generalPartialBody_mono_of_iOrder hres hτ' (hI₁.trans hI₂)
  · exact generalPartialBody_subset_iInter_tradOkounkovBody hτ' ωY

end Bounded

end SGPT.Okounkov.Valuative
