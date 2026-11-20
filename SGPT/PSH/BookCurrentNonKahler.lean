import SGPT.PSH.BookCurrentSpace
import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds

/-!
# The non-Kähler locus of a big class

Source: `chapter_pshfunctions.tex`, `def:nKlocus`: for a big class `α`, `nK(α)` is the
intersection of the polar loci of all Kähler currents with analytic singularities in `α`.

* `HasRationalAnalyticPresentationAt.add_continuousOn`: the bounded-remainder analytic
  singularity type (`def:neatanasing`, `HasRationalAnalyticType`) is stable under adding a
  continuous function near the point.
* `HasAnalyticSingularities T`: every presentation `T = θ + dd^c φ` has `φ` of analytic
  singularity type; `hasAnalyticSingularities_iff_of_isPresentation` (one presentation suffices).
* `nonKahlerLocus α` (`def:nKlocus`) and `nonKahlerLocus_eq_sourceNonKahlerLocus`: it is the
  existing polar intersection `sourceNonKahlerLocus` over TN's potential-presented Kähler
  currents (Envelopes lane).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.PSH.BookCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CurrentBottChernClass
open SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
open SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACRestriction
open SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame
open SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
open SGPT.PSH.VariableComplexAtlas

variable {m : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- Adding a function continuous near `x` preserves an analytic presentation at `x`. -/
theorem hasRationalAnalyticPresentationAt_add_continuousOn {u : X → EReal} {x : X}
    (hu : (ofFixedModel (m + 1) X).HasRationalAnalyticPresentationAt u x)
    {O : Set X} {g : X → ℝ} (hO : IsOpen O) (hxO : x ∈ O) (hg : ContinuousOn g O)
    {w : X → EReal} (hw : EqOn w (fun y => u y + (g y : EReal)) O) :
    (ofFixedModel (m + 1) X).HasRationalAnalyticPresentationAt w x := by
  let _ : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (ComplexModel (m + 1)) X
  obtain ⟨c, N, f, b, C, U, hc, hC, hU, _hUc, hxU, hf, hb, heq⟩ := hu
  have hgx : ∀ᶠ y in 𝓝 x, |g y - g x| < 1 := by
    have hcont : ContinuousAt (fun y => |g y - g x|) x :=
      ((hg x hxO).continuousAt (hO.mem_nhds hxO)).sub continuousAt_const |>.abs
    exact hcont.eventually_lt_const (by simp)
  obtain ⟨W, hWs, hW, hxW⟩ := mem_nhds_iff.mp hgx
  set V : Set X := U ∩ O ∩ W with hV
  have hVo : IsOpen V := (hU.inter hO).inter hW
  have hxV : x ∈ V := ⟨⟨hxU, hxO⟩, hxW⟩
  set U' : Set X := connectedComponentIn V x
  have hU'V : U' ⊆ V := connectedComponentIn_subset V x
  refine ⟨c, N, f, fun y => b y + g y, C + (|g x| + 1), U', hc, by positivity,
    hVo.connectedComponentIn, isConnected_connectedComponentIn_iff.mpr hxV,
    mem_connectedComponentIn hxV, ?_, ?_, ?_⟩
  · intro j i
    exact (hf j i).mono fun z hz => ⟨hz.1, (hU'V hz.2).1.1⟩
  · intro y hy
    have hyV := hU'V hy
    have h1 := hb y hyV.1.1
    have h2 : |g y - g x| < 1 := hWs hyV.2
    have h3 : |g y| ≤ |g x| + 1 := by
      have := abs_sub_abs_le_abs_sub (g y) (g x)
      linarith
    calc |b y + g y| ≤ |b y| + |g y| := abs_add_le _ _
      _ ≤ C + (|g x| + 1) := add_le_add h1 h3
  · intro y hy
    have hyV := hU'V hy
    rw [hw hyV.1.2]
    show u y + (g y : EReal) = ((c : ℝ) : EReal) * generatorLog f y + ((b y + g y : ℝ) : EReal)
    rw [heq hyV.1.1, EReal.coe_add, add_assoc]

/-- **Currents with analytic singularities**: every potential of every presentation has
analytic singularity type (`def:neatanasing`, bounded-remainder rational presentations). -/
def HasAnalyticSingularities (T : ClosedPositiveCurrent m X) : Prop :=
  ∀ (θ : ClosedRealOneOneForm (m + 1) X) (u : X → EReal), IsPresentation T θ u →
    (ofFixedModel (m + 1) X).HasRationalAnalyticType u

/-- One presentation suffices. -/
theorem hasAnalyticSingularities_iff_of_isPresentation {T : ClosedPositiveCurrent m X}
    {θ : ClosedRealOneOneForm (m + 1) X} {u : X → EReal} (h : IsPresentation T θ u) :
    HasAnalyticSingularities T ↔ (ofFixedModel (m + 1) X).HasRationalAnalyticType u := by
  refine ⟨fun H => H θ u h, fun H θ' u' h' x => ?_⟩
  obtain ⟨O, g, hO, hxO, hg, heq⟩ := exists_local_difference_of_isPresentation h' h x
  exact hasRationalAnalyticPresentationAt_add_continuousOn (H x) hO hxO hg heq

/-- `θ + dd^c u` minus `ω` is `(θ - ω) + dd^c u`. -/
theorem thetaPotentialCurrent_sub_smooth (θ ω : ClosedRealOneOneForm (m + 1) X)
    {u : X → EReal} (hu : IsThetaPshPotential θ.val u)
    (hu' : IsThetaPshPotential (θ - ω).val u) :
    thetaPotentialCurrent θ.val u hu -
        (smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ω).val =
      thetaPotentialCurrent (θ - ω).val u hu' := by
  have hsm : GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
        (k := degreeTwo (Nat.succ_pos m)) θ.val =
      GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
          (k := degreeTwo (Nat.succ_pos m)) (θ - ω).val +
        GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
          (k := degreeTwo (Nat.succ_pos m)) ω.val := by
    rw [← smoothGlobalCurrent_add, sub_add_cancel]
  unfold thetaPotentialCurrent
  change GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ.val + _ -
    GlobalCurrents.smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) ω.val = _
  rw [hsm]
  abel

/-- A TN Kähler current `θ + dd^c u`, `u ∈ PSH(X, θ - ω)`, is a Kähler current in `𝒵₊(X)`. -/
theorem kahlerCurrent_isKahlerCurrent {α : RealBottChern (m + 1) X} (K : KahlerCurrent α)
    (hu : IsThetaPshPotential K.representative.val K.potential) :
    IsKahlerCurrent (thetaPositiveCurrent K.representative K.potential hu) := by
  refine ⟨K.lowerBound, ?_⟩
  rw [thetaPositiveCurrent_current, thetaPotentialCurrent_sub_smooth _ _ hu K.strictlyPsh]
  exact isPositiveCurrent_of_isFullPositive _
    (thetaPotentialCurrent_full_positive _ K.potential K.strictlyPsh)

theorem kahlerCurrent_isThetaPsh {α : RealBottChern (m + 1) X} (K : KahlerCurrent α) :
    IsThetaPshPotential K.representative.val K.potential := by
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive K.strictlyPsh
    K.lowerBound.isSemipositive
  rwa [sub_add_cancel] at h

variable [CompactSpace X]

/-- **The non-Kähler locus** (`def:nKlocus`): the intersection of the polar loci of all Kähler
currents with analytic singularities in `α`. -/
def currentNonKahlerLocus (α : RealBottChern (m + 1) X) : Set X :=
  ⋂ (T : ClosedPositiveCurrent m X) (_ : currentClass T = α ∧ IsKahlerCurrent T ∧
    HasAnalyticSingularities T), polarLocus T

/-- The source non-Kähler locus is the polar intersection over TN's potential-presented Kähler
currents with analytic singularity type (`sourceNonKahlerLocus`). -/
theorem currentNonKahlerLocus_eq_sourceNonKahlerLocus (α : RealBottChern (m + 1) X) :
    currentNonKahlerLocus α = sourceNonKahlerLocus α := by
  ext x
  simp only [currentNonKahlerLocus, mem_iInter]
  constructor
  · intro hx K hK
    have hu := kahlerCurrent_isThetaPsh K
    have hpres := isPresentation_thetaPositiveCurrent K.representative K.potential hu
    have h := hx (thetaPositiveCurrent K.representative K.potential hu)
      ⟨by rw [currentClass_thetaPositiveCurrent, K.represents],
        kahlerCurrent_isKahlerCurrent K hu,
        (hasAnalyticSingularities_iff_of_isPresentation hpres).mpr hK⟩
    rw [polarLocus_eq_of_isPresentation hpres] at h
    exact h
  · rintro hx T ⟨hTα, ⟨κ, hpos⟩, han⟩
    let C := smoothClosedCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) κ.form
    let S : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m) :=
      T.val + (-1 : ℝ) • C
    have hS : S.val = T.current - C.val := by
      change T.current + (-1 : ℝ) • C.val = _
      module
    let S' : ClosedPositiveCurrent m X := ⟨S, by rw [hS]; exact hpos⟩
    obtain ⟨σ, u, hσu, hSeq⟩ := exists_presentation S'
    have hu' : IsThetaPshPotential ((σ + κ.form) - κ.form).val u := by
      rw [add_sub_cancel_right]; exact hσu
    have hu : IsThetaPshPotential (σ + κ.form).val u := by
      have h := LocalPotentials.isThetaPshPotential_add_of_semipositive hσu κ.isSemipositive
      exact h
    have hpresT : IsPresentation T (σ + κ.form) u := by
      refine ⟨hu, ?_⟩
      have h1 : T.current = S.val + C.val := by rw [hS]; abel
      have h2 := thetaPotentialCurrent_sub_smooth (σ + κ.form) κ.form hu hu'
      have h3 : thetaPotentialCurrent ((σ + κ.form) - κ.form).val u hu' =
          thetaPotentialCurrent σ.val u hσu := by
        congr 1
        simp
      rw [h1]
      change S'.current + C.val = _
      rw [hSeq, ← h3, ← h2]
      abel
    have hclassσ : RealBottChern.ofRepresentative (σ + κ.form) = α := by
      rw [← hpresT.currentClass_eq, hTα]
    let K : KahlerCurrent α := ⟨σ + κ.form, hclassσ, u, κ, hu'⟩
    have hKx := hx K (han _ _ hpresT)
    change x ∈ polarLocus T
    rw [polarLocus_eq_of_isPresentation hpresT]
    exact hKx

end SGPT.PSH.BookCurrent
