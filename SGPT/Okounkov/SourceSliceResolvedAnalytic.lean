import SGPT.Okounkov.SourceSliceResolvedTools
import SGPT.Okounkov.TranscendentalVolIdRestrict
import SGPT.Okounkov.TranscendentalSliceValuation
import SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal

/-! The actual resolved analytic Kähler-current zero-slice step.  The same
original divisor and original restriction enter both body formulas. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceSlice
open Set Matrix
open scoped Pointwise Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalCore SGPT.Okounkov.TranscendentalLifting
open SGPT.Okounkov.TranscendentalPartial SGPT.Okounkov.PartialBody
open SGPT.PSH
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalSlice SGPT.Okounkov.TranscendentalWN

/-- Actual original restriction of an analytic Kähler current with a resolved
bounded psh residual. Nondegeneracy of the actual restriction is the only
intermediate condition; the source trace consumer derives it internally. -/
theorem slice_zero_of_actual_resolved_decomposition
    {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 2))
    {θ : ClosedRealOneOneForm (m + 2) F.carrier} {φ b : F.carrier → EReal}
    (hφA : φ ∈ globalAnalyticCurrents θ) (hφK : IsKahlerCurrentPotential θ φ)
    (D : MeteredEffectiveQDivisor (m + 2) F.carrier)
    (hb : IsThetaPshPotential (θ - D.curvature).val b)
    (hbounded : ∃ C : ℝ, ∀ y, ((-C : ℝ) : EReal) ≤ b y ∧ b y ≤ (C : EReal))
    (heq : ∀ y, φ y = D.weight y + b y)
    (hnd : LocallyNondegenerate (fun y : F.tail.carrier => φ y.val)) :
    firstCoordinateSlice (generalPartialBody F θ φ) 0 =
      generalPartialBody F.tail (firstFlagRestriction F θ)
        (fun y : F.tail.carrier => φ y.val) := by
  let hf := contMDiff_firstFlagInclusion F
  have hφr := TranscendentalVolId.isThetaPshPotential_restrict
    (F := F) hφA.1.1 hnd (singularityLE_refl _)
  have hφrA : (fun y : F.tail.carrier => φ y.val) ∈
      globalAnalyticCurrents (firstFlagRestriction F θ) :=
    ⟨hφr, TranscendentalVolId.restrict_hasAnalyticSingularities (F := F) hφA.2⟩
  have hφrK : IsKahlerCurrentPotential (firstFlagRestriction F θ)
      (fun y : F.tail.carrier => φ y.val) := by
    obtain ⟨κ, hκ⟩ := hφK
    exact TranscendentalVolId.isKahlerCurrentPotential_restrict (F := F) hκ hnd
      (singularityLE_refl _)
  have hDnd : LocallyNondegenerate (fun y : F.tail.carrier => D.weight y.val) := by
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := hnd x U hU hxU
    refine ⟨y, hyU, fun hbot => hy ?_⟩
    change φ y.val = ⊥
    change D.weight y.val = ⊥ at hbot
    rw [heq y.val, hbot, EReal.bot_add]
  let DY := TranscendentalVolId.meteredPullback hf D hDnd
  have hform : firstFlagRestriction F (θ - D.curvature) =
      firstFlagRestriction F θ - DY.curvature :=
    TranscendentalBody.pullback_sub' hf θ D.curvature
  have hbndY : LocallyNondegenerate (fun y : F.tail.carrier => b y.val) := by
    obtain ⟨C, hC⟩ := hbounded
    intro x U hU hxU
    exact ⟨x, hxU, ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C)) (hC x.val).1⟩
  have hbr : IsThetaPshPotential (firstFlagRestriction F θ - DY.curvature).val
      (fun y : F.tail.carrier => b y.val) := by
    rw [← hform]
    exact GlobalPotentialPullback.isThetaPshPotential_comp hf hb.1 hbndY
  have hboundedY : ∃ C : ℝ, ∀ y : F.tail.carrier,
      ((-C : ℝ) : EReal) ≤ b y.val ∧ b y.val ≤ (C : EReal) := by
    obtain ⟨C, hC⟩ := hbounded
    exact ⟨C, fun y => hC y.val⟩
  have heqY : ∀ y : F.tail.carrier, φ y.val = DY.weight y + b y.val :=
    fun y => heq y.val
  have hbig := isBig_residual_of_actual_decomposition F hφK D hb hbounded heq
  have hbigY := isBig_residual_of_actual_decomposition F.tail hφrK DY hbr hboundedY heqY
  rw [← hform] at hbigY
  have hnef : NefWithRespectTo F.omega (θ - D.curvature) := by
    obtain ⟨C, hC⟩ := hbounded
    exact DominationIntersectionNumbers.nefWithRespectTo_of_isBoundedPotential F.omega
      hb.1 ⟨-C, C, hC⟩
  have hDglobal : D.weight ∈ globalAnalyticCurrents D.curvature := by
    obtain ⟨c, I, hc, hI, ht⟩ := MeteredDivisorGlobalIdeal.exists_hasAnalyticSingularitiesOfType D
    exact ⟨isThetaPshPotential_weight D, c, I, ht⟩
  obtain ⟨y, _, hy⟩ := hDnd (Classical.choice inferInstance) Set.univ isOpen_univ (mem_univ _)
  have hval : flagValuation F D.weight = Fin.cons 0 (flagValuation F.tail DY.weight) :=
    TranscendentalSlice.flagValuation_eq_cons_zero_of_ne_bot F
      (globalAnalyticCurrents_subset_analyticCurrents D.curvature hDglobal) y.property hy
  have hzero : flagValuation F D.weight 0 = 0 := by
    simpa only [Fin.cons_zero] using congrFun hval 0
  have htail : (fun j : Fin (m + 1) => flagValuation F D.weight j.succ) =
      flagValuation F.tail DY.weight := by
    funext j
    simpa only [Fin.cons_succ] using congrFun hval j.succ
  rw [generalPartialBody_eq_divisor_translate_of_bounded F hφA hφK D b hb hbounded heq,
    firstCoordinateSlice_vadd_zero _ hzero, htail,
    Valuative.slice_zero_eq_of_nef_of_big_restriction hbig hnef hbigY,
    generalPartialBody_eq_divisor_translate_of_bounded F.tail hφrA hφrK DY
      (fun y : F.tail.carrier => b y.val) hbr hboundedY heqY,
    hform]
end SGPT.Okounkov.SourceSlice
