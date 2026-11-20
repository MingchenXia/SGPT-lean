import SGPT.Bergman.SiuNativeSectionMetric
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor
import SGPT.Foundations.Analysis.Pending.CanonicalCurrentFrame

/-! Actual original native frame equation gives the SAME complete normalized
local divisor current. Blueprint: `native-section-local-current.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.BDivisor.NSKodaira
open LelongPoincareDivisor CanonicalCurrentFrame

section Presentation

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)
  (hL : IsSourceSmoothHermitianMetric L) (s : HolomorphicSections (n := n) L.Fiber)
  (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)

/-- The SAME physical log norm and original frame manufacture the genuine
one-equation local presentation, with coefficient ONE and actual curvature. -/
def nativeSectionFramePresentation (E : AtlasFrame L) :
    LocalPresentation (nativeSectionDivisorMetric L hL s hdense) where
  U := E.val.baseSet
  isOpen := E.val.open_baseSet
  N := 1
  a := fun _ => 1
  g := fun _ => sectionCoefficient L.Fiber E.val s
  h := fun y => Real.log (‖E.val.symm y 1‖ ^ 2)
  a_nonneg := fun _ => zero_le_one
  g_holo := fun _ y hy =>
    (SGPT.BDivisor.NSKodaira.nativeSectionCoefficient_holomorphicAt L s E hy).self_of_nhds.mdifferentiableWithinAt
  g_ne := by
    intro _ U hU hUE hUne
    obtain ⟨y, hy, hsy⟩ := hdense U hU hUne
    refine ⟨y, hy, ?_⟩
    intro h0
    have hn := norm_eq_coefficient_mul_frameNorm L.Fiber E.val s (hUE hy)
    rw [h0, norm_zero, zero_mul] at hn
    exact hsy (norm_eq_zero.mp hn)
  h_smooth := fun c => (hL c E).log (fun z hz =>
    (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero L E hz.2))).ne')
  weight_eq := fun y hy => by
    simpa only [nativeSectionDivisorMetric, Fin.sum_univ_one, Rat.cast_one, EReal.coe_one, one_mul] using
      nativeSectionLog_frame_eq L s E hy
  curvature_eq := fun c z hz he => nativeSection_frame_curvature L hL E c hz he

end Presentation

section Current

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (hL : IsSourceSmoothHermitianMetric L) (s : HolomorphicSections (n := m + 1) L.Fiber)
  (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)

/-- The complete unchanged global section-divisor current reads the SAME
original physical frame coefficient's Hausdorff divisor current, with
Euclidean normalization ONE. No local-current identity is a premise. -/
theorem nativeSectionFrameCurrent_coefficient_reading
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X) :
    let P := nativeSectionFramePresentation L hL s hdense E
    restrictForm
      ((integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (nativeSectionDivisorMetric L hL s hdense)).coefficients (canonicalBasis (m + 1)) c)
      (P.chartDomain_le c) =
        DivisorIntegrationCurrent.divisorCurrent
          (P.differentiableOn_chartG c ⟨0, by change 0 < 1; omega⟩)
          (P.frequently_chartG_ne c ⟨0, by change 0 < 1; omega⟩) := by
  let P := nativeSectionFramePresentation L hL s hdense E
  have h := restrictForm_coefficients_eq_sum (canonicalBasis (m + 1)) (Nat.succ_pos m) P c
  have hhaar : haarFactor (canonicalBasis (m + 1)) = 1 := by
    unfold haarFactor
    simp only [addHaar_canonicalBasis, MeasureTheory.Measure.addHaarScalarFactor_self]
  simpa only [hhaar, NNReal.coe_one, one_smul, P, nativeSectionFramePresentation,
    Fin.sum_univ_one, Rat.cast_one] using h

end Current

end SGPT.Projective.NumEq.CompleteIntersections
