import SGPT.Projective.OkounkovOriginalBookPartial

/-! Positive ORIGINAL I-volume gives EXISTING actual ORIGINAL h0-growth bigness, every dimension.
Blueprint: okounkov-original-big-of-ivolume.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalBook
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.AlgebraicValuation
open scoped Topology ENNReal
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
local instance bigOfIVolumeTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance bigOfIVolumeCharts {n : ℕ} [SmoothOfRelativeDimension n f] : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance bigOfIVolumeManifold {n : ℕ} [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual positive ORIGINAL I-volume manufactures true original algebraic section growth, ALL dimensions. -/
theorem original_isBig_of_positive_iVolume_allDimensions
    (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact; IsThetaPshPotential (H.curvature a).val φ)
    (hpos : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      0 < iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ) :
    SGPT.LineBundle.IsBig f L n := by
  let := E.isSeparated
  let := E.quasiCompact
  let : MeasurableSpace (SchemeComplexPoint f) := borel _
  have : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨Y,hY⟩ := exists_original_smoothFlag_allDimensions f n E
  cases n with
  | zero => exact PobDimZero.isBig f E Y hY a
  | succ m =>
    let V : ℝ := (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ).toReal /
      ((m+1).factorial:ℝ)
    have hfinite := original_iVolume_ne_top_allDimensions f (m+1) E a H hφ
    have hV : 0<V := div_pos (ENNReal.toReal_pos hpos.ne' hfinite) (by exact_mod_cast Nat.factorial_pos (m+1))
    have hlim := ValGen.tendsto_normalized_multiplierH0 f E Y hY a H hφ
    rw [AlgPOB.volume_real_generalPartialBody f E Y hY a H hφ] at hlim
    refine ⟨V/2,half_pos hV,?_⟩
    filter_upwards [(tendsto_order.mp hlim).1 (V/2) (by linarith),eventually_gt_atTop 0] with k hk hk0
    have hkpow : (0:ℝ)<(k:ℝ)^(m+1) := pow_pos (by exact_mod_cast hk0) _
    have hh : V/2≤(SGPT.IGood.DXMain.multiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic L k:ℝ)/(k:ℝ)^(m+1) := by
      calc
        _ ≤ (k:ℝ)⁻¹^(m+1)*(SGPT.IGood.DXMain.multiplierH0 f (m+1) E hφ.1.quasiPlurisubharmonic L k:ℝ) := hk.le
        _ = _ := by rw [div_eq_mul_inv,inv_pow,mul_comm]
    have hlow := (le_div_iff₀ hkpow).mp hh
    exact hlow.trans (by exact_mod_cast SGPT.IGood.DXMain.multiplierH0_le_h0 f (m+1) E hφ.1.quasiPlurisubharmonic a k)
end SGPT.Okounkov.OriginalBook
