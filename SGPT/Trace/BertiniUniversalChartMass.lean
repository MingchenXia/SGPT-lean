import SGPT.Trace.BertiniUniversalTargetProduct
import SGPT.Trace.BertiniUniversalProductIntegrability

/-! Actual original global multiplier H0 gives finite SAME norm density
in every compact native X chart and the literal retained q product. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft

section General
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (B : HermitianHolomorphicLineBundle.{0,0} n X) (φ : X → EReal)
  (hφ : IsGlobalQuasiPshPotential (n := n) φ) (T : nativeMultiplierSections B φ)
  (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) (e : ComplexChart n X)

include hφ μ hμ
theorem originalMultiplier_chart_integral_lt_top {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    (∫⁻ z in K, originalSectionDensity B.Fiber φ 1 T.val (e.val.symm z)) < ⊤ := by
  let f := originalSectionDensity B.Fiber φ 1 T.val
  have hf : Measurable f := measurable_originalSectionDensity B.Fiber hφ.1.upperSemicontinuous.measurable 1 T.val
  have hglobal : (∫⁻ x, f x ∂μ) < ⊤ := by
    simpa only [f,Nat.cast_one] using
      (fullHolomorphicDegreeIdealSections_iff_finite_integral B.Fiber 1 hφ T.val hμ).mp T.property
  obtain ⟨ρ,hρ,hρpos,hmap⟩ := hμ e
  have hweighted : (∫⁻ z in K, ENNReal.ofReal (ρ z) * f (e.val.symm z)) < ⊤ := by
    rw [← setLIntegral_source_inter_preimage e hρ.continuousOn hmap hK hKt hf]
    exact (setLIntegral_le_lintegral _ f).trans_lt hglobal
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀,hz₀,hmin⟩ := hK.exists_isMinOn hne (hρ.continuousOn.mono hKt)
  have ha : 0 < ρ z₀ := hρpos z₀ (hKt hz₀)
  have hbound : (∫⁻ z in K, f (e.val.symm z)) ≤
      (ENNReal.ofReal (ρ z₀))⁻¹ * ∫⁻ z in K, ENNReal.ofReal (ρ z) * f (e.val.symm z) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    have hmin' : ENNReal.ofReal (ρ z₀) ≤ ENNReal.ofReal (ρ z) := ENNReal.ofReal_le_ofReal (hmin hz)
    calc
      f (e.val.symm z) = (ENNReal.ofReal (ρ z₀))⁻¹ * (ENNReal.ofReal (ρ z₀) * f (e.val.symm z)) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top,one_mul]
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' hmin' le_rfl)
  exact hbound.trans_lt (ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha)))) hweighted)

theorem originalMultiplier_product_chart_integral_lt_top {k : ℕ}
    (b : ComplexModel k) (R : ℝ) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    (∫⁻ u in (closedBall b R) ×ˢ K,
      originalSectionDensity B.Fiber φ 1 T.val (e.val.symm u.2) ∂volume.prod volume) < ⊤ := by
  rw [← Measure.prod_restrict]
  calc
    _ ≤ ∫⁻ _b : ComplexModel k, (∫⁻ z in K,
      originalSectionDensity B.Fiber φ 1 T.val (e.val.symm z)) ∂volume.restrict (closedBall b R) := lintegral_prod_le _
    _ = (∫⁻ z in K, originalSectionDensity B.Fiber φ 1 T.val (e.val.symm z)) *
      volume (closedBall b R) := by rw [lintegral_const,Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top
      (originalMultiplier_chart_integral_lt_top B φ hφ T μ hμ e hK hKt) (measure_closedBall_lt_top)

end General
section Retained
variable {k d : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel (d + 1)) X]
  [IsComplexManifold (d + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (B : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (φ : X → EReal)
  (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) (T : nativeMultiplierSections B φ)
  (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := d + 1) μ) (e : ComplexChart (d + 1) X)

include hφ μ hμ
theorem originalMultiplier_retained_chart_integral_lt_top
    (m : Fin (k + 1)) (b : ComplexModel k) (R : ℝ) {K : Set (ComplexModel (d + 1))}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    (∫⁻ y in deletedParameterProductEquiv k d '' ((closedBall b R) ×ˢ K),
      originalSectionDensity B.Fiber φ 1 T.val
        (e.val.symm (originalQTargetXCoordinates (d := d) m y))) < ⊤ := by
  have hemb : MeasurableEmbedding (deletedParameterProductEquiv k d) :=
    (deletedParameterProductEquiv k d).toHomeomorph.measurableEmbedding
  rw [← (measurePreserving_deletedParameterProductEquiv k d).setLIntegral_comp_emb hemb]
  have hreader (u : ComplexModel k × ComplexModel (d + 1)) :
      originalQTargetXCoordinates (d := d) m (deletedParameterProductEquiv k d u) = u.2 := by
    rcases u with ⟨b,z⟩
    exact originalQTargetXCoordinates_product k d m b z
  simp_rw [hreader]
  exact originalMultiplier_product_chart_integral_lt_top B φ hφ T μ hμ e b R hK hKt
end Retained
end SGPT.Trace.BertiniUniversal
