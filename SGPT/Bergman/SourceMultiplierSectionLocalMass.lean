import SGPT.Bergman.SourceMultiplierSectionDensity

/-!
# MultiplierSectionLocalMass

Local finiteness of `∫ |s|² e^{-cφ}` against a smooth positive volume, compared in charts.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

variable [MeasurableSpace X] [BorelSpace X] [ContinuousFiberNorm V]

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Exact original change of variables for the SAME full Hermitian density, including infinite weights. -/
theorem originalSection_setLIntegral_chart {φ : X → EReal} (hφ : Measurable φ) (c : ℝ)
    (s : HolomorphicSections (n := n) V) (e : OriginalFrame V) (a : ComplexChart n X)
    {μ : Measure X} {ρ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ a.val.target)
    (hρpos : ∀ z ∈ a.val.target, 0 < ρ z)
    (hmap : Measure.map a.val (μ.restrict a.val.source) =
      (volume.restrict a.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ a.val.target)
    (hKe : ∀ z ∈ K, a.val.symm z ∈ e.val.baseSet) :
    (∫⁻ x in a.val.source ∩ a.val ⁻¹' K, originalSectionDensity (n := n) V φ c s x ∂μ) =
      ∫⁻ z in K, ENNReal.ofReal (ρ z * frameNorm V e.val (a.val.symm z) ^ 2) *
        multiplierDensity (chartFunction φ a) c (sectionCoefficient V e.val s ∘ a.val.symm) z := by
  rw [setLIntegral_source_inter_preimage a hρ hmap hK hKt
    (measurable_originalSectionDensity (n := n) V hφ c s)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
  rw [originalSectionDensity_frame (n := n) V φ c e s (hKe z hz),
    ENNReal.ofReal_mul (hρpos z (hKt hz)).le, mul_assoc]
  rfl

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Genuine positive metric and smooth-volume density INTERNALLY give BOTH finite-mass comparisons
on every true compact original chart set. No finite-integral bound is an incoming certificate. -/
theorem originalSection_setLIntegral_finite_iff {φ : X → EReal} (hφ : Measurable φ) (c : ℝ)
    (s : HolomorphicSections (n := n) V) (e : OriginalFrame V) (a : ComplexChart n X)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ a.val.target)
    (hKe : ∀ z ∈ K, a.val.symm z ∈ e.val.baseSet) :
    (∫⁻ x in a.val.source ∩ a.val ⁻¹' K, originalSectionDensity (n := n) V φ c s x ∂μ) < ⊤ ↔
      (∫⁻ z in K, multiplierDensity (chartFunction φ a) c
        (sectionCoefficient V e.val s ∘ a.val.symm) z) < ⊤ := by
  let := e.property
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ a
  rw [originalSection_setLIntegral_chart (n := n) V hφ c s e a hρs.continuousOn hρpos hmap hK hKt hKe]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  let g : ComplexModel n → ℝ := fun z => ρ z * frameNorm V e.val (a.val.symm z) ^ 2
  let D := multiplierDensity (chartFunction φ a) c (sectionCoefficient V e.val s ∘ a.val.symm)
  have hgc : ContinuousOn g K := (hρs.continuousOn.mono hKt).mul
    (((frameNorm_continuousOn V e.val).comp (a.val.continuousOn_symm.mono hKt) hKe).pow 2)
  have hgp : ∀ z ∈ K, 0 < g z := fun z hz =>
    mul_pos (hρpos z (hKt hz)) (sq_pos_of_pos (frameNorm_pos V e.val (hKe z hz)))
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hgc
  have hg₀ : 0 < g z₀ := hgp z₀ hz₀
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hgc
  constructor
  · intro hf
    have hb : (∫⁻ z in K, D z) ≤ ENNReal.ofReal (g z₀)⁻¹ *
        ∫⁻ z in K, ENNReal.ofReal (g z) * D z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
      rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hg₀.le)]
      apply le_mul_of_one_le_left zero_le
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [inv_mul_eq_div, le_div_iff₀ hg₀, one_mul]
      exact hmin hz
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  · intro hf
    have hb : (∫⁻ z in K, ENNReal.ofReal (g z) * D z) ≤
        ENNReal.ofReal B * ∫⁻ z in K, D z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
      gcongr
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))
    exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end SGPT.Bergman.MultiplierSectionsDraft
