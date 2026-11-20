import SGPT.Foundations.Analysis.Pending.ThetaCurrentModificationGlobalACTransport
import SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
import SGPT.Foundations.Analysis.Pending.UniformNefCoreSupport

set_option autoImplicit false

/-!
# Actual pushforward reference-volume convergence

The smooth reference volumes of `pi*omega + delta*omegaY` converge after
pushforward to the original Kahler volume along any filter with delta → 0.
The endpoint measure and the finite polynomial integral are internally proved.
Reference: Boucksom, Theorem 4.6, supplementary descent calculation.
The complete blueprint statements and ENTIRE proofs precede this source.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.ModificationReferenceVolumeLimit
open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.GlobalAnalyticSingularities FirstPass.NumericalRestrictedVolumeScaffold
  IntegrationCurrent NefMixedMass ProductTestForms GlobalNonPluripolar
  MixedMassClassInvariance TopDegreeDensity SmoothCurrentTraceMeasure
  UniformNefCoreSupport BoundedGlobalProduct AnalyticModificationLocalDiscrepancy
  NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
  GlobalPositiveCurrentACTopMeasure AnalyticModificationStrongPullback

private theorem zero_has_analytic_type
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (fun _ : M => 0) := by
  intro e z _
  let one : Fin 1 → ComplexModel n → ℂ := fun _ _ => 1
  have hlog (y : ComplexModel n) : generatorLog one y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  refine ⟨1, 1, one, one_pos, ⟨univ, isOpen_univ, mem_univ _,
    fun _ => differentiableOn_const 1⟩, fun _ => 0,
    boundedRealGermAt_of_continuousAt continuousAt_const,
    Eventually.of_forall fun _ _ => contDiffAt_const,
    Eventually.of_forall fun y => ?_⟩
  simp only [chartFunction, hlog, mul_zero, EReal.coe_zero, add_zero]

variable {m : ℕ} {X Y : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel (m+1)) X] [IsComplexManifold (m+1) X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace (ComplexModel (m+1)) Y] [IsComplexManifold (m+1) Y]

/-- The actual smooth zero-potential product measure pushes forward to the
original Kahler volume; all positivity and compactness are internal. -/
theorem map_zero_reference_measure [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ω : KahlerBackground (m+1) X) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    let A := ClosedRealOneOneForm.pullback hπ.1 ω.form
    let hA := (LocalPotentials.thetaPlurisubharmonic_zero_iff A).mpr
      (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ω.isSemipositive)
    (globalMixedMeasure (fun _ : Fin (m+1) => A) (fun _ _ => 0) (fun _ => hA)).map π =
      kahlerVolume ω := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let A := ClosedRealOneOneForm.pullback hπ.1 ω.form
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive
  obtain ⟨huY, hmap⟩ :=
    ThetaCurrentModificationGlobalACTransport.exists_global_original_ac_transport hπ ω.form hu
  have hX := OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
    ω.form hu zero_has_analytic_type
  have hY := OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
    A huY zero_has_analytic_type
  dsimp only at hmap
  rw [hY, hX] at hmap
  exact hmap

section WeightedPolynomial
variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

private theorem integrable_mul_topRatio (ω : KahlerBackground n M)
    (g : M → ℝ) (hg : Continuous g) (Φ : SmoothRealForm n M (2*n)) :
    Integrable (fun y => g y * topRatio ω.form.val Φ y) (kahlerVolume ω) :=
  (hg.mul (continuous_topRatio ω.isKahler.1 Φ)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))

private theorem weighted_integral_add_smul_eq_sum (ω : KahlerBackground n M)
    (A B : Fin n → ClosedRealOneOneForm n M) (g : M → ℝ) (hg : Continuous g) (t : ℝ) :
    (∫ y, g y * topRatio ω.form.val (slotForm fun j => A j + t • B j) y ∂kahlerVolume ω) =
      ∑ s : Finset (Fin n), (∏ j, if j ∈ s then (1 : ℝ) else t) *
        ∫ y, g y * topRatio ω.form.val (slotForm (s.piecewise A B)) y ∂kahlerVolume ω := by
  classical
  simp_rw [topRatio_slotForm_add_smul, Finset.mul_sum]
  have heq (s : Finset (Fin n)) (y : M) :
      g y * ((∏ j, if j ∈ s then (1 : ℝ) else t) *
          topRatio ω.form.val (slotForm (s.piecewise A B)) y) =
      (∏ j, if j ∈ s then (1 : ℝ) else t) *
        (g y * topRatio ω.form.val (slotForm (s.piecewise A B)) y) := by ring
  simp_rw [heq]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun _ _ => integral_const_mul _ _
  · intro s _
    exact (integrable_mul_topRatio ω g hg _).const_mul _

private theorem continuous_weighted_integral_add_smul (ω : KahlerBackground n M)
    (A B : Fin n → ClosedRealOneOneForm n M) (g : M → ℝ) (hg : Continuous g) :
    Continuous fun t : ℝ =>
      ∫ y, g y * topRatio ω.form.val (slotForm fun j => A j + t • B j) y ∂kahlerVolume ω := by
  classical
  simp_rw [weighted_integral_add_smul_eq_sum ω A B g hg]
  exact continuous_finsetSum _ fun s _ => Continuous.mul (continuous_finsetProd _ fun j _ =>
    continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id) continuous_const

end WeightedPolynomial

private theorem integral_kahlerVolume_eq_weighted [CompactSpace Y]
    (ω Ω : KahlerBackground (m+1) Y) (g : Y → ℝ) :
    (∫ y, g y ∂kahlerVolume Ω) =
      ∫ y, g y * topRatio ω.form.val (slotForm fun _ => Ω.form) y ∂kahlerVolume ω := by
  rw [← withDensity_topRatio_formPow ω Ω,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun y => ENNReal.ofReal (topRatio ω.form.val (formPow Ω.form.val (m+1)) y))
      (ENNReal.measurable_ofReal.comp (continuous_topRatio ω.isKahler.1 _).measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hnonneg : 0 ≤ topRatio ω.form.val (formPow Ω.form.val (m+1)) y := by
    rw [topRatio_formPow_eq_slotForm]
    exact topRatio_slotForm_nonneg ω (fun _ => Ω.isSemipositive) y
  rw [ENNReal.toReal_ofReal hnonneg,
    smul_eq_mul, mul_comm, topRatio_formPow_eq_slotForm]

private theorem integral_zero_measure_eq_weighted [CompactSpace Y]
    (ω : KahlerBackground (m+1) Y) (A : ClosedRealOneOneForm (m+1) Y)
    (hA : ThetaPlurisubharmonic A.val (fun _ => 0)) (g : Y → ℝ) :
    (∫ y, g y ∂globalMixedMeasure (fun _ : Fin (m+1) => A) (fun _ _ => 0) (fun _ => hA)) =
      ∫ y, g y * topRatio ω.form.val (slotForm fun _ => A) y ∂kahlerVolume ω := by
  rw [← withDensity_topRatio_eq_globalMixedMeasure ω (slotForm fun _ => A) (fun _ => hA)
      (fun e z _ => topDensity_slotForm_coeff _ e z),
    integral_withDensity_eq_integral_toReal_smul
      (f := fun y => ENNReal.ofReal (topRatio ω.form.val (slotForm fun _ => A) y))
      (ENNReal.measurable_ofReal.comp (continuous_topRatio ω.isKahler.1 _).measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hsemi := (LocalPotentials.thetaPlurisubharmonic_zero_iff A).mp hA
  apply integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [ENNReal.toReal_ofReal (topRatio_slotForm_nonneg ω (fun _ => hsemi) y), smul_eq_mul,
    mul_comm]

/-- All continuous original-space tests converge for the actual geometric
reference family, along any filter. No calibration or limit is supplied. -/
theorem tendsto_integral_map_reference_volume [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := m+1) π)
    (ω : KahlerBackground (m+1) X) (ωY : KahlerBackground (m+1) Y)
    {ι : Type*} {l : Filter ι} (δ : ι → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (Ω : ι → KahlerBackground (m+1) Y)
    (hΩ : ∀ i, (Ω i).form = ClosedRealOneOneForm.pullback hπ.1 ω.form + δ i • ωY.form)
    (f : X → ℝ) (hf : Continuous f) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    Tendsto (fun i => ∫ x, f x ∂(kahlerVolume (Ω i)).map π) l
      (𝓝 (∫ x, f x ∂kahlerVolume ω)) := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let A := ClosedRealOneOneForm.pullback hπ.1 ω.form
  have hA := (LocalPotentials.thetaPlurisubharmonic_zero_iff A).mpr
    (ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ω.isSemipositive)
  let g : Y → ℝ := fun y => f (π y)
  have hg : Continuous g := hf.comp hπ.1.continuous
  have hlim := (continuous_weighted_integral_add_smul ωY (fun _ => A)
    (fun _ => ωY.form) g hg).tendsto 0 |>.comp hδ
  have htest (i : ι) : (∫ x, f x ∂(kahlerVolume (Ω i)).map π) =
      ∫ y, g y * topRatio ωY.form.val
        (slotForm fun _ => A + δ i • ωY.form) y ∂kahlerVolume ωY := by
    rw [integral_map hπ.1.continuous.measurable.aemeasurable hf.aestronglyMeasurable,
      integral_kahlerVolume_eq_weighted ωY (Ω i), hΩ i]
  have hend : (∫ x, f x ∂kahlerVolume ω) =
      ∫ y, g y * topRatio ωY.form.val (slotForm fun _ => A) y ∂kahlerVolume ωY := by
    rw [← map_zero_reference_measure hπ ω,
      integral_map hπ.1.continuous.measurable.aemeasurable hf.aestronglyMeasurable,
      integral_zero_measure_eq_weighted ωY A hA]
  have hfun : (fun i => ∫ x, f x ∂(kahlerVolume (Ω i)).map π) =
      (fun t : ℝ => ∫ y, g y * topRatio ωY.form.val
        (slotForm fun _ => A + t • ωY.form) y ∂kahlerVolume ωY) ∘ δ := funext htest
  rw [hfun, hend]
  simpa only [zero_smul, add_zero] using hlim

end SGPT.Foundations.Analysis.Pending.ModificationReferenceVolumeLimit
