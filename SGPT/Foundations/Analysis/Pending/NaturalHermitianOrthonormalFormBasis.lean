import SGPT.Foundations.Analysis.Pending.NaturalHermitianSmoothFormMetric
import SGPT.Foundations.Analysis.Pending.NaturalHermitianUnitVolume

/-! # Actual metric orthonormal coordinate bases of the original forms -/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianOrthonormalFormBasis

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianMusicalInverse NaturalHermitianDualMetric NaturalHermitianExteriorCovectorMetric
  NaturalHermitianOriginalFormMetric NaturalHermitianSmoothFormMetric
  NaturalHermitianUnitVolume NaturalHermitianTopFormOrientation

variable {n : ℕ}

local instance dualNormedAddCommGroup : NormedAddCommGroup (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance dualNormedSpace : NormedSpace ℝ (ComplexModel n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

/-- Actual original continuous basis coordinate covector, in its unchanged original dual norm. -/
def coordinateCovector (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (i : Fin (n * 2)) : ComplexModel n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (b.coord i)

/-- Original metric orthonormality proves the entire coordinate covector is the actual metric dual. -/
theorem coordinateCovector_eq_metric {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (i : Fin (n * 2)) : coordinateCovector b i = associatedMetricCLM a (b i) := by
  have h : (coordinateCovector b i).toLinearMap = (associatedMetricCLM a (b i)).toLinearMap := by
    apply b.ext
    intro j
    change b.coord i (b j) = associatedMetricCLM a (b i) (b j)
    rw [hb]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  exact ContinuousLinearMap.ext (fun v => DFunLike.congr_fun h v)

/-- Genuine original inverse musical calibration on every actual metric coordinate covector. -/
theorem coordinateCovector_inverse {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hp : IsStrictlyPositive a) (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (i : Fin (n * 2)) : (associatedMetricCLM a).inverse (coordinateCovector b i) = b i := by
  rw [coordinateCovector_eq_metric b hb i]
  exact (metric_inverse_identities hp).2 (b i)

/-- The actual dual metric coordinate values follow from the genuine inverse, without a dual-frame assumption. -/
theorem coordinateCovector_dual_metric {a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hp : IsStrictlyPositive a) (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (i j : Fin (n * 2)) :
    dualMetricCLM (associatedMetricCLM a).inverse (coordinateCovector b i) (coordinateCovector b j) =
      if i = j then 1 else 0 := by
  rw [dualMetricCLM_apply, coordinateCovector_inverse hp b hb i]
  simp [coordinateCovector, Module.Basis.coord_apply, Finsupp.single_apply]

variable (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ) (hJ : IsOneOne a) (hp : IsStrictlyPositive a)

/-- Genuine basis on the separate metric covector copy, with the original dual basis readback. -/
def metricCovectorBasis (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) :
    Module.Basis (Fin (n * 2)) ℝ (MetricCovector a hJ hp) :=
  b.dualBasis.map ((LinearMap.toContinuousLinearMap :
    Module.Dual ℝ (ComplexModel n) ≃ₗ[ℝ] (ComplexModel n →L[ℝ] ℝ)).trans
      (metricCovectorLinearEquiv a hJ hp).symm)

/-- Exact underlying original coordinate covectors of the actual metric-copy basis. -/
theorem metricCovectorBasis_val (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (i : Fin (n * 2)) : (metricCovectorBasis a hJ hp b i).val = coordinateCovector b i := by
  change LinearMap.toContinuousLinearMap (b.dualBasis i) = coordinateCovector b i
  rw [Module.Basis.coe_dualBasis]
  rfl

/-- Genuine orthonormality on the actual metric copy, with no norm change on the original dual. -/
theorem metricCovectorBasis_orthonormal (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) :
    Orthonormal ℝ (metricCovectorBasis a hJ hp b) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  change dualMetricCLM (associatedMetricCLM a).inverse
    (metricCovectorBasis a hJ hp b i).val (metricCovectorBasis a hJ hp b j).val = _
  rw [metricCovectorBasis_val, metricCovectorBasis_val]
  exact coordinateCovector_dual_metric hp b hb i j

/-- Actual orthonormal covector basis structure, internally proved from original metric basis values. -/
def metricCovectorOrthonormalBasis (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) :
    OrthonormalBasis (Fin (n * 2)) ℝ (MetricCovector a hJ hp) :=
  (metricCovectorBasis a hJ hp b).toOrthonormalBasis (metricCovectorBasis_orthonormal a hJ hp b hb)

/-- Actual all-degree metric determinant basis on the original form fiber, retaining its operator norm. -/
def metricFormBasis (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ) :
    Module.Basis (FormIndex n q) ℝ (FormCoefficients n q) :=
  ((metricCovectorBasis a hJ hp b).exteriorPower q).map (originalFormLinearEquiv a hJ hp q)

/-- Literal image of the actual exterior basis through the genuine original form dictionary. -/
theorem metricFormBasis_eq_exterior_dictionary
    (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)) (q : ℕ) (s : FormIndex n q) :
    metricFormBasis a hJ hp b q s = originalFormDictionary a hJ hp q
      ((metricCovectorBasis a hJ hp b).exteriorPower q s) := rfl

/-- Actual selected coordinate covectors give exactly the original metric form basis element. -/
theorem metricFormBasis_eq_dictionary (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (q : ℕ) (s : FormIndex n q) :
    metricFormBasis a hJ hp b q s = originalFormDictionary a hJ hp q
      (exteriorCovectorDecomposable a hJ hp q
        (fun i => coordinateCovector b (Set.powersetCard.ofFinEmbEquiv.symm s i))) := by
  rw [metricFormBasis_eq_exterior_dictionary, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  apply congrArg (originalFormDictionary a hJ hp q)
  apply congrArg (exteriorPower.ιMulti ℝ q)
  funext i
  apply (metricCovectorEquiv a hJ hp).injective
  exact metricCovectorBasis_val a hJ hp b (Set.powersetCard.ofFinEmbEquiv.symm s i)

/-- Entire original vector-tuple determinant readback of every actual metric basis element. -/
theorem metricFormBasis_apply (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (q : ℕ) (s : FormIndex n q) (v : Fin q → ComplexModel n) :
    metricFormBasis a hJ hp b q s v = Matrix.det (Matrix.of fun i j =>
      coordinateCovector b (Set.powersetCard.ofFinEmbEquiv.symm s j) (v i)) := by
  rw [metricFormBasis_eq_dictionary, originalFormDictionary_decomposable_apply]

/-- The actual exterior orthonormality calibrates the whole original form metric on every basis pair. -/
theorem metricFormBasis_metric (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (q : ℕ) (s t : FormIndex n q) :
    originalFormMetric a hJ hp q (metricFormBasis a hJ hp b q s) (metricFormBasis a hJ hp b q t) =
      if s = t then 1 else 0 := by
  rw [metricFormBasis_eq_exterior_dictionary, metricFormBasis_eq_exterior_dictionary,
    originalFormMetric_apply, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  let c := metricCovectorOrthonormalBasis a hJ hp b hb
  have hc : c.toBasis = metricCovectorBasis a hJ hp b :=
    Module.Basis.toBasis_toOrthonormalBasis _ _
  have h := orthonormal_iff_ite.mp (c.exteriorPower q).orthonormal s t
  have h' : inner ℝ (c.toBasis.exteriorPower q s) (c.toBasis.exteriorPower q t) =
      if s = t then 1 else 0 := by
    simpa only [← OrthonormalBasis.toBasis_exteriorPower, OrthonormalBasis.coe_toBasis] using h
  rw [hc] at h'
  exact h'

/-- Actual full coefficient coordinate formula for the entire original form metric on arbitrary tensors. -/
theorem metricFormBasis_metric_expansion (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (q : ℕ) (η θ : FormCoefficients n q) :
    originalFormMetric a hJ hp q η θ = ∑ s : FormIndex n q,
      (metricFormBasis a hJ hp b q).repr η s * (metricFormBasis a hJ hp b q).repr θ s := by
  conv_lhs =>
    rw [← (metricFormBasis a hJ hp b q).sum_repr η,
      ← (metricFormBasis a hJ hp b q).sum_repr θ]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    metricFormBasis_metric a hJ hp b hb q, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

/-- Genuine entire original metric sum-of-squares formula, including nondecomposable tensors. -/
theorem metricFormBasis_metric_self (b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (q : ℕ) (η : FormCoefficients n q) :
    originalFormMetric a hJ hp q η η = ∑ s : FormIndex n q,
      ((metricFormBasis a hJ hp b q).repr η s) ^ 2 := by
  rw [metricFormBasis_metric_expansion a hJ hp b hb q η η]
  simp only [pow_two]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Original Hermitian data internally supplies all actual metric bases, full coefficient formulas and unit volume. -/
theorem exists_original_chart_metric_form_bases (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    let a := w.coeff e z
    let hJ := (hw e z hz).1
    let hp := (hw e z hz).2
    ∃ b : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n),
      (∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) ∧
      b.orientation = (coordinateRealBasis n).orientation ∧
      (∀ q : ℕ,
        (∀ s t : FormIndex n q, formMetricCoefficients w e z q
          (metricFormBasis a hJ hp b q s) (metricFormBasis a hJ hp b q t) = if s = t then 1 else 0) ∧
        (∀ η θ : FormCoefficients n q, formMetricCoefficients w e z q η θ =
          ∑ s : FormIndex n q, (metricFormBasis a hJ hp b q).repr η s *
            (metricFormBasis a hJ hp b q).repr θ s) ∧
        ∀ η : FormCoefficients n q, formMetricCoefficients w e z q η η =
          ∑ s : FormIndex n q, ((metricFormBasis a hJ hp b q).repr η s) ^ 2) ∧
      ∀ v : Fin (n * 2) → ComplexModel n, (normalizedHermitianTopForm w).coeff e z v = b.det v := by
  obtain ⟨b, hb, ho⟩ := (original_chart_unit_volume w hw e z hz).1
  refine ⟨b, hb, ho, ?_, ?_⟩
  · intro q
    simp only [formMetricCoefficients_eq_original w hw e z hz q]
    exact ⟨metricFormBasis_metric (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb q,
      metricFormBasis_metric_expansion (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb q,
      metricFormBasis_metric_self (w.coeff e z) (hw e z hz).1 (hw e z hz).2 b hb q⟩
  · exact (original_chart_unit_volume w hw e z hz).2 b hb ho

end SGPT.Foundations.Analysis.Pending.NaturalHermitianOrthonormalFormBasis
