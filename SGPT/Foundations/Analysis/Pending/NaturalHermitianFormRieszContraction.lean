import SGPT.Foundations.Analysis.Pending.NaturalHermitianOrthonormalFormBasis
import SGPT.Foundations.Analysis.Pending.NaturalOriginalComplementaryWedgeDuality

set_option autoImplicit false

/-! Genuine original form metric Riesz maps and actual metric volume contractions. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFormRieszContraction

open FirstPass FirstPass.MongeAmpere NaturalHermitianMetricCoefficients
  NaturalHermitianMusicalInverse NaturalHermitianOriginalFormMetric
  NaturalHermitianExteriorCovectorMetric NaturalHermitianSmoothFormMetric
  NaturalHermitianOrthonormalFormBasis NaturalOriginalComplementaryWedgeDuality
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {n : ℕ}

local instance formNormedAddCommGroup (j : ℕ) : NormedAddCommGroup (FormCoefficients n j) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (j : ℕ) : NormedSpace ℝ (FormCoefficients n j) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (j : ℕ) :
    NormedAddCommGroup (FormCoefficients n j →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (j : ℕ) : NormedSpace ℝ (FormCoefficients n j →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

variable (a : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ)
  (hJ : IsOneOne a) (hp : IsStrictlyPositive a)

/-- Strict positivity internally proves invertibility of the actual original form metric map. -/
theorem formMetricRiesz_invertible (q : ℕ) : (originalFormMetric a hJ hp q).IsInvertible := by
  have hker : (originalFormMetric a hJ hp q).ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro η hη
    change η = 0
    change originalFormMetric a hJ hp q η = 0 at hη
    by_contra hne
    have hzero := congrArg (fun L : FormCoefficients n q →L[ℝ] ℝ => L η) hη
    exact ((originalFormMetric_symm_positive a hJ hp q).2 η hne).ne'
      (by simpa only [zero_apply] using hzero)
  have hdim : Module.finrank ℝ (FormCoefficients n q) =
      Module.finrank ℝ (FormCoefficients n q →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ (FormCoefficients n q) =
          Module.finrank ℝ (Module.Dual ℝ (FormCoefficients n q)) := Subspace.dual_finrank_eq.symm
      _ = Module.finrank ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : Module.Dual ℝ (FormCoefficients n q) ≃ₗ[ℝ]
          (FormCoefficients n q →L[ℝ] ℝ)).finrank_eq
  have hrange : (originalFormMetric a hJ hp q).range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    exact LinearMap.ker_eq_bot.mp hker
  exact ⟨ContinuousLinearEquiv.ofBijective (originalFormMetric a hJ hp q) hker hrange,
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- Genuine Riesz equivalence in the unchanged original form and dual operator norms. -/
def formMetricRieszEquiv (q : ℕ) : FormCoefficients n q ≃L[ℝ] (FormCoefficients n q →L[ℝ] ℝ) :=
  Classical.choose (formMetricRiesz_invertible a hJ hp q)

theorem formMetricRieszEquiv_toCLM (q : ℕ) :
    (formMetricRieszEquiv a hJ hp q : FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) =
      originalFormMetric a hJ hp q := Classical.choose_spec (formMetricRiesz_invertible a hJ hp q)

/-- Both identities of the actual total continuous inverse, proved in every natural degree. -/
theorem formMetricRiesz_inverse_identities (q : ℕ) :
    (∀ L : FormCoefficients n q →L[ℝ] ℝ,
      originalFormMetric a hJ hp q ((originalFormMetric a hJ hp q).inverse L) = L) ∧
    ∀ η : FormCoefficients n q,
      (originalFormMetric a hJ hp q).inverse (originalFormMetric a hJ hp q η) = η := by
  rcases formMetricRiesz_invertible a hJ hp q with ⟨A, hA⟩
  rw [← hA, ContinuousLinearMap.inverse_equiv]
  exact ⟨A.apply_symm_apply, A.symm_apply_apply⟩

/-- The actual original determinant form of an arbitrary tuple of metric covectors. -/
def metricTupleForm {q : ℕ} (v : Fin q → ComplexModel n) : FormCoefficients n q :=
  originalFormDictionary a hJ hp q
    (exteriorCovectorDecomposable a hJ hp q (fun i => associatedMetricCLM a (v i)))

theorem metricTupleForm_apply {q : ℕ} (v u : Fin q → ComplexModel n) :
    metricTupleForm a hJ hp v u = Matrix.det (Matrix.of fun i j =>
      associatedMetricCLM a (v j) (u i)) :=
  originalFormDictionary_decomposable_apply a hJ hp q _ u

/-- Entire metric evaluation identity, without orthonormality of the tuple or decomposability. -/
theorem form_metric_tuple_evaluation {q : ℕ} (η : FormCoefficients n q)
    (v : Fin q → ComplexModel n) :
    originalFormMetric a hJ hp q η (metricTupleForm a hJ hp v) = η v := by
  let b := coordinateRealBasis n
  let B := metricFormBasis a hJ hp b q
  have h : ((originalFormMetric a hJ hp q).flip (metricTupleForm a hJ hp v)).toLinearMap =
      (formEvaluationCLM v).toLinearMap := by
    apply B.ext
    intro s
    change originalFormMetric a hJ hp q (metricFormBasis a hJ hp b q s)
      (metricTupleForm a hJ hp v) = metricFormBasis a hJ hp b q s v
    rw [metricFormBasis_eq_dictionary, metricTupleForm, originalFormMetric_decomposable,
      originalFormDictionary_decomposable_apply]
    congr 1
    ext i j
    change associatedMetricCLM a (v i)
      ((associatedMetricCLM a).inverse
        (coordinateCovector b (Set.powersetCard.ofFinEmbEquiv.symm s j))) = _
    rw [associatedMetricCLM_apply, associatedMetric_symm hJ]
    simpa only [associatedMetricCLM_apply, Matrix.of_apply] using
      congrArg (fun α : ComplexModel n →L[ℝ] ℝ => α (v i))
        ((metric_inverse_identities hp).1
          (coordinateCovector b (Set.powersetCard.ofFinEmbEquiv.symm s j)))
  exact LinearMap.congr_fun h η

/-- An actual orthonormal split basis has literal original coordinate metric covectors. -/
theorem orthonormal_split_coordinate_metric {k q : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (i : Fin k ⊕ Fin q) :
    LinearMap.toContinuousLinearMap (b.coord i) = associatedMetricCLM a (b i) := by
  have h : (LinearMap.toContinuousLinearMap (b.coord i)).toLinearMap =
      (associatedMetricCLM a (b i)).toLinearMap := by
    apply b.ext
    intro j
    change b.coord i (b j) = associatedMetricCLM a (b i) (b j)
    rw [hb]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]
  exact ContinuousLinearMap.ext (fun v => DFunLike.congr_fun h v)

/-- Actual whole normalized volume contraction on the right basis block equals its metric form. -/
theorem rightVolumeContraction_basis_metric {k q : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0) :
    rightVolumeContraction (basisVolume b) (fun j => b (Sum.inr j)) =
      metricTupleForm a hJ hp (fun i => b (Sum.inl i)) := by
  classical
  ext u
  rw [rightVolumeContraction_apply, basisVolume_apply, metricTupleForm_apply]
  change (b.toMatrix (Sum.elim u (fun j => b (Sum.inr j)))).det = _
  let A : Matrix (Fin k) (Fin k) ℝ := fun i j => b.coord (Sum.inl i) (u j)
  let C : Matrix (Fin q) (Fin k) ℝ := fun i j => b.coord (Sum.inr i) (u j)
  have hmat : b.toMatrix (Sum.elim u (fun j => b (Sum.inr j))) =
      Matrix.fromBlocks A 0 C 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · simp [Module.Basis.toMatrix_apply]
    · rfl
    · simp [Module.Basis.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
  rw [hmat, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  have htranspose : (Matrix.of fun i j => associatedMetricCLM a (b (Sum.inl j)) (u i)) =
      A.transpose := by
    ext i j
    exact (congrArg (fun α : ComplexModel n →L[ℝ] ℝ => α (u i))
      (orthonormal_split_coordinate_metric a b hb (Sum.inl j))).symm
  rw [htranspose, Matrix.det_transpose]

/-- Entire original metric pairing with an actual normalized basis-volume contraction. -/
theorem form_metric_volume_contraction_evaluation {k q : ℕ}
    (b : Module.Basis (Fin k ⊕ Fin q) ℝ (ComplexModel n))
    (hb : ∀ i j, associatedMetricCLM a (b i) (b j) = if i = j then 1 else 0)
    (η : FormCoefficients n k) :
    originalFormMetric a hJ hp k η
      (rightVolumeContraction (basisVolume b) (fun j => b (Sum.inr j))) =
        η (fun i => b (Sum.inl i)) := by
  rw [rightVolumeContraction_basis_metric a hJ hp b hb]
  exact form_metric_tuple_evaluation a hJ hp η _

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFormRieszContraction
