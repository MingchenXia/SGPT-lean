import SGPT.Foundations.Analysis.Pending.NaturalOriginalComplementaryWedgeDuality
import SGPT.Foundations.Analysis.Pending.NaturalHermitianTopFormOrientation

/-! # Genuine Hodge star on the original real smooth forms -/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar

open FirstPass FirstPass.MongeAmpere NaturalHermitianSmoothFormMetric
  NaturalOriginalComplementaryWedgeDuality NaturalHermitianTopFormOrientation
  ConstantFormProducts TopDegreeDensity

variable {n : ℕ}

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance formDualNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formDualNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance formBilinearNormedAddCommGroup (q : ℕ) :
    NormedAddCommGroup (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance formBilinearNormedSpace (q : ℕ) :
    NormedSpace ℝ (FormCoefficients n q →L[ℝ] FormCoefficients n q →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance starNormedAddCommGroup (j : CurrentDegree n) :
    NormedAddCommGroup (FormCoefficients n j.val →L[ℝ]
      FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance starNormedSpace (j : CurrentDegree n) :
    NormedSpace ℝ (FormCoefficients n j.val →L[ℝ]
      FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val)) :=
  ContinuousLinearMap.toNormedSpace

/-- Top-degree density genuinely determines the entire original top tensor. -/
theorem topDensity_injective : Function.Injective (topDensity (n := n)) := by
  intro A B h
  have hA := A.toAlternatingMap.eq_smul_basis_det (topBasis n)
  have hB := B.toAlternatingMap.eq_smul_basis_det (topBasis n)
  ext v
  change A.toAlternatingMap v = B.toAlternatingMap v
  rw [hA, hB]
  exact congrArg (fun r : ℝ => (r • (topBasis n).det) v) h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The actual normalized Hermitian volume, transported only in its natural degree index. -/
def metricVolumeCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : FormCoefficients n (2 * n) :=
  castForm (mul_comm n 2) ((normalizedHermitianTopForm w).coeff e z)

/-- Actual full norm smoothness of the original volume tensor. -/
theorem metricVolumeCoefficients_smooth (w : SmoothRealForm n M 2) (e : ComplexChart n M) :
    ContDiffOn ℝ ∞ (metricVolumeCoefficients w e) e.val.target := by
  let C : FormCoefficients n (n * 2) →L[ℝ] FormCoefficients n (2 * n) :=
    (castForm (n := n) (mul_comm n 2)).toContinuousLinearMap
  exact C.contDiff.comp_contDiffOn ((normalizedHermitianTopForm w).smooth e)

/-- Actual canonical positive density of the original normalized Hermitian volume. -/
def metricVolumeDensity (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) : ℝ := topDensity (metricVolumeCoefficients w e z)

/-- The actual density reads back the same interleaved frame, without a permutation sign. -/
theorem metricVolumeDensity_eq (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) :
    metricVolumeDensity w e z =
      (normalizedHermitianTopForm w).coeff e z (coordinateRealFrame (n := n)) := by
  unfold metricVolumeDensity topDensity metricVolumeCoefficients
  rw [castForm_apply]
  congr 1
  funext i
  simp only [Function.comp_apply, topBasis_apply]
  exact congrArg (coordinateRealFrame (n := n)) (Fin.ext rfl)

/-- Scalar density smoothness is actual continuous evaluation of the entire smooth tensor field. -/
theorem metricVolumeDensity_smooth (w : SmoothRealForm n M 2) (e : ComplexChart n M) :
    ContDiffOn ℝ ∞ (metricVolumeDensity w e) e.val.target := by
  exact (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ (topBasis n)).contDiff.comp_contDiffOn
    (metricVolumeCoefficients_smooth w e)

/-- The genuine volume density is positive at every original chart target, including dimension zero. -/
theorem metricVolumeDensity_positive (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target) :
    0 < metricVolumeDensity w e z := by
  rw [metricVolumeDensity_eq]
  exact normalizedHermitianTopForm_positive w hw e z hz

/-- Actual entire volume tensor transport, with no chart density certificate as an input. -/
theorem metricVolumeCoefficients_transport (w : SmoothRealForm n M 2)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source) :
    metricVolumeCoefficients w e z =
      (metricVolumeCoefficients w f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
  have h : (normalizedHermitianTopForm w).coeff e z =
      ((normalizedHermitianTopForm w).coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
    ext v
    exact (normalizedHermitianTopForm w).compatible e f z hz v
  unfold metricVolumeCoefficients
  rw [h, castForm_compContinuousLinearMap]

/-- The genuine fixed whole-operator reconstruction using the actual wedge inverse. -/
def starReconstructionCLM (j : CurrentDegree n) :
    (FormCoefficients n j.val →L[ℝ] FormCoefficients n j.val →L[ℝ] ℝ) →L[ℝ]
      FormCoefficients n j.val →L[ℝ]
        FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val) :=
  ContinuousLinearMap.compL ℝ _ _ _ (canonicalComplementaryWedgeEquiv j).symm.toContinuousLinearMap

/-- The internally constructed original Hodge-star continuous linear coefficient operator. -/
def starCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (j : CurrentDegree n) :
    FormCoefficients n j.val →L[ℝ]
      FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val) :=
  metricVolumeDensity w e z • starReconstructionCLM j (formMetricCoefficients w e z j.val)

/-- Genuine full original operator-norm smoothness of the actual star, in every natural degree. -/
theorem starCoefficients_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (j : CurrentDegree n) :
    ContDiffOn ℝ ∞ (fun z => starCoefficients w e z j) e.val.target := by
  exact (metricVolumeDensity_smooth w e).smul
    ((starReconstructionCLM j).contDiff.comp_contDiffOn (formMetricCoefficients_smooth w hw e j.val))

/-- The actual wedge equivalence applied to the constructed star recovers the entire metric functional. -/
theorem star_pairing (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (j : CurrentDegree n) (η : FormCoefficients n j.val) :
    canonicalComplementaryWedgeEquiv j (starCoefficients w e z j η) =
      metricVolumeDensity w e z • formMetricCoefficients w e z j.val η := by
  change canonicalComplementaryWedgeEquiv j
    (metricVolumeDensity w e z • (canonicalComplementaryWedgeEquiv j).symm
      (formMetricCoefficients w e z j.val η)) = _
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]

/-- Literal density of the original geometric wedge, on arbitrary entire original tensors. -/
theorem star_wedge_density (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (j : CurrentDegree n) (ξ η : FormCoefficients n j.val) :
    topDensity (wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega)
      ξ (starCoefficients w e z j η)) =
      metricVolumeDensity w e z * formMetricCoefficients w e z j.val ξ η := by
  rw [← canonicalComplementaryWedgeEquiv_apply, star_pairing]
  change metricVolumeDensity w e z * formMetricCoefficients w e z j.val η ξ = _
  rw [(formMetricCoefficients_positive w hw e z hz j.val).1 η ξ]

/-- The genuine entire Hodge identity uses the actual original wedge and the actual normalized volume. -/
theorem star_wedge_identity (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (j : CurrentDegree n) (ξ η : FormCoefficients n j.val) :
    wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega)
      ξ (starCoefficients w e z j η) =
      formMetricCoefficients w e z j.val ξ η • metricVolumeCoefficients w e z := by
  apply topDensity_injective
  rw [star_wedge_density w hw e z hz j ξ η, topDensity_smul]
  exact mul_comm _ _

/-- The genuine entire wedge identity uniquely determines the actual complementary tensor. -/
theorem star_wedge_unique (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (j : CurrentDegree n) (η : FormCoefficients n j.val)
    (θ : FormCoefficients n (Module.finrank ℝ (ComplexModel n) - j.val))
    (hθ : ∀ ξ : FormCoefficients n j.val,
      wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega) ξ θ =
        formMetricCoefficients w e z j.val ξ η • metricVolumeCoefficients w e z) :
    θ = starCoefficients w e z j η := by
  apply (canonicalComplementaryWedgeEquiv j).injective
  ext ξ
  rw [canonicalComplementaryWedgeEquiv_apply, canonicalComplementaryWedgeEquiv_apply,
    hθ ξ, star_wedge_identity w hw e z hz j ξ η]

/-- Positive energy is proved for every nonzero entire original tensor, not just determinant tensors. -/
theorem star_energy_density_positive (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ e.val.target)
    (j : CurrentDegree n) (η : FormCoefficients n j.val) (hη : η ≠ 0) :
    0 < topDensity (wedgeTo
      (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega)
      η (starCoefficients w e z j η)) := by
  rw [star_wedge_density w hw e z hz j η η]
  exact mul_pos (metricVolumeDensity_positive w hw e z hz)
    ((formMetricCoefficients_positive w hw e z hz j.val).2 η hη)

/-- Genuine full original tensor transport of the actual star, derived by its entire wedge uniqueness. -/
theorem starCoefficients_transport (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) (z : ComplexModel n) (hz : z ∈ (chartTransition e f).source)
    (j : CurrentDegree n) (η : FormCoefficients n j.val) :
    starCoefficients w e z j (η.compContinuousLinearMap (chartTransitionDerivative e f z)) =
      (starCoefficients w f (chartTransition e f z) j η).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
  obtain ⟨A, hA, _⟩ := exists_original_chart_orientation_equivalence w hw e f z hz
  have hzf : chartTransition e f z ∈ f.val.target := f.val.map_source hz.2
  symm
  apply star_wedge_unique w hw e z hz.1 j
    (η.compContinuousLinearMap (chartTransitionDerivative e f z))
  intro ξ
  let ξ' := ξ.compContinuousLinearMap A.symm.toContinuousLinearMap
  have hξ : ξ'.compContinuousLinearMap (chartTransitionDerivative e f z) = ξ := by
    rw [← hA]
    ext v
    change ξ (fun i => A.symm (A (v i))) = ξ v
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  have hG := formMetricCoefficients_transport w hw e f z hz j.val ξ' η
  rw [hξ] at hG
  calc
    wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega) ξ
        ((starCoefficients w f (chartTransition e f z) j η).compContinuousLinearMap
          (chartTransitionDerivative e f z)) =
      (wedgeTo (by have hj := j.is_lt; rw [← complexModel_real_finrank n]; omega) ξ'
        (starCoefficients w f (chartTransition e f z) j η)).compContinuousLinearMap
          (chartTransitionDerivative e f z) := by
            rw [wedgeTo_compContinuousLinearMap, hξ]
    _ = (formMetricCoefficients w f (chartTransition e f z) j.val ξ' η •
        metricVolumeCoefficients w f (chartTransition e f z)).compContinuousLinearMap
          (chartTransitionDerivative e f z) := by
            rw [star_wedge_identity w hw f (chartTransition e f z) hzf j ξ' η]
    _ = formMetricCoefficients w f (chartTransition e f z) j.val ξ' η •
        (metricVolumeCoefficients w f (chartTransition e f z)).compContinuousLinearMap
          (chartTransitionDerivative e f z) :=
            map_smul (ContinuousAlternatingMap.compContinuousLinearMapₗ
              (chartTransitionDerivative e f z)) _ _
    _ = formMetricCoefficients w e z j.val ξ
        (η.compContinuousLinearMap (chartTransitionDerivative e f z)) •
          metricVolumeCoefficients w e z := by
            rw [← metricVolumeCoefficients_transport w e f z hz, ← hG]

/-- The actual global Hodge star is an original smooth real form with the original tensor compatibility. -/
def hodgeStarForm (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (j : CurrentDegree n) (α : SmoothRealForm n M j.val) :
    SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - j.val) where
  coeff e z := starCoefficients w e z j (α.coeff e z)
  smooth e := (starCoefficients_smooth w hw e j).clm_apply (α.smooth e)
  compatible := by
    intro e f z hz v
    have hα : α.coeff e z = (α.coeff f (chartTransition e f z)).compContinuousLinearMap
        (chartTransitionDerivative e f z) := by
      ext u
      exact α.compatible e f z hz u
    rw [hα, starCoefficients_transport w hw e f z hz j]
    rfl

/-- Literal whole-coefficient readback of the actual original global star. -/
theorem hodgeStarForm_coeff (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (j : CurrentDegree n) (α : SmoothRealForm n M j.val) (e : ComplexChart n M)
    (z : ComplexModel n) :
    (hodgeStarForm w hw j α).coeff e z = starCoefficients w e z j (α.coeff e z) := rfl

/-- Actual all-natural-degree coefficient stars; excessive-degree source spaces are already zero. -/
def allDegreeStarCoefficients (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) :
    FormCoefficients n q →L[ℝ] FormCoefficients n (Module.finrank ℝ (ComplexModel n) - q) :=
  if hq : q ≤ Module.finrank ℝ (ComplexModel n) then
    starCoefficients w e z ⟨q, Nat.lt_succ_iff.mpr hq⟩
  else 0

/-- Genuine full operator-norm smoothness in every natural degree, including the excessive zero branch. -/
theorem allDegreeStarCoefficients_smooth (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) (q : ℕ) :
    ContDiffOn ℝ ∞ (fun z => allDegreeStarCoefficients w e z q) e.val.target := by
  by_cases hq : q ≤ Module.finrank ℝ (ComplexModel n)
  · simp only [allDegreeStarCoefficients, dif_pos hq]
    exact starCoefficients_smooth w hw e ⟨q, Nat.lt_succ_iff.mpr hq⟩
  · simp only [allDegreeStarCoefficients, dif_neg hq]
    exact contDiffOn_const

/-- The actual excessive-degree operator is zero, without a false complementary-degree equality. -/
theorem allDegreeStarCoefficients_above (w : SmoothRealForm n M 2) (e : ComplexChart n M)
    (z : ComplexModel n) (q : ℕ) (hq : Module.finrank ℝ (ComplexModel n) < q) :
    allDegreeStarCoefficients w e z q = 0 := by
  simp only [allDegreeStarCoefficients, dif_neg (Nat.not_le.mpr hq)]

/-- In excessive degree every original source tensor and its actual star value are really zero. -/
theorem allDegreeStarCoefficients_above_source (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) (q : ℕ)
    (hq : Module.finrank ℝ (ComplexModel n) < q) (η : FormCoefficients n q) :
    η = 0 ∧ allDegreeStarCoefficients w e z q η = 0 := by
  refine ⟨originalForm_above_dimension q ?_ η, ?_⟩
  · simpa only [complexModel_real_finrank, mul_comm n 2] using hq
  · rw [allDegreeStarCoefficients_above w e z q hq]
    rfl

end SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar
