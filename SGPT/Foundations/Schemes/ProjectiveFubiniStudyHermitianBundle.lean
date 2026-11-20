import SGPT.Foundations.Schemes.ProjectiveFubiniStudyTangentMetric
import SGPT.Foundations.Schemes.SchemeTangentComplex

/-! # Actual Hermitian compatibility and inverse-chart calibration

Genuine mixed complex analyticity proves that the actual native ratio-chart
real derivatives commute with the existing imaginary tangent action.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] projectiveFubiniStudyPointTopology projectiveFubiniStudyPointChartedSpace
  projectiveFubiniStudyPointRealManifold

theorem polynomialProjStandardToRatioTransition_real_fderiv (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (z : Fin n → ℂ) (hz : z ∈ (polynomialProjStandardToRatioTransition n p i).source) :
    fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z =
      (fderiv ℂ (polynomialProjStandardToRatioTransition n p i) z).restrictScalars ℝ :=
  (polynomialProjStandardToRatioTransition_analyticOnNhd n p i z hz).differentiableAt.fderiv_restrictScalars ℝ

theorem polynomialProjStandardToRatioTransition_fderiv_commutes_J (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (z : Fin n → ℂ) (hz : z ∈ (polynomialProjStandardToRatioTransition n p i).source)
    (v : Fin n → ℂ) :
    fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z (smoothComplexModelJ n v) =
      smoothComplexModelJ n (fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z v) := by
  rw [polynomialProjStandardToRatioTransition_real_fderiv n p i z hz]
  change (fderiv ℂ (polynomialProjStandardToRatioTransition n p i) z) (Complex.I • v) =
    Complex.I • (fderiv ℂ (polynomialProjStandardToRatioTransition n p i) z) v
  exact map_smul _ _ _

/-- The actual native derivative is the genuine mixed transition derivative in the native base chart. -/
theorem polynomialProjRatioChart_mfderiv_standard_base (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p =
      fderiv ℝ (polynomialProjStandardToRatioTransition n p i)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p p) := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e.symm (e p)
  have hp := schemeAnalyticCoordinateChart_point_mem_source (polynomialProjStructureMap ℂ n) n p
  have h : A.comp D = fderiv ℝ (polynomialProjStandardToRatioTransition n p i) (e p) :=
    polynomialProjRatioChart_mfderiv_standardInverse n p i p hp hi
  have hD : D = ContinuousLinearMap.id ℝ (Fin n → ℂ) := by
    have h' := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℂ)) (x := p)
    simp only [mfld_simps, mfderivWithin_univ] at h'
    convert! h' using 1
  rw [hD, ContinuousLinearMap.comp_id] at h
  exact h

theorem polynomialProjRatioChart_mfderiv_commutes_J (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p
      (smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v) =
      smoothComplexModelJ n
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p v) := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  have hp : p ∈ e.source := schemeAnalyticCoordinateChart_point_mem_source _ n p
  have ht : e p ∈ (polynomialProjStandardToRatioTransition n p i).source := by
    change e p ∈ e.target ∧ e.symm (e p) ∈ (polynomialProjRatioChart n i).source
    rw [e.left_inv hp]
    exact ⟨e.map_source hp, hi⟩
  rw [polynomialProjRatioChart_mfderiv_standard_base n i p hi]
  exact polynomialProjStandardToRatioTransition_fderiv_commutes_J n p i (e p) ht v

/-- The actual global metric is Hermitian for the existing native smooth imaginary action. -/
theorem polynomialProjFubiniStudyMetric_hermitian (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    (polynomialProjFubiniStudyMetric n).inner p
      (smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v)
      (smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p w) =
        (polynomialProjFubiniStudyMetric n).inner p v w := by
  obtain ⟨i, hi⟩ := polynomialProjRatioChart_sources_cover n p
  rw [polynomialProjFubiniStudyMetric_inner_chart n i p hi,
    polynomialProjFubiniStudyMetric_inner_chart n i p hi,
    polynomialProjRatioChart_mfderiv_commutes_J n i p hi,
    polynomialProjRatioChart_mfderiv_commutes_J n i p hi]
  exact projectiveFubiniStudyRealMetric_imaginary n _ _ _

/-- Exact calibration along every actual native inverse ratio chart and its genuine derivative. -/
theorem polynomialProjFubiniStudyMetric_inverse_chart (n : ℕ) (i : Fin (n + 1))
    (z v w : Fin n → ℂ) :
    (polynomialProjFubiniStudyMetric n).inner ((polynomialProjRatioChart n i).symm z)
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i).symm z v)
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i).symm z w) =
        projectiveFubiniStudyRealMetric z v w := by
  let e := polynomialProjRatioChart n i
  have ht : z ∈ e.target := by rw [polynomialProjRatioChart_target]; exact Set.mem_univ z
  have hx := e.map_target ht
  rw [polynomialProjFubiniStudyMetric_inner_chart n i (e.symm z) hx]
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e (e.symm z)
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e.symm z
  have h : A.comp D = ContinuousLinearMap.id ℝ (Fin n → ℂ) :=
    (polynomialProjRatioChart_real_mdifferentiable n i).comp_symm_deriv ht
  have hv := congrArg (fun L => L v) h
  have hw := congrArg (fun L => L w) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hv hw
  change projectiveFubiniStudyRealMetric (e (e.symm z)) (A (D v)) (A (D w)) = _
  rw [e.right_inv ht, hv, hw]

end

end SGPT.Foundations.Schemes
