import SGPT.Foundations.Schemes.ProjectiveFubiniStudyCoordinateKahlerForm
import SGPT.Foundations.Schemes.ProjectiveFubiniStudyHermitianBundle

/-! # The actual projective fundamental two-form

The tensors live in the native tangent fibers. Their coordinate coefficients
are computed through actual native chart derivatives; all regularity and
exterior derivative statements below are derived from the literal potential.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] projectiveFubiniStudyPointTopology projectiveFubiniStudyPointChartedSpace
  projectiveFubiniStudyPointRealManifold

def realBilinearAlternatingPart {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp B)

theorem realBilinearAlternatingPart_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (v w : V) :
    realBilinearAlternatingPart B ![v, w] = (B v w - B w v) / 2 := by
  rw [realBilinearAlternatingPart, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.removeNth_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num
  change (1 / 2 : ℝ) * (B v w - B w v) = _
  ring

theorem realBilinearAlternatingPart_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (realBilinearAlternatingPart (V := Fin n → ℂ)) := by
  let L : ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) →L[ℝ]
      ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) [⋀^Fin 1]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Fin n → ℂ) (F := ℝ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.postcomp (Fin n → ℂ)
  have hL : ContDiff ℝ ∞ (L : ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) →
      ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) [⋀^Fin 1]→L[ℝ] ℝ)) := by
    rw [← contDiffOn_univ]
    apply contDiffOn_clm_apply.mpr
    intro v
    change ContDiffOn ℝ ∞ (fun (B : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) =>
      ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (B v)) Set.univ
    exact (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := Fin n → ℂ) (F := ℝ) (0 : Fin 1)).contDiff.comp_contDiffOn
        (contDiffOn_id.clm_apply contDiffOn_const)
  have hA : ContDiff ℝ ∞ (ContinuousAlternatingMap.alternatizeUncurryFinCLM
      (n := 1) ℝ (Fin n → ℂ) ℝ) :=
    by
      let A : ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ]
          (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
        ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin n → ℂ) ℝ
      exact ContinuousLinearMap.contDiff (𝕜 := ℝ)
        (E := (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) [⋀^Fin 1]→L[ℝ] ℝ)
        (F := (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ) A
  exact (hA.comp hL).const_smul _

def polynomialProjFubiniStudyFormInChart (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) p [⋀^Fin 2]→L[ℝ] ℝ := by
  change (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ
  exact (projectiveFubiniStudyCoordinateForm n (polynomialProjRatioChart n i p)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p)

theorem polynomialProjFubiniStudyFormInChart_apply (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyFormInChart n i p ![v, w] =
      projectiveFubiniStudyRealMetric (polynomialProjRatioChart n i p)
        (smoothComplexModelJ n (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p v))
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p w) := by
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p
  change ((projectiveFubiniStudyCoordinateForm n (polynomialProjRatioChart n i p)).compContinuousLinearMap A)
    ![v, w] = _
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hv : (fun a => A (![v, w] a)) = ![A v, A w] := by
    ext a; fin_cases a <;> rfl
  simp only [Function.comp_def]
  rw [hv, projectiveFubiniStudyCoordinateForm_apply]
  rfl

theorem polynomialProjFubiniStudyFormInChart_eq_metric (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyFormInChart n i p ![v, w] =
      (polynomialProjFubiniStudyMetric n).inner p
        (smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v) w := by
  rw [polynomialProjFubiniStudyFormInChart_apply,
    polynomialProjFubiniStudyMetric_inner_chart n i p hi,
    polynomialProjRatioChart_mfderiv_commutes_J n i p hi]

def polynomialProjFubiniStudyFundamentalForm (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) p [⋀^Fin 2]→L[ℝ] ℝ :=
  polynomialProjFubiniStudyFormInChart n (polynomialProjFubiniStudyChartIndex n p) p

theorem polynomialProjFubiniStudyFundamentalForm_apply (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyFundamentalForm n p ![v, w] =
      (polynomialProjFubiniStudyMetric n).inner p
        (smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v) w :=
  polynomialProjFubiniStudyFormInChart_eq_metric n _ p
    (polynomialProjFubiniStudyChartIndex_mem_source n p) v w

theorem polynomialProjFubiniStudyFundamentalForm_chart (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source) :
    polynomialProjFubiniStudyFundamentalForm n p = polynomialProjFubiniStudyFormInChart n i p := by
  ext v
  have hv : v = ![v 0, v 1] := by ext a; fin_cases a <;> rfl
  rw [hv, polynomialProjFubiniStudyFundamentalForm_apply,
    polynomialProjFubiniStudyFormInChart_eq_metric n i p hi]

theorem polynomialProjFubiniStudyFundamentalForm_complex_diagonal (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyFundamentalForm n p
      ![v, smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v] =
      (polynomialProjFubiniStudyMetric n).inner p v v := by
  rw [polynomialProjFubiniStudyFundamentalForm_apply, polynomialProjFubiniStudyMetric_hermitian]

theorem polynomialProjFubiniStudyFundamentalForm_complex_diagonal_pos (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) (hv : v ≠ 0) :
    0 < polynomialProjFubiniStudyFundamentalForm n p
      ![v, smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v] := by
  rw [polynomialProjFubiniStudyFundamentalForm_complex_diagonal]
  exact (polynomialProjFubiniStudyMetric n).pos p v hv

theorem polynomialProjFubiniStudyFundamentalForm_type_one_one (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyFundamentalForm n p
      ![smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p v,
        smoothSchemeTangentJ (polynomialProjStructureMap ℂ n) n p w] =
      polynomialProjFubiniStudyFundamentalForm n p ![v, w] := by
  rw [polynomialProjFubiniStudyFundamentalForm_apply, polynomialProjFubiniStudyFundamentalForm_apply]
  exact polynomialProjFubiniStudyMetric_hermitian n p _ w

/-- Exact readback of the genuine tangent tensors along every actual native inverse ratio chart. -/
theorem polynomialProjFubiniStudyFundamentalForm_inverse_chart (n : ℕ) (i : Fin (n + 1))
    (z : Fin n → ℂ) :
    (polynomialProjFubiniStudyFundamentalForm n ((polynomialProjRatioChart n i).symm z)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i).symm z) =
        projectiveFubiniStudyCoordinateForm n z := by
  let e := polynomialProjRatioChart n i
  have ht : z ∈ e.target := by rw [polynomialProjRatioChart_target]; exact Set.mem_univ z
  have hx := e.map_target ht
  rw [polynomialProjFubiniStudyFundamentalForm_chart n i (e.symm z) hx]
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e (e.symm z)
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e.symm z
  change ((projectiveFubiniStudyCoordinateForm n (e (e.symm z))).compContinuousLinearMap A).compContinuousLinearMap D = _
  rw [e.right_inv ht]
  have h : A.comp D = ContinuousLinearMap.id ℝ (Fin n → ℂ) :=
    (polynomialProjRatioChart_real_mdifferentiable n i).comp_symm_deriv ht
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  have hv : (fun a => A (D (v a))) = v := by
    funext a
    exact congrArg (fun L => L (v a)) h
  rw [hv]

end

end SGPT.Foundations.Schemes
