import SGPT.Foundations.Schemes.ProjectiveRatioChartCompatibility
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded

/-! # The literal Fubini–Study form on the actual native projective tangent bundle

Each form is pulled back through an actual native chart derivative. The
proved actual quotient derivative covariance makes these forms independent
of the choice of projective coordinate.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

local instance projectiveFubiniStudyPointTopology (n : ℕ) :
    TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :=
  schemeAnalyticPointTopology (polynomialProjStructureMap ℂ n)

local instance projectiveFubiniStudyPointChartedSpace (n : ℕ) :
    ChartedSpace (Fin n → ℂ) (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :=
  smoothSchemeComplexChartedSpace (polynomialProjStructureMap ℂ n) n

local instance projectiveFubiniStudyPointRealManifold (n : ℕ) :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :=
  smoothSchemeReal_isManifold (polynomialProjStructureMap ℂ n) n ∞

theorem polynomialProjRatioChart_mfderiv_transition (n : ℕ) (i j : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source)
    (hj : p ∈ (polynomialProjRatioChart n j).source) :
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n j) p =
      (fderiv ℝ (polynomialProjRatioChartTransition n i j) (polynomialProjRatioChart n i p)).comp
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p) := by
  let e := polynomialProjRatioChart n i
  let d := polynomialProjRatioChart n j
  let T := polynomialProjRatioChartTransition n i j
  have ht : e p ∈ T.source := by
    change e p ∈ e.target ∧ e.symm (e p) ∈ d.source
    rw [e.left_inv hi]
    exact ⟨e.map_source hi, hj⟩
  have hT : DifferentiableAt ℝ T (e p) :=
    ((polynomialProjRatioChartTransition_contDiffOn n i j 1).restrict_scalars ℝ).contDiffAt
      (T.open_source.mem_nhds ht) |>.differentiableAt one_ne_zero
  have he : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e p :=
    (polynomialProjRatioChart_real_mdifferentiable n i).mdifferentiableAt hi
  have hcomp : (T ∘ e : _ → Fin n → ℂ) =ᶠ[𝓝 p] d := by
    filter_upwards [e.open_source.mem_nhds hi] with q hq
    change d (e.symm (e q)) = d q
    rw [e.left_inv hq]
  rw [← hcomp.mfderiv_eq]
  rw [mfderiv_comp p hT.mdifferentiableAt he, mfderiv_eq_fderiv]

/-- Pullback of the literal local form through the actual native real chart derivative. -/
def polynomialProjFubiniStudyInChart (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) p →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin n → ℂ) p →L[ℝ] ℝ := by
  change (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p
  exact (projectiveFubiniStudyContinuousBilinear n (polynomialProjRatioChart n i p)).bilinearComp A A

theorem polynomialProjFubiniStudyInChart_apply (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyInChart n i p v w =
      projectiveFubiniStudyRealMetric (polynomialProjRatioChart n i p)
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p v)
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p w) := rfl

/-- Genuine native derivative covariance makes the tangent form independent of the coordinate. -/
theorem polynomialProjFubiniStudyInChart_eq (n : ℕ) (i j : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source)
    (hj : p ∈ (polynomialProjRatioChart n j).source) :
    polynomialProjFubiniStudyInChart n i p = polynomialProjFubiniStudyInChart n j p := by
  have ht : polynomialProjRatioChart n i p ∈ (polynomialProjRatioChartTransition n i j).source := by
    change _ ∈ (polynomialProjRatioChart n i).target ∧
      (polynomialProjRatioChart n i).symm (polynomialProjRatioChart n i p) ∈
        (polynomialProjRatioChart n j).source
    rw [(polynomialProjRatioChart n i).left_inv hi]
    exact ⟨(polynomialProjRatioChart n i).map_source hi, hj⟩
  have hnz : projectiveRatioCoordinateVector n i (polynomialProjRatioChart n i p) j ≠ 0 := by
    rwa [polynomialProjRatioChartTransition_source] at ht
  ext v w
  rw [polynomialProjFubiniStudyInChart_apply, polynomialProjFubiniStudyInChart_apply,
    polynomialProjRatioChart_mfderiv_transition n i j p hi hj]
  have hcoord : polynomialProjRatioChartTransition n i j (polynomialProjRatioChart n i p) =
      polynomialProjRatioChart n j p := by
    change polynomialProjRatioChart n j ((polynomialProjRatioChart n i).symm
      (polynomialProjRatioChart n i p)) = _
    rw [(polynomialProjRatioChart n i).left_inv hi]
  rw [← hcoord]
  exact (polynomialProjRatioChartTransition_metric_real_fderiv n i j
    (polynomialProjRatioChart n i p) _ _ hnz).symm

def polynomialProjFubiniStudyChartIndex (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) : Fin (n + 1) :=
  Classical.choose (polynomialProjRatioChart_sources_cover n p)

theorem polynomialProjFubiniStudyChartIndex_mem_source (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    p ∈ (polynomialProjRatioChart n (polynomialProjFubiniStudyChartIndex n p)).source :=
  Classical.choose_spec (polynomialProjRatioChart_sources_cover n p)

/-- The global form is defined using a derived covering coordinate and its actual native derivative. -/
def polynomialProjFubiniStudyTangentForm (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    TangentSpace 𝓘(ℝ, Fin n → ℂ) p →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin n → ℂ) p →L[ℝ] ℝ :=
  polynomialProjFubiniStudyInChart n (polynomialProjFubiniStudyChartIndex n p) p

/-- Its exact expression in every actual covering ratio chart. -/
theorem polynomialProjFubiniStudyTangentForm_chart (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source) :
    polynomialProjFubiniStudyTangentForm n p = polynomialProjFubiniStudyInChart n i p :=
  polynomialProjFubiniStudyInChart_eq n _ i p (polynomialProjFubiniStudyChartIndex_mem_source n p) hi

theorem polynomialProjFubiniStudyTangentForm_symm (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    polynomialProjFubiniStudyTangentForm n p v w = polynomialProjFubiniStudyTangentForm n p w v :=
  projectiveFubiniStudyRealMetric_symm _ _ _

theorem polynomialProjFubiniStudyTangentForm_pos (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (v : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) (hv : v ≠ 0) :
    0 < polynomialProjFubiniStudyTangentForm n p v v := by
  let i := polynomialProjFubiniStudyChartIndex n p
  have hi := polynomialProjFubiniStudyChartIndex_mem_source n p
  have hnonzero : mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
      (polynomialProjRatioChart n i) p v ≠ 0 := by
    intro h
    apply hv
    exact (polynomialProjRatioChart_real_mdifferentiable n i).mfderiv_injective hi
      (by simpa using h)
  exact projectiveFubiniStudyRealMetric_pos _ _ hnonzero

theorem polynomialProjFubiniStudyTangentForm_isVonNBounded (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    Bornology.IsVonNBounded ℝ {v | polynomialProjFubiniStudyTangentForm n p v v < 1} := by
  let i := polynomialProjFubiniStudyChartIndex n p
  let e := polynomialProjRatioChartRealTangentEquiv n i p
    (polynomialProjFubiniStudyChartIndex_mem_source n p)
  have hb := (projectiveFubiniStudyRealMetric_isVonNBounded n (polynomialProjRatioChart n i p)).image
    e.symm.toContinuousLinearMap
  apply hb.subset
  intro v hv
  refine ⟨e v, hv, e.symm_apply_apply v⟩

def polynomialProjFubiniStudyStandardCoefficients (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (z : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ :=
  (projectiveFubiniStudyContinuousBilinear n (polynomialProjStandardToRatioTransition n p i z)).bilinearComp
    (fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z)
    (fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z)

theorem polynomialProjFubiniStudyStandardCoefficients_contDiffOn (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (polynomialProjFubiniStudyStandardCoefficients n p i)
      (polynomialProjStandardToRatioTransition n p i).source := by
  let T : (Fin n → ℂ) → (Fin n → ℂ) := polynomialProjStandardToRatioTransition n p i
  let S := (polynomialProjStandardToRatioTransition n p i).source
  have hT : ContDiffOn ℝ ∞ T S :=
    (polynomialProjStandardToRatioTransition_contDiffOn n p i ∞).restrict_scalars ℝ
  have hg : ContDiffOn ℝ ∞ (fun z => projectiveFubiniStudyContinuousBilinear n (T z)) S :=
    (projectiveFubiniStudyContinuousBilinear_contDiff n).comp_contDiffOn hT
  have hA : ContDiffOn ℝ ∞ (fderiv ℝ T) S :=
    hT.fderiv_of_isOpen (polynomialProjStandardToRatioTransition n p i).open_source (by simp)
  change ContDiffOn ℝ ∞ (fun z => (projectiveFubiniStudyContinuousBilinear n (T z)).bilinearComp
    (fderiv ℝ T z) (fderiv ℝ T z)) S
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun z => projectiveFubiniStudyContinuousBilinear n (T z)
    (fderiv ℝ T z v) (fderiv ℝ T z w)) S
  exact (hg.clm_apply (hA.clm_apply contDiffOn_const)).clm_apply
    (hA.clm_apply contDiffOn_const)

theorem polynomialProjRatioChart_mfderiv_standardInverse (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (x : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hx : x ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).source)
    (hi : x ∈ (polynomialProjRatioChart n i).source) :
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) x).comp
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
          (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x)) =
      fderiv ℝ (polynomialProjStandardToRatioTransition n p i)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  have he : e.MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) :=
    mdifferentiable_chart p
  have hr : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
      (polynomialProjRatioChart n i) (e.symm (e x)) := by
    rw [e.left_inv hx]
    exact (polynomialProjRatioChart_real_mdifferentiable n i).mdifferentiableAt hi
  have h := mfderiv_comp (e x) hr (he.mdifferentiableAt_symm (e.map_source hx))
  change mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
      (polynomialProjStandardToRatioTransition n p i) (e x) = _ at h
  rw [mfderiv_eq_fderiv, e.left_inv hx] at h
  exact h.symm

theorem polynomialProjFubiniStudyTangentForm_standard_readback (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (x : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hx : x ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).source)
    (hi : x ∈ (polynomialProjRatioChart n i).source) (v w : Fin n → ℂ) :
    polynomialProjFubiniStudyTangentForm n x
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
          (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) v)
      (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
          (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) w) =
      polynomialProjFubiniStudyStandardCoefficients n p i
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) v w := by
  rw [polynomialProjFubiniStudyTangentForm_chart n i x hi, polynomialProjFubiniStudyInChart_apply]
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) x
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
      (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x)
  change projectiveFubiniStudyRealMetric (polynomialProjRatioChart n i x) (A (D v)) (A (D w)) = _
  have h : A.comp D = fderiv ℝ (polynomialProjStandardToRatioTransition n p i)
      (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) :=
    polynomialProjRatioChart_mfderiv_standardInverse n p i x hx hi
  have hv := congrArg (fun A => A v) h
  have hw := congrArg (fun A => A w) h
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  rw [hv, hw]
  have hc : polynomialProjStandardToRatioTransition n p i
      (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) =
        polynomialProjRatioChart n i x := by
    change polynomialProjRatioChart n i
      ((schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x)) = _
    rw [(schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).left_inv hx]
  simp only [polynomialProjFubiniStudyStandardCoefficients, ContinuousLinearMap.bilinearComp_apply, hc]
  rfl

/-- Actual preferred tangent trivializations are the native derivatives of the actual standard inverse. -/
theorem polynomialProjFubiniStudy_standard_symmL (n : ℕ)
    (p x : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hx : x ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).source) :
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x =
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).symm
          (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) := by
  have h := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, Fin n → ℂ)) (x₀ := p) (x := x) hx
  simp only [mfld_simps, mfderivWithin_univ] at h
  convert! h using 1

/-- The nested native hom-bundle trivialization reads the actual standard metric coefficients. -/
theorem polynomialProjFubiniStudyTangentForm_trivialization (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (x : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hx : x ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).source)
    (hi : x ∈ (polynomialProjRatioChart n i).source) :
    (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
          (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
            (polynomialProjFubiniStudyTangentForm n x))).2 =
      polynomialProjFubiniStudyStandardCoefficients n p i
        (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p x) := by
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [polynomialProjFubiniStudy_standard_symmL n p x hx]
  have hcot : x ∈ (trivializationAt ((Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p).baseSet := by
    change x ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).source ∩ Set.univ
    exact ⟨hx, Set.mem_univ x⟩
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hcot]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply]
  rw [polynomialProjFubiniStudy_standard_symmL n p x hx]
  have hscalar : (trivializationAt ℝ (fun _ : SchemeComplexPoint (polynomialProjStructureMap ℂ n) => ℝ)
      p).continuousLinearMapAt ℝ x = ContinuousLinearMap.id ℝ ℝ := by
    change (Bundle.Trivial.trivialization (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) ℝ).continuousLinearMapAt ℝ x = _
    exact Bundle.Trivial.continuousLinearMapAt_trivialization ℝ
      (SchemeComplexPoint (polynomialProjStructureMap ℂ n)) ℝ x
  rw [hscalar, ContinuousLinearMap.id_apply]
  exact polynomialProjFubiniStudyTangentForm_standard_readback n p i x hx hi v w

/-- The actual choice-independent tangent form is a genuinely smooth native bilinear bundle section. -/
theorem polynomialProjFubiniStudyTangentForm_contMDiff (n : ℕ) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ)
      (𝓘(ℝ, Fin n → ℂ).prod 𝓘(ℝ, (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
        (polynomialProjFubiniStudyTangentForm n x)) := by
  intro p
  rw [contMDiffAt_section p]
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  let i := polynomialProjFubiniStudyChartIndex n p
  have hp : p ∈ e.source := schemeAnalyticCoordinateChart_point_mem_source _ n p
  have hi : p ∈ (polynomialProjRatioChart n i).source :=
    polynomialProjFubiniStudyChartIndex_mem_source n p
  have heq : (fun x => (trivializationAt ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ)
      (fun y => TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, Fin n → ℂ) y →L[ℝ] ℝ) p
          (TotalSpace.mk' ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) x
            (polynomialProjFubiniStudyTangentForm n x))).2) =ᶠ[𝓝 p]
      (fun x => polynomialProjFubiniStudyStandardCoefficients n p i (e x)) := by
    filter_upwards [e.open_source.mem_nhds hp, (polynomialProjRatioChart n i).open_source.mem_nhds hi]
      with x hx hxi
    exact polynomialProjFubiniStudyTangentForm_trivialization n p i x hx hxi
  have ht : e p ∈ (polynomialProjStandardToRatioTransition n p i).source := by
    change e p ∈ e.target ∧ e.symm (e p) ∈ (polynomialProjRatioChart n i).source
    rw [e.left_inv hp]
    exact ⟨e.map_source hp, hi⟩
  have hc := (polynomialProjFubiniStudyStandardCoefficients_contDiffOn n p i).contDiffAt
    ((polynomialProjStandardToRatioTransition n p i).open_source.mem_nhds ht)
  have he : ContMDiffAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞ e p :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hp
  exact (hc.contMDiffAt.comp p he).congr_of_eventuallyEq heq

/-- The manuscript-normalized actual smooth Riemannian metric on native polynomial projective space. -/
def polynomialProjFubiniStudyMetric (n : ℕ) :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℂ) ∞ (Fin n → ℂ)
      (fun x : SchemeComplexPoint (polynomialProjStructureMap ℂ n) => TangentSpace 𝓘(ℝ, Fin n → ℂ) x) where
  inner := polynomialProjFubiniStudyTangentForm n
  symm := polynomialProjFubiniStudyTangentForm_symm n
  pos := polynomialProjFubiniStudyTangentForm_pos n
  isVonNBounded := polynomialProjFubiniStudyTangentForm_isVonNBounded n
  contMDiff := polynomialProjFubiniStudyTangentForm_contMDiff n

theorem polynomialProjFubiniStudyMetric_inner_chart (n : ℕ) (i : Fin (n + 1))
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (hi : p ∈ (polynomialProjRatioChart n i).source)
    (v w : TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :
    (polynomialProjFubiniStudyMetric n).inner p v w =
      projectiveFubiniStudyRealMetric (polynomialProjRatioChart n i p)
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p v)
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) p w) := by
  change polynomialProjFubiniStudyTangentForm n p v w = _
  rw [polynomialProjFubiniStudyTangentForm_chart n i p hi, polynomialProjFubiniStudyInChart_apply]

end

end SGPT.Foundations.Schemes
