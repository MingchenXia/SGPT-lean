import SGPT.Foundations.Schemes.ProjectiveFubiniStudyGlobalKahlerForm

/-! # Actual native coordinate coefficients and exterior derivative

The coefficients are read from the constructed tangent tensors through the
actual inverse chart derivative. Their smoothness and closedness are proved
on the genuine scheme-derived chart targets.
-/

open CategoryTheory AlgebraicGeometry Algebra Manifold Bundle Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] projectiveFubiniStudyPointTopology projectiveFubiniStudyPointChartedSpace
  projectiveFubiniStudyPointRealManifold

def polynomialProjFubiniStudyFormStandardCoefficients (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  let F : (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ := polynomialProjFubiniStudyFundamentalForm n (e.symm z)
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e.symm z
  exact F.compContinuousLinearMap D

def polynomialProjFubiniStudyFormCoordinatePullback (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) (z : Fin n → ℂ) :
    (Fin n → ℂ) [⋀^Fin 2]→L[ℝ] ℝ :=
  (projectiveFubiniStudyCoordinateForm n (polynomialProjStandardToRatioTransition n p i z)).compContinuousLinearMap
    (fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z)

theorem polynomialProjFubiniStudyFormStandardCoefficients_readback (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (z : Fin n → ℂ) (hz : z ∈ (polynomialProjStandardToRatioTransition n p i).source) :
    polynomialProjFubiniStudyFormStandardCoefficients n p z =
      polynomialProjFubiniStudyFormCoordinatePullback n p i z := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  let x := e.symm z
  have ht : z ∈ e.target := hz.1
  have hi : x ∈ (polynomialProjRatioChart n i).source := hz.2
  have hx : x ∈ e.source := e.map_target ht
  let A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (polynomialProjRatioChart n i) x
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
    mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) e.symm z
  have hF := polynomialProjFubiniStudyFundamentalForm_chart n i x hi
  change (polynomialProjFubiniStudyFundamentalForm n x).compContinuousLinearMap D = _
  rw [hF]
  change ((projectiveFubiniStudyCoordinateForm n (polynomialProjRatioChart n i x)).compContinuousLinearMap A).compContinuousLinearMap D = _
  have h : A.comp D = fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z := by
    have he : e.MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) :=
      mdifferentiable_chart p
    have hr : MDifferentiableAt 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (polynomialProjRatioChart n i) (e.symm z) :=
      (polynomialProjRatioChart_real_mdifferentiable n i).mdifferentiableAt hi
    have h' := mfderiv_comp z hr (he.mdifferentiableAt_symm ht)
    change mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
      (polynomialProjStandardToRatioTransition n p i) z = A.comp D at h'
    rw [mfderiv_eq_fderiv] at h'
    exact h'.symm
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  have hv : (fun a => A (D (v a))) =
      (fun a => fderiv ℝ (polynomialProjStandardToRatioTransition n p i) z (v a)) := by
    funext a
    exact congrArg (fun L => L (v a)) h
  rw [hv]
  rfl

theorem polynomialProjFubiniStudyFormCoordinatePullback_eq_alternatingPart (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1))
    (z : Fin n → ℂ) (hz : z ∈ (polynomialProjStandardToRatioTransition n p i).source) :
    polynomialProjFubiniStudyFormCoordinatePullback n p i z =
      realBilinearAlternatingPart
        ((polynomialProjFubiniStudyStandardCoefficients n p i z).comp (smoothComplexModelJ n)) := by
  let T : (Fin n → ℂ) → (Fin n → ℂ) := polynomialProjStandardToRatioTransition n p i
  let D : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) := fderiv ℝ T z
  let B := (polynomialProjFubiniStudyStandardCoefficients n p i z).comp (smoothComplexModelJ n)
  have hB (v w : Fin n → ℂ) : B v w = projectiveFubiniStudyCoordinateForm n (T z) ![D v, D w] := by
    change projectiveFubiniStudyRealMetric (T z) (D (smoothComplexModelJ n v)) (D w) = _
    rw [polynomialProjStandardToRatioTransition_fderiv_commutes_J n p i z hz,
      projectiveFubiniStudyCoordinateForm_apply]
    rfl
  ext v
  have hv : v = ![v 0, v 1] := by ext a; fin_cases a <;> rfl
  rw [hv, realBilinearAlternatingPart_apply]
  have hswap : projectiveFubiniStudyCoordinateForm n (T z) ![D (v 1), D (v 0)] =
      -projectiveFubiniStudyCoordinateForm n (T z) ![D (v 0), D (v 1)] := by
    have hp : (![D (v 0), D (v 1)] : Fin 2 → (Fin n → ℂ)) ∘ Equiv.swap 0 1 =
        ![D (v 1), D (v 0)] := by ext a; fin_cases a <;> simp
    rw [← hp]
    exact (projectiveFubiniStudyCoordinateForm n (T z)).toAlternatingMap.map_swap _ (by decide : (0 : Fin 2) ≠ 1)
  change ((projectiveFubiniStudyCoordinateForm n (T z)).compContinuousLinearMap D) ![v 0, v 1] = _
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hm : D ∘ ![v 0, v 1] = ![D (v 0), D (v 1)] := by ext a; fin_cases a <;> rfl
  rw [hm]
  change projectiveFubiniStudyCoordinateForm n (T z) ![D (v 0), D (v 1)] = (B (v 0) (v 1) - B (v 1) (v 0)) / 2
  rw [hB, hB, hswap]
  ring

theorem polynomialProjFubiniStudyFormCoordinatePullback_contDiffOn (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) (i : Fin (n + 1)) :
    ContDiffOn ℝ ∞ (polynomialProjFubiniStudyFormCoordinatePullback n p i)
      (polynomialProjStandardToRatioTransition n p i).source := by
  have hG := polynomialProjFubiniStudyStandardCoefficients_contDiffOn n p i
  have hB := hG.clm_comp (contDiffOn_const (c := smoothComplexModelJ n))
  apply ((realBilinearAlternatingPart_contDiff n).comp_contDiffOn hB).congr
  intro z hz
  exact polynomialProjFubiniStudyFormCoordinatePullback_eq_alternatingPart n p i z hz

theorem polynomialProjFubiniStudyFormStandardCoefficients_contDiffOn (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n)) :
    ContDiffOn ℝ ∞ (polynomialProjFubiniStudyFormStandardCoefficients n p)
      (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).target := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  intro z hz
  obtain ⟨i, hi⟩ := polynomialProjRatioChart_sources_cover n (e.symm z)
  have ht : z ∈ (polynomialProjStandardToRatioTransition n p i).source := ⟨hz, hi⟩
  have hs := (polynomialProjStandardToRatioTransition n p i).open_source.mem_nhds ht
  have heq : polynomialProjFubiniStudyFormStandardCoefficients n p =ᶠ[𝓝 z]
      polynomialProjFubiniStudyFormCoordinatePullback n p i := by
    filter_upwards [hs] with w hw
    exact polynomialProjFubiniStudyFormStandardCoefficients_readback n p i w hw
  exact ((polynomialProjFubiniStudyFormCoordinatePullback_contDiffOn n p i).contDiffAt hs)
    |>.congr_of_eventuallyEq heq |>.contDiffWithinAt

/-- Actual native exterior differentiation of the genuine preferred-chart coefficients vanishes. -/
theorem polynomialProjFubiniStudyFormStandardCoefficients_closed (n : ℕ)
    (p : SchemeComplexPoint (polynomialProjStructureMap ℂ n))
    (z : Fin n → ℂ) (hz : z ∈ (schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p).target) :
    extDeriv (polynomialProjFubiniStudyFormStandardCoefficients n p) z = 0 := by
  let e := schemeAnalyticCoordinateChart (polynomialProjStructureMap ℂ n) n p
  obtain ⟨i, hi⟩ := polynomialProjRatioChart_sources_cover n (e.symm z)
  have ht : z ∈ (polynomialProjStandardToRatioTransition n p i).source := ⟨hz, hi⟩
  have hs := (polynomialProjStandardToRatioTransition n p i).open_source.mem_nhds ht
  have heq : polynomialProjFubiniStudyFormStandardCoefficients n p =ᶠ[𝓝 z]
      polynomialProjFubiniStudyFormCoordinatePullback n p i := by
    filter_upwards [hs] with w hw
    exact polynomialProjFubiniStudyFormStandardCoefficients_readback n p i w hw
  rw [heq.extDeriv_eq]
  have hT : ContDiffAt ℝ ∞ (polynomialProjStandardToRatioTransition n p i) z :=
    ((polynomialProjStandardToRatioTransition_contDiffOn n p i ∞).restrict_scalars ℝ).contDiffAt hs
  have hω := (projectiveFubiniStudyCoordinateForm_contDiff n).differentiable (by simp)
    (polynomialProjStandardToRatioTransition n p i z)
  change extDeriv (fun w => (projectiveFubiniStudyCoordinateForm n
      (polynomialProjStandardToRatioTransition n p i w)).compContinuousLinearMap
        (fderiv ℝ (polynomialProjStandardToRatioTransition n p i) w)) z = _
  rw [extDeriv_pullback hω hT
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2),
    projectiveFubiniStudyCoordinateForm_closed]
  rfl

end

end SGPT.Foundations.Schemes
