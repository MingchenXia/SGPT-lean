import SGPT.Foundations.Schemes.NativeProjectiveFubiniStudyRiemannianMetric

/-!
# Actual native inverse-chart derivatives and Fubini–Study coefficients

The existing native chart chain rule and actual inverse derivative identities
produce the missing coefficient overlap law. Existing genuine tangent inverse
trivializations and native FS positivity/type supply actual coefficient
positivity/type, without an overlap or tangent-linearity certificate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry Algebra SGPT.Foundations.Schemes Manifold Bundle Set
open scoped Topology ContDiff

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]

local instance nativeFSCoeffTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nativeFSCoeffCharts : ChartedSpace (Fin n → ℂ) (SchemeComplexPoint f) :=
  smoothSchemeComplexChartedSpace f n
local instance nativeFSCoeffRealManifold :
    IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ (SchemeComplexPoint f) := smoothSchemeReal_isManifold f n ∞

/-- The actual native inverse-chart derivative, retaining its true tangent meaning. -/
def schemeNativeInverseChartDerivative (p : SchemeComplexPoint f) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) (schemeAnalyticCoordinateChart f n p).symm z

/-- Actual native chart inverse derivatives are injective on their true target. -/
theorem schemeNativeInverseChartDerivative_injective (p : SchemeComplexPoint f)
    (z : Fin n → ℂ) (hz : z ∈ (schemeAnalyticCoordinateChart f n p).target) :
    Function.Injective (schemeNativeInverseChartDerivative f n p z) :=
  (mdifferentiable_chart p).symm.mfderiv_injective hz

/-- Genuine native chart chain and inverse derivative laws give the full overlap identity. -/
theorem schemeNativeInverseChartDerivative_transition (p q : SchemeComplexPoint f)
    (z : Fin n → ℂ) (hz : z ∈ (schemeAnalyticCoordinateTransition f n p q).source) :
    schemeNativeInverseChartDerivative f n p z =
      (schemeNativeInverseChartDerivative f n q (schemeAnalyticCoordinateTransition f n p q z)).comp
        (fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) z) := by
  let c := schemeAnalyticCoordinateChart f n p
  let d := schemeAnalyticCoordinateChart f n q
  have hc : c.MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) := mdifferentiable_chart p
  have hd : d.MDifferentiable 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) := mdifferentiable_chart q
  have hT := mfderiv_comp z (hd.mdifferentiableAt hz.2) (hc.mdifferentiableAt_symm hz.1)
  rw [mfderiv_eq_fderiv] at hT
  change fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) z =
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) d (c.symm z)).comp
      (schemeNativeInverseChartDerivative f n p z) at hT
  have hcancel := hd.symm_comp_deriv hz.2
  change (schemeNativeInverseChartDerivative f n q (schemeAnalyticCoordinateTransition f n p q z)).comp
    (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) d (c.symm z)) =
      ContinuousLinearMap.id ℝ (Fin n → ℂ) at hcancel
  calc
    schemeNativeInverseChartDerivative f n p z =
        (ContinuousLinearMap.id ℝ (Fin n → ℂ)).comp
          (schemeNativeInverseChartDerivative f n p z) := rfl
    _ = ((schemeNativeInverseChartDerivative f n q
        (schemeAnalyticCoordinateTransition f n p q z)).comp
        (mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) d (c.symm z))).comp
          (schemeNativeInverseChartDerivative f n p z) := by rw [hcancel]
    _ = _ := by rw [hT, ContinuousLinearMap.comp_assoc]

private theorem inverse_trivialization_I (p x : SchemeComplexPoint f)
    (hx : x ∈ (schemeAnalyticCoordinateChart f n p).source) (v : Fin n → ℂ) :
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x
        (smoothComplexModelJ n v) =
      smoothSchemeTangentJ f n x
        ((trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x v) := by
  let a := trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p
  have ha : x ∈ a.baseSet := hx
  have hJ := smoothSchemeTangentJ_inCoordinates f n p x hx
  rw [ContinuousLinearMap.inCoordinates_eq ha ha] at hJ
  have hv := congrArg (fun A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) => A v) hJ
  change (a.continuousLinearEquivAt ℝ x ha)
    (smoothSchemeTangentJ f n x ((a.continuousLinearEquivAt ℝ x ha).symm v)) =
      smoothComplexModelJ n v at hv
  have h := congrArg (a.continuousLinearEquivAt ℝ x ha).symm hv
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  rw [← a.symm_continuousLinearEquivAt_eq' ha]
  exact h.symm

private theorem inverse_trivialization_derivative (p x : SchemeComplexPoint f)
    (hx : x ∈ (schemeAnalyticCoordinateChart f n p).source) :
    (trivializationAt (Fin n → ℂ) (TangentSpace 𝓘(ℝ, Fin n → ℂ)) p).symmL ℝ x =
      mfderiv 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ)
        (schemeAnalyticCoordinateChart f n p).symm (schemeAnalyticCoordinateChart f n p x) := by
  have h := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, Fin n → ℂ)) (x₀ := p) (x := x) hx
  simp only [mfld_simps, mfderivWithin_univ] at h
  convert! h using 1

private theorem target_identity_of_source {M V : Type*} [TopologicalSpace M] [TopologicalSpace V]
    (c : OpenPartialHomeomorph M V) (D : V → V → V) (J : M → V → V) (I : V → V)
    (h : ∀ x, x ∈ c.source → ∀ v, D (c x) (I v) = J x (D (c x) v))
    (z : V) (hz : z ∈ c.target) (v : V) : D z (I v) = J (c.symm z) (D z v) := by
  have h' := h (c.symm z) (c.map_target hz) v
  simpa only [c.right_inv hz] using h'

/-- Existing ACTUAL inverse tangent trivializations give genuine imaginary compatibility. -/
theorem schemeNativeInverseChartDerivative_map_I
    (p : SchemeComplexPoint f) (z : Fin n → ℂ)
    (hz : z ∈ (schemeAnalyticCoordinateChart f n p).target) (v : Fin n → ℂ) :
    schemeNativeInverseChartDerivative f n p z (Complex.I • v) =
      smoothSchemeTangentJ f n ((schemeAnalyticCoordinateChart f n p).symm z)
        (schemeNativeInverseChartDerivative f n p z v) := by
  apply target_identity_of_source (schemeAnalyticCoordinateChart f n p)
    (fun t w => schemeNativeInverseChartDerivative f n p t w)
    (fun x w => smoothSchemeTangentJ f n x w) (smoothComplexModelJ n) ?_ z hz v
  intro x hx w
  have hJ := inverse_trivialization_I f n p x hx w
  rw [inverse_trivialization_derivative f n p x hx] at hJ
  exact hJ

/-- Literal global tensor definition plus the actual derivative identity gives native coefficient overlap. -/
theorem schemeNativeFubiniStudyCoefficients_overlap (E : ClosedProjectiveEmbedding f)
    (p q : SchemeComplexPoint f) (z : Fin n → ℂ)
    (hz : z ∈ (schemeAnalyticCoordinateTransition f n p q).source) :
    E.nativeFubiniStudyFormCoefficients n p z =
      (E.nativeFubiniStudyFormCoefficients n q (schemeAnalyticCoordinateTransition f n p q z)).compContinuousLinearMap
        (fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) z) := by
  let c := schemeAnalyticCoordinateChart f n p
  let d := schemeAnalyticCoordinateChart f n q
  have hpoint : d.symm (schemeAnalyticCoordinateTransition f n p q z) = c.symm z :=
    d.left_inv hz.2
  change (E.nativeFubiniStudyFundamentalForm n (c.symm z)).compContinuousLinearMap
      (schemeNativeInverseChartDerivative f n p z) =
    ((E.nativeFubiniStudyFundamentalForm n (d.symm (schemeAnalyticCoordinateTransition f n p q z))).compContinuousLinearMap
      (schemeNativeInverseChartDerivative f n q (schemeAnalyticCoordinateTransition f n p q z))).compContinuousLinearMap
        (fderiv ℝ (schemeAnalyticCoordinateTransition f n p q) z)
  rw [hpoint, schemeNativeInverseChartDerivative_transition f n p q z hz]
  ext v
  rfl

private theorem map_pair {V W : Type*} (g : V → W) (u v : V) :
    g ∘ ![u, v] = ![g u, g v] := by
  funext i
  fin_cases i <;> rfl

/-- The actual native coefficient two-form is of type (1,1) on every true target. -/
theorem schemeNativeFubiniStudyCoefficients_type_one_one (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) (z : Fin n → ℂ)
    (hz : z ∈ (schemeAnalyticCoordinateChart f n p).target) (u v : Fin n → ℂ) :
    E.nativeFubiniStudyFormCoefficients n p z ![Complex.I • u, Complex.I • v] =
      E.nativeFubiniStudyFormCoefficients n p z ![u, v] := by
  let x := (schemeAnalyticCoordinateChart f n p).symm z
  let S := schemeNativeInverseChartDerivative f n p z
  change E.nativeFubiniStudyFundamentalForm n x (S ∘ ![Complex.I • u, Complex.I • v]) =
    E.nativeFubiniStudyFundamentalForm n x (S ∘ ![u, v])
  rw [map_pair, map_pair, schemeNativeInverseChartDerivative_map_I f n p z hz u,
    schemeNativeInverseChartDerivative_map_I f n p z hz v]
  exact E.nativeFubiniStudyFundamentalForm_type_one_one n x (S u) (S v)

/-- Actual inverse-derivative injection and genuine native FS positivity give strict coefficient positivity. -/
theorem schemeNativeFubiniStudyCoefficients_pos (E : ClosedProjectiveEmbedding f)
    (p : SchemeComplexPoint f) (z : Fin n → ℂ)
    (hz : z ∈ (schemeAnalyticCoordinateChart f n p).target) (v : Fin n → ℂ) (hv : v ≠ 0) :
    0 < E.nativeFubiniStudyFormCoefficients n p z ![v, Complex.I • v] := by
  let x := (schemeAnalyticCoordinateChart f n p).symm z
  let S := schemeNativeInverseChartDerivative f n p z
  have hSv : S v ≠ 0 := by
    intro h
    exact hv (schemeNativeInverseChartDerivative_injective f n p z hz (h.trans S.map_zero.symm))
  change 0 < E.nativeFubiniStudyFundamentalForm n x (S ∘ ![v, Complex.I • v])
  rw [map_pair, schemeNativeInverseChartDerivative_map_I f n p z hz v]
  exact E.nativeFubiniStudyFundamentalForm_pos n x (S v) hSv

end SGPT.Okounkov
