import SGPT.Trace.BertiniUniversalJacobian

/-! Actual ORIGINAL member-normal flattening and true parameter/member
complex/ordinary-real Jacobian ratio, retaining the SAME original equation. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter Metric
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

omit [IsComplexManifold n X] in
theorem flatMap_eq_coordinateReplacement (i : Fin (N + 1)) (e : ComplexChart n X)
    (j : Fin (N + 1)) (M : Fin n) (w : ComplexModel (N + n)) :
    flatMap p i e j M w = coordinateReplacementMap (productCoordinateBasis N n)
      (Sum.inr M) (conormalGenerator p i e j 0) w := by
  have hb : productCoordinateBasis N n (Sum.inr M) = slDir (N := N) M := by
    simp [productCoordinateBasis,Module.Basis.prod_apply,EuclideanSpace.basisFun_apply,slDir]
  have hc : (productCoordinateBasis N n).repr w (Sum.inr M) = slCoord (N := N) M w := by
    change (((EuclideanSpace.basisFun (Fin N) ℂ).toBasis).prod
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).repr ((prodModelEquiv N n).symm w) (Sum.inr M) = _
    rw [Module.Basis.prod_repr_inr]
    rfl
  rw [coordinateReplacementMap,hb,hc]
  rfl

theorem flatMap_complex_det (i : Fin (N + 1)) (e : ComplexChart n X) (j : Fin (N + 1))
    (M : Fin n) {w : ComplexModel (N + n)} (hw : w ∈ conormalDomain p e j) :
    LinearMap.det (fderiv ℂ (flatMap p i e j M) w).toLinearMap = conormalGenerator p i e j M.succ w := by
  have hG := (differentiableOn_conormalGenerator p p.contMDiff i e j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff e j).mem_nhds hw)
  rw [funext (flatMap_eq_coordinateReplacement p i e j M),
    (coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inr M) hG.hasFDerivAt).fderiv,
    coordinateReplacementDerivative_det]
  have hb : productCoordinateBasis N n (Sum.inr M) = slDir (N := N) M := by
    simp [productCoordinateBasis,Module.Basis.prod_apply,EuclideanSpace.basisFun_apply,slDir]
  rw [hb]
  exact fderiv_conormalGenerator_zero_slDir p p.contMDiff hw M

variable {φ : X → EReal} (c : SliceChart n (p : X → ComplexProjectiveSpace N) φ)

theorem sliceInverse_complex_det {v : ComplexModel (N + n)} (hv : v ∈ c.Φ.target) :
    LinearMap.det (fderiv ℂ c.Φ.invFun v).toLinearMap =
      (conormalGenerator p c.i c.e c.j c.m.succ (c.Φ.invFun v))⁻¹ := by
  let w := c.Φ.invFun v
  have hw : w ∈ c.Φ.source := c.Φ.mapsTo_invFun hv
  have hF : DifferentiableAt ℂ c.Φ.toFun w :=
    (c.Φ.toFun_holomorphic w hw).differentiableAt (c.Φ.isOpen_source.mem_nhds hw)
  have hI : DifferentiableAt ℂ c.Φ.invFun v :=
    (c.Φ.invFun_holomorphic v hv).differentiableAt (c.Φ.isOpen_target.mem_nhds hv)
  have heq : (c.Φ.toFun ∘ c.Φ.invFun) =ᶠ[𝓝 v] id := by
    filter_upwards [c.Φ.isOpen_target.mem_nhds hv] with z hz
    exact c.Φ.right_inv z hz
  have hD := ((hF.hasFDerivAt.comp v hI.hasFDerivAt).congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_id v)
  have hdet := congrArg (fun A : ComplexModel (N + n) →L[ℂ] ComplexModel (N + n) => LinearMap.det A.toLinearMap) hD
  change LinearMap.det ((fderiv ℂ c.Φ.toFun w).toLinearMap.comp (fderiv ℂ c.Φ.invFun v).toLinearMap) =
    LinearMap.det (LinearMap.id : ComplexModel (N + n) →ₗ[ℂ] ComplexModel (N + n)) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  have hflat : LinearMap.det (fderiv ℂ c.Φ.toFun w).toLinearMap = conormalGenerator p c.i c.e c.j c.m.succ w := by
    rw [c.toFun_eq]
    exact flatMap_complex_det p c.i c.e c.j c.m (c.source_subset hw)
  rw [hflat] at hdet
  have hGM : conormalGenerator p c.i c.e c.j c.m.succ w ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hdet
    exact zero_ne_one hdet
  have hi : LinearMap.det (fderiv ℂ c.Φ.invFun v).toLinearMap =
      1 * (conormalGenerator p c.i c.e c.j c.m.succ w)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hGM).mpr (by simpa only [mul_comm] using hdet)
  simpa only [one_mul] using hi

def sliceToParameterFlattening (m : Fin N) : ComplexModel (N + n) → ComplexModel (N + n) :=
  parameterEquationFlattening p c.i c.j c.e m ∘ c.Φ.invFun

theorem sliceToParameterFlattening_complex_det (m : Fin N) {v : ComplexModel (N + n)}
    (hv : v ∈ c.Φ.target) :
    LinearMap.det (fderiv ℂ (sliceToParameterFlattening p c m) v).toLinearMap =
      parameterCoefficient p c.i c.j m (c.e.val.symm ((prodModelEquiv N n).symm (c.Φ.invFun v)).2) /
        conormalGenerator p c.i c.e c.j c.m.succ (c.Φ.invFun v) := by
  let w := c.Φ.invFun v
  have hw : w ∈ conormalDomain p c.e c.j := c.source_subset (c.Φ.mapsTo_invFun hv)
  have hG := (differentiableOn_conormalGenerator p p.contMDiff c.i c.e c.j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff c.e c.j).mem_nhds hw)
  have hP : DifferentiableAt ℂ (parameterEquationFlattening p c.i c.j c.e m) w :=
    (coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inl m) hG.hasFDerivAt).differentiableAt
  have hI : DifferentiableAt ℂ c.Φ.invFun v :=
    (c.Φ.invFun_holomorphic v hv).differentiableAt (c.Φ.isOpen_target.mem_nhds hv)
  unfold sliceToParameterFlattening
  rw [(hP.hasFDerivAt.comp v hI.hasFDerivAt).fderiv]
  change LinearMap.det ((fderiv ℂ (parameterEquationFlattening p c.i c.j c.e m) w).toLinearMap.comp
    (fderiv ℂ c.Φ.invFun v).toLinearMap) = _
  rw [LinearMap.det_comp,parameterEquationFlattening_complex_det p c.i c.j c.e m hw,
    sliceInverse_complex_det p c hv,div_eq_mul_inv]

theorem sliceToParameterFlattening_real_abs_det (m : Fin N) {v : ComplexModel (N + n)}
    (hv : v ∈ c.Φ.target) :
    |LinearMap.det (fderiv ℝ (sliceToParameterFlattening p c m) v).toLinearMap| =
      ‖parameterCoefficient p c.i c.j m (c.e.val.symm ((prodModelEquiv N n).symm (c.Φ.invFun v)).2) /
        conormalGenerator p c.i c.e c.j c.m.succ (c.Φ.invFun v)‖ ^ 2 := by
  let w := c.Φ.invFun v
  have hw : w ∈ conormalDomain p c.e c.j := c.source_subset (c.Φ.mapsTo_invFun hv)
  have hG := (differentiableOn_conormalGenerator p p.contMDiff c.i c.e c.j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff c.e c.j).mem_nhds hw)
  have hP : DifferentiableAt ℂ (parameterEquationFlattening p c.i c.j c.e m) w :=
    (coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inl m) hG.hasFDerivAt).differentiableAt
  have hI : DifferentiableAt ℂ c.Φ.invFun v :=
    (c.Φ.invFun_holomorphic v hv).differentiableAt (c.Φ.isOpen_target.mem_nhds hv)
  have hT : DifferentiableAt ℂ (sliceToParameterFlattening p c m) v := hP.comp v hI
  rw [hT.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ (sliceToParameterFlattening p c m) v).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq,
    sliceToParameterFlattening_complex_det p c m hv]

theorem sliceToParameterFlattening_normal (m : Fin N) {v : ComplexModel (N + n)}
    (hv : v ∈ c.Φ.target) :
    (productCoordinateBasis N n).repr (sliceToParameterFlattening p c m v) (Sum.inl m) = slCoord c.m v := by
  have hG : (productCoordinateBasis N n).repr
      (parameterEquationFlattening p c.i c.j c.e m (c.Φ.invFun v)) (Sum.inl m) =
      conormalGenerator p c.i c.e c.j 0 (c.Φ.invFun v) := by
    simp [parameterEquationFlattening,coordinateReplacementMap]
  have h := congrArg (slCoord (N := N) c.m) (c.Φ.right_inv v hv)
  rw [c.toFun_eq,slCoord_flatMap] at h
  exact hG.trans h

end SGPT.Trace.BertiniUniversal
