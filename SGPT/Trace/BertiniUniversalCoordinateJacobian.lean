import SGPT.Trace.BertiniUniversalNormalSliceJacobian

/-! Literal ordinary coordinate order and ACTUAL zero-normal original
member-to-q coordinate Jacobian. No full/fibre Jacobian identification premise. -/
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

section Coordinates
variable {N n : ℕ}

theorem productModel_apply_castAdd (u : ComplexModel N) (v : ComplexModel n) (m : Fin N) :
    prodModelEquiv N n (u,v) (m.castAdd n) = u m := by
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd]

theorem productModel_apply_natAdd (u : ComplexModel N) (v : ComplexModel n) (M : Fin n) :
    prodModelEquiv N n (u,v) (M.natAdd N) = v M := by
  simp [prodModelEquiv,EuclideanSpace.finAddEquivProd,EuclideanSpace.sumEquivProd]

theorem productCoordinateBasis_repr_parameter (w : ComplexModel (N + n)) (m : Fin N) :
    (productCoordinateBasis N n).repr w (Sum.inl m) = w (m.castAdd n) := by
  change (((EuclideanSpace.basisFun (Fin N) ℂ).toBasis).prod
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).repr ((prodModelEquiv N n).symm w) (Sum.inl m) = _
  rw [Module.Basis.prod_repr_inl]
  change ((prodModelEquiv N n).symm w).1 m = _
  have h := productModel_apply_castAdd ((prodModelEquiv N n).symm w).1 ((prodModelEquiv N n).symm w).2 m
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using h.symm

theorem productCoordinateBasis_repr_X (w : ComplexModel (N + n)) (M : Fin n) :
    (productCoordinateBasis N n).repr w (Sum.inr M) = w (M.natAdd N) := by
  change (((EuclideanSpace.basisFun (Fin N) ℂ).toBasis).prod
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).repr ((prodModelEquiv N n).symm w) (Sum.inr M) = _
  rw [Module.Basis.prod_repr_inr]
  change ((prodModelEquiv N n).symm w).2 M = _
  have h := productModel_apply_natAdd ((prodModelEquiv N n).symm w).1 ((prodModelEquiv N n).symm w).2 M
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using h.symm
end Coordinates

section General
variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart n (p : X → ComplexProjectiveSpace N) φ)

theorem sliceToParameterFlattening_standard_normal (m : Fin N) {v : ComplexModel (N + n)}
    (hv : v ∈ c.Φ.target) :
    sliceToParameterFlattening p c m v (m.castAdd n) = v (c.m.natAdd N) := by
  have h := sliceToParameterFlattening_normal p c m hv
  rw [productCoordinateBasis_repr_parameter] at h
  have hx : slCoord (N := N) c.m v = v (c.m.natAdd N) := by
    change ((prodModelEquiv N n).symm v).2 c.m = _
    exact productCoordinateBasis_repr_X v c.m
  exact h.trans hx

theorem differentiableAt_sliceToParameterFlattening (m : Fin N) {v : ComplexModel (N + n)}
    (hv : v ∈ c.Φ.target) : DifferentiableAt ℂ (sliceToParameterFlattening p c m) v := by
  let w := c.Φ.invFun v
  have hw : w ∈ conormalDomain p c.e c.j := c.source_subset (c.Φ.mapsTo_invFun hv)
  have hG := (differentiableOn_conormalGenerator p p.contMDiff c.i c.e c.j 0).differentiableAt
    ((isOpen_conormalDomain p p.contMDiff c.e c.j).mem_nhds hw)
  have hP : DifferentiableAt ℂ (parameterEquationFlattening p c.i c.j c.e m) w :=
    (coordinateReplacementMap_hasFDerivAt (productCoordinateBasis N n) (Sum.inl m) hG.hasFDerivAt).differentiableAt
  have hI : DifferentiableAt ℂ c.Φ.invFun v :=
    (c.Φ.invFun_holomorphic v hv).differentiableAt (c.Φ.isOpen_target.mem_nhds hv)
  exact hP.comp v hI
end General

section Member
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalSliceNormalJacobian_real_abs_det (m : Fin N) {z : ComplexModel (N + d)}
    (hz : parameterZeroInsert (c.m.natAdd N) z ∈ c.Φ.target) :
    |LinearMap.det (fderiv ℝ
      (normalSliceMap (d := N + d) (sliceToParameterFlattening (n := d + 1) p c m) (c.m.natAdd N) (m.castAdd (d + 1))) z).toLinearMap| =
      ‖parameterCoefficient p c.i c.j m
          (c.e.val.symm ((prodModelEquiv N (d + 1)).symm
            (c.Φ.invFun (parameterZeroInsert (c.m.natAdd N) z))).2) /
        conormalGenerator p c.i c.e c.j c.m.succ
          (c.Φ.invFun (parameterZeroInsert (c.m.natAdd N) z))‖ ^ 2 := by
  have hF := differentiableAt_sliceToParameterFlattening p c m hz
  have hcoord : (fun w => sliceToParameterFlattening p c m w (m.castAdd (d + 1)))
      =ᶠ[𝓝 (parameterZeroInsert (c.m.natAdd N) z)] (fun w => w (c.m.natAdd N)) := by
    filter_upwards [c.Φ.isOpen_target.mem_nhds hz] with w hw
    exact sliceToParameterFlattening_standard_normal p c m hw
  rw [normalSliceMap_real_abs_det (d := N + d) (c.m.natAdd N) (m.castAdd (d + 1)) hF hcoord]
  exact congrArg (fun t : ℂ => ‖t‖ ^ 2)
    (sliceToParameterFlattening_complex_det (n := d + 1) p c m hz)
end Member
end SGPT.Trace.BertiniUniversal
