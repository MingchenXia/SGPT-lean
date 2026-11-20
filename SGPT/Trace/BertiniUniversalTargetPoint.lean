import SGPT.Trace.BertiniUniversalPhysicalCOV

/-! Actual q target/inverse retains the SAME original X point, read only
from literal retained ordinary X coordinates. No physical comparison premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Topology Manifold ContDiff BigOperators TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini

section General
variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)

omit [IsComplexManifold n X] in
theorem parameterEquationFlattening_X (i j : Fin (N + 1)) (e : ComplexChart n X) (m : Fin N)
    (w : ComplexModel (N + n)) :
    ((prodModelEquiv N n).symm (parameterEquationFlattening p i j e m w)).2 =
      ((prodModelEquiv N n).symm w).2 := by
  let L : ComplexModel (N + n) →L[ℂ] ComplexModel n :=
    (ContinuousLinearMap.snd ℂ (ComplexModel N) (ComplexModel n)).comp
      ((prodModelEquiv N n).symm : _ →L[ℂ] _)
  have hb : productCoordinateBasis N n (Sum.inl m) = prodModelEquiv N n (EuclideanSpace.single m 1,0) := by
    simp [productCoordinateBasis,Module.Basis.prod_apply,EuclideanSpace.basisFun_apply]
  have hzero : L (productCoordinateBasis N n (Sum.inl m)) = 0 := by
    change ((prodModelEquiv N n).symm (productCoordinateBasis N n (Sum.inl m))).2 = 0
    rw [hb,ContinuousLinearEquiv.symm_apply_apply]
  change L (w + (conormalGenerator p i e j 0 w - (productCoordinateBasis N n).repr w (Sum.inl m)) •
    productCoordinateBasis N n (Sum.inl m)) = L w
  rw [map_add,map_smul,hzero,smul_zero,add_zero]
end General

section Coordinates
variable {d N : ℕ}

def originalQTargetXCoordinates (m : Fin N) (y : ComplexModel (N + d)) : ComplexModel (d + 1) :=
  ((prodModelEquiv N (d + 1)).symm (parameterZeroInsert (m.castAdd (d + 1)) y)).2
end Coordinates

section Member
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalQTargetXCoordinates_apply (m : Fin N) (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    originalQTargetXCoordinates (d := d) m (originalQCoordinateMap p c m (prodModelEquiv N d (q.1.val,q.2.val))) =
      c.originalTangentCoordinateMap q.1.val q.2.val := by
  let z := prodModelEquiv N d (q.1.val,q.2.val)
  let v := parameterZeroInsert (c.m.natAdd N) z
  have hv : v ∈ c.Φ.target := by
    dsimp only [v,z]
    rw [originalZeroNormalPoint p c]
    exact c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  have hnormal : sliceToParameterFlattening p c m v (m.castAdd (d + 1)) = 0 := by
    rw [sliceToParameterFlattening_standard_normal p c m hv]
    simp [v,parameterZeroInsert]
  change ((prodModelEquiv N (d + 1)).symm (parameterZeroInsert (m.castAdd (d + 1))
    (parameterDelete (m.castAdd (d + 1)) (sliceToParameterFlattening (n := d + 1) p c m v)))).2 = _
  rw [parameterZeroInsert_delete,hnormal,zero_smul,sub_zero]
  change ((prodModelEquiv N (d + 1)).symm
    (parameterEquationFlattening p c.i c.j c.e m (c.Φ.invFun v))).2 = _
  rw [parameterEquationFlattening_X]
  exact congrArg (fun t : ComplexModel (N + (d + 1)) => ((prodModelEquiv N (d + 1)).symm (c.Φ.invFun t)).2)
    (originalZeroNormalPoint p c q.1.val q.2.val)

def originalQTargetX (m : Fin N) (y : ComplexModel (N + d)) : X :=
  c.e.val.symm (originalQTargetXCoordinates (d := d) m y)

theorem originalQTargetX_apply (m : Fin N) (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    originalQTargetX p c m (originalQCoordinateMap p c m (prodModelEquiv N d (q.1.val,q.2.val))) = c.tangentPoint q :=
  congrArg c.e.val.symm (originalQTargetXCoordinates_apply p c m q)

theorem originalLocalQInverse_X (m : Fin N) {z₀ : ComplexModel (N + d)}
    (Θ : LocalHolomorphicEquivAt (n := N + d) z₀) (hsrc : Θ.source ⊆ originalQSourceDomain p c)
    (hfun : Θ.toFun = originalQCoordinateMap p c m) {y : ComplexModel (N + d)} (hy : y ∈ Θ.target) :
    originalQSourceX p c (Θ.invFun y) = originalQTargetX p c m y := by
  let q := originalQSourcePair p c ⟨Θ.invFun y,hsrc (Θ.mapsTo_invFun hy)⟩
  have hq : prodModelEquiv N d (q.1.val,q.2.val) = Θ.invFun y := (prodModelEquiv N d).apply_symm_apply _
  have hforward : originalQCoordinateMap p c m (Θ.invFun y) = y := by
    rw [← hfun]
    exact Θ.right_inv y hy
  have h := originalQTargetX_apply p c m q
  rw [hq,hforward] at h
  exact h.symm
end Member
end SGPT.Trace.BertiniUniversal
