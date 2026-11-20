import SGPT.Trace.BertiniUniversalCoordinateJacobian
import SGPT.Trace.BertiniOriginalMetricResidueDensity

/-! Actual SAME original member point/Jacobian and physical-L residue
cancellation. No arbitrary K norm or desired Hodge comparison is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
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
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

section Product
variable {N d : ℕ}

private theorem XNormal_succAbove_parameter (M : Fin (d + 1)) (j : Fin N) :
    (M.natAdd N).succAbove (j.castAdd d) = j.castAdd (d + 1) := by
  have h : (j.castAdd d).castSucc < M.natAdd N := by
    change j.val < N + M.val
    omega
  rw [Fin.succAbove_of_castSucc_lt _ _ h]
  rfl

private theorem XNormal_succAbove_X (M : Fin (d + 1)) (j : Fin d) :
    (M.natAdd N).succAbove (j.natAdd N) = (M.succAbove j).natAdd N := by
  by_cases h : j.castSucc < M
  · have h' : (j.natAdd N).castSucc < M.natAdd N := by
      change N + j.val < N + M.val
      exact Nat.add_lt_add_left h N
    rw [Fin.succAbove_of_castSucc_lt _ _ h',Fin.succAbove_of_castSucc_lt _ _ h]
    rfl
  · have hM : M ≤ j.castSucc := le_of_not_gt h
    have h' : M.natAdd N ≤ (j.natAdd N).castSucc := by
      change N + M.val ≤ N + j.val
      exact Nat.add_le_add_left hM N
    rw [Fin.succAbove_of_le_castSucc _ _ h',Fin.succAbove_of_le_castSucc _ _ hM]
    apply Fin.ext
    simp [Nat.add_assoc]

theorem parameterZeroInsert_XProduct (M : Fin (d + 1)) (ζ : ComplexModel N) (b : ComplexModel d) :
    parameterZeroInsert (M.natAdd N) (prodModelEquiv N d (ζ,b)) =
      prodModelEquiv N (d + 1) (ζ,parameterZeroInsert M b) := by
  let v := prodModelEquiv N (d + 1) (ζ,parameterZeroInsert M b)
  have hdel : parameterDelete (M.natAdd N) v = prodModelEquiv N d (ζ,b) := by
    ext l
    cases l using Fin.addCases with
    | left j =>
      change v ((M.natAdd N).succAbove (j.castAdd d)) = prodModelEquiv N d (ζ,b) (j.castAdd d)
      rw [XNormal_succAbove_parameter,productModel_apply_castAdd]
      exact (productModel_apply_castAdd ζ b j).symm
    | right j =>
      change v ((M.natAdd N).succAbove (j.natAdd N)) = prodModelEquiv N d (ζ,b) (j.natAdd N)
      rw [XNormal_succAbove_X,productModel_apply_natAdd]
      rw [productModel_apply_natAdd]
      simp [parameterZeroInsert]
  have hv0 : v (M.natAdd N) = 0 := by
    rw [productModel_apply_natAdd]
    simp [parameterZeroInsert]
  rw [← hdel,parameterZeroInsert_delete,hv0,zero_smul,sub_zero]
end Product

section Member
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalZeroNormalPoint (ζ : ComplexModel N) (b : ComplexModel d) :
    parameterZeroInsert (c.m.natAdd N) (prodModelEquiv N d (ζ,b)) =
      flatProj c.m (prodModelEquiv N (d + 1) (ζ,c.tangentLift b)) := by
  rw [parameterZeroInsert_XProduct]
  have hsingle : EuclideanSpace.single c.m (c.z₀ c.m) =
      c.z₀ c.m • EuclideanSpace.single c.m (1 : ℂ) := by
    ext l
    by_cases hl : l = c.m <;> simp [hl]
  have hlift : c.tangentLift b = parameterZeroInsert c.m b + c.z₀ c.m • EuclideanSpace.single c.m 1 := by
    change EuclideanSpace.single c.m (c.z₀ c.m) + parameterZeroInsert c.m b = _
    rw [hsingle]
    exact add_comm _ _
  rw [hlift,flatProj_prod_update,flatProj_apply]
  have hc0 : slCoord (N := N) c.m (prodModelEquiv N (d + 1) (ζ,parameterZeroInsert c.m b)) = 0 := by
    rw [slCoord_apply,ContinuousLinearEquiv.symm_apply_apply]
    simp [parameterZeroInsert]
  rw [hc0,zero_smul,sub_zero]

def originalQCoordinateMap (m : Fin N) : ComplexModel (N + d) → ComplexModel (N + d) :=
  normalSliceMap (d := N + d) (sliceToParameterFlattening (n := d + 1) p c m)
    (c.m.natAdd N) (m.castAdd (d + 1))

theorem originalQCoordinateMap_real_abs_det (m : Fin N)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) :
    |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m) (prodModelEquiv N d (q.1.val,q.2.val))).toLinearMap| =
      ‖parameterCoefficient p c.i c.j m (c.tangentPoint q) / c.tangentNormalDenominator q‖ ^ 2 := by
  have hz : parameterZeroInsert (c.m.natAdd N) (prodModelEquiv N d (q.1.val,q.2.val)) ∈ c.Φ.target := by
    rw [originalZeroNormalPoint p c]
    exact c.mapsTo_target q.1.val q.1.property (c.tangentLift q.2.val) q.2.property
  have h := originalSliceNormalJacobian_real_abs_det p c m hz
  rw [originalZeroNormalPoint p c] at h
  exact h

variable [CompactSpace X]

theorem originalPhysicalResidueDensity_qJacobian (m : Fin N)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber
      (c.tangentPoint q))
    (hm : parameterCoefficient p c.i c.j m (c.tangentPoint q) ≠ 0) (w : ℝ≥0∞) :
    ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ • c.originalAmbientLValue p.contMDiff q L T‖ ^ 2) * w =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (originalQCoordinateMap p c m)
        (prodModelEquiv N d (q.1.val,q.2.val))).toLinearMap| *
      (ENNReal.ofReal (‖(parameterCoefficient p c.i c.j m (c.tangentPoint q))⁻¹ •
        c.originalAmbientLValue p.contMDiff q L T‖ ^ 2) * w) := by
  let A := parameterCoefficient p c.i c.j m (c.tangentPoint q)
  let G := c.tangentNormalDenominator q
  let u := c.originalAmbientLValue p.contMDiff q L T
  have hA : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  have hG : ‖G‖ ≠ 0 := norm_ne_zero_iff.mpr (c.tangentNormalDenominator_ne_zero p.contMDiff q)
  have hnorm : ‖G⁻¹ • u‖ ^ 2 = ‖A / G‖ ^ 2 * ‖A⁻¹ • u‖ ^ 2 := by
    rw [norm_smul,norm_smul,norm_inv,norm_div,norm_inv]
    field_simp
  rw [originalQCoordinateMap_real_abs_det p c m q]
  change ENNReal.ofReal (‖G⁻¹ • u‖ ^ 2) * w =
    ENNReal.ofReal (‖A / G‖ ^ 2) * (ENNReal.ofReal (‖A⁻¹ • u‖ ^ 2) * w)
  rw [hnorm,ENNReal.ofReal_mul (sq_nonneg _),mul_assoc]
end Member
end SGPT.Trace.BertiniUniversal
