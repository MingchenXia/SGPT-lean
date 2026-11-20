import SGPT.Trace.BertiniUniversalTargetPoint
import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure

/-! Actual ordinary product coordinates after deleting a genuine parameter
coordinate. The X reader is literal and the ordinary measure is produced. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set MeasureTheory
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

variable (k d : ℕ)
private theorem deletedParameterDimension : k + (d + 1) = k + 1 + d := by omega
def deletedParameterCoordinateEquiv :
    ComplexModel (k + (d + 1)) ≃ₗᵢ[ℂ] ComplexModel (k + 1 + d) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (finCongr (deletedParameterDimension k d))

def deletedParameterProductEquiv :
    (ComplexModel k × ComplexModel (d + 1)) ≃L[ℂ] ComplexModel (k + 1 + d) :=
  (prodModelEquiv k (d + 1)).trans (deletedParameterCoordinateEquiv k d).toContinuousLinearEquiv

private theorem deletedParameterCoordinateEquiv_apply (v : ComplexModel (k + (d + 1)))
    (j : Fin (k + (d + 1))) :
    deletedParameterCoordinateEquiv k d v ((finCongr (deletedParameterDimension k d)) j) = v j := by
  simp [deletedParameterCoordinateEquiv,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

private theorem deletedParameterProduct_parameter (b : ComplexModel k) (z : ComplexModel (d + 1)) (j : Fin k) :
    deletedParameterProductEquiv k d (b,z) ((finCongr (deletedParameterDimension k d)) (j.castAdd (d + 1))) = b j := by
  change deletedParameterCoordinateEquiv k d (prodModelEquiv k (d + 1) (b,z)) _ = _
  rw [deletedParameterCoordinateEquiv_apply,productModel_apply_castAdd]

private theorem deletedParameterProduct_X (b : ComplexModel k) (z : ComplexModel (d + 1)) (j : Fin (d + 1)) :
    deletedParameterProductEquiv k d (b,z) ((finCongr (deletedParameterDimension k d)) (j.natAdd k)) = z j := by
  change deletedParameterCoordinateEquiv k d (prodModelEquiv k (d + 1) (b,z)) _ = _
  rw [deletedParameterCoordinateEquiv_apply,productModel_apply_natAdd]

private theorem parameter_succAbove_parameter (m : Fin (k + 1)) (j : Fin k) :
    (m.castAdd (d + 1)).succAbove ((finCongr (deletedParameterDimension k d)) (j.castAdd (d + 1))) =
      (m.succAbove j).castAdd (d + 1) := by
  by_cases h : j.castSucc < m
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    have h' : (((finCongr (deletedParameterDimension k d)) (j.castAdd (d + 1))) : Fin (k + 1 + d)).castSucc < m.castAdd (d + 1) := by
      change j.val < m.val
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h']
    rfl
  · have hle : m ≤ j.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hle]
    have h' : m.castAdd (d + 1) ≤ (((finCongr (deletedParameterDimension k d)) (j.castAdd (d + 1))) : Fin (k + 1 + d)).castSucc := by
      change m.val ≤ j.val
      exact hle
    rw [Fin.succAbove_of_le_castSucc _ _ h']
    rfl

private theorem parameter_succAbove_X (m : Fin (k + 1)) (j : Fin (d + 1)) :
    (m.castAdd (d + 1)).succAbove ((finCongr (deletedParameterDimension k d)) (j.natAdd k)) =
      j.natAdd (k + 1) := by
  have h : m.castAdd (d + 1) ≤ (((finCongr (deletedParameterDimension k d)) (j.natAdd k)) : Fin (k + 1 + d)).castSucc := by
    change m.val ≤ k + j.val
    omega
  rw [Fin.succAbove_of_le_castSucc _ _ h]
  apply Fin.ext
  change k + j.val + 1 = (k + 1) + j.val
  omega

theorem deletedParameterProduct_zeroInsert (m : Fin (k + 1)) (b : ComplexModel k) (z : ComplexModel (d + 1)) :
    parameterZeroInsert (m.castAdd (d + 1)) (deletedParameterProductEquiv k d (b,z)) =
      prodModelEquiv (k + 1) (d + 1) (parameterZeroInsert m b,z) := by
  ext j
  rcases (@finSumFinEquiv (k + 1) (d + 1)).surjective j with ⟨q,rfl⟩
  cases q with
  | inl q =>
    change parameterZeroInsert (m.castAdd (d + 1)) (deletedParameterProductEquiv k d (b,z)) (q.castAdd (d + 1)) =
      prodModelEquiv (k + 1) (d + 1) (parameterZeroInsert m b,z) (q.castAdd (d + 1))
    rw [productModel_apply_castAdd]
    rcases Fin.eq_self_or_eq_succAbove m q with rfl | ⟨a,rfl⟩
    · simp [parameterZeroInsert]
    · rw [← parameter_succAbove_parameter k d m a]
      simp only [parameterZeroInsert,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
        Fin.insertNth_apply_succAbove]
      exact deletedParameterProduct_parameter k d b z a
  | inr q =>
    change parameterZeroInsert (m.castAdd (d + 1)) (deletedParameterProductEquiv k d (b,z)) (q.natAdd (k + 1)) =
      prodModelEquiv (k + 1) (d + 1) (parameterZeroInsert m b,z) (q.natAdd (k + 1))
    rw [productModel_apply_natAdd,← parameter_succAbove_X k d m q]
    simp only [parameterZeroInsert,LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
      Fin.insertNth_apply_succAbove]
    exact deletedParameterProduct_X k d b z q

theorem originalQTargetXCoordinates_product (m : Fin (k + 1)) (b : ComplexModel k) (z : ComplexModel (d + 1)) :
    originalQTargetXCoordinates (d := d) m (deletedParameterProductEquiv k d (b,z)) = z := by
  unfold originalQTargetXCoordinates
  rw [deletedParameterProduct_zeroInsert,ContinuousLinearEquiv.symm_apply_apply]

theorem measurePreserving_deletedParameterProductEquiv :
    MeasurePreserving (deletedParameterProductEquiv k d) (volume.prod volume) volume := by
  let J := deletedParameterCoordinateEquiv k d
  have hJ := (IsometryEquiv.toRealLinearIsometryEquivOfMapZero J.toIsometryEquiv
    (by rw [LinearIsometryEquiv.coe_toIsometryEquiv]; exact map_zero _)).measurePreserving
  rw [IsometryEquiv.coe_toRealLinearIsometryEquivOfMapZero] at hJ
  exact hJ.comp (ProductMixedMeasure.measurePreserving_prodModelEquiv k (d + 1))

end SGPT.Trace.BertiniUniversal
