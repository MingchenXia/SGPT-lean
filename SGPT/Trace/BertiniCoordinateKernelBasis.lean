import SGPT.Trace.BertiniConormalResidueAdjunction

/-! Explicit coordinate regular-conormal kernel bases and actual nonzero volume. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SGPT.Trace.Bertini

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {d : ℕ}

private def coordinateDelete (k : Fin (d + 1)) : ComplexModel (d + 1) →ₗ[ℂ] ComplexModel d where
  toFun x := WithLp.toLp 2 (fun j => x (k.succAbove j))
  map_add' _ _ := by ext j; rfl
  map_smul' _ _ := by ext j; rfl

private def coordinateKernelLift (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ) (k : Fin (d + 1)) :
    ComplexModel d →ₗ[ℂ] ComplexModel (d + 1) :=
  (tangentCoordinateInsert k).toLinearMap -
    (((ell (EuclideanSpace.single k 1))⁻¹ • ell).comp
      (tangentCoordinateInsert k).toLinearMap).smulRight (EuclideanSpace.single k 1)

private theorem coordinateKernelLift_mem (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (hk : ell (EuclideanSpace.single k 1) ≠ 0) (b : ComplexModel d) :
    coordinateKernelLift ell k b ∈ LinearMap.ker ell := by
  change ell (tangentCoordinateInsert k b -
    ((ell (EuclideanSpace.single k 1))⁻¹ * ell (tangentCoordinateInsert k b)) •
      EuclideanSpace.single k 1) = 0
  rw [map_sub, map_smul, smul_eq_mul]
  field_simp [hk]
  ring

private theorem coordinateDelete_lift (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (b : ComplexModel d) :
    coordinateDelete k (coordinateKernelLift ell k b) = b := by
  ext j
  simp [coordinateDelete, coordinateKernelLift, tangentCoordinateInsert, Fin.succAbove_ne]

private theorem coordinateKernelLift_delete (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (hk : ell (EuclideanSpace.single k 1) ≠ 0)
    (x : LinearMap.ker ell) : coordinateKernelLift ell k (coordinateDelete k x.val) = x.val := by
  let b := coordinateDelete k x.val
  let gm := ell (EuclideanSpace.single k 1)
  have hsplit : x.val = tangentCoordinateInsert k b + x.val k • EuclideanSpace.single k 1 := by
    ext j
    rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩ <;>
      simp [tangentCoordinateInsert, b, coordinateDelete, Fin.succAbove_ne]
  have hz : ell (tangentCoordinateInsert k b) + x.val k * gm = 0 := by
    have h := x.property
    change ell x.val = 0 at h
    rw [hsplit, map_add, map_smul, smul_eq_mul] at h
    exact h
  have hxk : x.val k = -(gm⁻¹ * ell (tangentCoordinateInsert k b)) := by
    apply mul_right_cancel₀ hk
    calc
      x.val k * gm = -ell (tangentCoordinateInsert k b) := by linear_combination hz
      _ = (-(gm⁻¹ * ell (tangentCoordinateInsert k b))) * gm := by
        field_simp [show gm ≠ 0 from hk]
  change tangentCoordinateInsert k b - (gm⁻¹ * ell (tangentCoordinateInsert k b)) •
    EuclideanSpace.single k 1 = x.val
  calc
    _ = tangentCoordinateInsert k b + x.val k • EuclideanSpace.single k 1 := by
      rw [hxk, neg_smul, sub_eq_add_neg]
    _ = x.val := hsplit.symm

def coordinateConormalKernelEquiv (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (hk : ell (EuclideanSpace.single k 1) ≠ 0) :
    ComplexModel d ≃ₗ[ℂ] LinearMap.ker ell := by
  let R := (coordinateKernelLift ell k).codRestrict (LinearMap.ker ell)
    (coordinateKernelLift_mem ell k hk)
  apply LinearEquiv.ofBijective R
  constructor
  · intro b c hbc
    have h := congrArg (fun x : LinearMap.ker ell => coordinateDelete k x.val) hbc
    exact (coordinateDelete_lift ell k b).symm.trans (h.trans (coordinateDelete_lift ell k c))
  · intro x
    refine ⟨coordinateDelete k x.val, ?_⟩
    apply Subtype.ext
    exact coordinateKernelLift_delete ell k hk x

theorem coordinateConormalKernelEquiv_apply (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (hk : ell (EuclideanSpace.single k 1) ≠ 0) (b : ComplexModel d) :
    (coordinateConormalKernelEquiv ell k hk b).val =
      tangentCoordinateInsert k b -
        ((ell (EuclideanSpace.single k 1))⁻¹ * ell (tangentCoordinateInsert k b)) •
          EuclideanSpace.single k 1 := rfl

theorem coordinateConormalTuple_volume_ne_zero (ell : ComplexModel (d + 1) →ₗ[ℂ] ℂ)
    (k : Fin (d + 1)) (hk : ell (EuclideanSpace.single k 1) ≠ 0) :
    (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
      (Matrix.vecCons ((ell (EuclideanSpace.single k 1))⁻¹ • EuclideanSpace.single k 1)
        (fun j => (coordinateConormalKernelEquiv ell k hk
          ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)).val)) ≠ 0 := by
  let nu : ComplexModel (d + 1) := (ell (EuclideanSpace.single k 1))⁻¹ • EuclideanSpace.single k 1
  have hnu : ell nu = 1 := by
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hk
  let b := (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.map (coordinateConormalKernelEquiv ell k hk)
  let B := Module.Basis.mkFinCons nu b
    (by
      intro c x hx hcx
      have h := congrArg ell hcx
      simpa only [map_add, map_smul, hnu, LinearMap.mem_ker.mp hx, smul_eq_mul,
        mul_one, add_zero, map_zero] using h)
    (by
      intro z
      refine ⟨-ell z, ?_⟩
      change ell (z + (-ell z) • nu) = 0
      simp [hnu])
  have hB : (B : Fin (d + 1) → ComplexModel (d + 1)) =
      Matrix.vecCons nu (fun j => (b j).val) := Module.Basis.coe_mkFinCons _ _ _ _
  change (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
    (Matrix.vecCons nu (fun j => (b j).val)) ≠ 0
  rw [← hB]
  exact ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.isUnit_det B).ne_zero

end SGPT.Trace.Bertini
