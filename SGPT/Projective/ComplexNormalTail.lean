import SGPT.Foundations.Analysis.Pending.NaturalOriginalComplementaryWedgeDuality
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Analysis.InnerProductSpace.LinearMap
import SGPT.Foundations.Analysis.Pending.LocalCurrentDeterminant
import SGPT.Projective.ComplexNormalForm

/-! The actual coordinate normal/tail maps and complex-positive wedge.
Blueprint: `complex-normal-tail.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalTail

open Set Filter
open scoped Topology Manifold ContDiff BigOperators InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms ConstantFormProducts TopDegreeDensity
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Literal actual complex-linear zero-head inclusion. -/
def tailInclusion (m : ℕ) : ComplexModel m →L[ℂ] ComplexModel (m + 1) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (Fin.cons 0 (fun i => z i))
    map_add' := by
      intro z w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.cons]
    map_smul' := by
      intro a z
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.cons] }

/-- Literal actual complex-linear tail projection. -/
def tailProjection (m : ℕ) : ComplexModel (m + 1) →L[ℂ] ComplexModel m :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => WithLp.toLp 2 (fun i => z i.succ)
    map_add' := by intro z w; ext i; rfl
    map_smul' := by intro a z; ext i; rfl }

@[simp] theorem tailInclusion_head (m : ℕ) (z : ComplexModel m) :
    tailInclusion m z 0 = 0 := rfl

@[simp] theorem tailInclusion_succ (m : ℕ) (z : ComplexModel m) (i : Fin m) :
    tailInclusion m z i.succ = z i := rfl

@[simp] theorem tailProjection_apply (m : ℕ) (z : ComplexModel (m + 1)) (i : Fin m) :
    tailProjection m z i = z i.succ := rfl

@[simp] theorem tailProjection_tailInclusion (m : ℕ) (z : ComplexModel m) :
    tailProjection m (tailInclusion m z) = z := by
  ext i
  rfl

/-- The entire actual zero-head hyperplane, without choosing coordinates
or a vector-space replacement for its points. -/
theorem tailInclusion_tailProjection_of_head_zero (m : ℕ)
    (z : ComplexModel (m + 1)) (hz : z 0 = 0) :
    tailInclusion m (tailProjection m z) = z := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.symm
  · rfl

/-- Actual complex inner-product preservation of the literal inclusion. -/
theorem tailInclusion_inner (m : ℕ) (z w : ComplexModel m) :
    inner ℂ (tailInclusion m z) (tailInclusion m w) = inner ℂ z w := by
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, tailInclusion_head,
    inner_zero_left, zero_add, tailInclusion_succ]

/-- The genuine actual linear isometry underlying zero-head insertion. -/
def tailIsometry (m : ℕ) : ComplexModel m →ₗᵢ[ℂ] ComplexModel (m + 1) :=
  (tailInclusion m).toLinearMap.isometryOfInner (tailInclusion_inner m)

@[simp] theorem tailIsometry_apply (m : ℕ) (z : ComplexModel m) :
    tailIsometry m z = tailInclusion m z := rfl

/-- Actual original head/tail complex-linear coordinate equivalence. -/
def headTailEquiv (m : ℕ) : (ℂ × ComplexModel m) ≃L[ℂ] ComplexModel (m + 1) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun z => WithLp.toLp 2 (Fin.cons z.1 (fun i => z.2 i))
    invFun := fun z => (z 0, tailProjection m z)
    left_inv := by intro z; ext <;> rfl
    right_inv := by intro z; ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    map_add' := by
      intro z w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    map_smul' := by
      intro a z
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl }

@[simp] theorem headTailEquiv_head (m : ℕ) (z : ℂ × ComplexModel m) :
    headTailEquiv m z 0 = z.1 := rfl

@[simp] theorem headTailEquiv_succ (m : ℕ) (z : ℂ × ComplexModel m) (i : Fin m) :
    headTailEquiv m z i.succ = z.2 i := rfl

@[simp] theorem headTailEquiv_symm (m : ℕ) (z : ComplexModel (m + 1)) :
    (headTailEquiv m).symm z = (z 0, tailProjection m z) := rfl

@[simp] theorem tailInclusion_coordinateVector (m : ℕ) (i : Fin m) :
    tailInclusion m (coordinateVector i) = coordinateVector i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [coordinateVector]
  · simp [coordinateVector, Fin.succ_inj]

/-- The actual interleaved positive tail is the SAME original top frame
after its first two real normal entries. -/
theorem topBasis_tail (m : ℕ) (i : Fin (2 * m)) :
    topBasis (m + 1) (Fin.cast (by omega : 2 * m + 1 + 1 = 2 * (m + 1)) i.succ.succ) =
      tailInclusion m (topBasis m i) := by
  obtain ⟨⟨j, k⟩, hjk⟩ :=
    (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).surjective
      (Fin.cast (Nat.mul_comm 2 m) i)
  have hnew : Fin.cast (Nat.mul_comm 2 (m + 1))
      (Fin.cast (by omega : 2 * m + 1 + 1 = 2 * (m + 1)) i.succ.succ) =
        finProdFinEquiv (j.succ, k) := by
    apply Fin.ext
    have hx := congrArg Fin.val hjk
    change k.val + 2 * j.val = i.val at hx
    change i.val + 1 + 1 = k.val + 2 * (j.val + 1)
    omega
  have hold : topBasis m i =
      if k = 0 then coordinateVector j else Complex.I • coordinateVector j := by
    rw [topBasis_apply, ← hjk]
    simp only [coordinateRealFrame, Equiv.symm_apply_apply]
  rw [topBasis_apply, hnew]
  simp only [coordinateRealFrame, Equiv.symm_apply_apply]
  rw [hold]
  by_cases hk : k = 0 <;> simp [hk, map_smul]

/-- The actual positive top frame is the two original normal vectors
followed by the literal entire positive tail. -/
theorem topBasis_cons_cons (m : ℕ) :
    (fun i : Fin (2 * m + 1 + 1) => topBasis (m + 1)
      (Fin.cast (by omega : 2 * m + 1 + 1 = 2 * (m + 1)) i)) =
        Fin.cons (coordinateVector (0 : Fin (m + 1)))
          (Fin.cons (Complex.I • coordinateVector (0 : Fin (m + 1)))
            (fun i => tailInclusion m (topBasis m i))) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change topBasis (m + 1) 0 = coordinateVector 0
    rw [topBasis_apply]
    simp [coordinateRealFrame, finProdFinEquiv, Fin.divNat, Fin.modNat]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change topBasis (m + 1) 1 = Complex.I • coordinateVector 0
      rw [topBasis_apply]
      have hlt : 1 < 2 * (m + 1) := by omega
      simp [coordinateRealFrame, finProdFinEquiv, Fin.divNat, Fin.modNat, Nat.mod_eq_of_lt hlt]
    · exact topBasis_tail m j

def headRealCovector (m : ℕ) : ComplexModel (m + 1) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (0 : Fin (m + 1))).restrictScalars ℝ)

def headImagCovector (m : ℕ) : ComplexModel (m + 1) →L[ℝ] ℝ :=
  Complex.imCLM.comp ((EuclideanSpace.proj (0 : Fin (m + 1))).restrictScalars ℝ)

@[simp] theorem headRealCovector_apply (m : ℕ) (z : ComplexModel (m + 1)) :
    headRealCovector m z = (z 0).re := rfl

@[simp] theorem headImagCovector_apply (m : ℕ) (z : ComplexModel (m + 1)) :
    headImagCovector m z = (z 0).im := rfl

/-- The literal complex-positive coordinate normal two-form. -/
def coordinateNormal (m : ℕ) : RealForm (m + 1) 2 :=
  coordinateWedge (CoordinateWedgeAssoc.oneForm (m + 1) (headRealCovector m))
    (CoordinateWedgeAssoc.oneForm (m + 1) (headImagCovector m))

/-- Exact actual exterior associativity, without a shuffle normalization
or a prescribed evaluation identity supplied by the caller. -/
theorem coordinate_normal_wedge_iterated (m : ℕ) (η : RealForm (m + 1) (2 * m)) :
    wedgeTo (by omega : 2 + 2 * m = 2 * m + 1 + 1) (coordinateNormal m) η =
      ClosedProductCurrents.oneWedge (headRealCovector m)
        (ClosedProductCurrents.oneWedge (headImagCovector m) η) := by
  change wedgeTo _ (wedgeTo (rfl : 1 + 1 = 2)
    (CoordinateWedgeAssoc.oneForm (m + 1) (headRealCovector m))
    (CoordinateWedgeAssoc.oneForm (m + 1) (headImagCovector m))) η = _
  rw [wedgeTo_assoc rfl _ (by omega : 1 + 2 * m = 2 * m + 1)
    (by omega : 1 + (2 * m + 1) = 2 * m + 1 + 1),
    wedgeTo_oneForm_eq_oneWedge, wedgeTo_oneForm_eq_oneWedge]

/-- The original complex-positive coordinate normal wedge has exactly
the top density of the actual entire tail pullback, sign PLUS and factor ONE. -/
theorem coordinate_normal_wedge_tail (m : ℕ) (η : RealForm (m + 1) (2 * m)) :
    topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1)) (coordinateNormal m) η) =
      topDensity (η.compContinuousLinearMap ((tailInclusion m).restrictScalars ℝ)) := by
  rw [← castForm_wedgeTo (by omega : 2 + 2 * m = 2 * m + 1 + 1)
    (by omega : 2 * m + 1 + 1 = 2 * (m + 1))
    (by omega : 2 + 2 * m = 2 * (m + 1)) (coordinateNormal m) η,
    coordinate_normal_wedge_iterated]
  unfold topDensity
  rw [castForm_apply]
  change ClosedProductCurrents.oneWedge (headRealCovector m)
      (ClosedProductCurrents.oneWedge (headImagCovector m) η)
      (fun i => topBasis (m + 1) (Fin.cast (by omega : 2 * m + 1 + 1 = 2 * (m + 1)) i)) =
    η (fun i => tailInclusion m (topBasis m i))
  rw [topBasis_cons_cons]
  apply LocalCurrentDeterminant.oneWedge_oneWedge_apply_cons_cons
  · simp [coordinateVector]
  · simp [coordinateVector]
  · intro i
    simp

  · simp [coordinateVector]
  · intro i
    simp

/-- The ACTUAL original first coordinate functional has operator norm one. -/
theorem norm_headProjection (m : ℕ) :
    ‖(EuclideanSpace.proj (0 : Fin (m + 1)) : ComplexModel (m + 1) →L[ℂ] ℂ)‖ = 1 := by
  let p : ComplexModel (m + 1) →L[ℂ] ℂ := EuclideanSpace.proj (0 : Fin (m + 1))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖z (0 : Fin (m + 1))‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using PiLp.norm_apply_le z (0 : Fin (m + 1))
  · have h := p.le_opNorm (coordinateVector (0 : Fin (m + 1)))
    change ‖(coordinateVector (0 : Fin (m + 1))) 0‖ ≤ ‖p‖ * ‖coordinateVector (0 : Fin (m + 1))‖ at h
    simpa [coordinateVector] using h

/-- The original normalized normalForm is literally the actual positive
coordinate normal two-form; no norm calibration is an input. -/
theorem normalForm_headProjection (m : ℕ) :
    ComplexNormalForm.normalForm
      (EuclideanSpace.proj (0 : Fin (m + 1)) : ComplexModel (m + 1) →L[ℂ] ℂ) =
      coordinateNormal m := by
  rw [ComplexNormalForm.normalForm, norm_headProjection]
  simp only [one_pow, inv_one, one_smul]
  rfl

/-- Exact requested original normalized coordinate-normal wedge identity,
on every arbitrary original real complementary form and full actual tail. -/
theorem normalForm_coordinate_wedge_tail (m : ℕ) (η : RealForm (m + 1) (2 * m)) :
    topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
      (ComplexNormalForm.normalForm
        (EuclideanSpace.proj (0 : Fin (m + 1)) : ComplexModel (m + 1) →L[ℂ] ℂ)) η) =
      topDensity (η.compContinuousLinearMap ((tailInclusion m).restrictScalars ℝ)) := by
  rw [normalForm_headProjection]
  exact coordinate_normal_wedge_tail m η

end SGPT.Projective.NumEq.CompleteIntersections.ComplexNormalTail
