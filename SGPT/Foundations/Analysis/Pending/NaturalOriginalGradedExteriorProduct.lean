import SGPT.Foundations.Analysis.Pending.XiaoComplexProducts
import Mathlib.GroupTheory.Perm.Fin

set_option autoImplicit false

/-! Actual arbitrary-degree normalized graded exterior products, with the original coefficient
norms and the literal total-degree transports. -/

noncomputable section

open Equiv Finset
open scoped Fin.NatCast

namespace SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ConstantFormProducts
  CoordinateWedgeAssoc XiaoComplexProducts ProductTestForms

/-- Exchange the actual ordered blocks, read in the original total degree. -/
def blockFlip (p q : ℕ) : Perm (Fin (p + q)) :=
  finAddFlip.trans (finCongr (Nat.add_comm q p))

theorem blockFlip_castAdd (p q : ℕ) (i : Fin p) :
    blockFlip p q (Fin.castAdd q i) = Fin.cast (Nat.add_comm q p) (Fin.natAdd q i) := by
  simp only [blockFlip, Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply]

theorem blockFlip_natAdd (p q : ℕ) (j : Fin q) :
    blockFlip p q (Fin.natAdd p j) = Fin.cast (Nat.add_comm q p) (Fin.castAdd p j) := by
  simp only [blockFlip, Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply]

private theorem rotate_pow_apply (N k : ℕ) (i : Fin N) :
    haveI := i.neZero; (finRotate N ^ k) i = i + (↑k : Fin N) := by
  let := i.neZero
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, finRotate_apply]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]

private theorem blockFlip_eq_rotate_pow (p q : ℕ) :
    blockFlip p q = finRotate (p + q) ^ q := by
  ext i
  let := i.neZero
  rw [rotate_pow_apply]
  have hadd : (i + (↑q : Fin (p + q))).val = (i.val + q) % (p + q) := by
    simp only [Fin.val_add, Fin.val_natCast]
    simp only [Nat.add_mod, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
  rw [hadd]
  by_cases hi : i.val < p
  · have hl : i.val + q < p + q := by omega
    simp only [blockFlip, Equiv.trans_apply, finAddFlip_apply_mk_left hi,
      finCongr_apply, Fin.val_cast]
    rw [Nat.mod_eq_of_lt hl]
    omega
  · have hp : p ≤ i.val := by omega
    have he : i.val + q = (p + q) + (i.val - p) := by omega
    have hl : i.val - p < p + q := by omega
    simp only [blockFlip, Equiv.trans_apply, finAddFlip_apply_mk_right hp,
      finCongr_apply, Fin.val_cast]
    rw [he, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hl]
    exact (Nat.mod_eq_of_lt hl).symm

/-- The sign is that of the actual permutation, including both empty blocks. -/
theorem blockFlip_sign (p q : ℕ) :
    ((Perm.sign (blockFlip p q) : ℤ) : ℝ) = (-1 : ℝ) ^ (p * q) := by
  by_cases hq : q = 0
  · subst q
    rw [blockFlip_eq_rotate_pow]
    simp
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hexp : (p + q - 1) * q = p * q + q * (q - 1) := by
      have hN : p + q - 1 = p + (q - 1) := by omega
      rw [hN, add_mul, mul_comm (q - 1) q]
    rw [blockFlip_eq_rotate_pow, map_pow, sign_finRotate]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [← pow_mul, hexp, pow_add, (Nat.even_mul_pred_self q).neg_one_pow, mul_one]

/-- Literal exchange of both whole factors and their entire original vector blocks. -/
theorem coordinateWedge_exchange_apply {n p q : ℕ} (A : RealForm n p) (B : RealForm n q)
    (v : Fin (p + q) → ComplexModel n) :
    coordinateWedge A B v =
      coordinateWedge B A (v ∘ (finAddFlip : Fin (p + q) ≃ Fin (q + p)).symm) := by
  rw [coordinateWedge_apply_perm, coordinateWedge_apply_perm,
    Nat.mul_comm q.factorial p.factorial]
  congr 1
  let f : Fin (p + q) ≃ Fin (q + p) := finAddFlip
  refine Fintype.sum_equiv f.permCongr _ _ fun π => ?_
  rw [Perm.sign_permCongr]
  have h1 : (v ∘ f.symm) ∘ (f.permCongr π) ∘ finSumFinEquiv ∘ Sum.inl =
      v ∘ π ∘ finSumFinEquiv ∘ Sum.inr := by
    funext i
    simp [Equiv.permCongr_apply, f, finAddFlip]
  have h2 : (v ∘ f.symm) ∘ (f.permCongr π) ∘ finSumFinEquiv ∘ Sum.inr =
      v ∘ π ∘ finSumFinEquiv ∘ Sum.inl := by
    funext i
    simp [Equiv.permCongr_apply, f, finAddFlip]
  rw [show (finAddFlip : Fin (p + q) ≃ Fin (q + p)) = f from rfl, h1, h2]
  ring

/-- Genuine arbitrary-degree graded commutativity of the normalized original exterior product. -/
theorem coordinateWedge_graded_comm {n p q : ℕ} (A : RealForm n p) (B : RealForm n q) :
    coordinateWedge A B = (-1 : ℝ) ^ (p * q) •
      castForm (Nat.add_comm q p) (coordinateWedge B A) := by
  ext v
  rw [coordinateWedge_exchange_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, castForm_apply]
  have hv : v ∘ (finAddFlip : Fin (p + q) ≃ Fin (q + p)).symm =
      (v ∘ Fin.cast (Nat.add_comm q p)) ∘ blockFlip q p := by
    funext i
    have hf : (finAddFlip : Fin (p + q) ≃ Fin (q + p)).symm =
        (finAddFlip : Fin (q + p) ≃ Fin (p + q)) := by
      ext j
      simp [finAddFlip]
    rw [hf]
    simp only [Function.comp_apply, blockFlip, Equiv.trans_apply, finCongr_apply]
    congr 1
  rw [hv, form_map_perm, blockFlip_sign, Nat.mul_comm q p]

/-- Both literal transports into any prescribed common degree have the actual graded sign. -/
theorem wedgeTo_graded_comm {n p q m : ℕ} (h : p + q = m) (h' : q + p = m)
    (A : RealForm n p) (B : RealForm n q) :
    wedgeTo h A B = (-1 : ℝ) ^ (p * q) • wedgeTo h' B A := by
  rw [wedgeTo, coordinateWedge_graded_comm, map_smul, castForm_castForm]
  rfl

section Global

variable {n a b p q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal equal-degree substitution of the same original smooth form. -/
def castSmoothForm (h : a = b) : SmoothRealForm n M a →ₗ[ℝ] SmoothRealForm n M b where
  toFun A := h ▸ A
  map_add' A B := by subst h; rfl
  map_smul' c A := by subst h; rfl

theorem castSmoothForm_coeff (h : a = b) (A : SmoothRealForm n M a)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (castSmoothForm h A).coeff e z = castForm h (A.coeff e z) := by
  subst h
  rfl

/-- The genuine original global smooth exterior product has the full arbitrary-degree sign. -/
theorem exteriorProduct_graded_comm (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    castSmoothForm (Nat.add_comm p q) (exteriorProduct A B) =
      (-1 : ℝ) ^ (p * q) • exteriorProduct B A := by
  apply smoothRealForm_ext
  intro e z
  rw [castSmoothForm_coeff, exteriorProduct_coeff]
  change castForm (Nat.add_comm p q) (coordinateWedge (A.coeff e z) (B.coeff e z)) =
    (-1 : ℝ) ^ (p * q) • coordinateWedge (B.coeff e z) (A.coeff e z)
  exact wedgeTo_graded_comm (Nat.add_comm p q) rfl (A.coeff e z) (B.coeff e z)

end Global

end SGPT.Foundations.Analysis.Pending.NaturalOriginalGradedExteriorProduct
