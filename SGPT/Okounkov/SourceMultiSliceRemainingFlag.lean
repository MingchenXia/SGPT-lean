import SGPT.Okounkov.SourceMultiSliceOriginalInverse

/-! The actual remaining flag and zero-prefix coordinates retain every
original level and original tail coordinate of source rmk:slicepob. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set

/-- The literal original remaining index k+i. -/
def remainingIndex (m k : ℕ) (i : Fin (m + 1)) : Fin (m + k + 1) :=
  ⟨k + i.val, by omega⟩

/-- Every WHOLE original remaining flag carrier is retained, not just Y_k. -/
theorem originalInclusion_image_remainingFlag (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (i : Fin (m + 1)) :
    originalInclusion m k F '' (originalTail m k F).flag i =
      F.flag (remainingIndex m k i) := by
  induction k with
  | zero =>
      change id '' F.flag i = F.flag (remainingIndex m 0 i)
      rw [Set.image_id]
      congr 1
      exact Fin.ext (by simp only [remainingIndex, Nat.zero_add])
  | succ k ih =>
      have hidx : (remainingIndex m k i).succ = remainingIndex m (k + 1) i :=
        Fin.ext (by dsimp [remainingIndex]; omega)
      rw [← hidx]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        have hz : originalInclusion m k F.tail y ∈ F.tail.flag (remainingIndex m k i) := by
          rw [← ih F.tail]
          exact ⟨y,hy,rfl⟩
        exact hz
      · intro hx
        have hx1 : x ∈ F.flag (1 : Fin (m + k + 2)) :=
          F.smooth.2.1 (by change (1 : ℕ) ≤ (remainingIndex m k i).val + 1; omega) hx
        have hxT : (⟨x,hx1⟩ : F.tail.carrier) ∈ F.tail.flag (remainingIndex m k i) := hx
        have hxI : (⟨x,hx1⟩ : F.tail.carrier) ∈
            originalInclusion m k F.tail '' (originalTail m k F.tail).flag i := by
          rw [ih F.tail]
          exact hxT
        obtain ⟨y,hy,heq⟩ := hxI
        exact ⟨y,hy,congrArg Subtype.val heq⟩

/-- The canonical direct original Y_k identification retains precisely
all remaining original flag subsets, with whole image at every level. -/
theorem originalCarrierHomeomorph_image_remainingFlag (m k : ℕ)
    (F : OriginalFlagGeometry.{u} (m + k)) (i : Fin (m + 1)) :
    originalCarrierHomeomorph m k F '' (originalTail m k F).flag i =
      (Subtype.val ⁻¹' F.flag (remainingIndex m k i) : Set (F.flag (originalIndex m k))) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (originalCarrierHomeomorph m k F y).val ∈ F.flag (remainingIndex m k i)
    rw [originalCarrierHomeomorph_val, ← originalInclusion_image_remainingFlag m k F i]
    exact ⟨y,hy,rfl⟩
  · intro hx
    have hmem : x.val ∈ originalInclusion m k F '' (originalTail m k F).flag i := by
      rw [originalInclusion_image_remainingFlag]
      exact hx
    obtain ⟨y,hy,heq⟩ := hmem
    exact ⟨y,hy,Subtype.ext heq⟩

/-- The literal first k original coordinates are zero. -/
theorem zeroPrefix_first (m k : ℕ) (y : Fin m → ℝ) (i : Fin (m + k))
    (hi : i.val < k) : zeroPrefix m k y i = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro _
        rfl
      · intro hj
        exact ih j (by change j.val + 1 < k + 1 at hj; omega)

/-- The unchanged actual tail coordinates follow the k zeros. -/
theorem zeroPrefix_tail (m k : ℕ) (y : Fin m → ℝ) (j : Fin m) :
    zeroPrefix m k y (⟨k + j.val,by omega⟩ : Fin (m + k)) = y j := by
  induction k with
  | zero =>
      change y ⟨0 + j.val,by omega⟩ = y j
      congr 1
      exact Fin.ext (Nat.zero_add _)
  | succ k ih =>
      have hidx : (⟨k + 1 + j.val,by omega⟩ : Fin (m + (k + 1))) =
          (⟨k + j.val,by omega⟩ : Fin (m + k)).succ := Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [hidx]
      exact ih
end SGPT.Okounkov.SourceMultiSlice
