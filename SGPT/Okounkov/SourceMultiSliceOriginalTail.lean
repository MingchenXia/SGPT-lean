import SGPT.Okounkov.SourceSliceAllDimensions
import SGPT.Okounkov.FlagLiftingTail

/-! Actual all-k original tails and zero-prefix slices for source rmk:slicepob.
Every point inclusion and whole original carrier is manufactured internally. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov.SourceMultiSlice
open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalMain SGPT.Okounkov.TranscendentalWN

/-- The original k-th flag index with n=m+k; this includes k=0 and k=n. -/
def originalIndex (m k : ℕ) : Fin (m + k + 1) := ⟨k, by omega⟩

/-- The true original nested tail, with its actual inherited complex atlas. -/
def originalTail (m : ℕ) : (k : ℕ) → OriginalFlagGeometry.{u} (m + k) → OriginalFlagGeometry.{u} m
  | 0, F => F
  | k + 1, F => originalTail m k F.tail

/-- Literal projection to the same original point, retaining all nested subtype data. -/
def originalInclusion (m : ℕ) : (k : ℕ) → (F : OriginalFlagGeometry.{u} (m + k)) →
    (originalTail m k F).carrier → F.carrier
  | 0, _ => id
  | k + 1, F => Subtype.val ∘ originalInclusion m k F.tail

/-- The actual original inclusion is holomorphic, with original dimensions m and m+k. -/
theorem originalInclusion_contMDiff (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + k)) ∞
      (originalInclusion m k F) := by
  induction k with
  | zero => exact contMDiff_id
  | succ k ih => exact (contMDiff_firstFlagInclusion F).comp (ih F.tail)

/-- No unrelated model points enter the actual original tail. -/
theorem originalInclusion_injective (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    Function.Injective (originalInclusion m k F) := by
  induction k with
  | zero => exact Function.injective_id
  | succ k ih => exact Subtype.val_injective.comp (ih F.tail)

/-- The whole carrier image is precisely original Y_k, including both endpoint indices. -/
theorem originalInclusion_range (m k : ℕ) (F : OriginalFlagGeometry.{u} (m + k)) :
    Set.range (originalInclusion m k F) = F.flag (originalIndex m k) := by
  induction k with
  | zero =>
      change Set.range (id : F.carrier → F.carrier) = F.flag 0
      rw [Set.range_id, F.smooth.1]
  | succ k ih =>
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        have hy : originalInclusion m k F.tail y ∈ F.tail.flag (originalIndex m k) := by
          rw [← ih F.tail]
          exact mem_range_self y
        exact hy
      · intro hx
        have hx1 : x ∈ F.flag (1 : Fin (m + k + 2)) :=
          F.smooth.2.1 (by change (1 : ℕ) ≤ k + 1; omega) hx
        have hxTail : (⟨x, hx1⟩ : F.tail.carrier) ∈ F.tail.flag (originalIndex m k) := hx
        rw [← ih F.tail] at hxTail
        obtain ⟨y, hy⟩ := hxTail
        exact ⟨y, congrArg Subtype.val hy⟩

/-- The actual source tuple with exactly k initial zero coordinates. -/
def zeroPrefix (m : ℕ) : (k : ℕ) → (Fin m → ℝ) → (Fin (m + k) → ℝ)
  | 0, y => y
  | k + 1, y => Fin.cons 0 (zeroPrefix m k y)

/-- The actual first-k-zero slice is a literal inverse image. -/
def zeroSlice (m k : ℕ) (B : Set (Fin (m + k) → ℝ)) : Set (Fin m → ℝ) :=
  (zeroPrefix m k) ⁻¹' B

/-- Literal recursion relates all-k slicing to the actual first-coordinate slice. -/
theorem zeroSlice_succ (m k : ℕ) (B : Set (Fin (m + (k + 1)) → ℝ)) :
    zeroSlice m (k + 1) B = zeroSlice m k (firstCoordinateSlice B 0) := rfl

/-- The unchanged original zero-prefix preimage commutes with arbitrary intersections. -/
theorem zeroSlice_iInter (m k : ℕ) {ι : Sort*}
    (B : ι → Set (Fin (m + k) → ℝ)) :
    zeroSlice m k (⋂ i, B i) = ⋂ i, zeroSlice m k (B i) := by
  ext y
  simp only [zeroSlice, mem_preimage, mem_iInter]
end SGPT.Okounkov.SourceMultiSlice
