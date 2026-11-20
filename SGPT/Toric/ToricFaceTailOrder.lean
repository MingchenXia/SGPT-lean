import SGPT.Toric.ToricFacePrimeDivisors
import SGPT.Toric.ToricFaceFlagComplex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original base vertex lies on its SAME selected face. -/
def toricFaceBaseVertex (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ToricNativeFaceVertex (hs := hs) v J := ⟨v, toricNativeFace_vertex_mem v J⟩

/-- Exact source selected-ray membership, from genuine native ray injectivity. -/
theorem toricFaceBase_ray_mem_iff (v : latticePolytopeVertices γ) (J : Set (Fin n)) (k : Fin n) :
    polytopeToricRay γ hs v k ∈ polytopeToricRay γ hs v '' J ↔ k ∈ J := by
  constructor
  · rintro ⟨j, hj, hjk⟩
    have h := polytopeToricRayGenerator_injective hs v (congrArg Subtype.val hjk)
    exact h ▸ hj
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Genuine finite tail indices, retaining the ORIGINAL order j↦k+j. -/
def finToricTailIndexEquiv (n k : ℕ) (hk : k ≤ n) :
    Fin (n - k) ≃ {i : Fin n // k ≤ i.val} where
  toFun j := ⟨⟨k + j.val, by omega⟩, by change k ≤ k + j.val; omega⟩
  invFun i := ⟨i.val.val - k, by omega⟩
  left_inv j := by apply Fin.ext; change k + j.val - k = j.val; omega
  right_inv i := by apply Subtype.ext; apply Fin.ext; change k + (i.val.val - k) = i.val.val; omega

/-- Exact selected prefix membership in the ORIGINAL ambient ordering. -/
theorem mem_toricFlagSelectedIndices_iff (e : Fin n ≃ Fin n) (i : Fin (n + 1)) (k : Fin n) :
    k ∈ toricFlagSelectedIndices e i ↔ (e.symm k).val < i.val := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    change l.val < i.val at hl
    simpa only [Equiv.symm_apply_apply] using hl
  · intro hk
    exact ⟨e.symm k, hk, e.apply_symm_apply k⟩

/-- The actual remaining ORIGINAL coordinates, in their original order. -/
def toricFlagRemainingIndexEquiv (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Fin (n - i.val) ≃ {k : Fin n // k ∉ toricFlagSelectedIndices e i} :=
  (finToricTailIndexEquiv n i.val (by omega)).trans
    (e.subtypeEquiv (by
      intro l
      rw [mem_toricFlagSelectedIndices_iff, Equiv.symm_apply_apply]
      omega))

/-- Genuine conversion from the actual complement indices to the actual
native source cone rays outside σ, using true source ray injectivity. -/
def toricFaceBaseFreeIndexEquiv (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    {k : Fin n // k ∉ J} ≃
      {k : Fin n // polytopeToricRay γ hs (toricFaceBaseVertex (hs := hs) v J).val k ∉
        polytopeToricRay γ hs v '' J} :=
  (Equiv.refl (Fin n)).subtypeEquiv (fun k => (not_congr (toricFaceBase_ray_mem_iff v J k)).symm)

/-- The ACTUAL target native flag ordering whose free primitive rays follow
the remaining ORIGINAL ambient order. It is produced from the genuine
free-factor bijection and literal tail-index map, without a flag certificate. -/
def toricFaceTailOrder (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1)) :
    Fin (toricFaceDimension (toricFlagSelectedIndices e i)) ≃
      Fin (toricFaceDimension (toricFlagSelectedIndices e i)) :=
  (finCongr (toricFaceDimension_flagSelectedIndices e i)).trans
    ((toricFlagRemainingIndexEquiv e i).trans
      ((toricFaceBaseFreeIndexEquiv (hs := hs) v (toricFlagSelectedIndices e i)).trans
        (toricFaceNativeFreeEquiv (hs := hs) v (toricFlagSelectedIndices e i)
          (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i))).symm))

/-- Every produced target flag ray is lifted to the LITERAL remaining
original ambient ray, in the original source order. -/
theorem toricFaceTailOrder_free_index (v : latticePolytopeVertices γ)
    (e : Fin n ≃ Fin n) (i : Fin (n + 1))
    (j : Fin (toricFaceDimension (toricFlagSelectedIndices e i))) :
    toricFaceNativeFreeIndex (hs := hs) v (toricFlagSelectedIndices e i)
      (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e i)) (toricFaceTailOrder (hs := hs) v e i j) =
      e ⟨i.val + j.val, by have := j.isLt; have hd := toricFaceDimension_flagSelectedIndices e i; omega⟩ := by
  let J := toricFlagSelectedIndices e i
  let w := toricFaceBaseVertex (hs := hs) v J
  let t := toricFlagRemainingIndexEquiv e i
    ((finCongr (toricFaceDimension_flagSelectedIndices e i)) j)
  have h := (toricFaceNativeFreeEquiv (hs := hs) v J w).apply_symm_apply
    (toricFaceBaseFreeIndexEquiv (hs := hs) v J t)
  exact congrArg Subtype.val h

end SGPT.Toric
