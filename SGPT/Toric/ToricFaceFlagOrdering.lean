import SGPT.Toric.ToricFaceFlagComplex

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set
open scoped Classical

/-- Every actual selected set can be placed first in a genuine full ray
ordering. The permutation and stage are constructed from finite cardinality,
including the empty cone and full cone. -/
theorem exists_toricFlagSelectedIndices {n : ℕ} (J : Set (Fin n)) :
    ∃ (e : Fin n ≃ Fin n) (i : Fin (n + 1)), J = toricFlagSelectedIndices e i := by
  let r := Fintype.card J
  have hr : r ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun j : Fin n => j ∈ J)
  let I : Set (Fin n) := {l | l.val < r}
  have hI : Fintype.card I = r := by
    rw [Fintype.card_subtype]
    change (Finset.univ.filter (fun l : Fin n => l.val < r)).card = r
    rw [Fin.card_filter_val_lt]
    omega
  let e₀ : I ≃ J := Fintype.equivOfCardEq hI
  let e := e₀.extendSubtype
  let i : Fin (n + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  refine ⟨e, i, ?_⟩
  change J = e '' I
  ext k
  constructor
  · intro hk
    have hl : e.symm k ∈ I := by
      by_contra hnot
      have hn := e₀.extendSubtype_not_mem (e.symm k) hnot
      apply hn
      simpa only [e, Equiv.apply_symm_apply] using hk
    exact ⟨e.symm k, hl, e.apply_symm_apply k⟩
  · rintro ⟨l, hl, rfl⟩
    exact e₀.extendSubtype_mem l hl

/-- EVERY original source fan cone is an actual stage of an actual original
full toric flag; no ordering/extension certificate is assumed by the caller. -/
theorem exists_toricFlagRays_of_isToricFanCone
    {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
    {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
    {R : Set (PolytopeToricRays γ hs)} (hR : IsToricFanCone R) :
    ∃ (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n) (i : Fin (n + 1)),
      R = toricFlagRays hs v e i := by
  obtain ⟨v, J, rfl⟩ := hR
  obtain ⟨e, i, hJ⟩ := exists_toricFlagSelectedIndices J
  refine ⟨v, e, i, ?_⟩
  rw [hJ, toricFlagRays_eq_selectedIndices]

end SGPT.Toric
