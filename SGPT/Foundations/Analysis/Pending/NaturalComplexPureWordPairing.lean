import SGPT.Foundations.Analysis.Pending.NaturalComplexExteriorGeneratorProducts
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

/-!
# Internally pairing every genuine pure exterior coordinate word

The actual permutation is constructed from proved slot cardinalities,
complement subtypes and a concrete quotient/remainder equivalence. No
pairing, basis, orientation, or higher-degree span certificate is assumed.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexPureWordPairing

open NaturalComplexPureExteriorExpansion NaturalComplexExteriorGeneratorProducts

def interleavedSlotEquiv (p : ℕ) : Fin p ⊕ Fin p ≃ Fin (2 * p) where
  toFun := Sum.elim (fun r => ⟨2 * r.val, by omega⟩)
    (fun r => ⟨2 * r.val + 1, by omega⟩)
  invFun i := if i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by omega⟩
    else Sum.inr ⟨i.val / 2, by omega⟩
  left_inv := by
    intro s
    cases s with
    | inl r =>
      dsimp only [Sum.elim]
      rw [if_pos (show (2 * r.val) % 2 = 0 by omega)]
      congr 1
      apply Fin.ext
      dsimp
      omega
    | inr r =>
      dsimp only [Sum.elim]
      rw [if_neg (show (2 * r.val + 1) % 2 ≠ 0 by omega)]
      congr 1
      apply Fin.ext
      dsimp
      omega
  right_inv := by
    intro i
    dsimp only
    split_ifs with h
    · apply Fin.ext
      dsimp
      omega
    · apply Fin.ext
      dsimp
      omega

def pairedWord {n p : ℕ} (j k : Fin p → Fin n) : Fin (2 * p) → Fin 2 × Fin n :=
  fun i => Sum.elim (fun r => (0, j r)) (fun r => (1, k r))
    ((interleavedSlotEquiv p).symm i)

theorem pairedWord_apply {n p : ℕ} (j k : Fin p → Fin n) (i : Fin (2 * p)) :
    pairedWord j k i = if i.val % 2 = 0 then (0, j ⟨i.val / 2, by omega⟩)
      else (1, k ⟨i.val / 2, by omega⟩) := by
  by_cases h : i.val % 2 = 0 <;>
    simp [pairedWord, interleavedSlotEquiv, Equiv.symm, h]

theorem exists_pairedWord_permutation {n p : ℕ}
    (a : Fin (2 * p) → Fin 2 × Fin n) (ha : (holomorphicSlots a).card = p) :
    ∃ (j k : Fin p → Fin n) (σ : Equiv.Perm (Fin (2 * p))),
      a ∘ σ = pairedWord j k := by
  classical
  have hcard : Fintype.card {i : Fin (2 * p) // (a i).1 = 0} = p := by
    simpa only [Fintype.card_subtype, holomorphicSlots] using ha
  have hcompl : Fintype.card {i : Fin (2 * p) // ¬(a i).1 = 0} = p := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcard]
    omega
  let eh : {i : Fin (2 * p) // (a i).1 = 0} ≃ Fin p := Fintype.equivFinOfCardEq hcard
  let ea : {i : Fin (2 * p) // ¬(a i).1 = 0} ≃ Fin p := Fintype.equivFinOfCardEq hcompl
  let j : Fin p → Fin n := fun r => (a (eh.symm r)).2
  let k : Fin p → Fin n := fun r => (a (ea.symm r)).2
  let σ : Equiv.Perm (Fin (2 * p)) := (interleavedSlotEquiv p).symm.trans
    ((Equiv.sumCongr eh.symm ea.symm).trans (Equiv.sumCompl fun i => (a i).1 = 0))
  refine ⟨j, k, σ, ?_⟩
  funext i
  cases hi : (interleavedSlotEquiv p).symm i with
  | inl r =>
    simp only [Function.comp_apply, σ, Equiv.trans_apply, hi, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, pairedWord, Sum.elim_inl]
    exact Prod.ext (eh.symm r).property rfl
  | inr r =>
    simp only [Function.comp_apply, σ, Equiv.trans_apply, hi, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr, pairedWord, Sum.elim_inr]
    apply Prod.ext
    · have h : (a (ea.symm r)).1 ≠ 0 := (ea.symm r).property
      have hv : ((a (ea.symm r)).1).val ≠ 0 := by
        intro hv
        apply h
        exact Fin.ext hv
      have hl := ((a (ea.symm r)).1).isLt
      apply Fin.ext
      change ((a (ea.symm r)).1).val = 1
      omega
    · rfl

theorem pairedWord_succ {n p : ℕ} (j k : Fin (p + 1) → Fin n) :
    pairedWord j k = concatWord
      (pairedWord (fun r : Fin p => j r.castSucc) (fun r : Fin p => k r.castSucc))
      ![(0, j (Fin.last p)), (1, k (Fin.last p))] := by
  funext i
  refine Fin.addCases (m := 2 * p) (n := 2) ?_ ?_ i
  · intro r
    simp only [pairedWord_apply, concatWord, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl]
    rfl
  · intro s
    have hdiv0 : (2 * p) / 2 = p := by omega
    have hdiv1 : (2 * p + 1) / 2 = p := by omega
    have hmod0 : (2 * p) % 2 = 0 := by omega
    fin_cases s <;>
      simp [pairedWord_apply, concatWord, finSumFinEquiv_symm_apply_natAdd,
        hdiv0, hdiv1, hmod0, Fin.last]

end SGPT.Foundations.Analysis.Pending.NaturalComplexPureWordPairing
