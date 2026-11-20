import SGPT.Foundations.Analysis.Pending.NaturalRealAlternatingComplexification
import SGPT.Foundations.Analysis.Pending.ConstantFormProducts

/-!
# Actual pure real type and the degree-one positive-span dictionary

All pure-type predicates use the unique complex extension of the actual real
alternating tensor. Only degree one is identified with the existing positive
span. Higher-degree J-invariance is not a replacement for pure bidegree.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalRealPPSubmodule

open SGPT.Foundations.Analysis.FirstPass
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open scoped TensorProduct

theorem complexify_add {n d : ℕ}
    (A B : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    complexify (A + B) = complexify A + complexify B := by
  symm
  apply complexify_unique
  intro v
  simp [complexify_realEmbedding]

theorem complexify_real_smul {n d : ℕ}
    (c : ℝ) (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    complexify (c • A) = c • complexify A := by
  symm
  apply complexify_unique
  intro v
  simp [complexify_realEmbedding, smul_eq_mul]

def purePPSubmodule (n p : ℕ) :
    Submodule ℝ (ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) where
  carrier := {A | IsPureRealPP p A}
  zero_mem' := by
    have hz : complexify (0 : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) = 0 := by
      symm
      apply complexify_unique
      intro v
      simp
    intro S hS v
    rw [hz]
    rfl
  add_mem' := by
    intro A B hA hB S hS v
    rw [complexify_add]
    simp only [AlternatingMap.add_apply, hA S hS v, hB S hS v, add_zero]
  smul_mem' := by
    intro c A hA S hS v
    rw [complexify_real_smul]
    simp only [AlternatingMap.smul_apply, hA S hS v, smul_zero]

theorem eq_sum_mixed_blocks {n d : ℕ}
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ)
    (v : Fin d → complexification n) :
    F v = ∑ S : Finset (Fin d), F (blockProjection S v) := by
  classical
  have hv : v = (fun j => holomorphicProjection n (v j)) +
      (fun j => antiholomorphicProjection n (v j)) := by
    funext j
    exact (projections_add n (v j)).symm
  conv_lhs => rw [hv, F.map_add_univ]
  rfl

private theorem extendedJ_square {n : ℕ} (z : complexification n) :
    extendedJ n (extendedJ n z) = -z := by
  change ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
      (((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ) z) = -z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [smul_smul, Complex.I_mul_I, TensorProduct.tmul_neg]
  | add z w hz hw => simp [hz, hw, add_comm]

private theorem extendedJ_plus {n : ℕ} (z : complexification n) :
    extendedJ n (holomorphicProjection n z) = Complex.I • holomorphicProjection n z := by
  simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub, extendedJ_square]
  simp only [smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

private theorem extendedJ_minus {n : ℕ} (z : complexification n) :
    extendedJ n (antiholomorphicProjection n z) = -Complex.I • antiholomorphicProjection n z := by
  simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add, extendedJ_square]
  simp only [smul_add, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

private theorem two_phase (S : Finset (Fin 2)) :
    (∏ j : Fin 2, if j ∈ S then Complex.I else -Complex.I) =
      if S.card = 1 then 1 else -1 := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · have hs : S = Finset.univ := by ext j; fin_cases j <;> simp [h0, h1]
    subst S
    norm_num [Fin.prod_univ_two, Complex.I_mul_I]
  · have hs : S = {0} := by ext j; fin_cases j <;> simp [h0, h1]
    subst S
    norm_num [Fin.prod_univ_two, Complex.I_mul_I]
  · have hs : S = {1} := by ext j; fin_cases j <;> simp [h0, h1]
    subst S
    norm_num [Fin.prod_univ_two, Complex.I_mul_I]
  · have hs : S = ∅ := by ext j; fin_cases j <;> simp [h0, h1]
    subst S
    norm_num [Fin.prod_univ_two, Complex.I_mul_I]

private theorem pure_two_iff_extendedJ_invariant {n : ℕ}
    (F : complexification n [⋀^Fin 2]→ₗ[ℂ] ℂ) :
    IsPureBidegree 1 1 F ↔
      ∀ v, F (fun j => extendedJ n (v j)) = F v := by
  classical
  constructor
  · intro h v
    change (F.compLinearMap (extendedJ n)) v = F v
    rw [eq_sum_mixed_blocks, eq_sum_mixed_blocks]
    apply Finset.sum_congr rfl
    intro S _
    have hv : (fun j => extendedJ n (blockProjection S v j)) =
        fun j => (if j ∈ S then Complex.I else -Complex.I) • blockProjection S v j := by
      funext j
      by_cases hj : j ∈ S
      · simp only [blockProjection, if_pos hj, extendedJ_plus]
      · simp only [blockProjection, if_neg hj, extendedJ_minus]
    change F (fun j => extendedJ n (blockProjection S v j)) = F (blockProjection S v)
    rw [hv, F.map_smul_univ, two_phase]
    by_cases hS : S.card = 1
    · simp only [if_pos hS, one_smul]
    · simp only [if_neg hS, h S hS v, smul_zero]
  · intro h
    apply (isPureBidegree_iff_eigenblocks (r := 1) (s := 1) F).mpr
    intro S hS v hp hm
    have hv : (fun j => extendedJ n (v j)) =
        fun j => (if j ∈ S then Complex.I else -Complex.I) • v j := by
      funext j
      by_cases hj : j ∈ S
      · simp only [if_pos hj, hp j hj]
      · simp only [if_neg hj, hm j hj]
    have he := h v
    rw [hv, F.map_smul_univ, two_phase, if_neg hS, neg_one_smul] at he
    have htwo : (2 : ℂ) * F v = 0 := by linear_combination -he
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem isOneOne_iff_pureRealPP {n : ℕ}
    (β : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) :
    IsOneOne β ↔ IsPureRealPP 1 β.toAlternatingMap := by
  let L : ComplexModel n →ₗ[ℝ] ComplexModel n := Complex.I • LinearMap.id
  constructor
  · intro hβ
    have hreal : β.toAlternatingMap.compLinearMap L = β.toAlternatingMap := by
      ext v
      have hv : v = ![v 0, v 1] := by ext j; fin_cases j <;> rfl
      rw [hv]
      change β (fun j => L (![v 0, v 1] j)) = β ![v 0, v 1]
      have ht : (fun j => L (![v 0, v 1] j)) = ![Complex.I • v 0, Complex.I • v 1] := by
        ext j
        fin_cases j <;> rfl
      rw [ht]
      exact hβ _ _
    apply (pure_two_iff_extendedJ_invariant (complexify β.toAlternatingMap)).mpr
    have hc : (complexify β.toAlternatingMap).compLinearMap (L.baseChange ℂ) =
        complexify β.toAlternatingMap := by
      rw [← complexify_compLinearMap, hreal]
    change (complexify β.toAlternatingMap).compLinearMap (extendedJ n) =
      complexify β.toAlternatingMap at hc
    intro v
    exact DFunLike.congr_fun hc v
  · intro hβ u v
    have h := (pure_two_iff_extendedJ_invariant (complexify β.toAlternatingMap)).mp hβ
      (fun j => realEmbedding n (![u, v] j))
    have hj (w : ComplexModel n) : extendedJ n (realEmbedding n w) =
        realEmbedding n (Complex.I • w) := by
      change (L.baseChange ℂ) (TensorProduct.mk ℝ ℂ (ComplexModel n) 1 w) =
        TensorProduct.mk ℝ ℂ (ComplexModel n) 1 (Complex.I • w)
      simp [L]
    simp only [hj] at h
    rw [complexify_realEmbedding, complexify_realEmbedding] at h
    have ht : (fun j : Fin 2 => Complex.I • (![u, v] j)) = ![Complex.I • u, Complex.I • v] := by
      ext j
      fin_cases j <;> rfl
    rw [ht] at h
    apply Complex.ofReal_injective
    exact h

theorem mem_formSpan_one_iff_pureRealPP {n : ℕ}
    (β : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ) :
    β ∈ LocalProductCurrents.formSpan n 1 ↔ IsPureRealPP 1 β.toAlternatingMap := by
  rw [← isOneOne_iff_pureRealPP]
  constructor
  · intro hβ u v
    have h := ConstantFormProducts.formSpan_le_jInvariant 1 hβ
    have he := DFunLike.congr_fun h ![u, v]
    change β (fun j => Complex.I • (![u, v] j)) = β ![u, v] at he
    have ht : (fun j : Fin 2 => Complex.I • (![u, v] j)) = ![Complex.I • u, Complex.I • v] := by
      ext j
      fin_cases j <;> rfl
    rw [ht] at he
    exact he
  · exact LocalProductCurrents.oneOne_mem_formSpan

end SGPT.Foundations.Analysis.Pending.NaturalRealPPSubmodule
