import SGPT.Foundations.Analysis.Pending.NaturalComplexificationConjugation
import SGPT.Foundations.Analysis.Pending.NaturalRealPPSubmodule

/-!
# Genuine normalized projection onto complex (p,p) tensors

Balanced mixed blocks are summed and alternatized internally. Purity,
fixed-point identity and actual naturality are proved for that constructor.
No supplied projector or decomposition certificate occurs in the inputs.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexPPProjector

open SGPT.Foundations.Analysis.FirstPass
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open NaturalComplexificationConjugation
open scoped TensorProduct

def balancedMultilinear {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin (p + p) => complexification n) ℂ :=
  ∑ S : Finset (Fin (p + p)), if S.card = p then
    F.toMultilinearMap.compLinearMap
      (fun j => if j ∈ S then holomorphicProjection n else antiholomorphicProjection n)
    else 0

theorem balancedMultilinear_apply {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ)
    (v : Fin (p + p) → complexification n) :
    balancedMultilinear F v =
      ∑ S : Finset (Fin (p + p)), if S.card = p then F (blockProjection S v) else 0 := by
  classical
  simp only [balancedMultilinear, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = p
  · simp only [if_pos hS, MultilinearMap.compLinearMap_apply]
    change F (fun j => (if j ∈ S then holomorphicProjection n else antiholomorphicProjection n) (v j)) =
      F (blockProjection S v)
    congr 1
    funext j
    by_cases hj : j ∈ S <;> simp [blockProjection, hj]
  · simp [hS]

def ppProjector {n p : ℕ} (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ :=
  ((p + p).factorial : ℂ)⁻¹ • MultilinearMap.alternatization (balancedMultilinear F)

theorem ppProjector_apply {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ)
    (v : Fin (p + p) → complexification n) :
    ppProjector F v = ((p + p).factorial : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin (p + p)), Equiv.Perm.sign σ •
        ∑ S : Finset (Fin (p + p)),
          if S.card = p then F (blockProjection S (v ∘ σ)) else 0 := by
  simp only [ppProjector, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, balancedMultilinear_apply]
  rfl

private theorem extendedJ_square {n : ℕ} (z : complexification n) :
    extendedJ n (extendedJ n z) = -z := by
  change ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
      (((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ) z) = -z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [smul_smul, Complex.I_mul_I, TensorProduct.tmul_neg]
  | add z w hz hw => simp [hz, hw, add_comm]

private theorem holomorphic_antiholomorphic {n : ℕ} (z : complexification n) :
    holomorphicProjection n (antiholomorphicProjection n z) = 0 := by
  simp only [holomorphicProjection, antiholomorphicProjection, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add,
    extendedJ_square, smul_add, smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

private theorem antiholomorphic_holomorphic {n : ℕ} (z : complexification n) :
    antiholomorphicProjection n (holomorphicProjection n z) = 0 := by
  simp only [holomorphicProjection, antiholomorphicProjection, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub,
    extendedJ_square, smul_add, smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

private theorem mismatched_slot {d : ℕ} (S T : Finset (Fin d))
    (σ : Equiv.Perm (Fin d)) (h : S.card ≠ T.card) :
    ∃ j, ¬ (j ∈ S ↔ σ j ∈ T) := by
  classical
  by_contra hn
  have hm : ∀ j, j ∈ S ↔ σ j ∈ T := by simpa using hn
  have he : S.map σ.toEmbedding = T := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, hk, hkj⟩ := Finset.mem_map.mp hj
      subst j
      exact (hm k).mp hk
    · intro hj
      apply Finset.mem_map.mpr
      exact ⟨σ.symm j, (hm (σ.symm j)).mpr (by simpa using hj), by simp⟩
  apply h
  rw [← he, Finset.card_map]

private theorem balanced_wrong_block {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ)
    (T : Finset (Fin (p + p))) (hT : T.card ≠ p)
    (v : Fin (p + p) → complexification n) (σ : Equiv.Perm (Fin (p + p))) :
    balancedMultilinear F (blockProjection T v ∘ σ) = 0 := by
  classical
  rw [balancedMultilinear_apply]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hS : S.card = p
  · rw [if_pos hS]
    obtain ⟨j, hj⟩ := mismatched_slot S T σ (by omega)
    apply F.map_coord_zero j
    by_cases hs : j ∈ S <;> by_cases ht : σ j ∈ T
    · exact False.elim (hj (by simp [hs, ht]))
    · simp [blockProjection, hs, ht, holomorphic_antiholomorphic]
    · simp [blockProjection, hs, ht, antiholomorphic_holomorphic]
    · exact False.elim (hj (by simp [hs, ht]))
  · simp [hS]

theorem ppProjector_isPure {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    IsPureBidegree p p (ppProjector F) := by
  classical
  intro T hT v
  simp only [ppProjector, AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]
  have hz : ∑ σ : Equiv.Perm (Fin (p + p)), Equiv.Perm.sign σ •
      balancedMultilinear F (blockProjection T v ∘ σ) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    rw [balanced_wrong_block F T hT v σ, smul_zero]
  simpa only [Function.comp_def, smul_zero] using
    congrArg (fun z : ℂ => ((p + p).factorial : ℂ)⁻¹ • z) hz

theorem ppProjector_of_isPure {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) (hF : IsPureBidegree p p F) :
    ppProjector F = F := by
  classical
  have he : balancedMultilinear F = F.toMultilinearMap := by
    ext v
    change balancedMultilinear F v = F v
    rw [balancedMultilinear_apply, NaturalRealPPSubmodule.eq_sum_mixed_blocks F v]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hS : S.card = p
    · simp [hS]
    · simp [hS, hF S hS v]
  rw [ppProjector, he, AlternatingMap.coe_alternatization]
  ext v
  simp [Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, Nat.factorial_ne_zero]

theorem ppProjector_idempotent {n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ) :
    ppProjector (ppProjector F) = ppProjector F :=
  ppProjector_of_isPure _ (ppProjector_isPure F)

private theorem baseChange_projector {m n : ℕ}
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) (z : complexification m) :
    L.baseChange ℂ (holomorphicProjection m z) = holomorphicProjection n (L.baseChange ℂ z) ∧
    L.baseChange ℂ (antiholomorphicProjection m z) = antiholomorphicProjection n (L.baseChange ℂ z) := by
  have hJ : L.baseChange ℂ (extendedJ m z) = extendedJ n (L.baseChange ℂ z) := by
    change L.baseChange ℂ
        (((Complex.I • (LinearMap.id : ComplexModel m →ₗ[ℝ] ComplexModel m)).baseChange ℂ) z) =
      ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
        (L.baseChange ℂ z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [hL]
    | add z w hz hw => simp [hz, hw]
  constructor <;>
    simp only [holomorphicProjection, antiholomorphicProjection, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, map_sub, hJ]

theorem ppProjector_compLinearMap {m n p : ℕ}
    (F : complexification n [⋀^Fin (p + p)]→ₗ[ℂ] ℂ)
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    ppProjector (F.compLinearMap (L.baseChange ℂ)) =
      (ppProjector F).compLinearMap (L.baseChange ℂ) := by
  classical
  ext v
  simp only [ppProjector_apply, AlternatingMap.compLinearMap_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = p
  · simp only [if_pos hS]
    congr 1
    funext j
    by_cases hj : j ∈ S <;>
      simp [blockProjection, hj, (baseChange_projector L hL _).1,
        (baseChange_projector L hL _).2]
  · simp [hS]

theorem ppProjector_complexify_im {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ)
    (v : Fin (p + p) → ComplexModel n) :
    (ppProjector (complexify A) (fun j => realEmbedding n (v j))).im = 0 := by
  classical
  rw [ppProjector_apply]
  have hr : ∀ σ : Equiv.Perm (Fin (p + p)),
      (∑ S : Finset (Fin (p + p)), if S.card = p then
        complexify A (blockProjection S ((fun j => realEmbedding n (v j)) ∘ σ)) else 0).im = 0 := by
    intro σ
    exact balancedBlockSum_im A (v ∘ σ)
  simp only [smul_eq_mul, Complex.mul_im, Complex.inv_im, Complex.natCast_im,
    neg_zero, zero_div, zero_mul, add_zero]
  have hs : (∑ σ : Equiv.Perm (Fin (p + p)), Equiv.Perm.sign σ •
      ∑ S : Finset (Fin (p + p)), if S.card = p then
        complexify A (blockProjection S ((fun j => realEmbedding n (v j)) ∘ σ)) else 0).im = 0 := by
    simp only [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hr σ]
  rw [hs, mul_zero]

end SGPT.Foundations.Analysis.Pending.NaturalComplexPPProjector
