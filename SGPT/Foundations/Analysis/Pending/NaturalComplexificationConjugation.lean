import SGPT.Foundations.Analysis.Pending.NaturalRealAlternatingComplexification
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# Actual conjugation and reality of balanced bidegree blocks

Conjugation is constructed on the actual real tensor complexification.
The symmetry of the unique extension is proved internally; the caller
does not provide a reality certificate. Global type projection is separate.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexificationConjugation

open SGPT.Foundations.Analysis.FirstPass
open NaturalComplexBidegreeTransport NaturalRealAlternatingComplexification
open scoped TensorProduct

def conjugation (n : ℕ) : complexification n →ₗ[ℝ] complexification n :=
  TensorProduct.map (Complex.conjCLE : ℂ →ₗ[ℝ] ℂ)
    (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)

@[simp] theorem conjugation_tmul (n : ℕ) (c : ℂ) (v : ComplexModel n) :
    conjugation n (c ⊗ₜ[ℝ] v) = (starRingEnd ℂ c) ⊗ₜ[ℝ] v := rfl

theorem conjugation_smul (n : ℕ) (c : ℂ) (z : complexification n) :
    conjugation n (c • z) = (starRingEnd ℂ c) • conjugation n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add z w hz hw => simp [smul_add, hz, hw]

@[simp] theorem conjugation_involutive (n : ℕ) (z : complexification n) :
    conjugation n (conjugation n z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add z w hz hw => simp [hz, hw]

@[simp] theorem conjugation_realEmbedding (n : ℕ) (v : ComplexModel n) :
    conjugation n (realEmbedding n v) = realEmbedding n v := by
  simp [realEmbedding]

theorem conjugation_baseChange {m n : ℕ}
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n) (z : complexification m) :
    conjugation n (L.baseChange ℂ z) = L.baseChange ℂ (conjugation m z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp
  | add z w hz hw => simp [hz, hw]

theorem conjugation_extendedJ (n : ℕ) (z : complexification n) :
    conjugation n (extendedJ n z) = extendedJ n (conjugation n z) := by
  change conjugation n
      (((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ) z) =
    ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
      (conjugation n z)
  exact conjugation_baseChange _ z

theorem conjugation_holomorphicProjection (n : ℕ) (z : complexification n) :
    conjugation n (holomorphicProjection n z) =
      antiholomorphicProjection n (conjugation n z) := by
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
    simp only [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one]
  simp [holomorphicProjection, antiholomorphicProjection, conjugation_smul,
    conjugation_extendedJ, h2]

theorem conjugation_antiholomorphicProjection (n : ℕ) (z : complexification n) :
    conjugation n (antiholomorphicProjection n z) =
      holomorphicProjection n (conjugation n z) := by
  have h2 : starRingEnd ℂ (2 : ℂ) = 2 := by
    simp only [show (2 : ℂ) = 1 + 1 by norm_num, map_add, map_one]
  simp [holomorphicProjection, antiholomorphicProjection, conjugation_smul,
    conjugation_extendedJ, h2, sub_eq_add_neg]

theorem conjugation_blockProjection {n d : ℕ} (S : Finset (Fin d))
    (v : Fin d → complexification n) :
    (fun j => conjugation n (blockProjection S v j)) =
      blockProjection Sᶜ (fun j => conjugation n (v j)) := by
  classical
  funext j
  by_cases hj : j ∈ S <;>
    simp [blockProjection, hj, conjugation_holomorphicProjection,
      conjugation_antiholomorphicProjection]

private theorem conjugation_update {n d : ℕ} [DecidableEq (Fin d)]
    (v : Fin d → complexification n)
    (i : Fin d) (x : complexification n) :
    (fun j => conjugation n (Function.update v i x j)) =
      Function.update (fun j => conjugation n (v j)) i (conjugation n x) := by
  funext j
  by_cases h : j = i <;> simp [h]

def conjugateForm {n d : ℕ} (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) :
    complexification n [⋀^Fin d]→ₗ[ℂ] ℂ where
  toFun v := starRingEnd ℂ (F (fun j => conjugation n (v j)))
  map_update_add' := by
    intro inst v i x y
    simp only [conjugation_update, map_add, F.map_update_add, map_add]
  map_update_smul' := by
    intro inst v i c x
    simp only [conjugation_update, conjugation_smul, F.map_update_smul,
      smul_eq_mul, map_mul]
    simp
  map_eq_zero_of_eq' v i j h hij := by
    rw [F.map_eq_zero_of_eq _ (congrArg (conjugation n) h) hij]
    simp

@[simp] theorem conjugateForm_apply {n d : ℕ}
    (F : complexification n [⋀^Fin d]→ₗ[ℂ] ℂ) (v : Fin d → complexification n) :
    conjugateForm F v = starRingEnd ℂ (F (fun j => conjugation n (v j))) := rfl

theorem conjugateForm_complexify {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) :
    conjugateForm (complexify A) = complexify A := by
  apply complexify_unique
  intro v
  simp [complexify_realEmbedding]

theorem complexify_conjugation {n d : ℕ}
    (A : ComplexModel n [⋀^Fin d]→ₗ[ℝ] ℝ) (v : Fin d → complexification n) :
    complexify A (fun j => conjugation n (v j)) = starRingEnd ℂ (complexify A v) := by
  have h := congrArg (fun F => F v) (conjugateForm_complexify A)
  have h' := congrArg (starRingEnd ℂ) h
  simpa using h'

def balancedBlockSum {n p : ℕ} (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ)
    (v : Fin (p + p) → ComplexModel n) : ℂ :=
  ∑ S : Finset (Fin (p + p)),
    if S.card = p then complexify A (blockProjection S (fun j => realEmbedding n (v j))) else 0

theorem balancedBlockSum_conj {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) (v : Fin (p + p) → ComplexModel n) :
    starRingEnd ℂ (balancedBlockSum A v) = balancedBlockSum A v := by
  classical
  have hcard (S : Finset (Fin (p + p))) : Sᶜ.card = p ↔ S.card = p := by
    have h := Finset.card_compl S
    have hle := Finset.card_le_univ S
    simp only [Fintype.card_fin] at h hle
    omega
  have hc (S : Finset (Fin (p + p))) :
      starRingEnd ℂ (complexify A (blockProjection S (fun j => realEmbedding n (v j)))) =
        complexify A (blockProjection Sᶜ (fun j => realEmbedding n (v j))) := by
    rw [← complexify_conjugation, conjugation_blockProjection]
    simp
  unfold balancedBlockSum
  rw [map_sum]
  let e : Finset (Fin (p + p)) ≃ Finset (Fin (p + p)) :=
    ⟨fun S => Sᶜ, fun S => Sᶜ, compl_compl, compl_compl⟩
  apply Fintype.sum_equiv e
  intro S
  by_cases hS : S.card = p
  · simp [e, hS, hcard S, hc S]
  · simp [e, hS, hcard S]

theorem balancedBlockSum_im {n p : ℕ}
    (A : ComplexModel n [⋀^Fin (p + p)]→ₗ[ℝ] ℝ) (v : Fin (p + p) → ComplexModel n) :
    (balancedBlockSum A v).im = 0 := by
  have h := congrArg Complex.im (balancedBlockSum_conj A v)
  simp only [Complex.conj_im] at h
  linarith

end SGPT.Foundations.Analysis.Pending.NaturalComplexificationConjugation
