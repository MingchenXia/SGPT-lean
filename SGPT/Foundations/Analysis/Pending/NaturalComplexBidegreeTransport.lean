import SGPT.Foundations.Analysis.FirstPass.ComplexManifold
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Tactic.Module

/-!
# Genuine complexification and bidegree transport

We complexify the actual real tangent model and extend its actual complex
structure. Pure bidegree is defined by all mixed eigenspace blocks of an
actual complex alternating form. The general real-form extension and the
equality of usual real `(p,p)` forms with `LocalProductCurrents.formSpan`
are separate, still open producers.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexBidegreeTransport

open SGPT.Foundations.Analysis.FirstPass
open TensorProduct
open scoped TensorProduct

abbrev complexification (n : ℕ) := ℂ ⊗[ℝ] ComplexModel n

def realEmbedding (n : ℕ) : ComplexModel n →ₗ[ℝ] complexification n :=
  TensorProduct.mk ℝ ℂ (ComplexModel n) 1

def realPart (n : ℕ) : complexification n →ₗ[ℝ] ComplexModel n :=
  TensorProduct.lift
    (Complex.reCLM.toLinearMap.smulRight (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n))

private def realJ (n : ℕ) : ComplexModel n →ₗ[ℝ] ComplexModel n :=
  Complex.I • LinearMap.id

def extendedJ (n : ℕ) : complexification n →ₗ[ℂ] complexification n :=
  (realJ n).baseChange ℂ

def holomorphicProjection (n : ℕ) : complexification n →ₗ[ℂ] complexification n :=
  (1 / 2 : ℂ) • (LinearMap.id - Complex.I • extendedJ n)

def antiholomorphicProjection (n : ℕ) : complexification n →ₗ[ℂ] complexification n :=
  (1 / 2 : ℂ) • (LinearMap.id + Complex.I • extendedJ n)

theorem realPart_realEmbedding (n : ℕ) (v : ComplexModel n) :
    realPart n (realEmbedding n v) = v := by
  simp [realPart, realEmbedding]

theorem realEmbedding_injective (n : ℕ) : Function.Injective (realEmbedding n) := by
  intro v w h
  simpa only [realPart_realEmbedding] using congrArg (realPart n) h

private theorem extendedJ_square (n : ℕ) (z : complexification n) :
    extendedJ n (extendedJ n z) = -z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [extendedJ, realJ, smul_smul, Complex.I_mul_I,
      TensorProduct.tmul_neg]
  | add z w hz hw => simp [hz, hw, add_comm]

theorem projections_add (n : ℕ) (z : complexification n) :
    holomorphicProjection n z + antiholomorphicProjection n z = z := by
  simp only [holomorphicProjection, antiholomorphicProjection, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply]
  module

private theorem holomorphicProjection_eigen (n : ℕ) (z : complexification n) :
    extendedJ n (holomorphicProjection n z) = Complex.I • holomorphicProjection n z := by
  simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub, extendedJ_square]
  simp only [smul_sub, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

private theorem antiholomorphicProjection_eigen (n : ℕ) (z : complexification n) :
    extendedJ n (antiholomorphicProjection n z) = -Complex.I • antiholomorphicProjection n z := by
  simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add, extendedJ_square]
  simp only [smul_add, smul_smul, smul_neg]
  match_scalars <;> ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicProjection_fixed_iff (n : ℕ) (z : complexification n) :
    holomorphicProjection n z = z ↔ extendedJ n z = Complex.I • z := by
  constructor
  · intro h
    simpa only [h] using holomorphicProjection_eigen n z
  · intro h
    simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, h, smul_smul, Complex.I_mul_I, neg_one_smul]
    module

theorem antiholomorphicProjection_fixed_iff (n : ℕ) (z : complexification n) :
    antiholomorphicProjection n z = z ↔ extendedJ n z = -Complex.I • z := by
  constructor
  · intro h
    simpa only [h] using antiholomorphicProjection_eigen n z
  · intro h
    simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.id_apply, h, smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    module

def blockProjection {n d : ℕ} (A : Finset (Fin d))
    (v : Fin d → complexification n) : Fin d → complexification n :=
  fun j => if j ∈ A then holomorphicProjection n (v j) else antiholomorphicProjection n (v j)

def IsPureBidegree {n : ℕ} (r s : ℕ)
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ) : Prop :=
  ∀ (A : Finset (Fin (r + s))), A.card ≠ r →
    ∀ v, F (blockProjection A v) = 0

theorem isPureBidegree_iff_eigenblocks {n r s : ℕ}
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ) :
    IsPureBidegree r s F ↔
      ∀ (A : Finset (Fin (r + s))), A.card ≠ r →
        ∀ v, (∀ j, j ∈ A → extendedJ n (v j) = Complex.I • v j) →
          (∀ j, j ∉ A → extendedJ n (v j) = -Complex.I • v j) → F v = 0 := by
  constructor
  · intro h A hA v hp hm
    have hv : blockProjection A v = v := by
      funext j
      by_cases hj : j ∈ A
      · simp only [blockProjection, if_pos hj]
        exact (holomorphicProjection_fixed_iff n (v j)).mpr (hp j hj)
      · simp only [blockProjection, if_neg hj]
        exact (antiholomorphicProjection_fixed_iff n (v j)).mpr (hm j hj)
    simpa only [hv] using h A hA v
  · intro h A hA v
    apply h A hA (blockProjection A v)
    · intro j hj
      simp only [blockProjection, if_pos hj]
      exact holomorphicProjection_eigen n (v j)
    · intro j hj
      simp only [blockProjection, if_neg hj]
      exact antiholomorphicProjection_eigen n (v j)

private theorem baseChange_commutes_extendedJ {m n : ℕ}
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v)
    (z : complexification m) :
    L.baseChange ℂ (extendedJ m z) = extendedJ n (L.baseChange ℂ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [extendedJ, realJ, hL]
  | add z w hz hw => simp [hz, hw]

theorem isPureBidegree_comp {m n r s : ℕ}
    (F : complexification n [⋀^Fin (r + s)]→ₗ[ℂ] ℂ)
    (L : ComplexModel m →ₗ[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v)
    (hF : IsPureBidegree r s F) :
    IsPureBidegree r s (F.compLinearMap (L.baseChange ℂ)) := by
  intro A hA v
  have hp (z : complexification m) :
      L.baseChange ℂ (holomorphicProjection m z) =
        holomorphicProjection n (L.baseChange ℂ z) := by
    simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, map_smul, map_sub, baseChange_commutes_extendedJ L hL]
  have hm (z : complexification m) :
      L.baseChange ℂ (antiholomorphicProjection m z) =
        antiholomorphicProjection n (L.baseChange ℂ z) := by
    simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.id_apply, map_smul, map_add, baseChange_commutes_extendedJ L hL]
  have hv : (fun j => L.baseChange ℂ (blockProjection A v j)) =
      blockProjection A (fun j => L.baseChange ℂ (v j)) := by
    funext j
    by_cases hj : j ∈ A <;> simp only [blockProjection, hj, ↓reduceIte, hp, hm]
  change F (fun j => L.baseChange ℂ (blockProjection A v j)) = 0
  rw [hv]
  exact hF A hA _

end SGPT.Foundations.Analysis.Pending.NaturalComplexBidegreeTransport
