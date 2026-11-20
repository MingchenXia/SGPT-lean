import SGPT.Foundations.Analysis.Pending.NaturalComplexBidegreeTransport
import Mathlib.Analysis.Complex.Basic

/-!
# Genuine holomorphic and antiholomorphic covectors

The covectors are actual complex-linear maps on the actual real tensor
complexification. They are constructed by the heterobasic tensor universal
property, not by an input extension, basis or bidegree equivalence certificate.
No full exterior-span or current-class theorem is asserted here.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexCovectors

open SGPT.Foundations.Analysis.FirstPass NaturalComplexBidegreeTransport
open scoped TensorProduct

def extendRealCovector {n : ℕ} (ℓ : ComplexModel n →ₗ[ℝ] ℂ) :
    complexification n →ₗ[ℂ] ℂ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ (ComplexModel n →ₗ[ℝ] ℂ) ℓ)

theorem extendRealCovector_tmul {n : ℕ}
    (ℓ : ComplexModel n →ₗ[ℝ] ℂ) (c : ℂ) (v : ComplexModel n) :
    extendRealCovector ℓ (c ⊗ₜ[ℝ] v) = c * ℓ v := by
  simp [extendRealCovector, smul_eq_mul]

theorem extendRealCovector_realEmbedding {n : ℕ}
    (ℓ : ComplexModel n →ₗ[ℝ] ℂ) (v : ComplexModel n) :
    extendRealCovector ℓ (realEmbedding n v) = ℓ v := by
  simp [realEmbedding, extendRealCovector_tmul]

theorem extendRealCovector_unique {n : ℕ}
    (ℓ : ComplexModel n →ₗ[ℝ] ℂ) (F : complexification n →ₗ[ℂ] ℂ)
    (hF : ∀ v, F (realEmbedding n v) = ℓ v) : F = extendRealCovector ℓ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c v
  have hc : c ⊗ₜ[ℝ] v = c • realEmbedding n v := by
    simp [realEmbedding, TensorProduct.smul_tmul']
  rw [hc, map_smul, hF]
  simp [extendRealCovector_realEmbedding, smul_eq_mul]

def holomorphicCovector {n : ℕ} (α : ComplexModel n →ₗ[ℂ] ℂ) :
    complexification n →ₗ[ℂ] ℂ :=
  extendRealCovector (α.restrictScalars ℝ)

def antiholomorphicCovector {n : ℕ} (α : ComplexModel n →ₗ[ℂ] ℂ) :
    complexification n →ₗ[ℂ] ℂ :=
  extendRealCovector (Complex.conjAe.toLinearMap.comp (α.restrictScalars ℝ))

private theorem extendedJ_tmul {n : ℕ} (c : ℂ) (v : ComplexModel n) :
    extendedJ n (c ⊗ₜ[ℝ] v) = c ⊗ₜ[ℝ] (Complex.I • v) := by
  change ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
    (c ⊗ₜ[ℝ] v) = _
  simp

theorem holomorphicCovector_extendedJ {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    holomorphicCovector α (extendedJ n z) = Complex.I * holomorphicCovector α z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [extendedJ_tmul]
    simp [holomorphicCovector, extendRealCovector_tmul, smul_eq_mul, mul_left_comm]
  | add z w hz hw => simp [hz, hw, mul_add]

theorem antiholomorphicCovector_extendedJ {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    antiholomorphicCovector α (extendedJ n z) = -Complex.I * antiholomorphicCovector α z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    rw [extendedJ_tmul]
    simp [antiholomorphicCovector, extendRealCovector_tmul, smul_eq_mul, mul_left_comm]
  | add z w hz hw => simp [hz, hw, mul_add]

theorem holomorphicCovector_holomorphicProjection {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    holomorphicCovector α (holomorphicProjection n z) = holomorphicCovector α z := by
  simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub, holomorphicCovector_extendedJ, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicCovector_antiholomorphicProjection {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    holomorphicCovector α (antiholomorphicProjection n z) = 0 := by
  simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add, holomorphicCovector_extendedJ, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem antiholomorphicCovector_holomorphicProjection {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    antiholomorphicCovector α (holomorphicProjection n z) = 0 := by
  simp only [holomorphicProjection, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_smul, map_sub, antiholomorphicCovector_extendedJ, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem antiholomorphicCovector_antiholomorphicProjection {n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (z : complexification n) :
    antiholomorphicCovector α (antiholomorphicProjection n z) = antiholomorphicCovector α z := by
  simp only [antiholomorphicProjection, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, map_smul, map_add, antiholomorphicCovector_extendedJ, smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem holomorphicCovector_comp {m n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (L : ComplexModel m →ₗ[ℂ] ComplexModel n) :
    holomorphicCovector (α.comp L) =
      (holomorphicCovector α).comp ((L.restrictScalars ℝ).baseChange ℂ) := by
  symm
  apply extendRealCovector_unique
  intro v
  simp [holomorphicCovector, realEmbedding, extendRealCovector_tmul]

theorem antiholomorphicCovector_comp {m n : ℕ}
    (α : ComplexModel n →ₗ[ℂ] ℂ) (L : ComplexModel m →ₗ[ℂ] ComplexModel n) :
    antiholomorphicCovector (α.comp L) =
      (antiholomorphicCovector α).comp ((L.restrictScalars ℝ).baseChange ℂ) := by
  symm
  apply extendRealCovector_unique
  intro v
  simp [antiholomorphicCovector, realEmbedding, extendRealCovector_tmul]

end SGPT.Foundations.Analysis.Pending.NaturalComplexCovectors
