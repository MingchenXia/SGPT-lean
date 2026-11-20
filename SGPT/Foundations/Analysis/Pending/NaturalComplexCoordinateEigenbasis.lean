import SGPT.Foundations.Analysis.Pending.NaturalComplexCovectors
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Actual coordinate eigenbasis of the real tensor complexification

The coordinate projections and projected standard vectors internally give
two inverse linear maps and a genuine complex basis. Every actual complex
multilinear tensor has its full finite expansion in these coordinates.
No basis, spanning or type-equivalence certificate is an input. A general
pure-bidegree exterior basis and real positive-product span remain separate.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.NaturalComplexCoordinateEigenbasis

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open NaturalComplexBidegreeTransport NaturalComplexCovectors
open scoped TensorProduct

def eigenVector {n : ℕ} (a : Fin 2 × Fin n) : complexification n :=
  if a.1 = 0 then holomorphicProjection n (realEmbedding n (coordinateVector a.2))
  else antiholomorphicProjection n (realEmbedding n (coordinateVector a.2))

def eigenCovector {n : ℕ} (a : Fin 2 × Fin n) : complexification n →ₗ[ℂ] ℂ :=
  if a.1 = 0 then holomorphicCovector (EuclideanSpace.projₗ a.2)
  else antiholomorphicCovector (EuclideanSpace.projₗ a.2)

theorem eigenCovector_eigenVector {n : ℕ} (a b : Fin 2 × Fin n) :
    eigenCovector a (eigenVector b) = if a = b then 1 else 0 := by
  classical
  rcases a with ⟨s, j⟩
  rcases b with ⟨t, k⟩
  fin_cases s <;> fin_cases t <;>
    simp [eigenCovector, eigenVector]
  all_goals
    simp only [
      holomorphicCovector_holomorphicProjection,
      holomorphicCovector_antiholomorphicProjection,
      antiholomorphicCovector_holomorphicProjection,
      antiholomorphicCovector_antiholomorphicProjection]
  all_goals
    simp [holomorphicCovector, antiholomorphicCovector,
      extendRealCovector_realEmbedding, coordinateVector,
      EuclideanSpace.projₗ, PiLp.projₗ, PiLp.single_apply]

def coordinateMap (n : ℕ) : complexification n →ₗ[ℂ] (Fin 2 × Fin n → ℂ) :=
  LinearMap.pi fun a => eigenCovector a

def synthesisMap (n : ℕ) : (Fin 2 × Fin n → ℂ) →ₗ[ℂ] complexification n where
  toFun c := ∑ a, c a • eigenVector a
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c d := by simp [Pi.smul_apply, smul_smul, Finset.smul_sum]

private theorem eigenCovector_realEmbedding {n : ℕ} (a : Fin 2 × Fin n)
    (v : ComplexModel n) :
    eigenCovector a (realEmbedding n v) = if a.1 = 0 then v a.2 else star (v a.2) := by
  by_cases h : a.1 = 0
  · simp only [eigenCovector, if_pos h, holomorphicCovector,
      extendRealCovector_realEmbedding]
    rfl
  · simp only [eigenCovector, if_neg h, antiholomorphicCovector,
      extendRealCovector_realEmbedding]
    rfl

private theorem extendedJ_realEmbedding {n : ℕ} (v : ComplexModel n) :
    extendedJ n (realEmbedding n v) = realEmbedding n (Complex.I • v) := by
  change ((Complex.I • (LinearMap.id : ComplexModel n →ₗ[ℝ] ComplexModel n)).baseChange ℂ)
    (realEmbedding n v) = _
  simp [realEmbedding]

private theorem imaginary_projection_difference {n : ℕ} (v : ComplexModel n) :
    Complex.I • holomorphicProjection n (realEmbedding n v) +
      (-Complex.I) • antiholomorphicProjection n (realEmbedding n v) =
      realEmbedding n (Complex.I • v) := by
  rw [← extendedJ_realEmbedding]
  simp only [holomorphicProjection, antiholomorphicProjection, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply]
  calc
    Complex.I • ((1 / 2 : ℂ) • (realEmbedding n v - Complex.I • extendedJ n (realEmbedding n v))) +
        (-Complex.I) • ((1 / 2 : ℂ) • (realEmbedding n v + Complex.I • extendedJ n (realEmbedding n v))) =
        (-Complex.I ^ 2) • extendedJ n (realEmbedding n v) := by module
    _ = extendedJ n (realEmbedding n v) := by simp

private theorem reconstruction_realEmbedding (n : ℕ) :
    (((synthesisMap n).comp (coordinateMap n)).restrictScalars ℝ).comp (realEmbedding n) =
      realEmbedding n := by
  apply (coordinateRealBasis n).ext
  intro k
  obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [coe_coordinateRealBasis, coordinateRealFrame,
    Equiv.symm_apply_apply]
  fin_cases s
  · simpa [LinearMap.comp_apply, synthesisMap, coordinateMap, eigenCovector_realEmbedding,
      coordinateVector, PiLp.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      eigenVector] using projections_add n (realEmbedding n (coordinateVector j))
  · simpa [LinearMap.comp_apply, synthesisMap, coordinateMap, eigenCovector_realEmbedding,
      coordinateVector, PiLp.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      apply_ite, eigenVector] using imaginary_projection_difference (coordinateVector j)

theorem synthesis_coordinates {n : ℕ} (z : complexification n) :
    synthesisMap n (coordinateMap n z) = z := by
  have h := reconstruction_realEmbedding n
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c v =>
    have he := LinearMap.congr_fun h v
    have hc : c ⊗ₜ[ℝ] v = c • realEmbedding n v := by
      simp [realEmbedding, TensorProduct.smul_tmul']
    rw [hc, map_smul, map_smul]
    simpa [LinearMap.comp_apply] using congrArg (c • ·) he
  | add z w hz hw => simp [hz, hw]

theorem coordinates_synthesis {n : ℕ} (c : Fin 2 × Fin n → ℂ) :
    coordinateMap n (synthesisMap n c) = c := by
  classical
  funext a
  simp [coordinateMap, synthesisMap, map_sum, eigenCovector_eigenVector]

def coordinateEquiv (n : ℕ) : complexification n ≃ₗ[ℂ] (Fin 2 × Fin n → ℂ) where
  toFun := coordinateMap n
  invFun := synthesisMap n
  left_inv := synthesis_coordinates
  right_inv := coordinates_synthesis
  map_add' := (coordinateMap n).map_add
  map_smul' := (coordinateMap n).map_smul

def eigenBasis (n : ℕ) : Module.Basis (Fin 2 × Fin n) ℂ (complexification n) :=
  Module.Basis.ofEquivFun (coordinateEquiv n)

theorem eigenBasis_apply {n : ℕ} (a : Fin 2 × Fin n) :
    eigenBasis n a = eigenVector a := by
  classical
  simp [eigenBasis, Module.Basis.coe_ofEquivFun, coordinateEquiv, synthesisMap]

theorem eigenBasis_coord {n : ℕ} (a : Fin 2 × Fin n) :
    (eigenBasis n).coord a = eigenCovector a := by
  ext z
  simp [eigenBasis, Module.Basis.coord_apply, coordinateEquiv, coordinateMap]

private theorem eigenCovector_extendedJ {n : ℕ} (a : Fin 2 × Fin n)
    (z : complexification n) :
    eigenCovector a (extendedJ n z) =
      (if a.1 = 0 then Complex.I else -Complex.I) * eigenCovector a z := by
  by_cases h : a.1 = 0
  · simp only [eigenCovector, if_pos h, holomorphicCovector_extendedJ]
  · simp only [eigenCovector, if_neg h, antiholomorphicCovector_extendedJ]

theorem eigenVector_extendedJ {n : ℕ} (a : Fin 2 × Fin n) :
    extendedJ n (eigenVector a) =
      (if a.1 = 0 then Complex.I else -Complex.I) • eigenVector a := by
  classical
  apply (coordinateEquiv n).injective
  funext b
  change eigenCovector b (extendedJ n (eigenVector a)) =
    eigenCovector b ((if a.1 = 0 then Complex.I else -Complex.I) • eigenVector a)
  rw [eigenCovector_extendedJ, map_smul, eigenCovector_eigenVector]
  by_cases h : b = a
  · subst b
    simp [smul_eq_mul]
  · simp [h]

def coordinateMonomial {n d : ℕ} (a : Fin d → Fin 2 × Fin n) :
    MultilinearMap ℂ (fun _ : Fin d => complexification n) ℂ :=
  (MultilinearMap.mkPiRing ℂ (Fin d) (1 : ℂ)).compLinearMap fun j => eigenCovector (a j)

private theorem coordinateMonomial_eigenVector {n d : ℕ}
    (a b : Fin d → Fin 2 × Fin n) :
    coordinateMonomial a (fun j => eigenVector (b j)) = if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [coordinateMonomial, eigenCovector_eigenVector]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    simp only [coordinateMonomial, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiRing_apply, eigenCovector_eigenVector, if_neg h]
    rw [Finset.prod_eq_zero (Finset.mem_univ j)]
    · simp
    · exact if_neg hj

theorem multilinear_eq_coordinate_sum {n d : ℕ}
    (F : MultilinearMap ℂ (fun _ : Fin d => complexification n) ℂ) :
    F = ∑ a : Fin d → Fin 2 × Fin n,
      F (fun j => eigenVector (a j)) • coordinateMonomial a := by
  classical
  apply Module.Basis.ext_multilinear fun _ => eigenBasis n
  intro b
  simp only [_root_.sum_apply, _root_.smul_apply, eigenBasis_apply,
    coordinateMonomial_eigenVector, smul_eq_mul]
  simp

end SGPT.Foundations.Analysis.Pending.NaturalComplexCoordinateEigenbasis
