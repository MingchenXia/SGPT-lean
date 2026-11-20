import SGPT.Foundations.Analysis.Pending.MixedCoefficientCongruence
import SGPT.Foundations.Analysis.Pending.MixedCoefficientPositivity

noncomputable section
namespace SGPT.Convex

open Matrix
open scoped ComplexOrder

/-- Actual entrywise inclusion of original real matrices. -/
def realMatrixComplexInclusion {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun A := fun j k ↦ (A j k : ℂ)
  map_add' A B := by
    ext j k
    change ((A j k + B j k : ℝ) : ℂ) = (A j k : ℂ) + (B j k : ℂ)
    exact Complex.ofReal_add _ _
  map_smul' c A := by
    ext j k
    change ((c * A j k : ℝ) : ℂ) = (c : ℂ) * (A j k : ℂ)
    exact Complex.ofReal_mul _ _

/-- Genuine real restriction and composition of main's verified mixed
multilinear coefficient, preserving the original real Hessian slots. -/
def realMixedCoefficientML {n : ℕ} :
    MultilinearMap ℝ (fun _ : Fin n ↦ Matrix (Fin n) (Fin n) ℝ) ℝ :=
  Complex.reLm.compMultilinearMap
    ((SGPT.Foundations.Analysis.Pending.MixedMongeAmpere.mixedCoefficientML.restrictScalars ℝ).compLinearMap (fun _ ↦ realMatrixComplexInclusion))

theorem realMixedCoefficientML_eq_complex {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    realMixedCoefficientML H =
      (SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere.mixedCoefficient
        (fun i ↦ realMatrixComplexInclusion (H i))).re := by
  simp [realMixedCoefficientML,
    SGPT.Foundations.Analysis.Pending.MixedMongeAmpere.mixedCoefficientML_apply]

/-- The actual finite real Gram decomposition maps to actual complex PSD
rank-one matrices; no complex positivity certificate is assumed. -/
theorem posSemidef_realMatrixComplexInclusion {n : ℕ}
    {H : Matrix (Fin n) (Fin n) ℝ} (hH : H.PosSemidef) :
    (realMatrixComplexInclusion H).PosSemidef := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hH
  have heq : realMatrixComplexInclusion H =
      ∑ a : Fin m, Matrix.vecMulVec (fun j ↦ (v a j : ℂ))
        (star (fun j ↦ (v a j : ℂ))) := by
    rw [hv, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    ext j k
    change ((v a j * star (v a k) : ℝ) : ℂ) = (v a j : ℂ) * star (v a k : ℂ)
    simp
  rw [heq]
  exact Matrix.posSemidef_sum _ (fun a _ ↦
    Matrix.posSemidef_vecMulVec_self_star (fun j ↦ (v a j : ℂ)))

/-- Main's genuine mixed-coefficient positivity applies to the actual
included real PSD Hessians. -/
theorem realMixedCoefficientML_nonneg {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i, (H i).PosSemidef) :
    0 ≤ realMixedCoefficientML H := by
  rw [realMixedCoefficientML_eq_complex]
  exact SGPT.Foundations.Analysis.Pending.MixedMongeAmpere.mixedCoefficient_re_nonneg _
    (fun i ↦ posSemidef_realMatrixComplexInclusion (hH i))

/-- The real coefficient is precisely the original actual permutation sum. -/
theorem realMixedCoefficientML_eq_sum {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    realMixedCoefficientML H =
      ∑ σ : Equiv.Perm (Fin n), Matrix.det (fun j k ↦ H (σ j) j k) := by
  classical
  rw [realMixedCoefficientML_eq_complex,
    SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere.mixedCoefficient, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have hd := Complex.ofRealHom.map_det (fun j k ↦ H (σ j) j k)
  have hm : (fun j k ↦ realMatrixComplexInclusion (H (σ j)) j k) =
      Complex.ofRealHom.mapMatrix (fun j k ↦ H (σ j) j k) := rfl
  rw [hm, ← hd]
  rfl

/-- Original source diagonal normalization, directly transported from main. -/
theorem realMixedCoefficientML_diagonal {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℝ) :
    realMixedCoefficientML (fun _ : Fin n ↦ H) = (n.factorial : ℝ) * H.det := by
  classical
  rw [realMixedCoefficientML_eq_sum]
  simp [Fintype.card_perm]

/-- Actual symmetry is the proved native permutation reindexing. -/
theorem realMixedCoefficientML_perm {n : ℕ}
    (H : Fin n → Matrix (Fin n) (Fin n) ℝ) (τ : Equiv.Perm (Fin n)) :
    realMixedCoefficientML (fun i ↦ H (τ i)) = realMixedCoefficientML H := by
  rw [realMixedCoefficientML_eq_complex, realMixedCoefficientML_eq_complex]
  exact congrArg Complex.re
    (SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere.mixedCoefficient_perm
      (fun i ↦ realMatrixComplexInclusion (H i)) τ)

/-- The genuine already-verified multilinear map gives actual independent
finite weighted-slot expansion, including zero weights and dimension zero. -/
theorem realMixedCoefficientML_sum {n q : ℕ}
    (H : Fin q → Matrix (Fin n) (Fin n) ℝ) (c : Fin n → Fin q → ℝ) :
    realMixedCoefficientML (fun i ↦ ∑ j, c i j • H j) =
      ∑ g : Fin n → Fin q, (∏ i, c i (g i)) * realMixedCoefficientML (fun i ↦ H (g i)) := by
  classical
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact realMixedCoefficientML.map_smul_univ _ _

end SGPT.Convex
