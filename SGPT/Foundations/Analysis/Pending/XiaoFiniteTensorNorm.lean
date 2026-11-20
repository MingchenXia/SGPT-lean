import SGPT.Foundations.Analysis.FirstPass.PositiveClasses
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

/-! # Genuine finite tensor coordinates and actual uniform tensor norm bounds -/

open Set

namespace SGPT.Foundations.Analysis.Pending.XiaoFiniteTensorNorm

noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

/-- The actual finite list of evaluations of an actual alternating tensor on tuples of actual basis vectors. -/
def tensorCoordinates (b : Module.Basis I ℝ E) :
    (E [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin 2 → I) → ℝ) where
  toFun A s := A (fun i => b (s i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] in
/-- Genuine tensors are separated by their actual evaluations on all actual basis-vector tuples. -/
theorem tensorCoordinates_injective (b : Module.Basis I ℝ E) :
    Function.Injective (tensorCoordinates b) := by
  intro A B hAB
  have hT : A.toAlternatingMap.toMultilinearMap = B.toAlternatingMap.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ : Fin 2 => b) (fun s => congrFun hAB s)
  apply ContinuousAlternatingMap.ext
  intro v
  exact congrArg (fun T => T v) hT

/-- The genuine tensor operator norm is bounded by a fixed positive multiple of the actual finite coordinate norm. -/
theorem exists_tensor_norm_le_coordinates (b : Module.Basis I ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : E [⋀^Fin 2]→L[ℝ] ℝ,
      ‖A‖ ≤ C * ‖tensorCoordinates b A‖ := by
  let : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
    Module.Finite.of_injective (tensorCoordinates b) (tensorCoordinates_injective b)
  obtain ⟨K, hK, hAnti⟩ :=
    (tensorCoordinates b).injective_iff_antilipschitz.mp (tensorCoordinates_injective b)
  refine ⟨K, by exact_mod_cast hK, fun A => ?_⟩
  simpa only [dist_eq_norm, map_zero, sub_zero] using hAnti.le_mul_dist A 0

/-- Actual finite coordinate absolute values give the corresponding scalar sum bound. -/
theorem exists_tensor_norm_le_sum (b : Module.Basis I ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : E [⋀^Fin 2]→L[ℝ] ℝ,
      ‖A‖ ≤ C * ∑ s : Fin 2 → I, |A (fun i => b (s i))| := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_tensor_norm_le_coordinates b
  refine ⟨C, hC, fun A => (hbound A).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  have hsum : 0 ≤ ∑ s : Fin 2 → I, |A (fun i => b (s i))| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  apply (pi_norm_le_iff_of_nonneg (x := tensorCoordinates b A) hsum).mpr
  intro s
  change |A (fun i => b (s i))| ≤ _
  exact Finset.single_le_sum
    (f := fun t : Fin 2 → I => |A (fun i => b (t i))|)
    (fun t _ => abs_nonneg (A (fun i => b (t i)))) (Finset.mem_univ s)

end

end SGPT.Foundations.Analysis.Pending.XiaoFiniteTensorNorm
