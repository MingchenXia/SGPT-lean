import SGPT.Foundations.Analysis.Pending.NaturalSupportedSmoothCompleteness
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Actual exterior differentiation on the original supported smooth stages

The supported derivative followed by actual alternating uncurry is continuous
on the existing all-jet topology and obeys its genuine one-order seminorm bound.
-/

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalSupportedExteriorDerivative

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {q : ℕ}

local instance tensorNormedAddCommGroup (j : ℕ) :
    NormedAddCommGroup (E [⋀^Fin j]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance tensorNormedSpace (j : ℕ) :
    NormedSpace ℝ (E [⋀^Fin j]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedSpace

local instance derivativeTensorNormedSpace (j : ℕ) :
    NormedSpace ℝ (E →L[ℝ] E [⋀^Fin j]→L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

local instance derivativeTensorNormedAddCommGroup (j : ℕ) :
    NormedAddCommGroup (E →L[ℝ] E [⋀^Fin j]→L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Actual exterior differentiation, with its genuine original stage topology. -/
def stageExteriorDerivativeCLM (K : Compacts E) :
    𝓓_{K}(E, E [⋀^Fin q]→L[ℝ] F) →L[ℝ]
      𝓓_{K}(E, E [⋀^Fin (q + 1)]→L[ℝ] F) :=
  (ContDiffMapSupportedIn.postcompCLM
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)).comp
      (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

/-- Exact whole-field readback of the actual stage map. -/
theorem stageExteriorDerivativeCLM_apply (K : Compacts E)
    (A : 𝓓_{K}(E, E [⋀^Fin q]→L[ℝ] F)) (x : E) :
    stageExteriorDerivativeCLM K A x = extDeriv A x := by
  simp only [stageExteriorDerivativeCLM, ContinuousLinearMap.comp_apply,
    ContDiffMapSupportedIn.postcompCLM_apply,
    ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ A (by simp : (⊤ : ℕ∞) + 1 ≤ ⊤)]
  rfl

/-- Every full derivative commutes with the same alternating uncurry operator. -/
theorem stageExteriorDerivative_iteratedFDeriv (K : Compacts E)
    (A : 𝓓_{K}(E, E [⋀^Fin q]→L[ℝ] F)) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (stageExteriorDerivativeCLM K A) x =
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ A) x) := by
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).iteratedFDeriv_comp_left
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ A).contDiff.contDiffAt
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))

/-- Genuine one-order control by the original all-jet seminorms. -/
theorem stageExteriorDerivative_seminorm_le (K : Compacts E)
    (A : 𝓓_{K}(E, E [⋀^Fin q]→L[ℝ] F)) (j : ℕ) :
    N[ℝ]_{K, j} (stageExteriorDerivativeCLM K A) ≤
      ‖ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (n := q)‖ * N[ℝ]_{K, j + 1} A := by
  have h := ContDiffMapSupportedIn.seminorm_postcompLM_le ℝ
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F)
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ A) (i := j)
  change N[ℝ]_{K, j} (stageExteriorDerivativeCLM K A) ≤
    ‖ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F (n := q)‖ *
      N[ℝ]_{K, j} (ContDiffMapSupportedIn.fderivLM ℝ ⊤ ⊤ A) at h
  rw [ContDiffMapSupportedIn.seminorm_fderivLM_top] at h
  exact h

/-- The actual stage differential squares to zero everywhere. -/
theorem stageExteriorDerivative_sq (K : Compacts E)
    (A : 𝓓_{K}(E, E [⋀^Fin q]→L[ℝ] F)) :
    stageExteriorDerivativeCLM K (stageExteriorDerivativeCLM K A) = 0 := by
  apply ContDiffMapSupportedIn.ext
  intro x
  simp only [stageExteriorDerivativeCLM_apply]
  have heq : (stageExteriorDerivativeCLM K A : E → E [⋀^Fin (q + 1)]→L[ℝ] F) = extDeriv A :=
    funext (stageExteriorDerivativeCLM_apply K A)
  rw [heq]
  exact extDeriv_extDeriv_apply A.contDiff.contDiffAt
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

end SGPT.Foundations.Analysis.Pending.NaturalSupportedExteriorDerivative
