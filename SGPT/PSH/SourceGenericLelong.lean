import SGPT.PSH.VariableComponentConverse

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open scoped ENNReal

variable {X : Type*} [TopologicalSpace X] (A : VariableComplexAtlas X)

/-- The book's original generic Lelong value on the literal original carrier. -/
def sourceGenericLelong (u : X → EReal) (F : Set X) : ℝ≥0∞ :=
  ⨅ q ∈ F, A.sourceLelong u q

variable {A}

/-- Original hypotheses give the literal attained minimum, with every infinite value retained. -/
theorem IsPSH.exists_sourceGenericLelong_minimum [T2Space X] [ParacompactSpace X]
    {u : X → EReal} (hu : A.IsPSH u) {F : Set X}
    (hF : A.HasIrreducibleAnalyticChartEquations F) :
    ∃ p ∈ F, A.sourceGenericLelong u F = A.sourceLelong u p ∧
      ∀ q ∈ F, A.sourceGenericLelong u F ≤ A.sourceLelong u q := by
  obtain ⟨p, hp, hmin⟩ := hu.exists_sourceLelong_irreducible_minimum hF
  refine ⟨p, hp, hmin.symm, ?_⟩
  intro q hq
  exact iInf_le_of_le q (iInf_le_of_le hq le_rfl)

end SGPT.PSH.VariableComplexAtlas
