import SGPT.Foundations.Analysis.Pending.ScalarFullTestTranspose
import SGPT.Foundations.Analysis.Pending.SingularTopFormLocalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.ScalarAdjointDomainCongruence

open FirstPass StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  CompactVariableCurrentTests LocalCurrentLebesgue LocalPositiveCurrentGluing ScalarFullTestTranspose
  SingularTopFormLocalization

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

/-- Equality of entire genuine test functions preserves the full scalar adjoint across domains. -/
theorem scalarAdjointTest_congr_functions {m : ℕ}
    {U V : Opens (ComplexModel (m + 1))}
    (α : 𝓓(U, RealForm (m + 1) (2 * m)))
    (β : 𝓓(V, RealForm (m + 1) (2 * m)))
    (h : (α : ComplexModel (m + 1) → RealForm (m + 1) (2 * m)) =
      (β : ComplexModel (m + 1) → RealForm (m + 1) (2 * m))) :
    (scalarAdjointTest α : ComplexModel (m + 1) → ℝ) =
      (scalarAdjointTest β : ComplexModel (m + 1) → ℝ) := by
  have hd {A B : Opens (ComplexModel (m + 1))} (f : 𝓓(A, ℝ)) (g : 𝓓(B, ℝ))
      (hfg : (f : ComplexModel (m + 1) → ℝ) = (g : ComplexModel (m + 1) → ℝ))
      (v : ComplexModel (m + 1)) :
      (dTest v f : ComplexModel (m + 1) → ℝ) =
        (dTest v g : ComplexModel (m + 1) → ℝ) := by
    funext x
    rw [dTest_apply, dTest_apply]
    rw [hfg]
  have hc : ∀ i, (coeffTest α i : ComplexModel (m + 1) → ℝ) =
      (coeffTest β i : ComplexModel (m + 1) → ℝ) := by
    intro i
    funext x
    simp only [coeffTest, TestFunction.postcompCLM_apply, Function.comp_apply]
    rw [congrFun h x]
  funext x
  simp only [scalarAdjointTest, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [congrFun (hd _ _ (hd _ _ (hc i) (realBasis (m + 1) a))
    (realBasis (m + 1) b)) x]

/-- The actual local-open and chart-target test adjoints agree as entire scalar functions. -/
theorem scalarAdjoint_chartTest_eq_localizedTensorTest {m : ℕ}
    {U : Opens (ComplexModel (m + 1))} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (e : ComplexChart (m + 1) M) (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (G : SmoothRealForm (m + 1) M (2 * m)) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ e.val.source) (hU : e.val '' tsupport χ ⊆ U) :
    (scalarAdjointTest (chartTest e χ hχ G hc hs hU) : ComplexModel (m + 1) → ℝ) =
      (scalarAdjointTest (localizedTensorTest e χ hχ G hc hs) : ComplexModel (m + 1) → ℝ) := by
  apply scalarAdjointTest_congr_functions
  rfl

end SGPT.Foundations.Analysis.Pending.ScalarAdjointDomainCongruence
