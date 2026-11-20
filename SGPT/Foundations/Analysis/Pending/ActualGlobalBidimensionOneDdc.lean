import SGPT.Foundations.Analysis.Pending.ActualBorelWeightedPatchGlobalCurrent
import SGPT.Foundations.Analysis.Pending.CompactDifferentialOverlap

set_option autoImplicit false

/-! # Actual normalized second transposition of arbitrary signed global currents

The mathematical statements and entire proofs were written before this source.
-/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualGlobalBidimensionOneDdc

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  StronglyPositiveForms CompactDifferentialTests CompactDifferentialOverlap
  ActualBorelWeightedPatchGlobalCurrent

/-- Test inclusion preserves the ambient function and its actual second differential. -/
theorem localDdcTestCLM_mono {N k : ℕ} {U V : Opens (ComplexModel N)}
    (hUV : U ≤ V) (α : TestForm U k) :
    (TestFunction.monoCLM ℝ (localDdcTestCLM α) : TestForm V (k + 1 + 1)) =
      localDdcTestCLM (TestFunction.monoCLM ℝ α : TestForm V k) := by
  have hα : (TestFunction.monoCLM ℝ α : ComplexModel N → RealForm N k) =
      (α : ComplexModel N → RealForm N k) :=
    funext (testForm_inclusion_apply hUV α)
  apply TestFunction.ext
  intro z
  rw [testForm_inclusion_apply hUV, localDdcTestCLM_apply, localDdcTestCLM_apply]
  rw [hα]

def topDegree (N : ℕ) : CurrentDegree N :=
  ⟨2 * N, by rw [complexModel_real_finrank]; omega⟩

private theorem twoComplement (n : ℕ) :
    Module.finrank ℝ (ComplexModel (n + 1)) - 2 * n = 2 := by
  rw [complexModel_real_finrank]
  omega

private theorem zeroComplement (N : ℕ) :
    Module.finrank ℝ (ComplexModel N) - 2 * N = 0 := by
  rw [complexModel_real_finrank]
  omega

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]

private abbrev FullFamily (q : ℕ) :=
  {G : (e : ComplexChart (n + 1) M) → TestForm (chartTarget e) q →L[ℝ] ℝ //
    ∀ (e d : ComplexChart (n + 1) M)
      (η : TestForm (overlapSource e d) q) (ζ : TestForm (overlapTarget e d) q),
      OverlapTestRelated e d η ζ →
        G e (TestFunction.monoCLM ℝ η) = G d (TestFunction.monoCLM ℝ ζ)}

private def asTwo (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n)) :
    FullFamily (n := n) (M := M) 2 :=
  cast (congrArg (FullFamily (n := n) (M := M)) (twoComplement n)) S

/-- Read the original entire chart functional at its actual complementary degree two. -/
def bidimensionOneChartFunctional
    (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n))
    (e : ComplexChart (n + 1) M) : TestForm (chartTarget e) 2 →L[ℝ] ℝ :=
  (asTwo S).val e

theorem bidimensionOneChartFunctional_actualChart
    (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n))
    (e : ComplexChart (n + 1) M) :
    HEq (bidimensionOneChartFunctional S e) (S.inChart e) := by
  have htransport (q : ℕ) (hq : q = 2) (F : FullFamily (n := n) (M := M) q) :
      HEq ((cast (congrArg (FullFamily (n := n) (M := M)) hq) F).val e)
        (F.val e) := by
    cases hq
    rfl
  exact htransport _ (twoComplement n) S

/-- Genuine top-degree gluing of the literal normalized second transpose. -/
def globalDdc (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n)) :
    GlobalCurrent (n + 1) M (topDegree (n + 1)) := by
  let F := asTwo S
  let D : FullFamily (n := n) (M := M) 0 :=
    ⟨fun e => (F.val e).comp localDdcTestCLM, by
      intro e d η ζ hrel
      change F.val e (localDdcTestCLM (TestFunction.monoCLM ℝ η)) =
        F.val d (localDdcTestCLM (TestFunction.monoCLM ℝ ζ))
      rw [← localDdcTestCLM_mono (overlapSource_le e d),
        ← localDdcTestCLM_mono (overlapTarget_le e d)]
      exact F.property e d (localDdcTestCLM η) (localDdcTestCLM ζ)
        (overlapTestRelated_localDdcTestCLM e d η ζ hrel)⟩
  exact cast (congrArg (FullFamily (n := n) (M := M))
    (zeroComplement (n + 1)).symm) D

theorem globalDdc_inChart (S : GlobalCurrent (n + 1) M (borelBidimensionOneDegree n))
    (e : ComplexChart (n + 1) M) :
    HEq ((globalDdc S).inChart e)
      ((bidimensionOneChartFunctional S e).comp localDdcTestCLM) := by
  have htransport (q : ℕ) (hq : q = 0)
      (D : FullFamily (n := n) (M := M) 0) :
      HEq ((cast (congrArg (FullFamily (n := n) (M := M)) hq.symm) D).val e)
        (D.val e) := by
    cases hq
    rfl
  exact htransport _ (zeroComplement (n + 1))
    ⟨fun e => ((asTwo S).val e).comp localDdcTestCLM, by
      intro e d η ζ hrel
      change (asTwo S).val e (localDdcTestCLM (TestFunction.monoCLM ℝ η)) =
        (asTwo S).val d (localDdcTestCLM (TestFunction.monoCLM ℝ ζ))
      rw [← localDdcTestCLM_mono (overlapSource_le e d),
        ← localDdcTestCLM_mono (overlapTarget_le e d)]
      exact (asTwo S).property e d (localDdcTestCLM η) (localDdcTestCLM ζ)
        (overlapTestRelated_localDdcTestCLM e d η ζ hrel)⟩

end SGPT.Foundations.Analysis.Pending.ActualGlobalBidimensionOneDdc
