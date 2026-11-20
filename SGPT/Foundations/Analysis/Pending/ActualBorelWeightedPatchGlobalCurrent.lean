import SGPT.Foundations.Analysis.Pending.BorelChartWeightedOverlapFullPairing

set_option autoImplicit false

/-! # The actual signed global current from the original Borel patch data

The complete mathematical statements and entire proofs precede this source.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualBorelWeightedPatchGlobalCurrent
open FirstPass FirstPass.GlobalPotentialPatches _root_.SGPT.Foundations.Analysis.LocalCurrents
  LocalProductCurrents BorelChartWeightedPatchCurrent BorelChartWeightedOverlapFullPairing

def borelBidimensionOneDegree (n : ℕ) : CurrentDegree (n + 1) :=
  ⟨2 * n, by rw [complexModel_real_finrank]; omega⟩

private theorem complementary_testDegree (n : ℕ) :
    Module.finrank ℝ (ComplexModel (n + 1)) - 2 * n = 2 := by
  rw [complexModel_real_finrank]
  omega

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (n + 1)) M] [IsComplexManifold (n + 1) M]
  {θ : Fin (n + 1) → ClosedRealOneOneForm (n + 1) M}
  {u : Fin (n + 1) → M → EReal}

def borelWeightedPatchGlobalCurrent (P : Patch θ u)
    {T : LocalProductCurrent (n + 1) P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n + 1) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    GlobalCurrent (n + 1) M (borelBidimensionOneDegree n) := by
  let F : ℕ → Type _ := fun q =>
    {G : (e : ComplexChart (n + 1) M) → TestForm (chartTarget e) q →L[ℝ] ℝ //
    ∀ (e d : ComplexChart (n + 1) M)
      (η : TestForm (overlapSource e d) q) (ζ : TestForm (overlapTarget e d) q),
      OverlapTestRelated e d η ζ →
        G e (TestFunction.monoCLM ℝ η) = G d (TestFunction.monoCLM ℝ ζ)}
  let S : F 2 := ⟨fun e =>
    chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb,
    fun e d η ζ hrel =>
      chartBorelWeightedFullTestFunctional_overlap e d P hT χ hχ hsupp hnonneg
        f hf hb η ζ hrel⟩
  exact cast (congrArg F (complementary_testDegree n).symm) S

theorem borelWeightedPatchGlobalCurrent_inChart (e : ComplexChart (n + 1) M) (P : Patch θ u)
    {T : LocalProductCurrent (n + 1) P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := n + 1) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    HEq ((borelWeightedPatchGlobalCurrent P hT χ hχ hsupp hnonneg f hf hb).inChart e)
      (chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb) := by
  let F : ℕ → Type _ := fun q =>
    {G : (e : ComplexChart (n + 1) M) → TestForm (chartTarget e) q →L[ℝ] ℝ //
    ∀ (e d : ComplexChart (n + 1) M)
      (η : TestForm (overlapSource e d) q) (ζ : TestForm (overlapTarget e d) q),
      OverlapTestRelated e d η ζ →
        G e (TestFunction.monoCLM ℝ η) = G d (TestFunction.monoCLM ℝ ζ)}
  have htransport (q : ℕ) (hq : q = 2) (S : F 2) :
      HEq ((cast (congrArg F hq.symm) S).val e) (S.val e) := by
    cases hq
    rfl
  exact htransport _ (complementary_testDegree n)
    ⟨fun e => chartBorelWeightedFullTestFunctional e P hT χ hχ hsupp hnonneg f hf hb,
      fun e d η ζ hrel =>
        chartBorelWeightedFullTestFunctional_overlap e d P hT χ hχ hsupp hnonneg
          f hf hb η ζ hrel⟩

end SGPT.Foundations.Analysis.Pending.ActualBorelWeightedPatchGlobalCurrent
