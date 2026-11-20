import SGPT.Foundations.Analysis.Pending.NaturalCrossChartWeightedTensorTransport
import SGPT.Foundations.Analysis.Pending.NaturalCompactSmoothFormEmbedding

/-!
# Genuine finite relocalization of original smooth forms

Actual chart tensor transport and support inclusions construct the continuous
comparison map between original supported stage products. The original full
coefficient compatibility and the partition identity internally give exact
relocalization of every global smooth representative, including off-target zeros.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalFiniteChartRelocalization

open FirstPass NaturalCrossChartWeightedTensorTransport NaturalCompactSmoothFormEmbedding

variable {n q m l : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem chartSupport_subset_target (e : ComplexChart n M) (χ : M → ℝ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source) :
    (chartSupport e χ hc hs : Set (ComplexModel n)) ⊆ e.val.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.val.map_source (hs hx)

omit [IsComplexManifold n M] in
private theorem outputCompact_le_chartSupport (e f : ComplexChart n M)
    (χ ψ : M → ℝ) (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ e.val.source)
    (hcψ : IsCompact (tsupport ψ)) (hsψ : tsupport ψ ⊆ f.val.source) :
    outputCompact e f (chartSupport e χ hc hs) (chartSupport_subset_target e χ hc hs)
      ψ hsψ ≤ chartSupport f ψ hcψ hsψ := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx.2, rfl⟩

/-- Actual finite continuous comparison between original supported stage products. -/
def relocalizeCLM (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source) :
    (Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) →L[ℝ]
      Π j : Fin l, 𝓓_{chartSupport (f j) (ψ j) (hcψ j) (hsψ j)}(ComplexModel n,
        (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.pi fun j => ∑ i,
    (ContDiffMapSupportedIn.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (K₁ := outputCompact (e i) (f j) (chartSupport (e i) (χ i) (hc i) (hs i))
        (chartSupport_subset_target (e i) (χ i) (hc i) (hs i)) (ψ j) (hsψ j))
      (K₂ := chartSupport (f j) (ψ j) (hcψ j) (hsψ j))).comp
      ((chartWeightedPullCLM (e i) (f j) (chartSupport (e i) (χ i) (hc i) (hs i))
        (chartSupport_subset_target (e i) (χ i) (hc i) (hs i))
        (ψ j) (hψ j) (hsψ j)).comp (ContinuousLinearMap.proj i))

/-- Exact whole readback of the actual finite comparison map. -/
theorem relocalizeCLM_apply (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hc : ∀ i, IsCompact (tsupport (χ i))) (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source)
    (A : Π i : Fin m, 𝓓_{chartSupport (e i) (χ i) (hc i) (hs i)}(ComplexModel n,
      (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) (j : Fin l) (z : ComplexModel n) :
    relocalizeCLM e χ hc hs f ψ hψ hcψ hsψ A j z =
      ∑ i, (chartTransition (f j) (e i)).source.indicator (fun y =>
        ψ j ((f j).val.symm y) • (A i (chartTransition (f j) (e i) y)).compContinuousLinearMap
          (chartTransitionDerivative (f j) (e i) y)) z := by
  classical
  simp [relocalizeCLM, ContDiffMapSupportedIn.monoCLM_apply,
    outputCompact_le_chartSupport, chartWeightedPullCLM_apply]

/-- Exact relocalization of every original global smooth form, from its true full compatibility. -/
theorem relocalizeCLM_localized (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1)
    (f : Fin l → ComplexChart n M) (ψ : Fin l → M → ℝ)
    (hψ : ∀ j, ChartSmooth (n := n) (ψ j)) (hcψ : ∀ j, IsCompact (tsupport (ψ j)))
    (hsψ : ∀ j, tsupport (ψ j) ⊆ (f j).val.source) (α : SmoothRealForm n M q) :
    relocalizeCLM e χ hc hs f ψ hψ hcψ hsψ
      (fun i => localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α) =
        fun j => localizedSupported (f j) (ψ j) (hψ j) (hcψ j) (hsψ j) α := by
  classical
  funext j
  apply ContDiffMapSupportedIn.ext
  intro z
  rw [relocalizeCLM_apply]
  change (∑ i, _) = (f j).val.target.indicator
    (fun y => ψ j ((f j).val.symm y) • α.coeff (f j) y) z
  by_cases hz : z ∈ (f j).val.target
  · have heach (i : Fin m) :
        (chartTransition (f j) (e i)).source.indicator (fun y =>
          ψ j ((f j).val.symm y) •
            ((localizedSupported (e i) (χ i) (hχ i) (hc i) (hs i) α)
              (chartTransition (f j) (e i) y)).compContinuousLinearMap
              (chartTransitionDerivative (f j) (e i) y)) z =
        ψ j ((f j).val.symm z) • (χ i ((f j).val.symm z) • α.coeff (f j) z) := by
      by_cases hi : (f j).val.symm z ∈ (e i).val.source
      · have ho : z ∈ (chartTransition (f j) (e i)).source := ⟨hz, hi⟩
        have htar : chartTransition (f j) (e i) z ∈ (e i).val.target :=
          (e i).val.map_source hi
        rw [indicator_of_mem ho]
        change ψ j ((f j).val.symm z) •
          ((e i).val.target.indicator
            (fun y => χ i ((e i).val.symm y) • α.coeff (e i) y)
            (chartTransition (f j) (e i) z)).compContinuousLinearMap
              (chartTransitionDerivative (f j) (e i) z) = _
        have hinv : (e i).val.symm (chartTransition (f j) (e i) z) =
            (f j).val.symm z := (e i).val.left_inv hi
        rw [indicator_of_mem htar, hinv]
        congr 1
        ext v
        simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
          ContinuousAlternatingMap.smul_apply, Function.comp_def]
        rw [← α.compatible (f j) (e i) z ho v]
      · have ho : z ∉ (chartTransition (f j) (e i)).source := fun h => hi h.2
        have hzero : χ i ((f j).val.symm z) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun h => hi (hs i h)
        simp only [indicator_of_notMem ho, hzero, zero_smul, smul_zero]
    rw [Finset.sum_congr rfl (fun i _ => heach i), indicator_of_mem hz, ← Finset.smul_sum,
      ← Finset.sum_smul, h1, one_smul]
  · rw [indicator_of_notMem hz]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun h => hz h.1) _

end SGPT.Foundations.Analysis.Pending.NaturalFiniteChartRelocalization
