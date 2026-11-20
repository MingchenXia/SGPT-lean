import SGPT.Foundations.Analysis.Pending.ActualWeightedGlobalFormOverlapPairing

set_option autoImplicit false

/-! # The actual compact global pairing independent of finite chart partitions

The mathematical statement and complete proof preceded this source.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalFormPairing

open FirstPass ChartPartition ActualWeightedGlobalFormChartTests
  ActualWeightedGlobalFormOverlapPairing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem sum_pairings_eq {k : CurrentDegree n} (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    {m l : ℕ} (e : Fin m → ComplexChart n M) (f : Fin l → ComplexChart n M)
    (χ : Fin m → M → ℝ) (ψ : Fin l → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i)) (hψ : ∀ j, ChartSmooth (n := n) (ψ j))
    (hχc : ∀ i, IsCompact (tsupport (χ i)))
    (hχs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (hψs : ∀ j, tsupport (ψ j) ⊆ (f j).val.source)
    (hχ1 : ∀ x, ∑ i, χ i x = 1) (hψ1 : ∀ x, ∑ j, ψ j x = 1)
    (ηe : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (ηf : ∀ j, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (f j))
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (he : ∀ i z, ηe i z = (e i).val.target.indicator
      (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z)
    (hf : ∀ j z, ηf j z = (f j).val.target.indicator
      (fun y => ψ j ((f j).val.symm y) • γ.coeff (f j) y) z) :
    ∑ i, T.inChart (e i) (ηe i) = ∑ j, T.inChart (f j) (ηf j) := by
  classical
  have hprod (i : Fin m) (j : Fin l) :=
    exists_tests_with_pairing T γ (e i) (f j) (fun x => χ i x * ψ j x)
      (fun a => (hχ i a).mul (hψ j a))
      ((hχc i).of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
      (fun x hx => ⟨hχs i (tsupport_mul_subset_left hx),
        hψs j (tsupport_mul_subset_right hx)⟩)
  choose ξe ξf hξe hξf hpair using hprod
  have hsumE (i : Fin m) : ηe i = ∑ j, ξe i j := by
    apply TestFunction.ext
    intro z
    by_cases hz : z ∈ (e i).val.target
    · simp only [he i z, indicator_of_mem hz]
      have hsum : (∑ j, χ i ((e i).val.symm z) * ψ j ((e i).val.symm z)) =
          χ i ((e i).val.symm z) := by
        rw [← Finset.mul_sum, hψ1, mul_one]
      simp [hξe, hz, ← Finset.sum_smul, hsum]
    · simp [he, hξe, hz]
  have hsumF (j : Fin l) : ηf j = ∑ i, ξf i j := by
    apply TestFunction.ext
    intro z
    by_cases hz : z ∈ (f j).val.target
    · simp only [hf j z, indicator_of_mem hz]
      have hsum : (∑ i, χ i ((f j).val.symm z) * ψ j ((f j).val.symm z)) =
          ψ j ((f j).val.symm z) := by
        rw [← Finset.sum_mul, hχ1, one_mul]
      simp [hξf, hz, ← Finset.sum_smul, hsum]
    · simp [hf, hξf, hz]
  calc
    ∑ i, T.inChart (e i) (ηe i) = ∑ i, ∑ j, T.inChart (e i) (ξe i j) := by
      simp only [hsumE, map_sum]
    _ = ∑ i, ∑ j, T.inChart (f j) (ξf i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpair i j
    _ = ∑ j, ∑ i, T.inChart (f j) (ξf i j) := Finset.sum_comm
    _ = ∑ j, T.inChart (f j) (ηf j) := by simp only [hsumF, map_sum]


/-- Compactness produces the unique actual pairing independent of every chart partition. -/
theorem exists_unique_pairing [CompactSpace M] {k : CurrentDegree n}
    (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) :
    ∃! a : ℝ, ∀ (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ),
      (∀ i, ChartSmooth (n := n) (χ i)) →
      (∀ i, IsCompact (tsupport (χ i))) →
      (∀ i, tsupport (χ i) ⊆ (e i).val.source) →
      (∀ x, ∑ i, χ i x = 1) →
      ∀ η : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        (∀ i z, η i z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z) →
        a = ∑ i, T.inChart (e i) (η i) := by
  classical
  obtain ⟨m, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin m → ComplexChart n M := fun i => complexChartAt (idx i)
  have htests (i : Fin m) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e i).val.target.indicator
          (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e i) γ (χ i) (hχ i) (hχc i) (hχs i)
    exact ⟨η, hη⟩
  choose η hη using htests
  refine ⟨∑ i, T.inChart (e i) (η i), ?_, ?_⟩
  · intro l f ψ hψ hψc hψs hψ1 ζ hζ
    exact (sum_pairings_eq T γ f e ψ χ hψ hχ hψc hψs hχs hψ1 hχ1 ζ η hζ hη).symm
  · intro a ha
    exact ha m e χ hχ hχc hχs hχ1 η hη

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalFormPairing
