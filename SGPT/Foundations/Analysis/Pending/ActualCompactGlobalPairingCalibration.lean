import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalLinearPairing

set_option autoImplicit false

/-!
# The actual compact current pairing and its single-chart calibration

The pairing on all global smooth forms is constructed from finite chart
partitions. Weighted forms supported in a single original chart have exactly
their native chart-current evaluation. No metric or positivity is needed.
-/

noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration

open FirstPass StronglyPositiveForms ChartPartition ProductTestForms ActualCompactGlobalLinearPairing
  ActualWeightedGlobalFormChartTests ActualWeightedGlobalFormOverlapPairing

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  {k : CurrentDegree n}

/-- The unique native real linear pairing on all compact global complementary forms. -/
def pairingLM (T : GlobalCurrent n M k) :
    SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →ₗ[ℝ] ℝ :=
  Classical.choose (exists_unique_linear_pairing T).exists

/-- The constructed functional reads every genuine finite chart partition. -/
theorem pairing_eq_sum (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (m : ℕ) (e : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hχc : ∀ i, IsCompact (tsupport (χ i)))
    (hχs : ∀ i, tsupport (χ i) ⊆ (e i).val.source)
    (hχ1 : ∀ x, ∑ i, χ i x = 1)
    (η : ∀ i, _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e i))
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (hη : ∀ i z, η i z = (e i).val.target.indicator
      (fun y => χ i ((e i).val.symm y) • γ.coeff (e i) y) z) :
    pairingLM T γ = ∑ i, T.inChart (e i) (η i) :=
  Classical.choose_spec (exists_unique_linear_pairing T).exists
    γ m e χ hχ hχc hχs hχ1 η hη

private theorem pairing_smulFun_eq (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hχc : IsCompact (tsupport χ)) (hχs : tsupport χ ⊆ e.val.source)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel n) - k.val))
    (hη : ∀ z, η z = e.val.target.indicator
      (fun y => χ (e.val.symm y) • γ.coeff e y) z) :
    pairingLM T (smulFun χ hχ γ) = T.inChart e η := by
  classical
  obtain ⟨m, ψ, idx, hψ, -, hψs, hψc, hψ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let f : Fin m → ComplexChart n M := fun j => complexChartAt (idx j)
  have hprod (j : Fin m) :=
    exists_tests_with_pairing T γ e (f j) (fun x => χ x * ψ j x)
      (fun a => (hχ a).mul (hψ j a))
      (hχc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_left)
      (fun x hx => ⟨hχs (tsupport_mul_subset_left hx),
        hψs j (tsupport_mul_subset_right hx)⟩)
  choose ξe ξf hξe hξf hpair using hprod
  have hsum : η = ∑ j, ξe j := by
    apply TestFunction.ext
    intro z
    by_cases hz : z ∈ e.val.target
    · simp only [hη z, indicator_of_mem hz]
      have hscalar : (∑ j, χ (e.val.symm z) * ψ j (e.val.symm z)) =
          χ (e.val.symm z) := by
        rw [← Finset.mul_sum, hψ1, mul_one]
      simp [hξe, hz, ← Finset.sum_smul, hscalar]
    · simp [hη, hξe, hz]
  have htest (j : Fin m) (z : ComplexModel n) :
      ξf j z = (f j).val.target.indicator
        (fun y => ψ j ((f j).val.symm y) • (smulFun χ hχ γ).coeff (f j) y) z := by
    by_cases hz : z ∈ (f j).val.target
    · rw [hξf j z, indicator_of_mem hz, indicator_of_mem hz, smulFun_coeff,
        ← mul_smul, mul_comm]
    · rw [hξf j z, indicator_of_notMem hz, indicator_of_notMem hz]
  calc
    pairingLM T (smulFun χ hχ γ) = ∑ j, T.inChart (f j) (ξf j) :=
      pairing_eq_sum T (smulFun χ hχ γ) m f ψ hψ hψc hψs hψ1 ξf htest
    _ = ∑ j, T.inChart e (ξe j) :=
      Finset.sum_congr rfl fun j _ => (hpair j).symm
    _ = T.inChart e η := by rw [hsum, map_sum]

/-- A single weighted form internally produces its actual native test and pairing. -/
theorem exists_testForm_with_pairing (T : GlobalCurrent n M k)
    (γ : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (e : ComplexChart n M) (χ : M → ℝ) (hχ : ChartSmooth (n := n) χ)
    (hcompact : IsCompact (tsupport χ)) (hsource : tsupport χ ⊆ e.val.source) :
    ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val),
      (∀ z, η z = e.val.target.indicator
        (fun y => χ (e.val.symm y) • γ.coeff e y) z) ∧
      tsupport (η : ComplexModel n → RealForm n
        (Module.finrank ℝ (ComplexModel n) - k.val)) ⊆ e.val '' tsupport χ ∧
      pairingLM T (smulFun χ hχ γ) = T.inChart e η := by
  obtain ⟨η, hη, hs⟩ := exists_testForm e γ χ hχ hcompact hsource
  exact ⟨η, hη, hs, pairing_smulFun_eq T γ e χ hχ hcompact hsource η hη⟩

end SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration
