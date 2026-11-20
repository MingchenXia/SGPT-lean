import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcTransposition

/-! Genuine global normalized second transposition read in any actual finite
chart partition. The original global scalar and all full local tests remain
visible, with no product-overlap or measure hypothesis. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalDdcPartitionReadback

open Set TopologicalSpace
open scoped Distributions Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms ProductTestForms ActualBorelWeightedPatchGlobalCurrent ActualGlobalBidimensionOneDdc
  ActualCompactGlobalDdcTransposition ActualCompactGlobalPairingCalibration
  ActualWeightedGlobalFormChartTests XiaoComplexDifferential

private theorem test_cast_apply {N a b : ℕ} {U : Opens (ComplexModel N)} (h : a = b)
    (α : LocalCurrents.TestForm U a) (z : ComplexModel N) :
    (h ▸ α : LocalCurrents.TestForm U b) z = (h ▸ α z : RealForm N b) := by
  cases h
  rfl

private theorem form_cast_coeff {N a b : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X] (h : a = b)
    (α : SmoothRealForm N X a) (e : ComplexChart N X) (z : ComplexModel N) :
    (h ▸ α : SmoothRealForm N X b).coeff e z = (h ▸ α.coeff e z : RealForm N b) := by
  cases h
  rfl

private theorem form_cast_smul {N a b : ℕ} (h : a = b) (c : ℝ) (α : RealForm N a) :
    (h ▸ (c • α) : RealForm N b) = c • (h ▸ α : RealForm N b) := by
  cases h
  rfl

private theorem form_cast_zero {N a b : ℕ} (h : a = b) :
    (h ▸ (0 : RealForm N a) : RealForm N b) = 0 := by
  cases h
  rfl

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M] [CompactSpace M]

/-- Every finite actual chart partition supplies genuine full local tests
whose sum is exactly the compact second-transpose pairing. -/
theorem exists_partition_tests_pairing_globalDdc
    (S : GlobalCurrent (m+1) M (borelBidimensionOneDegree m))
    (β : SmoothRealForm (m+1) M 0) (a : ℕ) (e : Fin a → ComplexChart (m+1) M)
    (χ : Fin a → M → ℝ) (hχ : ∀ i, ChartSmooth (n := m+1) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1) :
    ∃ α : ∀ i, LocalCurrents.TestForm (chartTarget (e i)) 2,
      (∀ i z, α i z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • (ddc β).coeff (e i) y) z) ∧
      pairingLM (globalDdc S) ((top_complement m).symm ▸ β) =
        ∑ i, S.inChart (e i) ((bidimensionOne_complement m).symm ▸ α i) := by
  classical
  have hex (i : Fin a) : ∃ α : LocalCurrents.TestForm (chartTarget (e i)) 2,
      (∀ z, α z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) • (ddc β).coeff (e i) y) z) ∧
      tsupport (α : ComplexModel (m+1) → RealForm (m+1) 2) ⊆
        (e i).val '' tsupport (χ i) := by
    exact exists_testForm (e i) (ddc β) (χ i) (hχ i) (hc i) (hs i)
  choose α hα hαsupp using hex
  refine ⟨α, hα, ?_⟩
  rw [pairing_globalDdc]
  apply pairing_eq_sum S _ a e χ hχ hc hs h1
  intro i z
  rw [test_cast_apply, hα i z]
  by_cases hz : z ∈ (e i).val.target
  · rw [indicator_of_mem hz, indicator_of_mem hz, form_cast_coeff, form_cast_smul]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, form_cast_zero]

/-- For an actual global smooth scalar, the manufactured local tests have
exactly the original normalized scalar `smoothDDC` as their coefficients. -/
theorem exists_partition_tests_pairing_globalDdc_scalar
    (S : GlobalCurrent (m+1) M (borelBidimensionOneDegree m))
    (f : M → ℝ) (hf : ChartSmooth (n := m+1) f)
    (a : ℕ) (e : Fin a → ComplexChart (m+1) M)
    (χ : Fin a → M → ℝ) (hχ : ∀ i, ChartSmooth (n := m+1) (χ i))
    (hc : ∀ i, IsCompact (tsupport (χ i)))
    (hs : ∀ i, tsupport (χ i) ⊆ (e i).val.source) (h1 : ∀ x, ∑ i, χ i x = 1) :
    ∃ α : ∀ i, LocalCurrents.TestForm (chartTarget (e i)) 2,
      (∀ i z, α i z = (e i).val.target.indicator
        (fun y => χ i ((e i).val.symm y) •
          smoothDDC (fun z => f ((e i).val.symm z)) y) z) ∧
      pairingLM (globalDdc S)
        ((top_complement m).symm ▸ (smulFun f hf (unitForm : SmoothRealForm (m+1) M 0))) =
        ∑ i, S.inChart (e i) ((bidimensionOne_complement m).symm ▸ α i) := by
  obtain ⟨α, hα, hp⟩ := exists_partition_tests_pairing_globalDdc S
    (smulFun f hf (unitForm : SmoothRealForm (m+1) M 0)) a e χ hχ hc hs h1
  refine ⟨α, ?_, hp⟩
  simpa only [ddc_smulFun_unitForm, SmoothDDCForm.ddcForm_coeff] using hα

end SGPT.PSH.HermitianGlobalDdcPartitionReadback
