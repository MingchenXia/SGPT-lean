import SGPT.Foundations.Analysis.Pending.NaturalThetaPshWeakLimitRealization
import SGPT.Foundations.Analysis.Pending.NaturalWeakThetaPshStrongChartL1
import SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshWeakLimit
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Original singular normalized theta-PSH subsequence compactness

The actual cofinal ultrafilter first produces a genuine original weak
limit. Original canonical strong convergence is obtained internally;
only its one global scalar error is used for strict subsequence extraction.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshCompactness

open FirstPass NaturalThetaPshWeakLimitRealization NaturalWeakThetaPshStrongChartL1
  NaturalNormalizedThetaPshWeakLimit ChartwiseGlobalL1

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {θ : SmoothRealForm n M 2}

/-- Original normalized singular theta-PSH sequences have a genuine normalized canonical L1 strictly increasing subsequence. -/
theorem exists_strictMono_subseq_of_sup_eq_zero
    {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential θ (u j))
    (hsup : ∀ j, (⨆ x, u j x) = 0) :
    ∃ (v : M → EReal) (s : ℕ → ℕ),
      IsThetaPshPotential θ v ∧ (⨆ x, v x) = 0 ∧ StrictMono s ∧
      ManifoldL1LocallyTendsto (n := n) (fun k => u (s k)) atTop v ∧
      Tendsto (fun k => globalL1EDistance μ (u (s k)) v) atTop (𝓝 0) := by
  have hθ : HasSmoothLocalPotentials θ := (hu 0).1.hasSmoothLocalPotentials
  have hle (j : ℕ) (x : M) : u j x ≤ 0 := hsup j ▸ le_iSup (u j) x
  have hnorm (j : ℕ) : ∃ x₀, 0 ≤ u j x₀ := by
    obtain ⟨x₀, hx₀⟩ := exists_eq_zero_of_sup_eq_zero (hu j) (hsup j)
    exact ⟨x₀, hx₀ ▸ le_rfl⟩
  let U : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨v, hv, hweak⟩ := exists_genuine_weak_limit_of_normalized hθ U u hu hle hnorm
  have hvnorm : (⨆ x, v x) = 0 := sup_eq_zero_of_chart_weak_tests hu hv hsup hweak
  have hchart : ManifoldL1LocallyTendsto (n := n) u (U : Filter ℕ) v :=
    manifoldL1LocallyTendsto_of_chart_weak_tests hu hv hweak
      (C := 0) (fun j x => by simpa using hle j x)
  let error : ℕ → ℝ≥0∞ := fun j => globalL1EDistance μ (u j) v
  have hglobal : Tendsto error (U : Filter ℕ) (𝓝 0) :=
    (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hμ
      (fun j => (hu j).1.quasiPlurisubharmonic) hv.1.quasiPlurisubharmonic).mp hchart
  have hmapNe : NeBot (Filter.map error (U : Filter ℕ)) := inferInstance
  have hmapLe : Filter.map error (U : Filter ℕ) ≤
      (𝓝 (0 : ℝ≥0∞)) ⊓ Filter.map error atTop :=
    le_inf hglobal (Filter.map_mono (Ultrafilter.of_le (atTop : Filter ℕ)))
  have hcommon : NeBot ((𝓝 (0 : ℝ≥0∞)) ⊓ Filter.map error atTop) := hmapNe.mono hmapLe
  obtain ⟨s, hs, herror⟩ := Filter.subseq_tendsto_of_neBot hcommon
  have hglobalSub : Tendsto (fun k => globalL1EDistance μ (u (s k)) v) atTop (𝓝 0) :=
    herror
  refine ⟨v, s, hv, hvnorm, hs, ?_, hglobalSub⟩
  exact (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hμ
    (fun k => (hu (s k)).1.quasiPlurisubharmonic) hv.1.quasiPlurisubharmonic).mpr hglobalSub

end SGPT.Foundations.Analysis.Pending.NaturalNormalizedThetaPshCompactness
