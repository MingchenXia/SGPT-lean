import SGPT.PSH.HermitianProductPatches
import SGPT.Foundations.Analysis.FirstPass.LocalPotentials
import SGPT.Foundations.Analysis.Pending.ActualBorelWeightedPatchGlobalCurrent

/-!
# Supported mixed currents as genuine global currents

The existing supported-current constructor uses potential patches only for
their geometry. An explicit adapter fills those unused potential fields with
the actual zero form and zero function; the original local current is retained
literally. Thus a nonclosed Hermitian mixed current supplies an actual global
current on every full real two-form test, with the proved native overlap law.
Finite partitions and bounded Borel weights give signed global currents too.
Identifying their local restrictions requires the separate analytic overlap
law for the mixed products.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents ActualBorelWeightedPatchGlobalCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A geometry adapter to the older supported-current API. Its auxiliary
form really is zero; it imposes no equation on the supplied local current
and contains no assertion about the Hermitian background. -/
def CoordinatePatch.zeroPotentialPatch (P : CoordinatePatch (m + 1) M) :
    Patch (fun _ : Fin (m + 1) => (0 : ClosedRealOneOneForm (m + 1) M))
      (fun _ : Fin (m + 1) => fun _ : M => (0 : EReal)) where
  chart := P.chart
  domain := P.domain
  domain_le_target := P.domain_le_target
  potential := fun _ _ => 0
  localPotential := fun _ => LocalPotentials.localPotential_zero P.chart P.domain.isOpen P.domain_le_target
  plurisubharmonic := fun _ z _ => by
    simpa only [chartFunction, zero_add, EReal.coe_zero] using
      (plurisubharmonicAt_const (0 : EReal) (by simp) z)

@[simp] theorem CoordinatePatch.zeroPotentialPatch_source
    (P : CoordinatePatch (m + 1) M) :
    P.zeroPotentialPatch.source = P.source := rfl

variable [MeasurableSpace M] [BorelSpace M]

/-- The original positive mixed current, multiplied by a supported smooth
cutoff and an actual bounded Borel function, defines a genuine signed global
current of bidimension one. Full-test compatibility is proved internally. -/
def weightedPatchCurrent (P : CoordinatePatch (m + 1) M)
    {T : LocalProductCurrent (m + 1) P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    GlobalCurrent (m + 1) M (borelBidimensionOneDegree m) :=
  borelWeightedPatchGlobalCurrent P.zeroPotentialPatch hT χ hχ hsupp hnonneg f hf hb

/-- Whole-chart evaluations retain the exact original supported local
full-test functional, including every real two-form test. -/
theorem weightedPatchCurrent_inChart (e : ComplexChart (m + 1) M)
    (P : CoordinatePatch (m + 1) M)
    {T : LocalProductCurrent (m + 1) P.domain 1} (hT : IsPositive T)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    HEq ((weightedPatchCurrent P hT χ hχ hsupp hnonneg f hf hb).inChart e)
      (BorelChartWeightedPatchCurrent.chartBorelWeightedFullTestFunctional e
        P.zeroPotentialPatch hT χ hχ hsupp hnonneg f hf hb) :=
  borelWeightedPatchGlobalCurrent_inChart e P.zeroPotentialPatch hT χ hχ hsupp hnonneg f hf hb

/-- The finite sum is a genuine global current before any independence of
the chosen patches or partition is claimed. Its derivatives consequently
use the native global-current calculus. -/
def partitionedGlobalCurrent {a k : ℕ} (P : Fin a → CoordinatePatch (m + 1) M)
    (T : ∀ i, LocalProductCurrent (m + 1) (P i).domain 1) (hT : ∀ i, IsPositive (T i))
    (idx : Fin k → Fin a) (χ : Fin k → M → ℝ)
    (hχ : ∀ j, ChartSmooth (n := m + 1) (χ j))
    (hsupp : ∀ j, tsupport (χ j) ⊆ (P (idx j)).source)
    (hnonneg : ∀ j x, 0 ≤ χ j x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    GlobalCurrent (m + 1) M (borelBidimensionOneDegree m) :=
  ∑ j, weightedPatchCurrent (P (idx j)) (hT (idx j)) (χ j) (hχ j)
    (hsupp j) (hnonneg j) f hf hb

/-- A compact finite cover internally produces a supported smooth partition
and hence a genuine global signed current from the original local currents. -/
theorem exists_partitionedGlobalCurrent [CompactSpace M] {a : ℕ}
    (P : Fin a → CoordinatePatch (m + 1) M)
    (T : ∀ i, LocalProductCurrent (m + 1) (P i).domain 1) (hT : ∀ i, IsPositive (T i))
    (hcover : ∀ x : M, ∃ i, x ∈ (P i).source)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    ∃ (k : ℕ) (idx : Fin k → Fin a) (χ : Fin k → M → ℝ)
      (hχ : ∀ j, ChartSmooth (n := m + 1) (χ j))
      (hsupp : ∀ j, tsupport (χ j) ⊆ (P (idx j)).source)
      (hnonneg : ∀ j x, 0 ≤ χ j x),
      (∀ x, ∑ j, χ j x = 1) ∧
      ∃ S : GlobalCurrent (m + 1) M (borelBidimensionOneDegree m),
        S = partitionedGlobalCurrent P T hT idx χ hχ hsupp hnonneg f hf hb := by
  obtain ⟨k, χ, idx, hχ, hnonneg, hsupp, _hc, hsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := m + 1) (fun i => (P i).source) hcover
  exact ⟨k, idx, χ, hχ, hsupp, hnonneg, hsum,
    partitionedGlobalCurrent P T hT idx χ hχ hsupp hnonneg f hf hb, rfl⟩

end SGPT.PSH.HermitianGlobalProducts
