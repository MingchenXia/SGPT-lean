import SGPT.PSH.HermitianCurrentPartitionReadback
import SGPT.Foundations.Analysis.Pending.PositiveCurrentBorelAddition
import SGPT.Foundations.Analysis.Pending.SupportedBorelNativeReconstruction

/-!
# Full native readers of the original partitioned Hermitian current

The same actual global current retains every original compact full two-form
reader on each correction patch. Its signed bounded Borel multiplication
is identified internally, and the unweighted reader recovers the original
mixed current. These identities justify actual partition cancellation before
any analytic torsion bound.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalCurrentPullback ChartPartitionRelativeSupports ChartWeightedPatchCurrent
  WholeChartPotentialPatchTransition BorelChartWeightedPatchCurrent BorelChartZeroExtension
  SupportedBorelNativeReconstruction PositiveCurrentBorelAddition
  BidimensionOneFullTestFunctional ActualBorelWeightedPatchGlobalCurrent
  ActualGlobalBidimensionOneDdc
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] {omega : Background (m + 1) M}

private theorem isPositive_finite_sum {n k r : ℕ} {U : Opens (ComplexModel n)}
    (T : Fin k → LocalProductCurrent n U r) (hT : ∀ j, IsPositive (T j)) :
    IsPositive (∑ j, T j) := by
  classical
  have hpos (s : Finset (Fin k)) : IsPositive (∑ j ∈ s, T j) := by
    induction s using Finset.induction_on with
    | empty => simpa using (isPositive_zero (n := n) (U := U) (q := r))
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (hT j).add ih
  exact hpos Finset.univ

private theorem chart_borel_eq_mulBorel (e : ComplexChart (m + 1) M)
    (P : CoordinatePatch (m + 1) M) {T : LocalProductCurrent (m + 1) P.domain 1}
    (hT : IsPositive T) (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hsupp : tsupport χ ⊆ P.source) (hnonneg : ∀ x, 0 ≤ χ x)
    (f : M → ℝ) (hf : Measurable f) (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    chartBorelWeightedPullback e P.zeroPotentialPatch hT χ hχ hsupp hnonneg f hf hb =
      mulBorel (chartWeightedPullback e P.zeroPotentialPatch hT χ hχ hsupp hnonneg)
        (chartBorelWeight e f) := by
  let PP := P.zeroPotentialPatch
  let hg := WholeChartPotentialPatchTransition.isBiholomorphicPair e PP
  let hw := chartWeight_relativeSupport e χ hχ PP.source hsupp hnonneg
  exact borelWeightedExtendedPullback_eq_mulBorel hg.2.2
    (isPositive_restrict hT hg.2.1) hg.1 (chartWeight e χ) hw.1 hw.2.2.2
    hw.2.1 (chartBorelWeight e f) (measurable_chartBorelWeight e f hf)
    (chartBorelWeight_bound e f hb)

namespace MixedCurrentPartition

/-- The actual whole-chart coefficient current whose full functional is
that of the SAME constructed native global current. -/
def chartCurrent (D : MixedCurrentPartition omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (e : ComplexChart (m + 1) M) : LocalProductCurrent (m + 1) (chartTarget e) 1 :=
  ∑ j, chartBorelWeightedPullback e (D.patch j).geometry.zeroPotentialPatch
    ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
    (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) f hf hfb

/-- On every correction patch the signed chart current is the original
Borel multiplication current, with all transport and partition identities
internally established. -/
theorem chartCurrent_restrict (D : MixedCurrentPartition omega) (u : Fin m → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (P : BackgroundPatch omega) :
    restrict P.geometry.domainInChart (D.chartCurrent u hu hb f hf hfb P.geometry.chart) =
      mulBorel (P.bidimensionOneCurrent u) (chartBorelWeight P.geometry.chart f) := by
  classical
  let W (j : Fin D.count) := chartWeightedPullback P.geometry.chart
    (D.patch j).geometry.zeroPotentialPatch ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
    (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j)
  have hp (j : Fin D.count) : IsPositive (W j) :=
    isPositive_chartWeightedPullback P.geometry.chart (D.patch j).geometry.zeroPotentialPatch
      ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
      (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j)
  have hfm := measurable_chartBorelWeight P.geometry.chart f hf
  have hfcompact : IsLocallyBoundedOn (chartBorelWeight P.geometry.chart f)
      (chartTarget P.geometry.chart) := by
    obtain ⟨C, hC⟩ := chartBorelWeight_bound P.geometry.chart f hfb
    exact fun K _ _ => ⟨C, fun x _ => hC x⟩
  have hsumB : D.chartCurrent u hu hb f hf hfb P.geometry.chart =
      mulBorel (∑ j, W j) (chartBorelWeight P.geometry.chart f) := by
    calc
      _ = ∑ j, mulBorel (W j) (chartBorelWeight P.geometry.chart f) :=
        Finset.sum_congr rfl fun j _ => chart_borel_eq_mulBorel P.geometry.chart
          (D.patch j).geometry ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
          (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) f hf hfb
      _ = _ := (mulBorel_finsetSum_positive Finset.univ W (fun j _ => hp j) hfm hfcompact).symm
  rw [hsumB, ← mulBorel_restrict (isPositive_finite_sum W hp)
    P.geometry.domainInChart hfm hfcompact]
  exact congrArg (fun T => mulBorel T (chartBorelWeight P.geometry.chart f))
    (D.unweighted_chartCurrent_restrict u hu hb P)

private theorem fullTestFunctional_finite_sum {n k : ℕ} {U : Opens (ComplexModel n)}
    (T : Fin k → LocalProductCurrent n U 1) :
    fullTestFunctional (∑ j, T j) = ∑ j, fullTestFunctional (T j) := by
  classical
  ext α
  simp only [fullTestFunctional, _root_.sum_apply, LinearMap.sum_apply]
  change (∑ i, (∑ j, T j (LocalCurrentLebesgue.formBasis n 1 i)) _) =
    ∑ j, ∑ i, T j (LocalCurrentLebesgue.formBasis n 1 i) _
  simp only [_root_.sum_apply]
  rw [Finset.sum_comm]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem inChart_finite_sum {k : ℕ}
    (S : Fin k → GlobalCurrent (m + 1) M (borelBidimensionOneDegree m))
    (e : ComplexChart (m + 1) M) :
    (∑ j, S j).inChart e = ∑ j, (S j).inChart e := by
  simp only [GlobalCurrent.inChart, Submodule.coe_sum, Finset.sum_apply]

private theorem heq_finite_sum {n k q r : ℕ} {U : Opens (ComplexModel n)}
    (hqr : q = r) (F : Fin k → TestForm U q →L[ℝ] ℝ)
    (G : Fin k → TestForm U r →L[ℝ] ℝ) (hFG : ∀ j, HEq (F j) (G j)) :
    HEq (∑ j, F j) (∑ j, G j) := by
  subst r
  apply heq_of_eq
  exact Finset.sum_congr rfl fun j _ => eq_of_heq (hFG j)

/-- Entire-chart full testing is the exact native reader of the SAME
constructed global signed current. -/
theorem current_nativeChartFunctional (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (e : ComplexChart (m + 1) M) :
    bidimensionOneChartFunctional (D.current u hu hb f hf hfb) e =
      fullTestFunctional (D.chartCurrent u hu hb f hf hfb e) := by
  have hdegree : Module.finrank ℝ (ComplexModel (m + 1)) -
      (borelBidimensionOneDegree m).val = 2 := by
    change Module.finrank ℝ (ComplexModel (m + 1)) - 2 * m = 2
    rw [complexModel_real_finrank]
    omega
  have hwhole : HEq ((D.current u hu hb f hf hfb).inChart e)
      (∑ j, chartBorelWeightedFullTestFunctional e (D.patch j).geometry.zeroPotentialPatch
        ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
        (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) f hf hfb) := by
    unfold current
    rw [inChart_finite_sum]
    exact heq_finite_sum hdegree _ _ (fun j => weightedPatchCurrent_inChart e
      (D.patch j).geometry ((D.patch j).bidimensionOneCurrent_isPositive u hu hb)
      (D.weight j) (D.smooth j) (D.supported j) (D.nonneg j) f hf hfb)
  have heq := eq_of_heq
    ((bidimensionOneChartFunctional_actualChart (D.current u hu hb f hf hfb) e).trans hwhole)
  rw [heq, chartCurrent, fullTestFunctional_finite_sum]
  rfl

/-- Every original local full two-form test reads the signed multiplication
of the original local mixed current. There is no covariance or readback
certificate among the premises. -/
theorem current_local_full_test (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (P : BackgroundPatch omega) (α : TestForm P.geometry.domain 2) :
    bidimensionOneChartFunctional (D.current u hu hb f hf hfb) P.geometry.chart
      (TestFunction.monoCLM ℝ α) =
      fullTestFunctional (mulBorel (P.bidimensionOneCurrent u)
        (chartBorelWeight P.geometry.chart f)) α := by
  rw [D.current_nativeChartFunctional u hu hb f hf hfb P.geometry.chart,
    ← fullTestFunctional_restrict P.geometry.domainInChart,
    D.chartCurrent_restrict u hu hb f hf hfb P]

/-- In the unweighted case the same native global current recovers the
original Hermitian mixed current on every original full compact test. -/
theorem current_one_local_full_test (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (P : BackgroundPatch omega) (α : TestForm P.geometry.domain 2) :
    bidimensionOneChartFunctional (D.current u hu hb (fun _ => 1) measurable_const
      ⟨1, fun _ => by simp⟩) P.geometry.chart (TestFunction.monoCLM ℝ α) =
      fullTestFunctional (P.bidimensionOneCurrent u) α := by
  rw [D.current_local_full_test u hu hb (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩ P α]
  have hT := P.bidimensionOneCurrent_isPositive u hu hb
  have heq : mulBorel (P.bidimensionOneCurrent u) (chartBorelWeight P.geometry.chart (fun _ => 1)) =
      P.bidimensionOneCurrent u := by
    calc
      _ = mulBorel (P.bidimensionOneCurrent u) (fun _ => 1) :=
        mulBorel_congr hT (measurable_chartBorelWeight P.geometry.chart (fun _ => 1) measurable_const)
          (fun K _ _ => ⟨1, fun x _ => by
            by_cases hx : x ∈ P.geometry.chart.val.target <;> simp [chartBorelWeight, hx]⟩)
          measurable_const (fun K _ _ => ⟨1, fun _ _ => by simp⟩)
          (fun x hx => by rw [chartBorelWeight, indicator_of_mem (P.geometry.domain_le_target hx)])
      _ = _ := by rw [mulBorel_const hT 1, one_smul]
  rw [heq]

end MixedCurrentPartition
end SGPT.PSH.HermitianGlobalProducts
