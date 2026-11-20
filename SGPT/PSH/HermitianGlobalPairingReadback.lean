import SGPT.PSH.HermitianMixedGlobalCurrent
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalDdcTransposition

/-!
# Full local density readback of the actual partitioned global derivative

The native compact second-transpose identity is evaluated using the actual
smooth partition that defines the global mixed current. Every chart test is
constructed from the original global smooth form. The full supported-patch
density theorem then reads the pairing as a finite sum of genuine integrals
against the original positive local mixed currents. No product overlap or
global/local identification is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalCurrentPullback LocalCurrentLebesgue
  ActualBorelWeightedPatchGlobalCurrent ActualGlobalBidimensionOneDdc
  ActualCompactGlobalPairingCalibration ActualCompactGlobalDdcTransposition
  SingularTopFormLocalization XiaoChartLocalization XiaoComplexDifferential
  BorelChartWeightedPatchCurrent WholeChartPotentialPatchTransition WeightedFullTestPullbackDensity
open Hermitian

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

private theorem test_cast_apply {n a b : ℕ} {U : Opens (ComplexModel n)}
    (h : a = b) (α : LocalCurrents.TestForm U a) (z : ComplexModel n) :
    (h ▸ α : LocalCurrents.TestForm U b) z = (h ▸ α z : RealForm n b) := by
  cases h
  rfl

private theorem form_cast_coeff {n a b : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (h : a = b) (α : SmoothRealForm n N a) (e : ComplexChart n N)
    (z : ComplexModel n) :
    (h ▸ α : SmoothRealForm n N b).coeff e z = (h ▸ α.coeff e z : RealForm n b) := by
  cases h
  rfl

private theorem cast_smul {n a b : ℕ} (h : a = b) (c : ℝ) (α : RealForm n a) :
    (h ▸ (c • α) : RealForm n b) = c • (h ▸ α : RealForm n b) := by
  cases h
  rfl

private theorem cast_zero {n a b : ℕ} (h : a = b) :
    (h ▸ (0 : RealForm n a) : RealForm n b) = 0 := by
  cases h
  rfl

private theorem clm_cast_apply {n a b : ℕ} {U : Opens (ComplexModel n)} (h : a = b)
    (F : LocalCurrents.TestForm U a →L[ℝ] ℝ)
    (G : LocalCurrents.TestForm U b →L[ℝ] ℝ) (hFG : HEq F G)
    (α : LocalCurrents.TestForm U b) : F (h.symm ▸ α) = G α := by
  cases h
  rw [eq_of_heq hFG]

private theorem inChart_sum {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    {k : CurrentDegree n} {ι : Type*} (s : Finset ι)
    (T : ι → GlobalCurrent n N k) (e : ComplexChart n N) :
    (∑ i ∈ s, T i).inChart e = ∑ i ∈ s, (T i).inChart e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, GlobalCurrent.inChart_add, ih]

namespace MixedCurrentPartition

variable {omega : Background (m + 1) M}

/-- The actual full compact test of the smooth global second differential,
localized with the original partition weight. -/
def localizedDdcTest (D : MixedCurrentPartition omega) (β : SmoothRealForm (m + 1) M 0)
    (j : Fin D.count) : LocalCurrents.TestForm (chartTarget (D.patch j).geometry.chart) 2 :=
  localizedTensorTest (D.patch j).geometry.chart (D.weight j) (D.smooth j) (XiaoComplexDifferential.ddc β)
    (isClosed_tsupport _).isCompact (fun _ hx => (D.supported j hx).1)

omit [MeasurableSpace M] [BorelSpace M] in
theorem localizedDdcTest_apply (D : MixedCurrentPartition omega)
    (β : SmoothRealForm (m + 1) M 0) (j : Fin D.count) (z : ComplexModel (m + 1)) :
    D.localizedDdcTest β j z = (D.patch j).geometry.chart.val.target.indicator
      (fun y => D.weight j ((D.patch j).geometry.chart.val.symm y) •
        (XiaoComplexDifferential.ddc β).coeff (D.patch j).geometry.chart y) z := rfl

/-- The native derivative of the actual partitioned mixed current reads as
the original full supported local tests, retaining every two-form component. -/
theorem pairing_ddc_eq_sum_fullTests (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (β : SmoothRealForm (m + 1) M 0) :
    pairingLM (D.ddc u hu hb f hf hfb) ((top_complement m).symm ▸ β) =
      ∑ j, ∑ i, chartBorelWeightedFullTestFunctional (D.patch j).geometry.chart
        (D.patch i).geometry.zeroPotentialPatch
        ((D.patch i).bidimensionOneCurrent_isPositive u hu hb)
        (D.weight i) (D.smooth i) (D.supported i) (D.nonneg i) f hf hfb
        (D.localizedDdcTest β j) := by
  classical
  rw [ddc, pairing_globalDdc]
  let η (j : Fin D.count) : LocalCurrents.TestForm (chartTarget (D.patch j).geometry.chart)
      (Module.finrank ℝ (ComplexModel (m + 1)) - (borelBidimensionOneDegree m).val) :=
    (bidimensionOne_complement m).symm ▸ D.localizedDdcTest β j
  have hη (j : Fin D.count) (z : ComplexModel (m + 1)) :
      η j z = (D.patch j).geometry.chart.val.target.indicator
        (fun y => D.weight j ((D.patch j).geometry.chart.val.symm y) •
          (((bidimensionOne_complement m).symm ▸ (XiaoComplexDifferential.ddc β : SmoothRealForm (m + 1) M 2) :
            SmoothRealForm (m + 1) M _).coeff (D.patch j).geometry.chart y)) z := by
    rw [test_cast_apply, localizedDdcTest_apply]
    by_cases hz : z ∈ (D.patch j).geometry.chart.val.target
    · rw [indicator_of_mem hz, indicator_of_mem hz, form_cast_coeff, cast_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, cast_zero]
  rw [pairing_eq_sum (D.current u hu hb f hf hfb) _ D.count
    (fun j => (D.patch j).geometry.chart) D.weight D.smooth
    (fun j => (isClosed_tsupport _).isCompact)
    (fun j x hx => (D.supported j hx).1) D.sum_one η hη]
  apply Finset.sum_congr rfl
  intro j _
  rw [current, inChart_sum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact clm_cast_apply (bidimensionOne_complement m) _ _
    (weightedPatchCurrent_inChart (D.patch j).geometry.chart (D.patch i).geometry
      ((D.patch i).bidimensionOneCurrent_isPositive u hu hb)
      (D.weight i) (D.smooth i) (D.supported i) (D.nonneg i) f hf hfb)
    (D.localizedDdcTest β j)

/-- The literal overlap density of the original local positive mixed
current, the original Borel weight, and the manufactured full `ddc` test. -/
def localizedDdcDensity (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (β : SmoothRealForm (m + 1) M 0)
    (j i : Fin D.count) (y : ComplexModel (m + 1)) : ℝ :=
  (f ((D.patch i).geometry.chart.val.symm y) *
      D.weight i ((D.patch i).geometry.chart.val.symm y)) *
    densityForm ((D.patch i).bidimensionOneCurrent_isPositive u hu hb) y
      (pullSpan 1 (fderiv ℂ (patchToChart (D.patch j).geometry.chart
        (D.patch i).geometry.zeroPotentialPatch) y)
        (oneOneProjection (D.localizedDdcTest β j
          (patchToChart (D.patch j).geometry.chart (D.patch i).geometry.zeroPotentialPatch y))))

/-- Every actual overlap density in the readback is integrable against its
original local trace measure; no finite-measure premise is supplied. -/
theorem localizedDdcDensity_integrableOn (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (β : SmoothRealForm (m + 1) M 0) (j i : Fin D.count) :
    IntegrableOn (D.localizedDdcDensity u hu hb f β j i)
      (patchOverlapDomain (D.patch j).geometry.chart (D.patch i).geometry.zeroPotentialPatch)
      ((D.patch i).bidimensionOneCurrent_isPositive u hu hb).traceMeasure :=
  (chartBorelWeightedFullTestFunctional_density (D.patch j).geometry.chart
    (D.patch i).geometry.zeroPotentialPatch
    ((D.patch i).bidimensionOneCurrent_isPositive u hu hb)
    (D.weight i) (D.smooth i) (D.supported i) (D.nonneg i) f hf hfb
    (D.localizedDdcTest β j)).1

/-- Exact finite density-integral readback of the genuine global second
derivative. The conclusion uses only actual native overlap domains and
original local trace measures, without product overlap assumptions. -/
theorem pairing_ddc_eq_sum_density (D : MixedCurrentPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (f : M → ℝ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, |f x| ≤ C)
    (β : SmoothRealForm (m + 1) M 0) :
    pairingLM (D.ddc u hu hb f hf hfb) ((top_complement m).symm ▸ β) =
      ∑ j, ∑ i, ∫ y in patchOverlapDomain (D.patch j).geometry.chart
          (D.patch i).geometry.zeroPotentialPatch,
        D.localizedDdcDensity u hu hb f β j i y
          ∂((D.patch i).bidimensionOneCurrent_isPositive u hu hb).traceMeasure := by
  rw [pairing_ddc_eq_sum_fullTests]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact (chartBorelWeightedFullTestFunctional_density (D.patch j).geometry.chart
    (D.patch i).geometry.zeroPotentialPatch
    ((D.patch i).bidimensionOneCurrent_isPositive u hu hb)
    (D.weight i) (D.smooth i) (D.supported i) (D.nonneg i) f hf hfb
    (D.localizedDdcTest β j)).2

end MixedCurrentPartition

end SGPT.PSH.HermitianGlobalProducts
