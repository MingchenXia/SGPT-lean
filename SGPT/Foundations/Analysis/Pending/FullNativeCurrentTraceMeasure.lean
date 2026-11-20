import SGPT.Foundations.Analysis.Pending.FullNativeGlobalPairingLimits
import SGPT.Foundations.Analysis.Pending.CurrentTraceMeasure

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions
namespace SGPT.Foundations.Analysis.Pending.FullNativeCurrentTraceMeasure
open FirstPass FirstPass.PositiveClasses StronglyPositiveForms ConstantFormProducts
  ProductTestForms PositiveProductCurrents CanonicalCurrentFrame GlobalCurrents
  ChartPartition ActualWeightedGlobalFormChartTests ActualCompactGlobalPairingCalibration

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Equality transport of the original alternating degree, as an actual LM. -/
def castSmoothDegree {a b : ℕ} (h : a = b) :
    SmoothRealForm n M a →ₗ[ℝ] SmoothRealForm n M b := by
  subst b
  exact LinearMap.id

private theorem coeff_castSmoothDegree {a b : ℕ} (h : a = b)
    (A : SmoothRealForm n M a) (e : ComplexChart n M) (z : ComplexModel n) :
    (castSmoothDegree h A).coeff e z = castForm h (A.coeff e z) := by
  subst b
  rfl

variable [CompactSpace M] {k : CurrentDegree n} {q : ℕ}

/-- Every actual global strongly positive test is read nonnegatively by a
full native positive current; its nonnegative chart partition is internal. -/
theorem pairing_nonneg_of_full_positive (h : Module.finrank ℝ (ComplexModel n) - k.val = 2 * q)
    (S : GlobalCurrent n M k)
    (hS : ∀ (e : ComplexChart n M)
      (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val)),
      (∀ z, z ∈ e.val.target → castForm h (η z) ∈ spCone q) → 0 ≤ S.inChart e η)
    (G : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))
    (hG : ∀ (e : ComplexChart n M) z, z ∈ e.val.target →
      castForm h (G.coeff e z) ∈ spCone q) : 0 ≤ pairingLM S G := by
  classical
  obtain ⟨r, χ, idx, hχ, hχnn, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n)
      (fun x : M => (⟨(complexChartAt (n := n) x).val.source,
        (complexChartAt (n := n) x).val.open_source⟩ : Opens M))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e : Fin r → ComplexChart n M := fun j => complexChartAt (idx j)
  have htests (j : Fin r) :
      ∃ η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget (e j))
          (Module.finrank ℝ (ComplexModel n) - k.val),
        ∀ z, η z = (e j).val.target.indicator
          (fun y => χ j ((e j).val.symm y) • G.coeff (e j) y) z := by
    obtain ⟨η, hη, -⟩ := exists_testForm (e j) G (χ j) (hχ j) (hχc j) (hχs j)
    exact ⟨η, hη⟩
  choose η hη using htests
  rw [pairing_eq_sum S G r e χ hχ hχc hχs hχ1 η hη]
  apply Finset.sum_nonneg
  intro j _
  apply hS (e j) (η j)
  intro z hz
  rw [hη j z, indicator_of_mem hz, map_smul]
  exact smul_mem_spCone (hG (e j) z hz) (hχnn j _)

variable [MeasurableSpace M] [BorelSpace M]

/-- Full native positivity itself supplies the finite regular trace, whose
scalar reading is the exact original full native pairing. -/
theorem exists_finite_regular_trace
    (h : Module.finrank ℝ (ComplexModel n) - k.val = 2 * q)
    (w : KahlerBackground n M) (S : GlobalCurrent n M k)
    (hS : ∀ (e : ComplexChart n M)
      (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e)
        (Module.finrank ℝ (ComplexModel n) - k.val)),
      (∀ z, z ∈ e.val.target → castForm h (η z) ∈ spCone q) → 0 ≤ S.inChart e η) :
    ∃ μ : Measure M, μ.Regular ∧ IsFiniteMeasure μ ∧
      (∀ (g : M → ℝ) (hg : ChartSmooth (n := n) g),
        ∫ x, g x ∂μ = pairingLM S
          (castSmoothDegree h.symm (smulFun g hg (formPow w.form.val q)))) ∧
      μ.real univ = pairingLM S (castSmoothDegree h.symm (formPow w.form.val q)) := by
  let P : ProductCurrent n M q := (pairingLM S).comp
    ((castSmoothDegree h.symm).comp (testSpace n M q).subtype)
  have hP : IsPositive P := by
    intro φ hφ
    change 0 ≤ pairingLM S (castSmoothDegree h.symm (φ : SmoothRealForm n M (2 * q)))
    apply pairing_nonneg_of_full_positive h S hS
    intro e z hz
    rw [coeff_castSmoothDegree, castForm_castForm, castForm_self]
    exact hφ e z hz
  let μ := CurrentTraceMeasure.traceMeasure w P hP
  refine ⟨μ, inferInstance, inferInstance, ?_, ?_⟩
  · intro g hg
    exact CurrentTraceMeasure.integral_traceMeasure_chartSmooth w P hP g hg
  · exact CurrentTraceMeasure.traceMeasure_real_univ w P hP

end SGPT.Foundations.Analysis.Pending.FullNativeCurrentTraceMeasure
