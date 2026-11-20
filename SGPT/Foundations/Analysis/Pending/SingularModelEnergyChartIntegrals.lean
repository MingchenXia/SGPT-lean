import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicStripCharts
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-!
# Actual singular-model energy is a finite sum of coordinate NP integrals

The fibre-energy identification in Xia SGPT PDF0171, using the actual
global NP patch construction and the actual full E1 mixed energy formula.
The common smooth base correction cancels in the canonical signed gap,
including poles. A genuine finite subordinate chart partition is produced;
actual E1 mixed-gap integrability justifies its finite integral sum.
No bounded reference, fibre-identity certificate or affinity is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyChartIntegrals

open FirstPass FirstPass.PositiveClasses FirstPass.GlobalPotentialPatches
  RelativeEnergy RelativeDarvasDistance RelativePreceqClasses GlobalNonPluripolar
  GlobalSlotStokes FiniteGeodesicStripCharts MixedNonPluripolar
  SingularModelFiniteEnergyMixedCocycle

noncomputable section

/-- A common finite correction cancels in the actual canonical signed difference, at every finite or infinite pair. -/
theorem canonicalDiff_add_common (a b : EReal) (c : ℝ) :
    canonicalERealDiffToReal (a + (c : EReal)) (b + (c : EReal)) =
      canonicalERealDiffToReal a b := by
  cases a <;> cases b <;>
    simp [canonicalERealDiffToReal, poleModifiedERealDiffToReal,
      ← EReal.coe_add, ← EReal.coe_sub]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}

private def commonPotentialChart (J : SlotChart (fun _ : Fin n => θ) θ) :
    SlotChart (fun _ : Fin n => θ) θ where
  chart := J.chart
  domain := J.domain
  domain_le_target := J.domain_le_target
  potential := fun _ => J.kahler
  localPotential := fun _ => J.kahlerLocal
  kahler := J.kahler
  kahlerLocal := J.kahlerLocal

/-- The actual local NP truncation limit of the endpoint tuple, with the genuine same base correction in every slot. -/
def endpointChartMeasure (θ : ClosedRealOneOneForm n M) (φ u : M → EReal)
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (J : SlotChart (fun _ : Fin n => θ) θ) (k : Fin (n + 1)) : Measure (ComplexModel n) :=
  let P := (commonPotentialChart J).patch (endpointMixedPotential k u φ)
    (endpointMixedPotential_thetaPlurisubharmonic θ k u φ hu hφ)
  mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic

/-- Genuine NP patch transport identifies the actual corrected coordinate energy integral with the actual global endpoint integral. -/
theorem integral_chart_endpoint_eq_global
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (J : SlotChart (fun _ : Fin n => θ) θ) (k : Fin (n + 1))
    {f : M → ℝ} (hf : tsupport f ⊆ (J.source : Set M)) :
    (∫ y, chartRead J.chart f y * canonicalERealDiffToReal
      (chartFunction u J.chart y + (J.kahler y : EReal))
      (chartFunction φ J.chart y + (J.kahler y : EReal))
      ∂endpointChartMeasure θ φ u hφ hu J k) =
      ∫ x, f x * canonicalERealDiffToReal (u x) (φ x)
        ∂endpointMixedMeasure θ φ u hφ hu k := by
  let hp := endpointMixedPotential_thetaPlurisubharmonic θ k u φ hu hφ
  let P := (commonPotentialChart J).patch (endpointMixedPotential k u φ) hp
  let ν := mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic
  have hsupp : ∀ x ∉ (P.source : Set M), f x * canonicalERealDiffToReal (u x) (φ x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hf h)), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  change (∫ y, chartRead J.chart f y * canonicalERealDiffToReal
      (chartFunction u J.chart y + (J.kahler y : EReal))
      (chartFunction φ J.chart y + (J.kahler y : EReal)) ∂ν) =
    ∫ x, f x * canonicalERealDiffToReal (u x) (φ x)
      ∂(globalMixedMeasure (fun _ => θ) (endpointMixedPotential k u φ) hp).restrict
        (P.source : Set M)
  rw [globalMixedMeasure_restrict_patch hp P, patchMeasure]
  change (∫ y, chartRead J.chart f y * canonicalERealDiffToReal
      (chartFunction u J.chart y + (J.kahler y : EReal))
      (chartFunction φ J.chart y + (J.kahler y : EReal)) ∂ν) =
    ∫ x, f x * canonicalERealDiffToReal (u x) (φ x) ∂P.pushMeasure ν
  rw [Patch.integral_pushMeasure P (μ := ν)
    (mixedTruncationLimitMeasure_compl P.plurisubharmonic)]
  have hae : ∀ᵐ y ∂ν, y ∈ (P.domain : Set (ComplexModel n)) :=
    ae_iff.mpr (mixedTruncationLimitMeasure_compl P.plurisubharmonic)
  apply integral_congr_ae
  filter_upwards [hae] with y hy
  rw [canonicalDiff_add_common, chartRead_of_mem (J.domain_le_target hy)]
  rfl

omit [MeasurableSpace M] [BorelSpace M] in
/-- Actual common local-potential chart sources produce a genuine finite nonnegative subordinate chart-smooth partition. -/
theorem exists_finite_energy_chart_partition (θ : ClosedRealOneOneForm n M) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (fun _ : Fin n => θ) θ),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
      (∀ a, tsupport (χ a) ⊆ ((J a).source : Set M)) ∧
      (∀ a, HasCompactSupport (χ a)) ∧ ∀ x, ∑ a, χ a x = 1 := by
  exact ChartPartition.exists_chartSmooth_partitionOfUnity
    (n := n) (fun J : SlotChart (fun _ : Fin n => θ) θ => J.source)
    (SlotChart.exists_mem_source (fun _ : Fin n => θ) θ)

variable [ConnectedSpace M] {hφ : IsModelPotential θ φ}

/-- Actual E1 mixed-gap integrability and a genuine finite chart partition identify the coordinate NP sum with the defining finite real model energy. -/
theorem sum_sum_chart_endpoint_eq_mul_toReal_energy (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) {m : ℕ}
    (χ : Fin m → M → ℝ) (J : Fin m → SlotChart (fun _ : Fin n => θ) θ)
    (hχs : ∀ a, ChartSmooth (n := n) (χ a)) (hχ0 : ∀ a x, 0 ≤ χ a x)
    (hχJ : ∀ a, tsupport (χ a) ⊆ ((J a).source : Set M))
    (hχ1 : ∀ x, ∑ a, χ a x = 1) :
    (∑ k : Fin (n + 1), ∑ a : Fin m, ∫ y,
      chartRead (J a).chart (χ a) y * canonicalERealDiffToReal
        (chartFunction u (J a).chart y + ((J a).kahler y : EReal))
        (chartFunction φ (J a).chart y + ((J a).kahler y : EReal))
      ∂endpointChartMeasure θ φ u hφ.plurisubharmonic hu.1.plurisubharmonic (J a) k) =
      ((n : ℝ) + 1) * (energy θ φ hφ u).toReal := by
  classical
  have hφf : RelativeFiniteEnergyPreceq θ φ φ hφ :=
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩
  have hi (k : Fin (n + 1)) := integrable_endpoint_canonicalDiff_of_preceq omega hu hφf k
  have hχbound (a : Fin m) (x : M) : ‖χ a x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 a x), ← hχ1 x]
    exact Finset.single_le_sum (fun b _ => hχ0 b x) (Finset.mem_univ a)
  have hip (k : Fin (n + 1)) (a : Fin m) :
      Integrable (fun x => χ a x * canonicalERealDiffToReal (u x) (φ x))
        (endpointMixedMeasure θ φ u hφ.plurisubharmonic hu.1.plurisubharmonic k) :=
    (hi k).bdd_mul (ChartSmooth.continuous (hχs a)).measurable.aestronglyMeasurable
      (Eventually.of_forall (hχbound a))
  have hj (k : Fin (n + 1)) :
      (∑ a : Fin m, ∫ y, chartRead (J a).chart (χ a) y * canonicalERealDiffToReal
        (chartFunction u (J a).chart y + ((J a).kahler y : EReal))
        (chartFunction φ (J a).chart y + ((J a).kahler y : EReal))
        ∂endpointChartMeasure θ φ u hφ.plurisubharmonic hu.1.plurisubharmonic (J a) k) =
        ∫ x, canonicalERealDiffToReal (u x) (φ x)
          ∂endpointMixedMeasure θ φ u hφ.plurisubharmonic hu.1.plurisubharmonic k := by
    simp_rw [integral_chart_endpoint_eq_global hφ.plurisubharmonic hu.1.plurisubharmonic
      _ k (hχJ _)]
    rw [← integral_finsetSum _ (fun a _ => hip k a)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (∑ a : Fin m, χ a x * canonicalERealDiffToReal (u x) (φ x)) = _
      rw [← Finset.sum_mul, hχ1 x, one_mul]
  rw [Finset.sum_congr rfl (fun k _ => hj k),
    ← mul_toReal_energy_sub_eq_sum_endpoint_integrals omega hu hφf]
  have hEφ : energy θ φ hφ φ = 0 := by
    rw [SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega θ hφ
      ⟨hφ.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
      relativeEnergyOfMinimalType_self, EReal.coe_zero]
  rw [hEφ, EReal.toReal_zero, sub_zero]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyChartIntegrals
