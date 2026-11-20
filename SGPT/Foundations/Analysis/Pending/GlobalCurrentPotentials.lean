import SGPT.Foundations.Analysis.FirstPass.GlobalCurrentPotentials
import SGPT.Foundations.Analysis.FirstPass.QuasiPshChartL1
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import SGPT.Foundations.Analysis.Pending.LocalCurrents
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.DDCOverlap

/-!
# Globalization of ddᶜ of genuine quasi-PSH potentials

Chartwise L¹ is proved in the core, and holomorphic overlap compatibility of
the chart family is proved in `Pending.DDCOverlap`. A.e. finiteness uses the
quasi-PSH pole-set theorem and the chart Haar-nullity bridge. Extraction,
closedness and type `(1,1)` use the inverse-pairing identity, `d² = 0` and
commutation of distributional derivatives. Every declaration here depends only
on the standard axioms. No connectedness of chart targets, compactness of the
manifold, or canonical complex orientation of an arbitrary basis is assumed.
No local potentials of general currents or full positive cone are asserted.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials

open FirstPass SGPT.Foundations.Analysis.LocalCurrents

/-- On small connected balls in each chart, local nondegeneracy excludes the
identically minus-infinite PSH summand.  The core chartwise integrability theorem
gives L¹ for the canonical Lebesgue measure; uniqueness of additive Haar
measure transfers it to the measure normalized by the chosen basis. -/
theorem quasiPsh_chart_locallyIntegrable
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [mE : MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (_hn : 0 < n) (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    ChartLocallyIntegrable b u := by
  have hm : mE = WithLp.measurableSpace 2 (Fin n → ℂ) :=
    BorelSpace.measurable_eq.trans
      (@BorelSpace.measurable_eq (ComplexModel n) _
        (WithLp.measurableSpace 2 (Fin n → ℂ)) inferInstance).symm
  subst mE
  intro e
  rw [Measure.isAddLeftInvariant_eq_smul b.addHaar volume]
  intro z hz
  obtain ⟨K, hK, hInt⟩ := hu.locallyIntegrableOn_chart_toReal e z hz
  refine ⟨K, hK, ?_⟩
  simpa only [IntegrableOn, Measure.restrict_smul] using
    hInt.smul_measure_nnreal

/-- Finiteness in Haar-almost every chart point follows from the existing
Pending quasi-PSH pole-set theorem and the checked quasi-everywhere-to-a.e.
bridge. Neither chart connectedness nor countability of the atlas is assumed. -/
theorem quasiPsh_chart_ae_finite
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [mE : MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (_hn : 0 < n) (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M) :
    ∀ᵐ z ∂b.addHaar.restrict (chartTarget e),
      chartFunction u e z ≠ ⊤ ∧ chartFunction u e z ≠ ⊥ := by
  have hm : mE = WithLp.measurableSpace 2 (Fin n → ℂ) :=
    BorelSpace.measurable_eq.trans
      (@BorelSpace.measurable_eq (ComplexModel n) _
        (WithLp.measurableSpace 2 (Fin n → ℂ)) inferInstance).symm
  subst mE
  exact ((Pending.quasiPsh_finite_quasiEverywhere hu).ae_in_chart e b.addHaar).mono
    (fun _ hz => hz.symm)

/-- The actual related overlap tests have equal pairings with ddᶜu.
This is distributional covariance under the holomorphic transition, with the
same Haar normalization and real basis on both sides. The analytic hypotheses
are exactly chartwise L¹; quasi-PSH is used separately to obtain that hypothesis.
The proof transposes ddᶜ onto the test forms, identifies the transposed tests
through smooth potentials and holomorphic covariance, and changes variables. -/
theorem ddCCurrentFamily_overlap
    {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M]
    [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
    (hn : 0 < n) (u : M → EReal) (hu : ChartLocallyIntegrable b u)
    (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) (Module.finrank ℝ (ComplexModel n) - 2))
    (θ : TestForm (overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - 2))
    (h : OverlapTestRelated e f η θ) :
    restrictLocalCurrent (overlapSource_le e f) (ddCCurrentFamily b hn u hu e) η =
      restrictLocalCurrent (overlapTarget_le e f) (ddCCurrentFamily b hn u hu f) θ :=
  DDCOverlap.ddCCurrentFamily_overlap b hn u hu e f η θ h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

/-- A.e. finiteness ensures that taking the real density loses no potential values
a.e. on the chart target. -/
theorem quasiPsh_chart_ae_coe_toReal (hn : 0 < n) (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := n) u) (e : ComplexChart n M) :
    (fun z => ((chartFunction u e z).toReal : EReal))
      =ᵐ[b.addHaar.restrict (chartTarget e)] chartFunction u e :=
  (quasiPsh_chart_ae_finite b hn u hu e).mono (fun _ hz => EReal.coe_toReal hz.1 hz.2)

/-- A genuine global current. The constructor consumes named L¹ and overlap
obligations instead of asking the caller for the desired global compatibility. -/
def globalDDC (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    GlobalCurrent n M (degreeTwo hn) :=
  ⟨ddCCurrentFamily b hn u (quasiPsh_chart_locallyIntegrable b hn u hu),
    fun e f η θ h => ddCCurrentFamily_overlap b hn u
      (quasiPsh_chart_locallyIntegrable b hn u hu) e f η θ h⟩

@[simp] theorem globalDDC_inChart (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := n) u) (e : ComplexChart n M) :
    (globalDDC b hn u hu).inChart e =
      ddCCurrentFamily b hn u (quasiPsh_chart_locallyIntegrable b hn u hu) e := rfl

/-- The exact shuffle formula of the constructed global current. -/
theorem globalDDC_apply (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u)
    (e : ComplexChart n M)
    (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n) - 2)) :
    (globalDDC b hn u hu).inChart e η = distributionTestPairing
      (((chartDDC b u e (quasiPsh_chart_locallyIntegrable b hn u hu e)).domCoprod
        (testFormAlternating η)) (currentPairingBasis b (degreeTwo hn))) :=
  ddCCurrentFamily_apply b hn u _ e η

/-- Extraction uses precisely the inverse-pairing identity. -/
theorem globalDDC_coefficients (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := n) u) (e : ComplexChart n M) :
    (globalDDC b hn u hu).coefficients b e =
      chartDDC b u e (quasiPsh_chart_locallyIntegrable b hn u hu e) :=
  Pending.CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

/-- Closedness follows from the coefficient identity `d² = 0`. -/
theorem globalDDC_isClosed (u : M → EReal) (hu : IsGlobalQuasiPshPotential (n := n) u) :
    (globalDDC b hn u hu).IsClosed b := by
  intro e
  rw [globalDDC_coefficients]
  exact Pending.LocalCurrents.ddC_isClosed _

/-- Type `(1,1)` follows from commutation of distributional derivatives. -/
theorem globalDDC_isTypeOneOne (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := n) u) :
    (globalDDC b hn u hu).IsTypeOneOne b hn := by
  intro e
  rw [globalDDC_coefficients]
  exact Pending.LocalCurrents.ddC_isOneOne _

/-- Chartwise a.e.-equal genuine potentials determine the same global current. -/
theorem globalDDC_congr_ae {u w : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (hw : IsGlobalQuasiPshPotential (n := n) w)
    (huw : ∀ e, chartFunction u e =ᵐ[b.addHaar.restrict (chartTarget e)] chartFunction w e) :
    globalDDC b hn u hu = globalDDC b hn w hw := by
  apply Subtype.ext
  exact ddCCurrentFamily_congr_ae b hn _ _ huw

end SGPT.Foundations.Analysis.Pending.GlobalCurrentPotentials
