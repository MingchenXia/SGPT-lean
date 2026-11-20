import SGPT.NPP.CompactFibreGeometry
import SGPT.NPP.NonPluripolarCurrent2Opens
import SGPT.NPP.CompactFibreLocalFubini
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import Lean.Elab.Command

/-! Genuine compact fibre slicing, original source proof fragments under proper canonical module identity. -/

section CompactFibreCanonicalFragment014

/-! The SAME original geometric-current product and its existing global
smooth wedge measure read as the proved actual original local NP measures. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending ProductComplexManifold
open LocalProductCurrents LocalBedfordTaylorLocality
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z] [CompactSpace Z]

def originalJointCurrent (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    (θ : ClosedRealOneOneForm n X) (γ : ClosedRealOneOneForm m Z)
    (V : Fin n → X × Z → EReal) (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i)) :
    PositiveCurrent (n + m) (X × Z) m :=
  originalThetaProduct (prodKahlerBackground omegaX omegaZ) (Nat.add_comm m n)
    (fun _ => prodForm θ γ) V hV

theorem originalJointCurrent_local_reading (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (J : OriginalProductPotentialChart θ γ) :
    IsWellDefinedOn (Nat.add_comm m n) J.domain
        (originalProductCorrectedTuple J.first J.second J.a J.b V) ∧
      restrict J.domain_le_target ((originalJointCurrent omegaX omegaZ θ γ V hV).inChart J.chart) =
        SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct (Nat.add_comm m n) J.domain
          (originalProductCorrectedTuple J.first J.second J.a J.b V) := by
  let ρ := fun q => J.a (coordinateMap Prod.fst J.chart J.first q) +
    J.b (coordinateMap Prod.snd J.chart J.second q)
  have hρ := isSmoothLocalPotential_product_chart J.firstPotential J.secondPotential
  have hc0 := originalThetaProduct_local_reading (prodKahlerBackground omegaX omegaZ)
    (Nat.add_comm m n) (fun _ => prodForm θ γ) V hV J.chart J.domain_le_target (fun _ => ρ) (fun _ => hρ)
  have hfst {q : ComplexModel (n + m)} (hq : q ∈ J.domain) :
      coordinateMap Prod.fst J.chart J.first q = ProductMixedMeasure.projFst n m q := by
    change J.first.val ((prodChart J.first.val J.second.val).symm q).1 = _
    rw [prodChart_symm_apply, ← ProductMixedMeasure.projFst_apply]
    exact J.first.val.right_inv (J.firstPotential.2.1 hq.1)
  have hsnd {q : ComplexModel (n + m)} (hq : q ∈ J.domain) :
      coordinateMap Prod.snd J.chart J.second q = ProductMixedMeasure.projSnd n m q := by
    change J.second.val ((prodChart J.first.val J.second.val).symm q).2 = _
    rw [prodChart_symm_apply, ← ProductMixedMeasure.projSnd_apply]
    exact J.second.val.right_inv (J.secondPotential.2.1 hq.2)
  have hc := nonPluripolarProduct_congr (Nat.add_comm m n) (U := J.domain)
    (φ := fun i q => chartFunction (V i) J.chart q + (ρ q : EReal))
    (φ' := originalProductCorrectedTuple J.first J.second J.a J.b V)
    (fun i q hq => by
      dsimp only [ρ, chartFunction, originalProductCorrectedTuple]
      rw [hfst hq, hsnd hq]
      rfl)
  exact ⟨hc.1.mp hc0.1, hc0.2.trans hc.2⟩

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Z] [BorelSpace Z]

def originalJointWedgeMeasure (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    (θ : ClosedRealOneOneForm n X) (γ : ClosedRealOneOneForm m Z)
    (V : Fin n → X × Z → EReal) (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i)) :
    Measure (X × Z) :=
  wedgeMeasureOn (originalJointCurrent omegaX omegaZ θ γ V hV)
    (originalBaseWedgeForm (X := X) omegaZ) isCompact_univ

theorem originalJointWedgeMeasure_restrict_product
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (J : OriginalProductPotentialChart θ γ) :
    (originalJointWedgeMeasure omegaX omegaZ θ γ V hV).restrict J.source =
      (Measure.withDensity (MixedNonPluripolar.mixedTruncationLimitMeasure J.domain
        (augmentedFibreTuple (originalProductCorrectedTuple J.first J.second J.a J.b V))
        (plurisubharmonicOn_augmentedFibreTuple
          (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i))))
        (fun q => ENNReal.ofReal
          (basePowerDensity J.Q J.D (omegaZ.form.val.coeff J.second) q))).map (chartInv J.chart) := by
  have hsource : J.source = chartPatchSource J.chart J.domain := by
    ext p
    constructor
    · intro hp
      exact ⟨J.source_subset hp, J.map_source hp⟩
    · intro hp
      have hm := J.map_target hp.2
      rwa [J.chart.val.left_inv hp.1] at hm
  have hc := originalJointCurrent_local_reading omegaX omegaZ hV J
  let U := originalProductCorrectedTuple J.first J.second J.a J.b V
  have hU (i : Fin n) : PlurisubharmonicOn (U i) J.domain :=
    plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)
  have hP := isPositive_nonPluripolarProduct (Nat.add_comm m n) hU hc.1
  have hbase : wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
        (Nat.add_comm m n) J.domain U) ((originalBaseWedgeForm (X := X) omegaZ).coeff J.chart) =
      wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
        (Nat.add_comm m n) J.domain U) (baseTwoFormPullback (omegaZ.form.val.coeff J.second)) := by
    rw [wedgePowerMeasure, dif_pos hP, wedgePowerMeasure, dif_pos hP]
    apply withDensity_congr_ae
    filter_upwards [ae_iff.mpr hP.traceMeasure_compl] with q hq
    rw [originalBaseWedgeForm_coeff omegaZ J hq]
  have ha : ContDiffOn ℝ ∞ (omegaZ.form.val.coeff J.second) J.D :=
    (omegaZ.form.val.smooth J.second).mono J.secondPotential.2.1
  have hap z (hz : z ∈ J.D) : StronglyPositiveForms.IsSemipositiveOneOne (omegaZ.form.val.coeff J.second z) :=
    ⟨(omegaZ.isKahler.1 J.second z (J.secondPotential.2.1 hz)).1,
      omegaZ.isSemipositive J.second z (J.secondPotential.2.1 hz)⟩
  change (wedgeMeasureOn (originalJointCurrent omegaX omegaZ θ γ V hV)
    (originalBaseWedgeForm (X := X) omegaZ) isCompact_univ).restrict J.source = _
  rw [hsource, global_wedgeMeasure_restrict_chart_patch _ _ _ J.domain_le_target,
    hc.2, hbase]
  apply congrArg (Measure.map (chartInv J.chart))
  exact original_np_wedgePowerMeasure_base_eq_npLimit hU hc.1 ha hap

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment014

section CompactFibreCanonicalFragment015

/-! The SAME actual original GLOBAL fibre mixed measure reads the actual
coordinate fibre integral of each genuine product-chart partition term. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar MixedNonPluripolar
open FiniteGeodesicStripCharts LocalProductCurrents
open SGPT.NPP.FibreSlicing
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def originalFibreMixedMeasure (θ : ClosedRealOneOneForm n X) (V : Fin n → X × Z → EReal)
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z))) (z : Z) : Measure X :=
  globalMixedMeasure (fun _ => θ) (fun i x => V i (x, z)) (fun i => (hVF z i).1)

theorem original_fibre_integral_eq_global
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z)))
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z))) (G : X × Z → ℝ)
    {z : ComplexModel m} (hz : z ∈ J.D) :
    (∫ x, productChartTest J hχ hχc hχJ (fibreMapM n m z x) *
      G (chartInv J.chart (fibreMapM n m z x))
      ∂mixedTruncationLimitMeasure (fibreOpensM J.domain z)
        (originalFibrePotentialsM (originalProductCorrectedTuple J.first J.second J.a J.b V) z)
        (plurisubharmonicOn_originalFibrePotentialsM
          (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)) z)) =
      ∫ x, χ (x, J.second.val.symm z) * G (x, J.second.val.symm z)
        ∂originalFibreMixedMeasure θ V hVF (J.second.val.symm z) := by
  let hv := fun i => (hVF (J.second.val.symm z) i).1
  let P := originalFibrePatch J.firstPotential (fun i x => V i (x, J.second.val.symm z)) hv
  let ν := mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic
  let F := fun x => χ (x, J.second.val.symm z) * G (x, J.second.val.symm z)
  have hcoord := original_fibre_npLimit_eq_original_patch J.firstPotential J.secondPotential hV hz hv
  have hzero (x : X) (hx : x ∉ P.source) : F x = 0 := by
    have hc : χ (x, J.second.val.symm z) = 0 := by
      by_contra hn
      have hp := hχJ (subset_tsupport χ (Function.mem_support.mpr hn))
      exact hx hp.1
    exact by dsimp only [F]; rw [hc, zero_mul]
  refine (congrArg (fun μ : Measure (ComplexModel n) =>
    ∫ x, productChartTest J hχ hχc hχJ (fibreMapM n m z x) *
      G (chartInv J.chart (fibreMapM n m z x)) ∂μ) hcoord).trans ?_
  change (∫ x, productChartTest J hχ hχc hχJ (fibreMapM n m z x) *
      G (chartInv J.chart (fibreMapM n m z x)) ∂ν) =
    ∫ x, F x ∂globalMixedMeasure (fun _ => θ) (fun i x => V i (x, J.second.val.symm z)) hv
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    globalMixedMeasure_restrict_patch hv P, patchMeasure]
  have hpush : (∫ x, F x ∂P.pushMeasure ν) = ∫ x, F (P.chart.val.symm x) ∂ν :=
    P.integral_pushMeasure (mixedTruncationLimitMeasure_compl P.plurisubharmonic) F
  apply Eq.trans ?_ hpush.symm
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (mixedTruncationLimitMeasure_compl P.plurisubharmonic)] with x hx
  have hxQ : x ∈ J.Q := hx
  have hq : fibreMapM n m z x ∈ J.domain := by
    change fibreMapM n m z x ∈ prodOpens J.Q J.D
    simp only [mem_prodOpens, projFst_fibreMapM, projSnd_fibreMapM]
    exact ⟨hxQ, hz⟩
  have hsymm : J.chart.val.symm (fibreMapM n m z x) =
      (J.first.val.symm x, J.second.val.symm z) := by
    change (prodChart J.first.val J.second.val).symm (fibreMapM n m z x) = _
    rw [prodChart_symm_apply]
    simp only [fibreMapM, ContinuousLinearEquiv.symm_apply_apply]
  change chartRead J.chart χ (fibreMapM n m z x) * G (chartInv J.chart (fibreMapM n m z x)) =
    F (J.first.val.symm x)
  rw [chartRead_of_mem (J.domain_le_target hq), chartInv_of_mem (J.domain_le_target hq), hsymm]

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment015

section CompactFibreCanonicalFragment017

/-! The actual outer global fibre integral is read in the original base chart,
without assuming the output function measurable or integrable. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar MixedNonPluripolar
open FiniteGeodesicStripCharts LocalProductCurrents TopDegreeDensity
open IntegrationCurrent DiagonalMass SmoothMixedMeasureDensity StronglyPositiveForms ProductTestForms
open SGPT.NPP.FibreSlicing
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

theorem original_outer_fibre_chart_pairing
    (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z)))
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z))) (G : X × Z → ℝ) :
    (Integrable (fun z => ∫ x, χ (x, z) * G (x, z) ∂originalFibreMixedMeasure θ V hVF z)
      (kahlerVolume omegaZ) ↔
    Integrable (fun z => topDensity (formPower (omegaZ.form.val.coeff J.second z) m) *
      ∫ x, productChartTest J hχ hχc hχJ (fibreMapM n m z x) *
        G (chartInv J.chart (fibreMapM n m z x))
        ∂mixedTruncationLimitMeasure (fibreOpensM J.domain z)
          (originalFibrePotentialsM (originalProductCorrectedTuple J.first J.second J.a J.b V) z)
          (plurisubharmonicOn_originalFibrePotentialsM
            (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)) z))) ∧
    (∫ z, ∫ x, χ (x, z) * G (x, z) ∂originalFibreMixedMeasure θ V hVF z
      ∂kahlerVolume omegaZ) =
    ∫ z, topDensity (formPower (omegaZ.form.val.coeff J.second z) m) *
      ∫ x, productChartTest J hχ hχc hχJ (fibreMapM n m z x) *
        G (chartInv J.chart (fibreMapM n m z x))
        ∂mixedTruncationLimitMeasure (fibreOpensM J.domain z)
          (originalFibrePotentialsM (originalProductCorrectedTuple J.first J.second J.a J.b V) z)
          (plurisubharmonicOn_originalFibrePotentialsM
            (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)) z) := by
  let φ := productChartTest J hχ hχc hχJ
  let I := fun z => ∫ x, φ (fibreMapM n m z x) * G (chartInv J.chart (fibreMapM n m z x))
    ∂mixedTruncationLimitMeasure (fibreOpensM J.domain z)
      (originalFibrePotentialsM (originalProductCorrectedTuple J.first J.second J.a J.b V) z)
      (plurisubharmonicOn_originalFibrePotentialsM
        (fun i => plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)) z)
  let F := fun z => ∫ x, χ (x, z) * G (x, z) ∂originalFibreMixedMeasure θ V hVF z
  let d := fun z => topDensity (formPower (omegaZ.form.val.coeff J.second z) m)
  have hI0 (z : ComplexModel m) (hz : z ∉ J.D) : I z = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      have hφ0 : φ (fibreMapM n m z x) = 0 := by
        by_contra hn
        have hq := φ.tsupport_subset (subset_tsupport φ (Function.mem_support.mpr hn))
        have hd : ProductMixedMeasure.projSnd n m (fibreMapM n m z x) ∈ J.D := hq.2
        rw [projSnd_fibreMapM] at hd
        exact hz hd
      change φ (fibreMapM n m z x) * G (chartInv J.chart (fibreMapM n m z x)) = 0
      rw [hφ0, zero_mul]
  have hF0 (z : Z) (hz : z ∉ J.second.val.source) : F z = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      have hc : χ (x, z) = 0 := by
        by_contra hn
        exact hz (hχJ (subset_tsupport χ (Function.mem_support.mpr hn))).2.1
      change χ (x, z) * G (x, z) = 0
      rw [hc, zero_mul]
  have hcoord (z : ComplexModel m) (hz : z ∈ J.second.val.target) : F (J.second.val.symm z) = I z := by
    by_cases hzD : z ∈ J.D
    · exact (original_fibre_integral_eq_global hV hVF J hχ hχc hχJ G hzD).symm
    · rw [hI0 z hzD]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun x => by
        have hc : χ (x, J.second.val.symm z) = 0 := by
          by_contra hn
          have hd := (hχJ (subset_tsupport χ (Function.mem_support.mpr hn))).2.2
          change J.second.val (J.second.val.symm z) ∈ J.D at hd
          rw [J.second.val.right_inv hz] at hd
          exact hzD hd
        change χ (x, J.second.val.symm z) * G (x, J.second.val.symm z) = 0
        rw [hc, zero_mul]
  have hpair := kahlerVolume_chart_pairing omegaZ J.second F hF0
  simp only [formPow_coeff] at hpair
  have hweight : (fun z => d z * F (J.second.val.symm z)) =ᵐ[volume.restrict J.second.val.target]
      (fun z => d z * I z) := by
    filter_upwards [ae_restrict_mem J.second.val.open_target.measurableSet] with z hz
    rw [hcoord z hz]
  have hout0 (z : ComplexModel m) (hz : z ∉ J.second.val.target) : d z * I z = 0 := by
    rw [hI0 z (fun hzD => hz (J.secondPotential.2.1 hzD)), mul_zero]
  have hind : J.second.val.target.indicator (fun z => d z * I z) = (fun z => d z * I z) := by
    funext z
    by_cases hz : z ∈ J.second.val.target
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, hout0 z hz]
  have hint : IntegrableOn (fun z => d z * F (J.second.val.symm z)) J.second.val.target volume ↔
      Integrable (fun z => d z * I z) := by
    refine (integrable_congr hweight).trans ?_
    change IntegrableOn (fun z => d z * I z) J.second.val.target volume ↔
      Integrable (fun z => d z * I z) volume
    rw [← integrable_indicator_iff J.second.val.open_target.measurableSet, hind]
  refine ⟨hpair.1.trans hint, ?_⟩
  exact hpair.2.trans ((integral_congr_ae hweight).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero hout0))

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment017

section CompactFibreCanonicalFragment023

/-! Literal Fubini for each genuine original product-chart partition term.
The current, both original measures and both integrability conclusions are produced. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar MixedNonPluripolar
open FiniteGeodesicStripCharts LocalProductCurrents TopDegreeDensity
open IntegrationCurrent StronglyPositiveForms ProductTestForms
open SGPT.NPP.FibreSlicing SGPT.NPP.NonPluripolarCurrent
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

theorem original_joint_partition_chart_pairing
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z)))
    {G : X × Z → ℝ} (hG : Measurable G) :
    (Integrable (fun p => χ p * G p) (originalJointWedgeMeasure omegaX omegaZ θ γ V hV) ↔
      Integrable (fun q => productChartTest J hχ hχc hχJ q * G (chartInv J.chart q))
        (wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
          (Nat.add_comm m n) J.domain
          (originalProductCorrectedTuple J.first J.second J.a J.b V))
          (baseTwoFormPullback (omegaZ.form.val.coeff J.second)))) ∧
    (∫ p, χ p * G p ∂originalJointWedgeMeasure omegaX omegaZ θ γ V hV) =
      ∫ q, productChartTest J hχ hχc hχJ q * G (chartInv J.chart q)
        ∂wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
          (Nat.add_comm m n) J.domain
          (originalProductCorrectedTuple J.first J.second J.a J.b V))
          (baseTwoFormPullback (omegaZ.form.val.coeff J.second)) := by
  let U := originalProductCorrectedTuple J.first J.second J.a J.b V
  let μ := originalJointWedgeMeasure omegaX omegaZ θ γ V hV
  let ν := wedgePowerMeasure (SGPT.NPP.NonPluripolarCurrent.nonPluripolarProduct
    (Nat.add_comm m n) J.domain U) (baseTwoFormPullback (omegaZ.form.val.coeff J.second))
  let F := fun p => χ p * G p
  have hc := originalJointCurrent_local_reading omegaX omegaZ hV J
  have hU (i : Fin n) : PlurisubharmonicOn (U i) J.domain :=
    plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)
  have ha : ContDiffOn ℝ ∞ (omegaZ.form.val.coeff J.second) J.D :=
    (omegaZ.form.val.smooth J.second).mono J.secondPotential.2.1
  have hap z (hz : z ∈ J.D) : IsSemipositiveOneOne (omegaZ.form.val.coeff J.second z) :=
    ⟨(omegaZ.isKahler.1 J.second z (J.secondPotential.2.1 hz)).1,
      omegaZ.isSemipositive J.second z (J.secondPotential.2.1 hz)⟩
  have hμ : μ.restrict J.source = ν.map (chartInv J.chart) := by
    exact (originalJointWedgeMeasure_restrict_product omegaX omegaZ hV J).trans
      (congrArg (Measure.map (chartInv J.chart))
        (original_np_wedgePowerMeasure_base_eq_npLimit hU hc.1 ha hap).symm)
  have hP := isPositive_nonPluripolarProduct (Nat.add_comm m n) hU hc.1
  have hν : ν (J.domain : Set (ComplexModel (n + m)))ᶜ = 0 := by
    dsimp only [ν]
    rw [wedgePowerMeasure, dif_pos hP]
    exact withDensity_absolutelyContinuous _ _ hP.traceMeasure_compl
  have hF : Measurable F := (GlobalSlotStokes.ChartSmooth.continuous hχ).measurable.mul hG
  have hF0 (p : X × Z) (hp : p ∉ J.source) : F p = 0 := by
    have hχ0 : χ p = 0 := by
      by_contra hn
      exact hp (hχJ (subset_tsupport χ (Function.mem_support.mpr hn)))
    exact by dsimp only [F]; rw [hχ0, zero_mul]
  have hind : (J.source : Set (X × Z)).indicator F = F := by
    funext p
    by_cases hp : p ∈ J.source
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp, hF0 p hp]
  have hint : Integrable F μ ↔ Integrable F (ν.map (chartInv J.chart)) := by
    rw [← hμ]
    change Integrable F μ ↔ IntegrableOn F J.source μ
    rw [← integrable_indicator_iff J.source.isOpen.measurableSet, hind]
  have hread : (fun q => F (chartInv J.chart q)) =ᵐ[ν]
      (fun q => productChartTest J hχ hχc hχJ q * G (chartInv J.chart q)) := by
    filter_upwards [ae_iff.mpr hν] with q hq
    change χ (chartInv J.chart q) * G (chartInv J.chart q) =
      chartRead J.chart χ q * G (chartInv J.chart q)
    rw [chartInv_of_mem (J.domain_le_target hq), chartRead_of_mem (J.domain_le_target hq)]
  refine ⟨?_, ?_⟩
  · exact hint.trans ((integrable_map_measure hF.aestronglyMeasurable
      (measurable_chartInv J.chart).aemeasurable).trans (integrable_congr hread))
  · calc
      _ = ∫ p in J.source, F p ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hF0).symm
      _ = ∫ p, F p ∂ν.map (chartInv J.chart) := by rw [hμ]
      _ = ∫ q, F (chartInv J.chart q) ∂ν :=
        integral_map (measurable_chartInv J.chart).aemeasurable hF.aestronglyMeasurable
      _ = _ := integral_congr_ae hread

theorem original_product_partition_term_fubini
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z)))
    (J : OriginalProductPotentialChart θ γ) {χ : X × Z → ℝ}
    (hχ : ChartSmooth (n := n + m) χ) (hχc : IsCompact (tsupport χ))
    (hχJ : tsupport χ ⊆ (J.source : Set (X × Z))) (hχ0 : ∀ p, 0 ≤ χ p)
    {G : X × Z → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ p, ‖G p‖ ≤ C) :
    Integrable (fun p => χ p * G p) (originalJointWedgeMeasure omegaX omegaZ θ γ V hV) ∧
    Integrable (fun z => ∫ x, χ (x, z) * G (x, z) ∂originalFibreMixedMeasure θ V hVF z)
      (kahlerVolume omegaZ) ∧
    (∫ p, χ p * G p ∂originalJointWedgeMeasure omegaX omegaZ θ γ V hV) =
      ∫ z, ∫ x, χ (x, z) * G (x, z) ∂originalFibreMixedMeasure θ V hVF z
        ∂kahlerVolume omegaZ := by
  let U := originalProductCorrectedTuple J.first J.second J.a J.b V
  have hU (i : Fin n) : PlurisubharmonicOn (U i) J.domain :=
    plurisubharmonicOn_original_product_corrected J.firstPotential J.secondPotential (hV i)
  have hc := originalJointCurrent_local_reading omegaX omegaZ hV J
  have ha : ContDiffOn ℝ ∞ (omegaZ.form.val.coeff J.second) J.D :=
    (omegaZ.form.val.smooth J.second).mono J.secondPotential.2.1
  have hap z (hz : z ∈ J.D) : IsSemipositiveOneOne (omegaZ.form.val.coeff J.second z) :=
    ⟨(omegaZ.isKahler.1 J.second z (J.secondPotential.2.1 hz)).1,
      omegaZ.isSemipositive J.second z (J.secondPotential.2.1 hz)⟩
  have hlocal := original_wedgePowerMeasure_fibre_fubini hU hc.1 ha hap
    (hG.comp (measurable_chartInv J.chart)) (fun q => hGb (chartInv J.chart q))
    (productChartTest J hχ hχc hχJ) (productChartTest_nonneg J hχ hχc hχJ hχ0)
  have hjoint := original_joint_partition_chart_pairing omegaX omegaZ hV J hχ hχc hχJ hG
  have houter := original_outer_fibre_chart_pairing omegaZ hV hVF J hχ hχc hχJ G
  exact ⟨hjoint.1.mpr hlocal.1, houter.1.mpr hlocal.2.1,
    hjoint.2.trans (hlocal.2.2.trans houter.2.symm)⟩

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment023

section CompactFibreCanonicalFragment024

/-! Whole genuine compact-product Fubini for the actual original current and
actual global fibre measures. A finite partition and all integrability are produced. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.NPP.CompactFibreSlicingNext

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending ProductComplexManifold GlobalNonPluripolar MixedNonPluripolar
open IntegrationCurrent GlobalSlotStokes
open scoped ProductComplexManifold

variable {n m : ℕ} {X Z : Type*}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

theorem original_compact_fibre_fubini
    (omegaX : KahlerBackground n X) (omegaZ : KahlerBackground m Z)
    {θ : ClosedRealOneOneForm n X} {γ : ClosedRealOneOneForm m Z}
    {V : Fin n → X × Z → EReal} (hV : ∀ i, IsThetaPshPotential (prodForm θ γ).val (V i))
    (hVF : ∀ z i, IsThetaPshPotential θ.val (fun x => V i (x, z)))
    {G : X × Z → ℝ} (hG : Measurable G) {C : ℝ} (hGb : ∀ p, ‖G p‖ ≤ C) :
    Integrable G (originalJointWedgeMeasure omegaX omegaZ θ γ V hV) ∧
    Integrable (fun z => ∫ x, G (x, z) ∂originalFibreMixedMeasure θ V hVF z)
      (kahlerVolume omegaZ) ∧
    (∫ p, G p ∂originalJointWedgeMeasure omegaX omegaZ θ γ V hV) =
      ∫ z, ∫ x, G (x, z) ∂originalFibreMixedMeasure θ V hVF z
        ∂kahlerVolume omegaZ := by
  obtain ⟨r, χ, J, hsm, hχ0, hsupp, hcpt, hsum⟩ := exists_finite_original_product_partition θ γ
  let μ := originalJointWedgeMeasure omegaX omegaZ θ γ V hV
  let ν := originalFibreMixedMeasure θ V hVF
  let F := fun (a : Fin r) (p : X × Z) => χ a p * G p
  have hterm (a : Fin r) := original_product_partition_term_fubini omegaX omegaZ hV hVF
    (J a) (hsm a) (hcpt a) (hsupp a) (hχ0 a) hG hGb
  have hχ1 (a : Fin r) (p : X × Z) : χ a p ≤ 1 := by
    calc
      _ ≤ ∑ b, χ b p := Finset.single_le_sum (fun b _ => hχ0 b p) (Finset.mem_univ a)
      _ = _ := hsum p
  have hFsum : (fun p => ∑ a, F a p) = G := by
    funext p
    change (∑ a, χ a p * G p) = G p
    rw [← Finset.sum_mul, hsum p, one_mul]
  have hinner (a : Fin r) (z : Z) : Integrable (fun x => F a (x, z)) (ν z) := by
    let : IsFiniteMeasure (ν z) := globalMixedMeasure_isFiniteMeasure omegaX (fun i => (hVF z i).1)
    have hm : Measurable (fun x => F a (x, z)) :=
      (((GlobalSlotStokes.ChartSmooth.continuous (hsm a)).measurable).mul hG).comp
        (measurable_id.prodMk measurable_const)
    refine integrable_of_measurable_bounded hm (Q := max C 0) (fun x => ?_) (ν z)
    change |χ a (x, z) * G (x, z)| ≤ max C 0
    rw [abs_mul, abs_of_nonneg (hχ0 a (x, z))]
    calc
      _ ≤ 1 * |G (x, z)| := mul_le_mul_of_nonneg_right (hχ1 a (x, z)) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul, ← Real.norm_eq_abs] using (hGb (x, z)).trans (le_max_left C 0)
  have hIsum (z : Z) : (∑ a, ∫ x, F a (x, z) ∂ν z) = ∫ x, G (x, z) ∂ν z := by
    calc
      _ = ∫ x, ∑ a, F a (x, z) ∂ν z :=
        (integral_finsetSum _ (fun a _ => hinner a z)).symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => congrFun hFsum (x, z))
  have hjoint : Integrable G μ :=
    (integrable_finsetSum Finset.univ (fun a _ => (hterm a).1)).congr
      (Eventually.of_forall fun p => congrFun hFsum p)
  have houter : Integrable (fun z => ∫ x, G (x, z) ∂ν z) (kahlerVolume omegaZ) :=
    (integrable_finsetSum Finset.univ (fun a _ => (hterm a).2.1)).congr
      (Eventually.of_forall hIsum)
  refine ⟨hjoint, houter, ?_⟩
  calc
    _ = ∫ p, ∑ a, F a p ∂μ := integral_congr_ae
      (Eventually.of_forall fun p => (congrFun hFsum p).symm)
    _ = ∑ a, ∫ p, F a p ∂μ := integral_finsetSum _ (fun a _ => (hterm a).1)
    _ = ∑ a, ∫ z, ∫ x, F a (x, z) ∂ν z ∂kahlerVolume omegaZ :=
      Finset.sum_congr rfl (fun a _ => (hterm a).2.2)
    _ = ∫ z, ∑ a, ∫ x, F a (x, z) ∂ν z ∂kahlerVolume omegaZ :=
      (integral_finsetSum _ (fun a _ => (hterm a).2.1)).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hIsum)

end SGPT.NPP.CompactFibreSlicingNext

end
end CompactFibreCanonicalFragment024

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.mainModule == `SGPT.NPP.CompactFibreGlobalFubini do throwError "Wrong proper module identity: {env.mainModule}"
  let forbidden : Array Name := #[`OriginalCurrentProductDictionaryDraft, `AllDimensionCurrentProductDraft, `GlobalWedgeChartDictionaryDraft, `OriginalProductPotentialsDraft, `OriginalProductPartitionDraft, `PositiveCoefficientMeasureDraft, `FibreTruncationDictionaryDraft, `FibreTruncationMeasureDraft, `CurrentBasePowerMeasureDraft, `SmoothBaseWedgeMeasureDraft, `OriginalBaseFormDictionaryDraft, `PositiveFibreMRegularizationDraft, `NonPluripolarFibreMPositiveDraft, `FibreOriginalMeasureDictionaryDraft, `OriginalGlobalCurrentMeasureDraft, `OriginalFibreIntegralDraft, `BaseVolumeBorelDictionaryDraft, `OriginalOuterFibreIntegralDraft, `RealNonPluripolarFibreDraft, `SignedMultiplierFibreDraft, `LocalSignedCurrentDictionaryDraft, `OriginalLocalCurrentFubiniDraft, `OriginalWedgeMeasureFubiniDraft, `OriginalPartitionTermDraft, `OriginalCompactFubiniDraft, `SignedTopFormDictionaryDraft, `OriginalSignedCurrentDictionaryDraft, `OriginalSignedFubiniDraft, `OriginalCompactSlicingSourceDraft, `LiteralCompactSlicingContractDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m then throwError "Historical flat private provider leaked: {m}"
  logInfo m!"CANONICAL_COMPACT_FIBRE_PAYLOAD module={env.mainModule} proper_root=true old_flat_modules=0"
