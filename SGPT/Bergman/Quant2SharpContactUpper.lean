import Mathlib.MeasureTheory.Measure.Portmanteau
import SGPT.Bergman.SourceOriginalAnalyticContactWeakLimit
import SGPT.IGood.LogVolume
import SGPT.Bergman.SourceIGoodPartialEnvelope
import SGPT.Bergman.SourceReferenceAdditiveInvariance
import SGPT.Bergman.SourceRelativeEnvelopeCases
import SGPT.Envelopes.DNTEnvelopes
import SGPT.Bergman.Quant2SharpKahlerDensity
import SGPT.Bergman.SourceBergmanFiniteMeasures
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Quant2SharpContactUpper

Contact-set nullity of weak limits, the analytic upper bound for cluster points and the reduction of weak convergence to the total-mass limit.

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpFilterOpenMassZero.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- Actual finite-measure subfilter Portmanteau reader: if the ORIGINAL measures
converge weakly and their mass on an open set tends to zero, their actual
weak limit gives that set zero mass. No probability normalization. -/
theorem sourceSharp_filter_open_zero_of_mass_tendsto_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {tau : FiniteMeasure X} {nu : ℕ → FiniteMeasure X}
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (hweak : Tendsto nu l (𝓝 tau)) {F : Set X} (hF : IsOpen F)
    (hzero : Tendsto (fun j => (nu j : Measure X) F) atTop (𝓝 0)) :
    (tau : Measure X) F = 0 := by
  have hmass : Tendsto (fun j => (nu j : Measure X) univ) l
      (𝓝 ((tau : Measure X) univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
  have hsub := ENNReal.Tendsto.sub hmass (hzero.mono_left hl) (Or.inr ENNReal.zero_ne_top)
  have hcomp : Tendsto (fun j => (nu j : Measure X) Fᶜ) l
      (𝓝 ((tau : Measure X) univ)) := by
    have heq : (fun j => (nu j : Measure X) Fᶜ) =
        (fun j => (nu j : Measure X) univ - (nu j : Measure X) F) := by
      funext j
      exact measure_compl hF.measurableSet (measure_ne_top _ _)
    rw [heq]
    simpa only [tsub_zero] using hsub
  have hclosed := FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak hF.isClosed_compl
  rw [hcomp.limsup_eq] at hclosed
  have hsum : (tau : Measure X) F + (tau : Measure X) Fᶜ ≤ (tau : Measure X) Fᶜ :=
    (measure_add_measure_compl hF.measurableSet).le.trans hclosed
  apply le_antisymm ?_ zero_le
  apply (ENNReal.add_le_add_iff_right (measure_ne_top (tau : Measure X) Fᶜ)).mp
  simpa only [zero_add] using hsum

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalFilterContact.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ReferenceEnvelopeConvergence
open SGPT.Bergman.ContactConcentration SGPT.Bergman.BackgroundEnvelopeLimit
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
/-- The original phi-contact nullity for ANY nontrivial cofinal cluster filter
of the SAME positive-degree raw beta sequence. Native integer gap-mass decay
is transferred to the filter, then finite-measure Portmanteau and the existing
countable original envelope identities apply. No arbitrary-net Fatou,
probability replacement or desired nullity is assumed. -/
theorem sourceSharp_original_filter_contact_zero
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (τ : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (j+1) (Nat.succ_pos j) φ) l (𝓝 τ)) :
    (τ : Measure X) (sourceEnvelopeGap
      (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)) φ v 0) = 0 := by
  obtain ⟨hφ,_hmass⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega _ (wholeWeightedSubset (n := n) v).nonPluripolar_carrier hcurrent
  have hq : IsGlobalQuasiPshPotential (n := n) φ := ⟨hφ.1.quasiPlurisubharmonic,hφ.2⟩
  have hanchart : (ofFixedModel n X).HasRationalAnalyticChartType φ :=
    hasRationalAnalyticType_iff_chartType.mp han
  rw [sourceEnvelopeGap_zero_eq_iUnion_epsilon omega _ hcurrent han v]
  apply measure_iUnion_null
  intro q
  have heps := sourceEpsilonSequence_pos q
  have hcurrentq := sourceKahlerCurrent_perturb_nonneg omega hcurrent heps.le
  obtain ⟨α,hmono,hα,hlim,hdecay⟩ := exists_source_fixedContactGap_mass_tendsto_zero
    omega L T hL hT v hv hq hanchart heps
  rw [sourceEnvelopeGap_zero_eq_iUnion_scaled omega _ hcurrentq v α hmono.monotone
    (fun k => (hα k).1) (fun k => (hα k).2) hlim]
  apply measure_iUnion_null
  intro m
  apply measure_sourceEnvelopeGap_zero_of_positive
  intro δ hδ
  let : TopologicalSpace.PseudoMetrizableSpace X :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n X
  apply sourceSharp_filter_open_zero_of_mass_tendsto_zero l hl hweak
    (sourceEnvelopeGap_isOpen _ _ v δ)
  simpa only [Function.comp_def,sourceBergmanFiniteMeasure_toMeasure] using
    (hdecay m δ hδ).comp (tendsto_add_atTop_nat 1)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalIEnvelopeEquality.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ReferenceEnvelopeConvergence SGPT.Bergman.IGoodPartialEnvelope
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
/-- Equality part of original eq:pbmconvanaly: the SAME analytic current
produces actual positive NPP mass and I-goodness in its actual background,
then the existing whole original partial-envelope theorem applies. Native
analytic type is the exact original rational/bounded-remainder dictionary;
no stronger global/neat type, I-goodness or mass certificate is assumed. -/
theorem sourceSharp_original_analytic_IEnvelope_eq
    (omega : KahlerBackground n X) (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ))
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ) :
    let θ := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)
    partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal)) =
      partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal)) := by
  intro θ
  obtain ⟨hnative,hmass⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega (sourceNativeFirstChernForm L hL) (wholeWeightedSubset (n := n) v).nonPluripolar_carrier hcurrent
  have hφ : (ofFixedModel n X).IsThetaPSH θ φ :=
    (isThetaPSH_iff_nativeThetaPotential θ φ).mpr (by
      simpa only [θ,sourceNativeAtlasForm_roundTrip] using hnative)
  have hpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ := by
    simpa only [sourcePotentialNonPluripolarMeasure,DiagonalMass.diagonalPotentialMass,
      θ,sourceNativeAtlasForm_roundTrip] using hmass
  have hA : HasManifoldAnalyticSingularityType (n := n) φ :=
    hasRationalAnalyticType_iff_chartType.mp han
  have hgoodWith := SGPT.IGood.LogVolume.sourceIGoodWith_of_analytic omega hφ hA hpos
  have hgood := (sourceIGood_iff_with_positive_background omega hφ hpos).mpr hgoodWith
  obtain ⟨x₀,_,hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty v.continuous.continuousOn
  exact partialIEnvelope_eq_partialEnvelope_of_iGood omega hφ hpos hgood univ
    (fun y : (univ : Set X) => (v y.val : EReal))
    ⟨v x₀,fun y => by exact_mod_cast hx₀ y.property⟩
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalEnvelopeContact.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ReferenceEnvelopeConvergence SGPT.Bergman.RelativeEnvelopeCases
open SGPT.PSH.VariableComplexAtlas SGPT.Okounkov.TranscendentalWNReg
open ManifoldTubePositivity
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
/-- The SAME original whole-X partial envelope has the actual native DNT
contact measure. A representative below v is manufactured by compact bounds;
existing additive invariance restores the original unshifted phi exactly.
Neither a normalized reference nor a contact/MA identity is an input. -/
theorem sourceSharp_original_envelope_contact_measure
    (omega : KahlerBackground n X) (L : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    let θ := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ hP : (ofFixedModel n X).IsThetaPSH θ P,
      sourcePotentialNonPluripolarMeasure θ P hP =
        (positiveTopMeasure omega (sourceNativeFirstChernForm L hL + ddcClosedForm v hv)).restrict
          {x | P x = (v x : EReal)} := by
  intro θ P
  obtain ⟨hnative,_hmass⟩ := exists_source_positiveMass_of_nonPluripolar_and_kahlerCurrent
    omega (sourceNativeFirstChernForm L hL) (wholeWeightedSubset (n := n) v).nonPluripolar_carrier hcurrent
  obtain ⟨M,hM⟩ := hnative.exists_global_upper_bound
  obtain ⟨x₀,_,hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty v.continuous.continuousOn
  let A := M - v x₀
  let u : X → EReal := fun x => φ x - (A : EReal)
  have hu : (ofFixedModel n X).IsThetaPSH θ u :=
    (isThetaPSH_iff_nativeThetaPotential θ u).mpr (by
      simpa only [θ,sourceNativeAtlasForm_roundTrip,u] using hnative.sub_const A)
  have hule (x : X) : u x ≤ (v x : EReal) := by
    calc
      _ ≤ (M : EReal) - (A : EReal) := EReal.sub_le_sub (hM x) le_rfl
      _ = (v x₀ : EReal) := by rw [← EReal.coe_sub];congr 1;dsimp only [A];ring
      _ ≤ _ := by exact_mod_cast hx₀ (mem_univ x)
  obtain ⟨hη,hmeasure⟩ := SGPT.Envelopes.DNT.sourceGeneralizedEnvelope_measure_eq omega θ hu hv hule
  have heq : sourceRelativeEnvelope θ u (fun x => (v x : EReal)) = P := by
    rw [← partialEnvelope_univ]
    exact sourcePartialEnvelope_sub_const θ φ univ (fun y : (univ : Set X) => (v y.val : EReal)) A
  have hP : (ofFixedModel n X).IsThetaPSH θ P := by simpa only [heq] using hη
  refine ⟨hP,?_⟩
  simpa only [heq,θ,sourceNativeAtlasForm_roundTrip] using hmeasure
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalFilterAnalyticUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent ManifoldTubePositivity
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.ReferenceEnvelopeConvergence SGPT.Bergman.RelativeEnvelopeCases
open SGPT.Bergman.ContactConcentration SGPT.Bergman.BackgroundEnvelopeLimit
open SGPT.PSH.VariableComplexAtlas SGPT.Okounkov.TranscendentalWNReg
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
/-- The original cofinal-filter cluster upper eq:muleq_temp1 for the SAME analytic
phi and literal original beta. The sharp physical upper, actual phi-contact
nullity, normalization, ordinary-envelope obstacle and DNT contact-measure
identity are internally composed. No mass limit or desired cluster measure
order is a hypothesis. Whole convergence still requires actual total mass. -/
theorem sourceSharp_original_filter_cluster_le_envelope
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop)
    (τ : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (j+1) (Nat.succ_pos j) φ) l (𝓝 τ)) :
    let θ := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ hP : (ofFixedModel n X).IsThetaPSH θ P,
      (τ : Measure X) ≤ sourcePotentialNonPluripolarMeasure θ P hP := by
  intro θ P
  obtain ⟨hP,hmeasure⟩ := sourceSharp_original_envelope_contact_measure omega L hL v hv hcurrent
  have hupper := sourceSharp_original_filter_cluster_le_positiveTopMeasure omega hvol L T hL hT v hv
    φ (fun j => j+1) (fun j => Nat.succ_pos j) (tendsto_add_atTop_nat 1) l hl τ hweak
  have hgap := sourceSharp_original_filter_contact_zero omega L T hL hT v hv hcurrent han
    l hl τ hweak
  obtain ⟨x₀,_,hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty v.continuous.continuousOn
  have hobs := partialEnvelope_obstacle θ φ (wholeWeightedSubset (n := n) v).nonPluripolar_carrier
    (f := fun y : (univ : Set X) => (v y.val : EReal))
    ⟨v x₀,fun y => by exact_mod_cast hx₀ y.property⟩
  change partialObstacle (n := n) univ (fun y : (univ : Set X) => (v y.val : EReal)) P at hobs
  have hq := (sourceQuasiEverywhere_iff_native _).mp
    ((partialObstacle_univ_iff (fun x : X => (v x : EReal)) P).mp hobs)
  have hle : ∀ x, P x ≤ (v x : EReal) :=
    ContinuousObstacleEnvelopeContact.le_coe_of_ae_in_charts_le
      ((isThetaPSH_iff_nativeThetaPotential θ P).mp hP).1 v.continuous
      (fun e => hq.ae_in_chart e volume)
  let C := {x | P x = (v x : EReal)}
  have hae : ∀ᵐ x ∂(τ : Measure X), x ∈ C := by
    rw [ae_iff]
    have heq : {x | ¬ x ∈ C} = sourceEnvelopeGap θ φ v 0 := by
      ext x
      change (¬ P x = (v x : EReal)) ↔ P x < ((v x - 0 : ℝ) : EReal)
      rw [sub_zero]
      exact ⟨fun h => lt_iff_le_and_ne.mpr ⟨hle x,h⟩,fun h => ne_of_lt h⟩
    rw [heq]
    exact hgap
  refine ⟨hP,?_⟩
  calc
    (τ : Measure X) = (τ : Measure X).restrict C := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ ≤ (positiveTopMeasure omega (sourceNativeFirstChernForm L hL + ddcClosedForm v hv)).restrict C :=
      Measure.restrict_mono le_rfl hupper
    _ = _ := hmeasure.symm

/-- Complete original sharp-upper slice: exact original beta cluster is
bounded by the SAME original ideal-envelope MA, and the original ordinary
and ideal envelopes/MA measures are equal. Actual total mass and whole weak
convergence are deliberately not asserted by this source upper producer. -/
theorem sourceSharp_original_filter_cluster_upper_full
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop)
    (τ : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (j+1) (Nat.succ_pos j) φ) l (𝓝 τ)) :
    let θ := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI),
      PI = P ∧ (τ : Measure X) ≤ sourcePotentialNonPluripolarMeasure θ PI hPI ∧
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP := by
  intro θ P PI
  obtain ⟨hP,hupper⟩ := sourceSharp_original_filter_cluster_le_envelope omega hvol L T hL hT v hv
    hcurrent han l hl τ hweak
  have hIEq : PI = P := sourceSharp_original_analytic_IEnvelope_eq omega L hL v hcurrent han
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI := by rw [hIEq];exact hP
  refine ⟨hP,hPI,hIEq,?_,?_⟩
  · simpa only [hIEq] using hupper
  · simp only [hIEq]
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalBetaCompactness.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.ContactConcentration
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal NNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
/-- The ACTUAL original positive-degree beta measures lie in a manufactured
compact set of finite measures. This is the original raw sequence, with no
probability replacement, mass-limit hypothesis or supplied compactness bound.
Bounded sets of finite measures on the compact space are compact (Prokhorov). -/
theorem sourceSharp_original_beta_compact_mass_set
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (φ : X → EReal) :
    let B := fun j : ℕ => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (j+1) (Nat.succ_pos j) φ
    ∃ C : ℝ≥0, IsCompact {ν : FiniteMeasure X | ν.mass ≤ C} ∧ ∀ j, (B j).mass ≤ C := by
  intro B
  obtain ⟨D,_hD,hbound⟩ := exists_source_smooth_weighted_measure_bound L T hL hT v hv
    (kahlerVolume omega) (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega)
  let C : ℝ≥0 := (ENNReal.ofReal D).toNNReal
  refine ⟨C,isCompact_setOfPred_finiteMeasure_le_of_compactSpace X C,fun j => ?_⟩
  have hm : (B j : Measure X) univ ≤ ENNReal.ofReal D := by
    calc
      _ ≤ (ENNReal.ofReal D • kahlerVolume omega) univ :=
        hbound (j+1) (Nat.succ_pos j) φ univ
      _ = _ := by rw [Measure.smul_apply,smul_eq_mul,hvol,mul_one]
  rw [← FiniteMeasure.ennreal_mass,← ENNReal.coe_toNNReal ENNReal.ofReal_ne_top] at hm
  exact ENNReal.coe_le_coe.mp hm
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalConvergenceReader.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.ContactConcentration SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
/-- EXACT CONDITIONAL READER, not a proof of the whole original proposition:
actual total mass convergence to the manufactured SAME original MA target
implies weak convergence of the actual positive-degree raw beta sequence.
All compactness, arbitrary cluster-filter upper bounds and equal-finite-mass
uniqueness are produced. The total mass implication remains visible and
UNdischarged; no DX/H0 mass theorem or original credit is claimed. -/
theorem sourceSharp_original_weakConvergence_from_actual_mass_limit
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (han : (ofFixedModel n X).HasRationalAnalyticType φ) :
    let θ := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)
    let P := partialEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let PI := partialIEnvelope θ φ univ (fun y : (univ : Set X) => (v y.val : EReal))
    let B := fun j : ℕ => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (j+1) (Nat.succ_pos j) φ
    ∃ (hP : (ofFixedModel n X).IsThetaPSH θ P) (hPI : (ofFixedModel n X).IsThetaPSH θ PI)
      (M : FiniteMeasure X), PI = P ∧ (M : Measure X) = sourcePotentialNonPluripolarMeasure θ PI hPI ∧
      sourcePotentialNonPluripolarMeasure θ PI hPI = sourcePotentialNonPluripolarMeasure θ P hP ∧
      (Tendsto (fun j => (B j : Measure X) univ) atTop (𝓝 ((M : Measure X) univ)) →
        Tendsto B atTop (𝓝 M)) := by
  intro θ P PI B
  obtain ⟨hP,_hcontact⟩ := sourceSharp_original_envelope_contact_measure omega L hL v hv hcurrent
  have hIEq : PI = P := sourceSharp_original_analytic_IEnvelope_eq omega L hL v hcurrent han
  have hPI : (ofFixedModel n X).IsThetaPSH θ PI := by rw [hIEq];exact hP
  let M := DiagonalMeasureRegularity.finiteDiagonalPotentialMeasure omega
    (atlasClosedFormToNative θ) PI ((isThetaPSH_iff_nativeThetaPotential θ PI).mp hPI)
  have hM : (M : Measure X) = sourcePotentialNonPluripolarMeasure θ PI hPI := rfl
  refine ⟨hP,hPI,M,hIEq,hM,?_,?_⟩
  · simp only [hIEq]
  · intro hmass
    obtain ⟨C,hCompact,hB⟩ := sourceSharp_original_beta_compact_mass_set omega hvol L T hL hT v hv φ
    apply hCompact.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hB)
    intro τ _hτC hτ
    let l : Filter ℕ := Filter.comap B (𝓝 τ) ⊓ atTop
    have hne : NeBot l := neBot_inf_comap_iff_map'.mpr hτ.clusterPt.neBot
    let : NeBot l := hne
    have hl : l ≤ atTop := inf_le_right
    have hweak : Tendsto B l (𝓝 τ) := tendsto_comap.mono_left inf_le_left
    obtain ⟨_hP',hPI',_hIEq',hupper,_hMAeq'⟩ :=
      sourceSharp_original_filter_cluster_upper_full omega hvol L T hL hT v hv
        hcurrent han l hl τ hweak
    apply FiniteMeasure.toMeasure_injective
    apply Measure.eq_of_le_of_measure_univ_eq
    · rw [hM]
      exact hupper
    · have hmτ : Tendsto (fun j => (B j : Measure X) univ) l (𝓝 ((τ : Measure X) univ)) := by
        simpa only [Function.comp_def,FiniteMeasure.ennreal_mass] using
          ENNReal.continuous_coe.continuousAt.tendsto.comp hweak.mass
      exact tendsto_nhds_unique hmτ (hmass.mono_left hl)
end SGPT.Bergman.SharpLocalUpper
end
end
