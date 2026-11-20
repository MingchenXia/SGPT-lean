import SGPT.Bergman.SourcePartialEquilibriumEnergy
import SGPT.Bergman.SourceRelativeEnvelopeCases
import SGPT.Bergman.SourcePartialIEnvelopeComparison
import SGPT.Bergman.SourcePartialToGlobal
import SGPT.Envelopes.SourceRooftopContactMeasures
import SGPT.Envelopes.SourceObstacleConcentration
import SGPT.Envelopes.SourceMinimalEnvelopeLocalBounds
import SGPT.Foundations.Analysis.Pending.BigClassNonKahlerLocusNull

/-! Original weighted-subset contact measures. The complete mathematical route
is written first in partial-equilibrium-measure.tex. No MA support or balayage
conclusion is an input. This bounded WORK source has no canonical acceptance.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.PartialEquilibriumMeasure

open Set Filter MeasureTheory TopologicalSpace
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeSameType
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original continuous subtype weight has a genuinely lsc ambient
extension, retaining exactly top off the SAME original closed set. -/
theorem extendedObstacle_lowerSemicontinuous {K : Set M} (hK : IsClosed K)
    (v : C(K, ℝ)) :
    LowerSemicontinuous (extendedObstacle K (fun x => (v x : EReal))) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a = ⊤
  · subst a
    simpa only [Iic_top, preimage_univ] using isClosed_univ
  · have heq : extendedObstacle K (fun x => (v x : EReal)) ⁻¹' Iic a =
        (Subtype.val : K → M) '' {x : K | (v x : EReal) ≤ a} := by
      ext x
      constructor
      · intro hx
        by_cases hxK : x ∈ K
        · exact ⟨⟨x, hxK⟩, by simpa [extendedObstacle, hxK] using hx, rfl⟩
        · have htop : (⊤ : EReal) ≤ a := by simpa [extendedObstacle, hxK] using hx
          exact (ha (top_le_iff.mp htop)).elim
      · rintro ⟨y, hy, rfl⟩
        simpa [extendedObstacle, y.property] using hy
    rw [heq]
    exact hK.isClosedMap_subtype_val _
      (isClosed_Iic.preimage (continuous_coe_real_ereal.comp v.continuous))

/-- Every original unrestricted partial competitor is the SAME native
extended-obstacle candidate, in BOTH directions and with the actual volume
independent of any desired measure conclusion. -/
theorem unrestrictedPartial_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (K : Set M) (f : K → EReal) :
    uscSup (fun v : {v : M → EReal // (ofFixedModel n M).IsThetaPSH θ v ∧
      partialObstacle (n := n) K f v} => v.val) =
      rooftopEnvelope (atlasClosedFormToNative θ).val (extendedObstacle K f) := by
  apply congrArg uscRegularization
  funext x
  rw [rooftopSupremum_apply]
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup_of_le v.val (le_iSup_of_le
      ⟨(isThetaPSH_iff_nativeThetaPotential θ v.val).mp v.property.1,
        (sourceQuasiEverywhere_iff_native _).mp
          ((partialObstacle_iff_extended K f v.val).mp v.property.2)⟩ le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    intro hv
    exact le_iSup (fun w : {w : M → EReal // (ofFixedModel n M).IsThetaPSH θ w ∧
        partialObstacle (n := n) K f w} => w.val x)
      ⟨v, (isThetaPSH_iff_nativeThetaPotential θ v).mpr hv.1,
        (partialObstacle_iff_extended K f v).mpr
          ((sourceQuasiEverywhere_iff_native _).mpr hv.2)⟩

/-- Original closed nonPP/continuous data manufacture a finite global lower
bound for the actual extended obstacle; no obstacle-value readback is used. -/
theorem weighted_extendedObstacle_bounded_below [CompactSpace M]
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    ∃ a : ℝ, ∀ x : M, (a : EReal) ≤ extendedObstacle W.carrier W.erealWeight x := by
  classical
  obtain ⟨a, _b, ha, _hb⟩ := W.partialEnvelope_weight_bounds
  refine ⟨a, ?_⟩
  intro x
  by_cases hx : x ∈ W.carrier
  · simpa only [extendedObstacle, dif_pos hx] using ha ⟨x, hx⟩
  · simp only [extendedObstacle, dif_neg hx, le_top]

/-- The actual Cases12 producer supplies the minimal-reference family;
the new two-way dictionary then gives the same native obstacle roof. -/
theorem minimalPartial_eq_native [CompactSpace M] [Nonempty M]
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialEnvelope θ (sourceMinimalEnvelope θ) K f =
      rooftopEnvelope (atlasClosedFormToNative θ).val (extendedObstacle K f) :=
  (RelativeEnvelopeCases.partialEnvelope_minimal_eq_unrestricted hφ K f).trans
    (unrestrictedPartial_eq_native θ K f)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- All three actual outputs used below are internally genuine. The ideal
output consumes the rooted E-infinity producer rather than an output premise. -/
theorem weighted_partials_genuine (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    (ofFixedModel n M).IsThetaPSH θ (partialEnvelope θ φ W.carrier W.erealWeight) ∧
    (ofFixedModel n M).IsThetaPSH θ (partialIEnvelope θ φ W.carrier W.erealWeight) ∧
    (ofFixedModel n M).IsThetaPSH θ
      (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight) := by
  obtain ⟨a, b, ha, hb⟩ := W.partialEnvelope_weight_bounds
  obtain ⟨_C, _D, hU, _hI, _hC, _hD⟩ := partialEnvelopes_genuine_bounded
    hφ hφpos W.nonPluripolar_carrier ⟨a, ha⟩ ⟨b, hb⟩
  have hI := (PartialEquilibriumEnergy.partialIEnvelope_eInfinity_continuous
    ω hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight).1
  have hV := RelativeEnvelopeCases.sourceMinimalEnvelope_genuine_of_reference hφ
  have hφV := RelativeEnvelopeCases.singularityLE_sourceMinimalEnvelope hφ hφ
  have hVpos : 0 < sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ) hV univ :=
    hφpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hφ hV hφV)
  obtain ⟨_E, _F, hH, _hHI, _hE, _hF⟩ := partialEnvelopes_genuine_bounded
    hV hVpos W.nonPluripolar_carrier ⟨a, ha⟩ ⟨b, hb⟩
  exact ⟨hU, hI, hH⟩

/-- Actual local polydisk balayage and actual non-Kahler-locus nullity prove
strict noncontact nullity for the SAME weighted partial envelope. -/
theorem weighted_minimal_strict_null_positive (hn : 0 < n) (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ
      (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).2.2
      {x | partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight x <
        extendedObstacle W.carrier W.erealWeight x} = 0 := by
  let T := atlasClosedFormToNative θ
  let H := partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight
  let f := extendedObstacle W.carrier W.erealWeight
  have hH := (weighted_partials_genuine ω hφ hφpos W).2.2
  have hHn : IsThetaPshPotential T.val H :=
    (isThetaPSH_iff_nativeThetaPotential θ H).mp hH
  have heq : H = rooftopEnvelope T.val f := minimalPartial_eq_native hφ _ _
  have hf : LowerSemicontinuous f := extendedObstacle_lowerSemicontinuous W.isClosed_carrier W.weight
  obtain ⟨a, hfa⟩ := weighted_extendedObstacle_bounded_below W
  obtain ⟨_l, b, _hl, hb⟩ := W.partialEnvelope_weight_bounds
  have hbound := partialEnvelope_obstacle θ (sourceMinimalEnvelope θ)
    W.nonPluripolar_carrier ⟨b, hb⟩
  have hHf : QuasiEverywhere (n := n) (fun x => H x ≤ f x) :=
    (sourceQuasiEverywhere_iff_native _).mp
      ((partialObstacle_iff_extended W.carrier W.erealWeight H).mp hbound)
  have hmax : ∀ v : M → EReal, IsThetaPshPotential T.val v →
      QuasiEverywhere (n := n) (fun x => v x ≤ f x) → v ≤ H := by
    intro v hv hvf
    rw [heq]
    exact le_rooftopEnvelope hv hvf
  have hbig := sourcePositiveMass_isBig ω hφ hφpos
  have hloc : ∀ x, x ∉ FirstPass.NonKahlerLocus.nonKahlerLocus
      (RealBottChern.ofRepresentative T) →
      ∃ N ∈ 𝓝 x, PatchLocalBoundedMeasure.IsBoundedPotentialOn H N := by
    intro x hx
    exact BigClassEnvelopeContact.exists_isBoundedPotentialOn_offNonKahlerLocus
      hn T hbig hfa (fun v hv hvf => hmax v hv (quasiEverywhere_of_forall hvf)) hHn hx
  have hgood : DiagonalMass.diagonalPotentialMeasure T H hHn
      ({x | H x < f x} \ FirstPass.NonKahlerLocus.nonKahlerLocus
        (RealBottChern.ofRepresentative T)) = 0 :=
    PolydiskPatchBalayageContactQE.diagonalPotentialMeasure_lt_eq_zero_of_locallyBounded_qe
      hn hf hHf hmax hHn (fun _ hx => hx.1) (fun x hx => hloc x hx.2)
  have hbad := BigClassNonKahlerLocusNull.diagonalPotentialMeasure_nonKahlerLocus_eq_zero
    hn T hbig hHn
  change DiagonalMass.diagonalPotentialMeasure T H hHn {x | H x < f x} = 0
  apply measure_mono_null (t := ({x | H x < f x} \
      FirstPass.NonKahlerLocus.nonKahlerLocus (RealBottChern.ofRepresentative T)) ∪
      FirstPass.NonKahlerLocus.nonKahlerLocus (RealBottChern.ofRepresentative T)) ?_
      (measure_union_null hgood hbad)
  intro x hx
  by_cases hxn : x ∈ FirstPass.NonKahlerLocus.nonKahlerLocus
      (RealBottChern.ofRepresentative T)
  · exact Or.inr hxn
  · exact Or.inl ⟨hx, hxn⟩

/-- The same exact strict noncontact nullity in EVERY source dimension.
The zero-dimensional branch uses actual discrete charts and the existing
unconditional native contact theorem, not a positive-dimensional assumption. -/
theorem weighted_minimal_strict_null (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ
      (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).2.2
      {x | partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight x <
        extendedObstacle W.carrier W.erealWeight x} = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · let T := atlasClosedFormToNative θ
    let H := partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight
    let f := extendedObstacle W.carrier W.erealWeight
    have hH := (weighted_partials_genuine ω hφ hφpos W).2.2
    have heq : H = rooftopEnvelope T.val f := minimalPartial_eq_native hφ _ _
    have hHn : IsThetaPshPotential T.val H := (isThetaPSH_iff_nativeThetaPotential θ H).mp hH
    have hroof : IsThetaPshPotential T.val (rooftopEnvelope T.val f) := heq ▸ hHn
    let : DiscreteTopology M := discreteTopology_iff_isOpen_singleton.mpr
      (RooftopDimZero.isOpen_singleton_of_dim_zero hn)
    have hf : ActualExtendedObstacleQuasiContinuity.QuasiContinuousERealFor
        (ThetaCapacity.thetaCapacity ω.form (fun _ => 0)) f := by
      intro η hη
      refine ⟨∅, isOpen_empty, ?_, ?_⟩
      · simpa only [ThetaCapacity.thetaCapacity_empty] using hη
      · exact (continuous_of_discreteTopology : Continuous f).continuousOn
    have hnb : rooftopEnvelope T.val f ≠ (fun _ => ⊥) := by
      intro hbot
      obtain ⟨y, _hy, hy⟩ := hroof.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
      exact hy (congrFun hbot y)
    have hnt : rooftopEnvelope T.val f ≠ (fun _ => ⊤) := by
      intro htop
      exact hroof.1.quasiPlurisubharmonic.ne_top (Classical.arbitrary M) (congrFun htop _)
    obtain ⟨_hP, hstrict, _hneq⟩ :=
      ActualQuasiContinuousEnvelopeContact.exists_genuine_envelope_and_contact ω T hf hnb hnt
    change DiagonalMass.diagonalPotentialMeasure T H hHn {x | H x < f x} = 0
    simpa only [heq] using hstrict
  · exact weighted_minimal_strict_null_positive hn ω hφ hφpos W

/-- The actual entire complement of the ambient contact locus is null;
the over-obstacle branch is removed by genuine pluripolar noncharging. -/
theorem weighted_minimal_noncontact_null (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ
      (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).2.2
      {x | partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight x ≠
        extendedObstacle W.carrier W.erealWeight x} = 0 := by
  let H := partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight
  let f := extendedObstacle W.carrier W.erealWeight
  have hH := (weighted_partials_genuine ω hφ hφpos W).2.2
  have hHn := (isThetaPSH_iff_nativeThetaPotential θ H).mp hH
  obtain ⟨_a, b, _ha, hb⟩ := W.partialEnvelope_weight_bounds
  have hqe : QuasiEverywhere (n := n) (fun x => H x ≤ f x) :=
    (sourceQuasiEverywhere_iff_native _).mp
      ((partialObstacle_iff_extended W.carrier W.erealWeight H).mp
        (partialEnvelope_obstacle θ (sourceMinimalEnvelope θ) W.nonPluripolar_carrier ⟨b, hb⟩))
  have hbad : sourcePotentialNonPluripolarMeasure θ H hH {x | ¬ H x ≤ f x} = 0 :=
    GlobalNonPluripolar.globalMixedMeasure_doesNotChargeManifoldPluripolar
      (fun _ : Fin n => hHn.1) _ hqe
  have hstrict := weighted_minimal_strict_null ω hφ hφpos W
  apply measure_mono_null (t := {x | H x < f x} ∪ {x | ¬ H x ≤ f x}) ?_
    (measure_union_null hstrict hbad)
  intro x hx
  by_cases hle : H x ≤ f x
  · exact Or.inl (lt_of_le_of_ne hle hx)
  · exact Or.inr hle

/-- WHOLE original lma:balayage: the sharp actual inequality on the triple
contact locus and both actual nullities, with genuine outputs internally
produced from the original weighted subset and positive source reference. -/
theorem weighted_partial_balayage (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    ∃ hU : (ofFixedModel n M).IsThetaPSH θ (partialEnvelope θ φ W.carrier W.erealWeight),
    ∃ hH : (ofFixedModel n M).IsThetaPSH θ
        (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight),
      sourcePotentialNonPluripolarMeasure θ (partialEnvelope θ φ W.carrier W.erealWeight) hU ≤
        (sourcePotentialNonPluripolarMeasure θ
          (partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight) hH).restrict
          {x | ∃ hx : x ∈ W.carrier,
            partialEnvelope θ φ W.carrier W.erealWeight x =
              partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight x ∧
            partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight x =
              W.erealWeight ⟨x, hx⟩} ∧
      sourcePotentialNonPluripolarMeasure θ (partialEnvelope θ φ W.carrier W.erealWeight) hU
        W.carrierᶜ = 0 ∧
      sourcePotentialNonPluripolarMeasure θ (partialEnvelope θ φ W.carrier W.erealWeight) hU
        {x | ∃ hx : x ∈ W.carrier,
          partialEnvelope θ φ W.carrier W.erealWeight x ≠ W.erealWeight ⟨x, hx⟩} = 0 := by
  let U := partialEnvelope θ φ W.carrier W.erealWeight
  let H := partialEnvelope θ (sourceMinimalEnvelope θ) W.carrier W.erealWeight
  have hU := (weighted_partials_genuine ω hφ hφpos W).1
  have hH := (weighted_partials_genuine ω hφ hφpos W).2.2
  let μ := sourcePotentialNonPluripolarMeasure θ U hU
  let ν := sourcePotentialNonPluripolarMeasure θ H hH
  let C : Set M := {x | ∃ hx : x ∈ W.carrier, U x = H x ∧ H x = W.erealWeight ⟨x, hx⟩}
  obtain ⟨R, _hR0, hR⟩ := W.exists_real_abs_bound
  have heq : U = sourceRelativeEnvelope θ φ H :=
    (PartialToGlobal.partialEnvelope_partial_to_global ω hφ hφpos
      W.nonPluripolar_carrier W.weight ⟨R, hR⟩).trans
      (RelativeEnvelopeCases.partialEnvelope_univ θ φ H)
  have hUn := (isThetaPSH_iff_nativeThetaPotential θ U).mp hU
  have hHn := (isThetaPSH_iff_nativeThetaPotential θ H).mp hH
  have hne : sourceRelativeEnvelope θ φ H ≠ ⊥ := by
    intro hbot
    obtain ⟨y, _hy, hy⟩ := hUn.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact hy (congrFun (heq.trans hbot) y)
  have hrelative (E : Set M) : μ E ≤ ν (E ∩ {x | U x = H x}) := by
    change sourcePotentialNonPluripolarMeasure θ U hU E ≤
      sourcePotentialNonPluripolarMeasure θ H hH (E ∩ {x | U x = H x})
    have hρ := sourceRelativeEnvelope_genuine_of_ne_bot hH hne
    have hm : sourcePotentialNonPluripolarMeasure θ U hU =
        sourcePotentialNonPluripolarMeasure θ (sourceRelativeEnvelope θ φ H) hρ :=
      MaxMassDecomposition.diagonalPotentialMeasure_congr hUn
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp hρ) heq
    rw [hm]
    have hset : {x | U x = H x} = {x | sourceRelativeEnvelope θ φ H x = H x} := by
      ext x
      rw [heq]
    rw [hset]
    exact sourceRelativeEnvelope_measure_le_apply ω hφ hH hne E
  have hnull : ν {x | H x ≠ extendedObstacle W.carrier W.erealWeight x} = 0 :=
    weighted_minimal_noncontact_null ω hφ hφpos W
  have hbound (E : Set M) : μ E ≤ ν (E ∩ C) := by
    apply (hrelative E).trans
    have hsub : E ∩ {x | U x = H x} ⊆ (E ∩ C) ∪
        {x | H x ≠ extendedObstacle W.carrier W.erealWeight x} := by
      intro x hx
      by_cases hcontact : H x = extendedObstacle W.carrier W.erealWeight x
      · have hxK : x ∈ W.carrier := by
          by_contra hxK
          have htop : H x = ⊤ := by simpa only [extendedObstacle, dif_neg hxK] using hcontact
          exact hHn.1.quasiPlurisubharmonic.ne_top x htop
        exact Or.inl ⟨hx.1, hxK, hx.2,
          by simpa only [extendedObstacle, dif_pos hxK] using hcontact⟩
      · exact Or.inr hcontact
    exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_eq
      (by rw [hnull, add_zero])
  refine ⟨hU, hH, ?_, ?_, ?_⟩
  · change μ ≤ ν.restrict C
    apply Measure.le_iff.mpr
    intro E hE
    simpa only [Measure.restrict_apply hE] using hbound E
  · change μ W.carrierᶜ = 0
    have hempty : W.carrierᶜ ∩ C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxK, _hUH, _hHv⟩
      exact hx hxK
    have h := hbound W.carrierᶜ
    rw [hempty, measure_empty] at h
    exact le_antisymm h zero_le
  · change μ {x | ∃ hx : x ∈ W.carrier, U x ≠ W.erealWeight ⟨x, hx⟩} = 0
    have hempty : {x | ∃ hx : x ∈ W.carrier, U x ≠ W.erealWeight ⟨x, hx⟩} ∩ C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨_hx, hneq⟩, _hx', hUH, hHv⟩
      exact hneq (hUH.trans hHv)
    have h := hbound {x | ∃ hx : x ∈ W.carrier, U x ≠ W.erealWeight ⟨x, hx⟩}
    rw [hempty, measure_empty] at h
    exact le_antisymm h zero_le

/-- The ordinary half of original cor:suppthetan, on the actual union of
the exterior and strict original subtype noncontact locus. -/
theorem weighted_partial_noncontact_union_null (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ (partialEnvelope θ φ W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).1
      (W.carrierᶜ ∪ {x | ∃ hx : x ∈ W.carrier,
        partialEnvelope θ φ W.carrier W.erealWeight x < W.erealWeight ⟨x, hx⟩}) = 0 := by
  obtain ⟨hU, _hH, _hsharp, houtside, hneq⟩ := weighted_partial_balayage ω hφ hφpos W
  apply measure_union_null houtside
  apply measure_mono_null (t := {x | ∃ hx : x ∈ W.carrier,
    partialEnvelope θ φ W.carrier W.erealWeight x ≠ W.erealWeight ⟨x, hx⟩}) ?_ hneq
  rintro x ⟨hx, hlt⟩
  exact ⟨hx, ne_of_lt hlt⟩

/-- The ideal half of original cor:suppthetan consumes the separately proved
exact I/P implementation bridge and the rooted actual positive I-model. -/
theorem weighted_partialI_noncontact_union_null (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).2.1
      (W.carrierᶜ ∪ {x | ∃ hx : x ∈ W.carrier,
        partialIEnvelope θ φ W.carrier W.erealWeight x < W.erealWeight ⟨x, hx⟩}) = 0 := by
  let B := sourceIEnvelope θ φ
  have hmodel := PartialEquilibriumEnergy.iEnvelope_model_of_positive ω hφ hφpos
  have hB : (ofFixedModel n M).IsThetaPSH θ B := hmodel.thetaPSH
  have hBpos : 0 < sourcePotentialNonPluripolarMeasure θ B hB univ := hmodel.choose_spec.2
  let Ienv := partialIEnvelope θ φ W.carrier W.erealWeight
  let J := partialEnvelope θ B W.carrier W.erealWeight
  have heq : Ienv = J :=
    PartialEnvelopeIComparison.partialIEnvelope_eq_partialEnvelope_iEnvelope hφ W.carrier W.erealWeight
  have hI := (weighted_partials_genuine ω hφ hφpos W).2.1
  have hJ := (weighted_partials_genuine ω hB hBpos W).1
  have hm : sourcePotentialNonPluripolarMeasure θ Ienv hI =
      sourcePotentialNonPluripolarMeasure θ J hJ :=
    MaxMassDecomposition.diagonalPotentialMeasure_congr
      ((isThetaPSH_iff_nativeThetaPotential θ Ienv).mp hI)
      ((isThetaPSH_iff_nativeThetaPotential θ J).mp hJ) heq
  change sourcePotentialNonPluripolarMeasure θ Ienv hI
    (W.carrierᶜ ∪ {x | ∃ hx : x ∈ W.carrier, Ienv x < W.erealWeight ⟨x, hx⟩}) = 0
  rw [hm]
  have hset : {x | ∃ hx : x ∈ W.carrier, Ienv x < W.erealWeight ⟨x, hx⟩} =
      {x | ∃ hx : x ∈ W.carrier, J x < W.erealWeight ⟨x, hx⟩} := by
    ext x
    rw [heq]
  rw [hset]
  exact weighted_partial_noncontact_union_null ω hB hBpos W

/-- WHOLE original cor:suppthetan / eq:thetandoesnotcharge1, BOTH distinct
original partial operators and their OWN actual non-pluripolar measures. -/
theorem weighted_partial_equilibrium_noncontact_null (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : SGPT.Bergman.WeightedSubset.WeightedSubset n M) :
    sourcePotentialNonPluripolarMeasure θ (partialEnvelope θ φ W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).1
      (W.carrierᶜ ∪ {x | ∃ hx : x ∈ W.carrier,
        partialEnvelope θ φ W.carrier W.erealWeight x < W.erealWeight ⟨x, hx⟩}) = 0 ∧
    sourcePotentialNonPluripolarMeasure θ (partialIEnvelope θ φ W.carrier W.erealWeight)
      (weighted_partials_genuine ω hφ hφpos W).2.1
      (W.carrierᶜ ∪ {x | ∃ hx : x ∈ W.carrier,
        partialIEnvelope θ φ W.carrier W.erealWeight x < W.erealWeight ⟨x, hx⟩}) = 0 :=
  ⟨weighted_partial_noncontact_union_null ω hφ hφpos W,
    weighted_partialI_noncontact_union_null ω hφ hφpos W⟩

end SGPT.Bergman.PartialEquilibriumMeasure
