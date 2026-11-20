import SGPT.Envelopes.SourceRelativeEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedConcavity
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyIncreasingGlobalAE

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The coefficient-preserving closed-form dictionary returns the entire same form. -/
theorem sourceNativeAtlasForm_roundTrip (θ : ClosedRealOneOneForm n M) :
    atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
  rcases θ with ⟨θ, hθ⟩
  cases θ
  rfl

/-- The original Kähler background has the genuine original zero potential. -/
theorem sourceKahlerZero_thetaPSH (ω : KahlerBackground n M) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas ω.form) (fun _ => 0) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact (LocalPotentials.isThetaPshPotential_zero_iff ω.form).mpr ω.isSemipositive

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual source volume ω^n, as the source diagonal product at zero. -/
def sourceKahlerVolume (ω : KahlerBackground n M) : Measure M :=
  sourcePotentialNonPluripolarMeasure (nativeClosedFormToAtlas ω.form)
    (fun _ => 0) (sourceKahlerZero_thetaPSH ω)

omit [BorelSpace M] in
/-- Source volume and native smooth positive Kähler volume are the identical measure. -/
theorem sourceKahlerVolume_eq_native (ω : KahlerBackground n M) :
    sourceKahlerVolume ω = IntegrationCurrent.kahlerVolume ω := by
  unfold sourceKahlerVolume sourcePotentialNonPluripolarMeasure IntegrationCurrent.kahlerVolume
  simp only [sourceNativeAtlasForm_roundTrip]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- Both entire indexed supremum operations use the same neighborhood regularization. -/
theorem sourceUscSup_eq_native {I : Type*} (ui : I → M → EReal) :
    SGPT.PSH.uscSup ui = uscRegularization (⨆ i, ui i) := by
  unfold SGPT.PSH.uscSup
  apply congrArg uscRegularization
  funext x
  simp only [iSup_apply]

variable [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- Whole original full-mass characterization by the ordinary singularity envelope. -/
theorem sourceRelativeFullMass_iff_envelope_eq (ω : KahlerBackground n M)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceRelativeFullMass θ φ u hφ ↔ sourceSingularityEnvelope θ u = φ := by
  rw [sourceRelativeFullMass_iff_native, sourceSingularityEnvelope_eq_native]
  exact RelativePreceqStatements.relativeFullMassPreceq_iff_singularityEnvelope_eq ω
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

omit [ConnectedSpace M] in
/-- Extended concavity on the whole original preceq class and closed interval. -/
theorem sourceRelativeEnergy_extended_concave (ω : KahlerBackground n M)
    (hu : SourceRelativePSH θ φ u) (hv : SourceRelativePSH θ φ v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : EReal) * sourceRelativeEnergy θ φ u hφ +
      ((1 - t : ℝ) : EReal) * sourceRelativeEnergy θ φ v hφ ≤
      sourceRelativeEnergy θ φ (ThetaPshConvexCombination.convexComb t u v) hφ := by
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelEnergyExtendedConcavity.energy_concave ω _ hφ.toNative
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) hu.2 hv.2 ht0 ht1

omit [ConnectedSpace M] in
/-- Original full mass propagates through the actual singularity-order sandwich. -/
theorem sourceRelativeFullMass_upward (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativePSH θ φ v)
    (huv : SGPT.PSH.SingularityLE u v) : SourceRelativeFullMass θ φ v hφ := by
  apply (sourceRelativeFullMass_iff_native θ φ v hφ).mpr
  exact RelativePreceqStatements.relativeFullMassPreceq_of_singularity_between ω
    ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) huv hv.2

/-- Original finite energy propagates through the full singularity-order sandwich. -/
theorem sourceRelativeFiniteEnergy_upward (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativePSH θ φ v)
    (huv : SGPT.PSH.SingularityLE u v) : SourceRelativeFiniteEnergy θ φ v hφ := by
  apply (sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mpr
  exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_singularity_between ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) huv hv.2

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The third original upward-closure clause retains the two actual comparisons. -/
theorem sourceRelativeEInfinity_upward
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativePSH θ φ v)
    (huv : SGPT.PSH.SingularityLE u v) : SourceRelativeEInfinity θ φ v :=
  ⟨hv.1, hv.2, hu.2.2.trans huv⟩

/-- Original full-mass rooftop closure, with genuine native roof internally produced. -/
theorem sourceRelativeFullMass_rooftop (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ) :
    SourceRelativeFullMass θ φ (thetaRooftop θ u v) hφ := by
  have hr := RelativePreceqClasses.relativeFullMassPreceq_rooftop ω
    ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFullMass_iff_native θ φ v hφ).mp hv)
  rw [sourceThetaRooftop_eq_native hu.choose hv.choose hr.plurisubharmonic]
  exact (sourceRelativeFullMass_iff_native θ φ _ hφ).mpr hr

omit [BorelSpace M] in
/-- Original same-type rooftop closure, for the unchanged raw source supremum. -/
theorem sourceRelativeEInfinity_rooftop (hφ : SourceModelPotential θ φ)
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativeEInfinity θ φ v) :
    SourceRelativeEInfinity θ φ (thetaRooftop θ u v) := by
  have hr := SingularModelEnergyFiniteDiamond.relativeEInfinity_rooftop
    hφ.toNative.plurisubharmonic
    ((sourceRelativeEInfinity_iff_native θ φ u).mp hu)
    ((sourceRelativeEInfinity_iff_native θ φ v).mp hv)
  rw [sourceThetaRooftop_eq_native hu.1 hv.1 hr.1]
  exact (sourceRelativeEInfinity_iff_native θ φ _).mpr hr

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Whole original PSH preceq class is closed under closed-interval combinations. -/
theorem sourceRelativePSH_convexComb
    (hu : SourceRelativePSH θ φ u) (hv : SourceRelativePSH θ φ v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SourceRelativePSH θ φ (ThetaPshConvexCombination.convexComb t u v) := by
  rcases eq_or_lt_of_le ht0 with hzero | ht0'
  · subst t
    rw [sourceConvexComb_zero]
    exact hv
  rcases eq_or_lt_of_le ht1 with hone | ht1'
  · subst t
    rw [sourceConvexComb_one]
    exact hu
  have hhigh : ThetaPshConvexCombination.convexComb t u v ≤ fun x => max (u x) (v x) := by
    have h := ThetaPshConvexCombination.convexComb_mono ht0 ht1
      (show u ≤ fun x => max (u x) (v x) from fun _ => le_max_left _ _)
      (show v ≤ fun x => max (u x) (v x) from fun _ => le_max_right _ _)
    rwa [ThetaCapacity.convexComb_self ht0' ht1'] at h
  exact ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr
    (ThetaPshConvexCombination.isThetaPshPotential_convexComb
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) ht0' ht1'),
    (MoreSingularOn.of_le fun x _ => hhigh x).trans
      (DominationPrincipleReduction.moreSingularOn_max hu.2 hv.2)⟩

/-- Actual full-mass rooftop and upward closure give closed-interval convexity. -/
theorem sourceRelativeFullMass_convexComb (ω : KahlerBackground n M)
    (hu : SourceRelativeFullMass θ φ u hφ) (hv : SourceRelativeFullMass θ φ v hφ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SourceRelativeFullMass θ φ (ThetaPshConvexCombination.convexComb t u v) hφ := by
  rcases eq_or_lt_of_le ht0 with hzero | ht0'
  · subst t
    rw [sourceConvexComb_zero]
    exact hv
  rcases eq_or_lt_of_le ht1 with hone | ht1'
  · subst t
    rw [sourceConvexComb_one]
    exact hu
  have hrel := sourceRelativePSH_convexComb
    (show SourceRelativePSH θ φ u from ⟨hu.choose, hu.choose_spec.1⟩)
    (show SourceRelativePSH θ φ v from ⟨hv.choose, hv.choose_spec.1⟩) ht0 ht1
  have hlow : thetaRooftop θ u v ≤ ThetaPshConvexCombination.convexComb t u v := by
    have h := ThetaPshConvexCombination.convexComb_mono ht0 ht1
      (thetaRooftop_le_left θ u v) (thetaRooftop_le_right θ u v)
    rwa [ThetaCapacity.convexComb_self ht0' ht1'] at h
  exact sourceRelativeFullMass_upward ω (sourceRelativeFullMass_rooftop ω hu hv) hrel
    (MoreSingularOn.of_le fun x _ => hlow x)

/-- Actual E1 rooftop barrier closure gives the entire closed-interval convexity. -/
theorem sourceRelativeFiniteEnergy_convexComb (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SourceRelativeFiniteEnergy θ φ (ThetaPshConvexCombination.convexComb t u v) hφ := by
  rcases eq_or_lt_of_le ht0 with hzero | ht0'
  · subst t
    rw [sourceConvexComb_zero]
    exact hv
  rcases eq_or_lt_of_le ht1 with hone | ht1'
  · subst t
    rw [sourceConvexComb_one]
    exact hu
  apply (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr
  exact SingularModelDarvasDiagonalComparison.relativeFiniteEnergyPreceq_convexComb ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv) ht0' ht1'

omit [ConnectedSpace M] in
/-- Every original bounded full-mass family has a genuine original full-mass supremum. -/
theorem sourceRelativeFullMass_uscSup {I : Type*} [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal} {C : ℝ}
    (hui : ∀ i, SourceRelativeFullMass θ φ (ui i) hφ)
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    SourceRelativeFullMass θ φ (SGPT.PSH.uscSup ui) hφ := by
  rw [sourceUscSup_eq_native, sourceRelativeFullMass_iff_native]
  exact SingularModelBoundedSupremumEnergyClosure.relativeFullMassPreceq_uscRegularization_iSup ω
    (fun i => (sourceRelativeFullMass_iff_native θ φ (ui i) hφ).mp (hui i)) hC

omit [ConnectedSpace M] in
/-- Every original bounded finite-energy family has its actual source E1 supremum. -/
theorem sourceRelativeFiniteEnergy_uscSup {I : Type*} [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal} {C : ℝ}
    (hui : ∀ i, SourceRelativeFiniteEnergy θ φ (ui i) hφ)
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    SourceRelativeFiniteEnergy θ φ (SGPT.PSH.uscSup ui) hφ := by
  rw [sourceUscSup_eq_native, sourceRelativeFiniteEnergy_iff_native]
  exact SingularModelBoundedSupremumEnergyClosure.relativeFiniteEnergyPreceq_uscRegularization_iSup ω
    (fun i => (sourceRelativeFiniteEnergy_iff_native θ φ (ui i) hφ).mp (hui i)) hC

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every original bounded same-type family has its actual original same-type supremum. -/
theorem sourceRelativeEInfinity_uscSup {I : Type*} [Nonempty I]
    (hφ : SourceModelPotential θ φ) {ui : I → M → EReal} {C : ℝ}
    (hui : ∀ i, SourceRelativeEInfinity θ φ (ui i))
    (hC : ∀ i x, ui i x ≤ (C : EReal)) :
    SourceRelativeEInfinity θ φ (SGPT.PSH.uscSup ui) := by
  rw [sourceUscSup_eq_native, sourceRelativeEInfinity_iff_native]
  exact SingularModelBoundedSupremumEnergyClosure.relativeEInfinity_uscRegularization_iSup
    (hφ := hφ.toNative) (fun i => (sourceRelativeEInfinity_iff_native θ φ (ui i)).mp (hui i)) hC

omit [ConnectedSpace M] in
/-- Both actual extended and finite real source energies converge on general decreasing E1 nets. -/
theorem sourceRelativeFiniteEnergy_decreasing_net
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, SourceRelativeFiniteEnergy θ φ (ui i) hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    (hanti : ∀ x, Antitone (fun i => ui i x)) (hinf : v = fun x => ⨅ i, ui i x) :
    Tendsto (fun i => sourceRelativeEnergy θ φ (ui i) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ)) ∧
    Tendsto (fun i => (sourceRelativeEnergy θ φ (ui i) hφ).toReal) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ).toReal) := by
  have hnui := fun i => (sourceRelativeFiniteEnergy_iff_native θ φ (ui i) hφ).mp (hui i)
  have hnv := (sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv
  have he : Tendsto (fun i => sourceRelativeEnergy θ φ (ui i) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ)) := by
    simp only [sourceRelativeEnergy_eq_native]
    exact SingularModelEnergyDecreasingNets.energy_tendsto_of_directed_antitone ω _ hφ.toNative
      (fun i => (hnui i).1.plurisubharmonic) (Classical.arbitrary I)
      (hnui (Classical.arbitrary I)).1.relativePSHPreceq.2 hanti
      (fun x => by rw [hinf]; exact tendsto_atTop_iInf (hanti x))
  have htop : sourceRelativeEnergy θ φ v hφ ≠ ⊤ := by
    rw [sourceRelativeEnergy_eq_native]
    exact RelativePreceqClasses.energy_ne_top_of_preceq hnv.1.relativePSHPreceq
  have hbot : sourceRelativeEnergy θ φ v hφ ≠ ⊥ := by
    rw [sourceRelativeEnergy_eq_native]
    exact (SingularModelFiniteEnergyPreceq.bot_lt_energy ω hnv).ne'
  exact ⟨he, (EReal.tendsto_toReal htop hbot).comp he⟩

/-- The original actual-volume AE increasing directed branch, with no regularized-limit premise. -/
theorem sourceRelativeFiniteEnergy_increasing_ae_net
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, SourceRelativeFiniteEnergy θ φ (ui i) hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    (hmono : ∀ x, Monotone (fun i => ui i x))
    (hl : ∀ᵐ x ∂sourceKahlerVolume ω,
      Tendsto (fun i => ui i x) atTop (𝓝 (v x))) :
    Tendsto (fun i => sourceRelativeEnergy θ φ (ui i) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ)) ∧
    Tendsto (fun i => (sourceRelativeEnergy θ φ (ui i) hφ).toReal) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ).toReal) := by
  rw [sourceKahlerVolume_eq_native] at hl
  simp only [sourceRelativeEnergy_eq_native]
  exact ⟨SingularModelEnergyIncreasingGlobalAE.energy_tendsto_of_directed_monotone_ae_kahlerVolume ω
    (fun i => (sourceRelativeFiniteEnergy_iff_native θ φ (ui i) hφ).mp (hui i))
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv) hmono hl,
    SingularModelEnergyIncreasingGlobalAE.toReal_energy_tendsto_of_directed_monotone_ae_kahlerVolume ω
    (fun i => (sourceRelativeFiniteEnergy_iff_native θ φ (ui i) hφ).mp (hui i))
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv) hmono hl⟩

/-- Whole original monotone E1 continuity, retaining both alternatives in one public root. -/
theorem sourceRelativeFiniteEnergy_monotone_net
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, SourceRelativeFiniteEnergy θ φ (ui i) hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ)
    (hcase : ((∀ x, Antitone (fun i => ui i x)) ∧ v = fun x => ⨅ i, ui i x) ∨
      ((∀ x, Monotone (fun i => ui i x)) ∧ ∀ᵐ x ∂sourceKahlerVolume ω,
        Tendsto (fun i => ui i x) atTop (𝓝 (v x)))) :
    Tendsto (fun i => sourceRelativeEnergy θ φ (ui i) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ)) ∧
    Tendsto (fun i => (sourceRelativeEnergy θ φ (ui i) hφ).toReal) atTop
      (𝓝 (sourceRelativeEnergy θ φ v hφ).toReal) := by
  rcases hcase with ⟨hanti, hinf⟩ | ⟨hmono, hl⟩
  · exact sourceRelativeFiniteEnergy_decreasing_net ω hui hv hanti hinf
  · exact sourceRelativeFiniteEnergy_increasing_ae_net ω hui hv hmono hl

end SGPT.PSH.VariableComplexAtlas
