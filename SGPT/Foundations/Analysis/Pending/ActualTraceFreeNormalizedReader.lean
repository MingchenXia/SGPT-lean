import SGPT.Foundations.Analysis.Pending.VaryingIModelNativeGlobalClass
import SGPT.Foundations.Analysis.Pending.NumericalTraceMass
import SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeStageGlobalPOrder
import SGPT.Foundations.Analysis.Pending.PositiveReferenceGlobalPOrder
import SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIGoodTraceRepresentative

set_option autoImplicit false

/-! # Literal normalized trace from the actual shrinking restricted sequence

Copy--4 `lem:trace-approximants`: the reader is identified through actual
positive original mass and full approximation fields, not a compatibility
certificate or a zero-mass fixed-background classification.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualTraceFreeNormalizedReader

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground FirstPass.POrder
  TraceRepresentativeConstruction PositiveNormalizedTrace NumericalTraceMass DiagonalMass
  TraceFreeLimit ThetaPshL1Topology SingularCanonicalSingularityDistance SingularGlobalPOrder
  PluripolarCapacityDichotomy IEnvelopeVaryingBackgroundModelInfimum

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Full trace and approximation fields internally identify the exact
shrinking-background trace-free reader with the positive normalized trace. -/
theorem traceFreeLimit_eq_normalizedTraceAlong
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M) {U : M → EReal}
    (hdefined : HasPositiveTraceRepresentativeAlong omega omegaV hι θ U)
    {ε : ℕ → ℝ} {USeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ U ε USeq)
    (hεpos : ∀ j, 0 < ε j) :
    traceFreeLimit (ClosedRealOneOneForm.pullback hι θ)
      (ClosedRealOneOneForm.pullback hι omega.form) ε (fun j y => USeq j (ι y)) =
      normalizedTraceAlong omega omegaV hι θ U hdefined := by
  classical
  let γ := ClosedRealOneOneForm.pullback hι θ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let A := normalizedTraceAlong omega omegaV hι θ U hdefined
  have hA : IsModelPotential γ A :=
    (normalizedTraceAlong_models omega omegaV hι θ U hdefined).1
  have hIA : IsIModelPotential γ.val A :=
    (normalizedTraceAlong_models omega omegaV hι θ U hdefined).2
  have hTA : IsTraceRepresentativeAlong omega omegaV hι U A :=
    NormalizedTraceBackgroundMonotonicity.isTraceRepresentativeAlong_normalizedTraceAlong
      omega omegaV hι θ U hdefined
  have hg := hTA.1
  let β : ℕ → ClosedRealOneOneForm k V := fun j => γ + ε j • ρ.form
  let R : ℕ → V → EReal := fun j y => USeq j (ι y)
  have hR (j : ℕ) : IsThetaPshPotential (β j).val (R j) := by
    simpa only [NefCoreKahlerCurrent.pullback_add_smul] using
      AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
        happ hι hg j
  have hAβ (j : ℕ) : IsThetaPshPotential (β j).val A :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hA.plurisubharmonic
      (KahlerDomination.isSemipositive_smul ρ.isSemipositive (hεpos j).le)
  have hA0 : A ≤ 0 := by
    rw [hA.envelope_eq]
    exact singularityEnvelope_le_zero γ.val A
  obtain ⟨_, _, K, hadm, _, _⟩ :=
    QuasiEquisingularIGoodTraceRepresentative.exists_iGood_traceRepresentative_of_quasiEquisingularApproximation
      ρ happ hι hg
  have hAK : IsThetaPshPotential K.form.val A := by
    have hx := LocalPotentials.isThetaPshPotential_add_of_semipositive (hAβ 0) (hadm.2 0)
    simpa only [NefCoreKahlerCurrent.pullback_add_smul, β, γ, ρ, add_sub_cancel] using hx
  have hsource (j : ℕ) : SourcePOrder (n := k) A (R j) :=
    TraceRepresentativeStageGlobalPOrder.sourcePOrder_restricted_stage_of_isTraceRepresentativeAlong
      omegaV ρ hι hTA happ K hadm hAK j
  have hRpos (j : ℕ) : HasPositivePotentialMass (β j) (R j) (hR j) := by
    have hlow := AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
      ρ.isSemipositive (hεpos j) hA.plurisubharmonic (hAβ j)
    have hmass : diagonalPotentialMass (β j) A (hAβ j) ≤
        diagonalPotentialMass (β j) (R j) (hR j) :=
      ActualMixedMassGlobalPMonotone.globalMixedMass_mono_of_sourcePOrder
        ρ (fun _ => hAβ j) (fun _ => hR j) (fun _ => hsource j)
    exact hA.positive_mass.trans_le (hlow.trans hmass)
  let P : ℕ → V → EReal := fun j => singularityEnvelope (β j).val (R j)
  have hP (j : ℕ) : IsModelPotential (β j) (P j) := by
    have hp := singularityEnvelope_isThetaPshPotential (β j).val
      (β j).property.1 (β j).property.2 (hR j).1.hasSmoothLocalPotentials (R j) (hR j)
    exact ⟨hp, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      ρ (β j) (R j) (hR j) (hRpos j)).symm,
      (singularityEnvelopeMassPreserving ρ (β j) (R j) (hR j) hp).symm ▸ hRpos j⟩
  have hPI (j : ℕ) : IsIModelPotential (β j).val (P j) := by
    have hanalytic := AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
      hι (happ.term_hasAnalyticSingularityType j)
    have heq := (AnalyticPotentialsIGood.iGoodWith_of_analytic_type_of_positive_mass
      ρ (hR j) hanalytic (hRpos j)).envelope_eq
    change IsIModelPotential (β j).val (singularityEnvelope (β j).val (R j))
    rw [heq]
    exact iSingularityEnvelope_isIModelPotential (β j).val (β j).property.1
      (β j).property.2 (hR j).1.hasSmoothLocalPotentials (R j) (hR j)
  have hAP (j : ℕ) : A ≤ P j :=
    (self_le_singularityEnvelope (hAβ j) hA0).trans
      (PositiveReferenceGlobalPOrder.pOrderWith_of_sourcePOrder_of_positive_right_mass
        ρ (β j) (hAβ j) (hR j) (hRpos j) (hsource j))
  have hanti : Antitone P := fun i j hij => singularityEnvelope_antitone
    ρ.isSemipositive happ.error_antitone
      (fun y l m hlm => happ.term_antitone (ι y) hlm) hij
  let H : V → EReal := ⨅ j, P j
  have hH : IsThetaPshPotential γ.val H :=
    isThetaPshPotential_iInf_varying_models ρ γ happ.error_antitone happ.error_tendsto hP hanti
  have hHpos : HasPositivePotentialMass γ H hH := hA.positive_mass.trans_le
    (diagonalPotentialMass_mono_of_kahler ρ hA.plurisubharmonic hH
      (MoreSingularOn.of_le fun y _ => (le_iInf hAP) y))
  let Γ := γ + (ε 0 + 1) • ρ.form
  have ht : 0 < ε 0 + 1 := by linarith [hεpos 0]
  have hΓ : IsBigClass (RealBottChern.ofRepresentative Γ) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
      ρ γ hA.plurisubharmonic ht
  have hdiff (j : ℕ) : (Γ - β j).val.IsSemipositive := by
    have heq : Γ - β j = (ε 0 + 1 - ε j) • ρ.form := by
      dsimp only [Γ, β]
      module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ρ.isSemipositive
      (by linarith [happ.error_antitone (Nat.zero_le j)])
  have hlift (j : ℕ) {p : V → EReal} (hp : IsThetaPshPotential (β j).val p) :
      IsThetaPshPotential Γ.val p := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdiff j)
  have hGR (j : ℕ) : IsThetaPshPotential Γ.val (R j) := hlift j (hR j)
  have hGP (j : ℕ) : IsThetaPshPotential Γ.val (P j) := hlift j (hP j).plurisubharmonic
  have hGA : IsThetaPshPotential Γ.val A :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hA.plurisubharmonic
      (KahlerDomination.isSemipositive_smul ρ.isSemipositive ht.le)
  have hGApos : HasPositivePotentialMass Γ A hGA := hA.positive_mass.trans_le
    (AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul
      ρ.isSemipositive ht hA.plurisubharmonic hGA)
  have hgoodA : IGoodWith γ A hA.plurisubharmonic :=
    ⟨hA.positive_mass, hA.envelope_eq.symm.trans hIA.envelope_eq⟩
  have hgoodGA : IGoodWith Γ A hGA :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
      ρ γ Γ hA.plurisubharmonic hGA hA.positive_mass hGApos).mp hgoodA
  obtain ⟨hRK, hRKlim, _⟩ := TraceRepresentativeAllChoices.native_limit_of_isTraceRepresentativeAlong
    omegaV ρ hι hTA happ K hadm hAK
  have hRlim := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    ρ K.form Γ (isBigClass_kahler K) hΓ atTop hRK hAK hGR hGA).mp hRKlim
  let := singularityPseudoMetricSpace ρ Γ hΓ
  let : TopologicalSpace (ThetaPshL1 Γ.val) :=
    (singularityPseudoMetricSpace ρ Γ hΓ).toUniformSpace.toTopologicalSpace
  let X : ℕ → ThetaPshL1 Γ.val := fun j => ⟨R j, hGR j⟩
  let Y : ℕ → ThetaPshL1 Γ.val := fun j => ⟨P j, hGP j⟩
  let T : ThetaPshL1 Γ.val := ⟨A, hGA⟩
  have hzero (j : ℕ) : dist (X j) (Y j) = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        ρ Γ hΓ (hGR j) (hGP j)).mpr
        (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ρ (β j) (hR j))
    change (singularityDistance ρ Γ hΓ (R j) (P j)).toReal = 0
    rw [hd, EReal.toReal_zero]
  have hdist (j : ℕ) : dist (Y j) T = dist (X j) T := by
    apply le_antisymm
    · have hh := dist_triangle (Y j) (X j) T
      rw [dist_comm (Y j) (X j), hzero j, zero_add] at hh
      exact hh
    · simpa only [hzero j, zero_add] using dist_triangle (X j) (Y j) T
  have hPlim : Tendsto Y atTop (𝓝 T) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hh : Tendsto X atTop (𝓝 T) := hRlim
    simpa only [hdist] using tendsto_iff_dist_tendsto_zero.mp hh
  have hclass := VaryingIModelNativeGlobalClass.sourcePEquivalent_iInf_of_native_varying_iModels
    ρ γ hεpos happ.error_antitone happ.error_tendsto hP hPI hanti hHpos
    hΓ hGP hGA hgoodGA hPlim
  have hIH := VaryingBackgroundIModelGlobalClass.isIModelPotential_iInf_varying_models
    ρ γ hεpos happ.error_antitone happ.error_tendsto hP hPI hanti
  have hPH : singularityEnvelope γ.val H = H := by
    calc singularityEnvelope γ.val H = singularityEnvelope γ.val (iSingularityEnvelope γ.val H) :=
          congrArg (singularityEnvelope γ.val) hIH.envelope_eq
      _ = iSingularityEnvelope γ.val H := singularityEnvelope_iSingularityEnvelope
          γ.val γ.property.1 γ.property.2 hH.1.hasSmoothLocalPotentials H hH
      _ = H := hIH.envelope_eq.symm
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith ρ γ hH hA.plurisubharmonic
    hHpos hA.positive_mass).mp hclass
  have heq := pEquivalentWith_iff_envelope_eq.mp hfixed
  rw [hPH, hA.envelope_eq.symm] at heq
  have hreader : traceFreeLimit (ClosedRealOneOneForm.pullback hι θ)
      (ClosedRealOneOneForm.pullback hι omega.form) ε (fun j y => USeq j (ι y)) = H := by
    funext y
    simp only [traceFreeLimit, H, P, β, γ, ρ, R, iInf_apply]
  exact hreader.trans heq

end
end SGPT.Foundations.Analysis.Pending.ActualTraceFreeNormalizedReader
