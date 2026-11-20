import SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionVaryingModelChain
import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
import SGPT.Foundations.Analysis.Pending.TraceRepresentativeGlobalPClass
import SGPT.Foundations.Analysis.Pending.TraceTargetAuxiliaryIndependence

set_option autoImplicit false

/-! # Ordinary positive restriction internally produces a full positive trace domain -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionTraceDomain

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  SingularGlobalPOrder DiagonalMass MixedMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  PluripolarCapacityDichotomy TraceRepresentativeConstruction PositiveNormalizedTrace
  PositiveOrdinaryRestrictionVaryingModelChain IEnvelopeVaryingBackgroundModelInfimum

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The ordinary positive restriction supplies every original-background
mass and full trace field internally, for any actual target auxiliary. -/
theorem hasPositiveTraceRepresentativeAlong_of_positive_ordinary_restriction
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {a : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u a U)
    (hu0 : u ≤ 0)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => u (ι y)))
    (hwpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ)
      (fun y => u (ι y)) hw) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  obtain ⟨b, hbpos, hbanti, hblim, happb, hP, hPanti, hPI, hposInf⟩ :=
    exists_positive_varying_iModel_chain_of_ordinary_restriction
      omega hι hpull happ hu0 hgeneric hw hwpos
  let R : ℕ → V → EReal := fun j y => U j (ι y)
  let P : ℕ → V → EReal := fun j => singularityEnvelope (η + b j • ρ.form).val (R j)
  let Γ : ClosedRealOneOneForm k V := η + (b 0 + 1) • ρ.form
  have ht : 0 < b 0 + 1 := by linarith [hbpos 0]
  have hΓ : IsBigClass (RealBottChern.ofRepresentative Γ) :=
    PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential ρ η hw ht
  have hR (j : ℕ) : IsThetaPshPotential (η + b j • ρ.form).val (R j) := by
    simpa only [NefCoreKahlerCurrent.pullback_add_smul] using
      AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
        happb hι hgeneric j
  have hdiff (j : ℕ) : (Γ - (η + b j • ρ.form)).val.IsSemipositive := by
    have hc : 0 ≤ b 0 + 1 - b j := by linarith [hbanti (Nat.zero_le j)]
    have heq : Γ - (η + b j • ρ.form) = (b 0 + 1 - b j) • ρ.form := by
      dsimp only [Γ]
      module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ρ.isSemipositive hc
  have hlift (j : ℕ) {p : V → EReal}
      (hp : IsThetaPshPotential (η + b j • ρ.form).val p) :
      IsThetaPshPotential Γ.val p := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hdiff j)
  have hGR (j : ℕ) : IsThetaPshPotential Γ.val (R j) := hlift j (hR j)
  have hGP (j : ℕ) : IsThetaPshPotential Γ.val (P j) := hlift j (hP j).plurisubharmonic
  have hGw : IsThetaPshPotential Γ.val (fun y => u (ι y)) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hw
      (KahlerDomination.isSemipositive_smul ρ.isSemipositive ht.le)
  have hGwpos : HasPositivePotentialMass Γ (fun y => u (ι y)) hGw :=
    hwpos.trans_le (DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      ρ ht hw hGw (le_refl _))
  have hwR (j : ℕ) : (fun y => u (ι y)) ≤ R j := by
    intro y
    apply le_of_tendsto (happ.term_tendsto (ι y))
    filter_upwards [eventually_ge_atTop j] with l hl
    exact happ.term_antitone (ι y) hl
  let L : ℝ≥0∞ := diagonalPotentialMass Γ (fun y => u (ι y)) hGw
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top ρ (fun _ : Fin k => hGw.1)).ne
  let δ : ℝ := L.toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hGwpos.ne' hLtop
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤ diagonalPotentialMass Γ (R j) (hGR j) := by
    rw [ENNReal.ofReal_toReal hLtop]
    exact diagonalPotentialMass_mono_of_kahler ρ hGw (hGR j)
      (MoreSingularOn.of_le fun y _ => hwR j y)
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k) (R j) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι
      (happ.term_hasAnalyticSingularityType j)
  have hRanti : Antitone R := fun i j hij y => happ.term_antitone (ι y) hij
  obtain ⟨hτ, hgoodτ, hRlim⟩ :=
    AnalyticAntitoneBigIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      ρ Γ hΓ hGR hA hRanti hδ hbound
  let τ : V → EReal := ⨅ j, singularityEnvelope Γ.val (R j)
  let := singularityPseudoMetricSpace ρ Γ hΓ
  let : TopologicalSpace (ThetaPshL1 Γ.val) :=
    (singularityPseudoMetricSpace ρ Γ hΓ).toUniformSpace.toTopologicalSpace
  let X : ℕ → ThetaPshL1 Γ.val := fun j => ⟨R j, hGR j⟩
  let Y : ℕ → ThetaPshL1 Γ.val := fun j => ⟨P j, hGP j⟩
  let T : ThetaPshL1 Γ.val := ⟨τ, hτ.plurisubharmonic⟩
  have hzero (j : ℕ) : dist (X j) (Y j) = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        ρ Γ hΓ (hGR j) (hGP j)).mpr
        (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
          ρ (η + b j • ρ.form) (hR j))
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
  have hclass : SourcePEquivalent (n := k) (⨅ j, P j) τ :=
    VaryingIModelNativeGlobalClass.sourcePEquivalent_iInf_of_native_varying_iModels
      ρ η hbpos hbanti hblim hP hPI hPanti hposInf hΓ hGP
        hτ.plurisubharmonic hgoodτ hPlim
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ρ (-Γ)
  let K : KahlerBackground k V := KahlerBackground.smul hC ρ
  have hKdiff : (K.form - Γ).val.IsSemipositive := by
    have heq : K.form - Γ = -Γ + C • ρ.form := by
      dsimp only [K, KahlerBackground.smul_form]
      module
    rw [heq]
    exact hsemi
  have hKof {p : V → EReal} (hp : IsThetaPshPotential Γ.val p) :
      IsThetaPshPotential K.form.val p := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp hKdiff
  have hKR (j : ℕ) : IsThetaPshPotential K.form.val (R j) := hKof (hGR j)
  have hKτ : IsThetaPshPotential K.form.val τ := hKof hτ.plurisubharmonic
  have hadm : IsAdmissibleTraceBackground hι omega θ b K.form := by
    refine ⟨K.isKahler, fun j => ?_⟩
    change (K.form - ClosedRealOneOneForm.pullback hι (θ + b j • omega.form)).val.IsSemipositive
    rw [NefCoreKahlerCurrent.pullback_add_smul]
    have heq : K.form - (η + b j • ρ.form) = (K.form - Γ) + (Γ - (η + b j • ρ.form)) := by module
    rw [heq]
    intro e z hz v
    exact add_nonneg (hKdiff e z hz v) (hdiff j e z hz v)
  have hKlim := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    ρ Γ K.form hΓ (isBigClass_kahler K) atTop hGR hτ.plurisubharmonic hKR hKτ).mp hRlim
  have hKlimV := (TraceTargetAuxiliaryIndependence.tendsto_native_iff_auxiliary_choices
    ρ omegaV K.form (isBigClass_kahler K) atTop
      (fun j => (⟨R j, hKR j⟩ : ThetaPshL1 K.form.val)) ⟨τ, hKτ⟩).mp hKlim
  have htraceτ : IsTraceRepresentativeAlong omega omegaV hι u τ :=
    ⟨hgeneric, θ, b, U, happb, K, hadm, hKτ, hKR, hKlimV⟩
  have htraceInf : IsTraceRepresentativeAlong omega omegaV hι u (⨅ j, P j) :=
    TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
      omegaV hι htraceτ hclass.symm
  exact ⟨⨅ j, P j, htraceInf,
    isThetaPshPotential_iInf_varying_models ρ η hbanti hblim hP hPanti, hposInf⟩

end
end SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionTraceDomain
