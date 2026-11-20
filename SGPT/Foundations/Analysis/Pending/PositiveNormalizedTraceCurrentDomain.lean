import SGPT.Foundations.Analysis.Pending.PositiveNormalizedTrace
import SGPT.Foundations.Analysis.Pending.CalibratedQuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.AnalyticAntitoneBigIGoodLimit
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Actual positive normalized trace domain from a genuine current margin -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  TraceRepresentativeConstruction DiagonalMass GlobalNonPluripolar
  ThetaPshL1Topology SingularCanonicalSingularityDistance PositiveNormalizedTrace
  PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

omit [CompactSpace M] in
/-- Actual analytic stage margins internally produce the original positive
pullback-background reader and its full admissible trace predicate. -/
theorem hasPositiveTraceRepresentativeAlong_of_calibrated_stage_margin
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε U)
    {d : ℝ} (hd : 0 < d)
    (hstrict : ∀ j, IsThetaPshPotential (θ - d • omega.form).val (U j))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let κ := KahlerBackground.smul hd ρ
  have hpullSmall : ClosedRealOneOneForm.pullback hι (θ - d • omega.form) =
      η - κ.form := by
    have hsub : θ - d • omega.form = θ + (-d) • omega.form := by module
    rw [hsub, NefCoreKahlerCurrent.pullback_add_smul]
    dsimp only [η, κ, ρ, KahlerBackground.smul_form]
    module
  have hsmall (j : ℕ) : IsThetaPshPotential (η - κ.form).val (fun y => U j (ι y)) := by
    rw [← hpullSmall]
    apply CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hstrict j).1
    · intro x _
      exact happ.term_hasAnalyticSingularityType j (complexChartAt (n := n) x)
        ((complexChartAt (n := n) x).val x)
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x))
    · exact AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero
        happ ι hgeneric j
  have hv (j : ℕ) : IsThetaPshPotential η.val (fun y => U j (ι y)) := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hsmall j) κ.isSemipositive
  have hbig : IsBigClass (RealBottChern.ofRepresentative η) := by
    simpa only [one_smul, sub_add_cancel] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
        κ (η - κ.form) (hsmall 0) zero_lt_one
  let hzero := isThetaPshPotential_zero κ
  let b : ℝ := (diagonalPotentialMass κ.form (fun _ => 0) hzero).toReal
  have hb : 0 < b := ENNReal.toReal_pos
    (KahlerVolumePositive.diagonalPotentialMass_zero_pos κ).ne'
    (globalMixedMeasure_apply_lt_top κ (fun _ : Fin k => hzero.1) univ).ne
  have hbound (j : ℕ) : ENNReal.ofReal b ≤
      diagonalPotentialMass η (fun y => U j (ι y)) (hv j) := by
    have hfloor : diagonalPotentialMass κ.form (fun _ => 0) hzero ≤
        diagonalPotentialMass η (fun y => U j (ι y)) (hv j) := by
      simpa only [sub_add_cancel] using
        AnalyticRestrictedApproximantUniformMass.diagonalPotentialMass_zero_le_add_unit κ (hsmall j)
    exact ENNReal.ofReal_toReal_le.trans hfloor
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k) (fun y => U j (ι y)) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
      hι (happ.term_hasAnalyticSingularityType j)
  have hanti : Antitone (fun j y => U j (ι y)) := fun i j hij y =>
    happ.term_antitone (ι y) hij
  obtain ⟨hτ, _, hlimη⟩ :=
    AnalyticAntitoneBigIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omegaV η hbig hv hA hanti hb hbound
  let τ := ⨅ j, singularityEnvelope η.val (fun y => U j (ι y))
  obtain ⟨C, hC, hadm, _, _, _, _⟩ :=
    AnalyticRestrictedApproximantUniformMass.exists_admissible_background_uniform_positive_restricted_mass
      omegaV happ hι hgeneric
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaV (-η)
  have hCD : 0 < C + D := add_pos hC hD
  let γ := KahlerBackground.smul hCD omegaV
  have hdiff : γ.form - η = (-η + D • omegaV.form) + C • omegaV.form := by
    dsimp only [γ, KahlerBackground.smul_form]
    module
  have hdiffSemi : (γ.form - η).val.IsSemipositive := by
    rw [hdiff]
    intro e z hz v
    exact add_nonneg (hsemi e z hz v)
      (KahlerDomination.isSemipositive_smul omegaV.isSemipositive hC.le e z hz v)
  have henlarge {v : V → EReal} (hp : IsThetaPshPotential η.val v) :
      IsThetaPshPotential γ.form.val v := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp hdiffSemi
  have hτγ : IsThetaPshPotential γ.form.val τ := henlarge hτ.plurisubharmonic
  have hUγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => U j (ι y)) := henlarge (hv j)
  have hadmγ : IsAdmissibleTraceBackground hι omega θ ε γ.form := by
    refine ⟨γ.isKahler, fun j => ?_⟩
    have hform : γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
        (C • omegaV.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)) +
          D • omegaV.form := by
      dsimp only [γ, KahlerBackground.smul_form]
      module
    change (γ.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form)).val.IsSemipositive
    rw [hform]
    intro e z hz v
    exact add_nonneg (hadm.2 j e z hz v)
      (KahlerDomination.isSemipositive_smul omegaV.isSemipositive hD.le e z hz v)
  have hlimγ := (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
    omegaV η γ.form hbig (isBigClass_kahler γ) atTop hv hτ.plurisubharmonic hUγ hτγ).mp hlimη
  exact ⟨τ, ⟨hgeneric, θ, ε, U, happ, γ, hadmγ, hτγ, hUγ, hlimγ⟩,
    hτ.plurisubharmonic, hτ.positive_mass⟩

/-- The actual current margin itself produces every approximation clause,
the positive original restriction reader and the natural normalized domain. -/
theorem hasPositiveTraceRepresentativeAlong_of_current_margin
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {δ : ℝ} (hδ : 0 < δ)
    (hu : IsThetaPshPotential (θ - δ • omega.form).val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι θ u := by
  obtain ⟨ε, U, happ, _, hstrict⟩ :=
    CalibratedQuasiEquisingularApproximation.exists_full_qea_with_original_background_stage_margin
      omega θ hδ hu
  exact hasPositiveTraceRepresentativeAlong_of_calibrated_stage_margin
    omega omegaV hι hpull happ (half_pos hδ) hstrict hgeneric

/-- Exactly the source's positive one-Kähler-enlargement domain:
the literal original PSH potential supplies its unit smaller-background margin. -/
theorem hasPositiveTraceRepresentativeAlong_add_kahler
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    HasPositiveTraceRepresentativeAlong omega omegaV hι (θ + omega.form) u := by
  apply hasPositiveTraceRepresentativeAlong_of_current_margin omega omegaV hι hpull zero_lt_one
  · simpa only [one_smul, add_sub_cancel_right] using hu
  · exact hgeneric

end

end SGPT.Foundations.Analysis.Pending.PositiveNormalizedTraceCurrentDomain
