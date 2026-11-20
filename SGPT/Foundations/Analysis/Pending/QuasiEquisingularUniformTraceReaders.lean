import SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
import SGPT.Foundations.Analysis.Pending.AnalyticAntitoneIGoodLimit
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback

set_option autoImplicit false

/-! # Actual target geometry chosen before every full approximation row -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformTraceReaders
open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  DiagonalMass RelativeEnergy ThetaPshL1Topology TraceRepresentativeConstruction
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- A single actual target is selected before all full rows. Each row's
literal ordinary-envelope infimum and its complete native reader are produced. -/
theorem exists_uniform_target_full_trace_readers
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    (θ : ClosedRealOneOneForm n M) {ε : ℕ → ℝ} (hε : Antitone ε) :
    ∃ C : ℝ, ∃ hC : 0 < C,
      let β := KahlerBackground.smul hC omegaV
      IsAdmissibleTraceBackground hι omega θ ε β.form ∧
      ∀ (u : M → EReal) (vSeq : ℕ → M → EReal),
        IsQuasiEquisingularApproximation omega θ u ε vSeq →
        (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0 →
        let τ : V → EReal := ⨅ j, singularityEnvelope β.form.val (fun y => vSeq j (ι y))
        ∃ hv : ∀ j, IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)),
        ∃ hτ : IsModelPotential β.form τ,
          IsTraceRepresentativeAlong omega omegaV hι u τ ∧
          Tendsto (fun j => (⟨fun y => vSeq j (ι y), hv j⟩ : ThetaPshL1 β.form.val))
            atTop (@nhds (ThetaPshL1 β.form.val)
              (singularityPseudoMetricSpace omegaV β.form
                (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
              ⟨τ, hτ.plurisubharmonic⟩) := by
  obtain ⟨C, hC, hadm, hmargin⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega omegaV θ hε
  let β := KahlerBackground.smul hC omegaV
  have hβform : β.form = C • omegaV.form := rfl
  refine ⟨C, hC, hadm, ?_⟩
  intro u vSeq happ hgeneric
  have hgamma (j : ℕ) : IsThetaPshPotential (β.form - omegaV.form).val
      (fun y => vSeq j (ι y)) := by
    have hp := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happ hι hgeneric j
    have hplus := LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hmargin j)
    have hforms : ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
        (C • omegaV.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) -
          omegaV.form) = β.form - omegaV.form := by rw [hβform]; module
    simpa only [hforms] using hplus
  have hv (j : ℕ) : IsThetaPshPotential β.form.val (fun y => vSeq j (ι y)) := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hgamma j) omegaV.isSemipositive
  let hzero := isThetaPshPotential_zero omegaV
  let δ : ℝ := (diagonalPotentialMass omegaV.form (fun _ => 0) hzero).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos
    (KahlerVolumePositive.diagonalPotentialMass_zero_pos omegaV).ne'
    (GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omegaV
      (fun _ : Fin k => hzero.1) univ).ne
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass β.form (fun y => vSeq j (ι y)) (hv j) := by
    have hfloor : diagonalPotentialMass omegaV.form (fun _ => 0) hzero ≤
        diagonalPotentialMass β.form (fun y => vSeq j (ι y)) (hv j) := by
      simpa only [sub_add_cancel] using
        AnalyticRestrictedApproximantUniformMass.diagonalPotentialMass_zero_le_add_unit
          omegaV (hgamma j)
    exact ENNReal.ofReal_toReal_le.trans hfloor
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k)
      (fun y => vSeq j (ι y)) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι
      (happ.term_hasAnalyticSingularityType j)
  have hanti : Antitone (fun j y => vSeq j (ι y)) :=
    fun i j hij y => happ.term_antitone (ι y) hij
  obtain ⟨hτ, _hgood, hlim⟩ :=
    AnalyticAntitoneIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omegaV β hv hA hanti hδ hbound
  refine ⟨hv, hτ, ?_, hlim⟩
  exact ⟨hgeneric, θ, ε, vSeq, happ, β, hadm, hτ.plurisubharmonic, hv, hlim⟩

end
end SGPT.Foundations.Analysis.Pending.QuasiEquisingularUniformTraceReaders
