import SGPT.Foundations.Analysis.Pending.QuasiEquisingularIGoodTraceRepresentative
import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

set_option autoImplicit false

/-! # Every actual trace representative is globally I-good -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeIGood

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground FirstPass.IEnvelope
  TraceRepresentativeConstruction DiagonalMass GlobalNonPluripolar
  ThetaPshL1Topology SingularCanonicalSingularityDistance PluripolarCapacityDichotomy

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- The defining approximation and native limit internally yield a common
background, uniform positive analytic stages and I-goodness of the original reader. -/
theorem iGood_of_isTraceRepresentativeAlong
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} {τ : V → EReal}
    (htrace : IsTraceRepresentativeAlong omega omegaV hι u τ) : IGood (n := k) τ := by
  obtain ⟨hgeneric, θ, ε, uSeq, happ, β₀, _, hτ₀, hv₀, hlim₀⟩ := htrace
  obtain ⟨C, hC, _, hvC, _, _, _⟩ :=
    AnalyticRestrictedApproximantUniformMass.exists_admissible_background_uniform_positive_restricted_mass
      omegaV happ hι hgeneric
  obtain ⟨D, hD, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul
    omegaV (C • omegaV.form - β₀.form)
  have hCD : 0 < C + D + 1 := by linarith
  let γ : KahlerBackground k V := KahlerBackground.smul hCD omegaV
  have hstageForm : (C + D) • omegaV.form + omegaV.form = γ.form := by
    dsimp only [γ, KahlerBackground.smul_form]
    module
  have hvSmall (j : ℕ) : IsThetaPshPotential ((C + D) • omegaV.form).val
      (fun y => uSeq j (ι y)) := by
    simpa only [add_smul] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hvC j) (KahlerDomination.isSemipositive_smul omegaV.isSemipositive hD.le)
  have hvγ (j : ℕ) : IsThetaPshPotential γ.form.val (fun y => uSeq j (ι y)) := by
    simpa only [hstageForm] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hvSmall j) omegaV.isSemipositive
  have hτSmall : IsThetaPshPotential ((C + D) • omegaV.form).val τ := by
    have hform : β₀.form + (C • omegaV.form - β₀.form + D • omegaV.form) =
        (C + D) • omegaV.form := by module
    simpa only [hform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hτ₀ hsemi
  have hτγ : IsThetaPshPotential γ.form.val τ := by
    simpa only [hstageForm] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hτSmall omegaV.isSemipositive
  let hzero := isThetaPshPotential_zero omegaV
  let δ : ℝ := (diagonalPotentialMass omegaV.form (fun _ => 0) hzero).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos
    (KahlerVolumePositive.diagonalPotentialMass_zero_pos omegaV).ne'
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => hzero.1) univ).ne
  have hbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass γ.form (fun y => uSeq j (ι y)) (hvγ j) := by
    have hfloor : diagonalPotentialMass omegaV.form (fun _ => 0) hzero ≤
        diagonalPotentialMass γ.form (fun y => uSeq j (ι y)) (hvγ j) := by
      simpa only [hstageForm] using
        AnalyticRestrictedApproximantUniformMass.diagonalPotentialMass_zero_le_add_unit
          omegaV (hvSmall j)
    exact ENNReal.ofReal_toReal_le.trans hfloor
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k)
      (fun y => uSeq j (ι y)) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
      hι (happ.term_hasAnalyticSingularityType j)
  have hanti : Antitone (fun j y => uSeq j (ι y)) := fun i j hij y =>
    happ.term_antitone (ι y) hij
  obtain ⟨hσ, hI, hσlim⟩ :=
    AnalyticAntitoneIGoodLimit.exists_iGood_native_model_limit_of_analytic_antitone_uniform_mass
      omegaV γ hvγ hA hanti hδ hbound
  let σ : ThetaPshL1 γ.form.val :=
    ⟨⨅ j, singularityEnvelope γ.form.val (fun y => uSeq j (ι y)), hσ.plurisubharmonic⟩
  let T : ThetaPshL1 γ.form.val := ⟨τ, hτγ⟩
  let X : ℕ → ThetaPshL1 γ.form.val := fun j => ⟨fun y => uSeq j (ι y), hvγ j⟩
  have hτlim : Tendsto X atTop (@nhds (ThetaPshL1 γ.form.val)
      (singularityPseudoMetricSpace omegaV γ.form
        (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace T) :=
    (SingularNativeCommonBackground.tendsto_native_iff_kahler_targets
      omegaV β₀ γ atTop hv₀ hτ₀ hvγ hτγ).mp hlim₀
  let := singularityPseudoMetricSpace omegaV γ.form (isBigClass_kahler γ)
  let : TopologicalSpace (ThetaPshL1 γ.form.val) :=
    (singularityPseudoMetricSpace omegaV γ.form
      (isBigClass_kahler γ)).toUniformSpace.toTopologicalSpace
  have hs : Tendsto X atTop (𝓝 σ) := hσlim
  have ht : Tendsto X atTop (𝓝 T) := hτlim
  have hdist : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (dist σ T)) := by
    simpa only [dist_self] using hs.dist ht
  have hdistZero : dist σ T = 0 := tendsto_nhds_unique hdist tendsto_const_nhds
  exact (IGoodGlobalPStability.iGoodWith_of_native_dist_eq_zero omegaV γ.form
    (isBigClass_kahler γ) σ T hI hdistZero).iGood

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeIGood
