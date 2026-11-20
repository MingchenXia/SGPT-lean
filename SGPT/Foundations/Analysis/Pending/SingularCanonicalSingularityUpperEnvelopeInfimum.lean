import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityTailSupremumMajorants
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # Actual positive upper-tail envelope infimum

SGPT PDF0228--0229 Step 1 of Proposition 6.2.3, identity (6.15), on the
natural geometric-step sequence domain. The target is only genuine PSH;
actual mass continuity produces its positivity internally. Actual positive
envelope idempotence, uniform-positive decreasing model convergence and
the genuine positive-background classification identify the infimum with
the target envelope. The general subsequence extraction, lower sandwich
and directed-net identity (6.11) remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityUpperEnvelopeInfimum

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  DiagonalMass MixedMass SingularCanonicalSingularityDistance
  SingularCanonicalSingularityTailSupremumMajorants SingularCanonicalSingularityMassLipschitz
  SingularCanonicalSingularityDecreasingModels ActualDecreasingModelPositiveInfimum
  SingularGlobalPEnvelopeBridge SingularGlobalPOrder SingularCanonicalDistanceZeroPEquivalence
  ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem envelope_isModel_of_positive (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hpos : 0 < diagonalPotentialMass θ u hu) :
    IsModelPotential θ (singularityEnvelope θ.val u) := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hu.1.hasSmoothLocalPotentials u hu
  exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
    omega θ u hu hpos).symm,
    (singularityEnvelopeMassPreserving omega θ u hu hP).symm ▸ hpos⟩

/-- Actual positive stage masses and native convergence first produce target
positivity; genuine decreasing upper envelopes then have actual infimum P[u]. -/
theorem upper_envelope_models_iInf_eq_target_envelope
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ A r : ℝ}
    (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property)
    (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) → Tendsto ui atTop (𝓝 u) →
      0 < diagonalPotentialMass θ u.val u.property ∧
      IsModelPotential θ (singularityEnvelope θ.val u.val) ∧
      (∀ i, IsModelPotential θ
        (singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val)))) ∧
      (∀ i, ∃ h : IsThetaPshPotential θ.val
          (singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val))),
        ENNReal.ofReal δ ≤ diagonalPotentialMass θ
          (singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val))) h) ∧
      Antitone (fun i => singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val))) ∧
      (⨅ i, singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val))) =
        singularityEnvelope θ.val u.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hstep hlim
  have hfinite (a : ThetaPshL1 θ.val) : diagonalPotentialMass θ a.val a.property ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => a.property.1)).ne
  have hmass : Tendsto (fun i => (diagonalPotentialMass θ (ui i).val (ui i).property).toReal)
      atTop (𝓝 (diagonalPotentialMass θ u.val u.property).toReal) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hlim
  have hδu : ENNReal.ofReal δ ≤ diagonalPotentialMass θ u.val u.property :=
    ENNReal.ofReal_le_of_le_toReal (ge_of_tendsto hmass (Eventually.of_forall fun i =>
      (ENNReal.ofReal_le_iff_le_toReal (hfinite (ui i))).mp (hstage i)))
  have hup : 0 < diagonalPotentialMass θ u.val u.property :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le hδu
  have hPu := envelope_isModel_of_positive omega u.property hup
  have hB : ∀ i x, (ui i).val x ≤ (0 : EReal) := by
    intro i x
    rw [(hmodels i).envelope_eq]
    exact singularityEnvelope_le_zero θ.val _ x
  obtain ⟨ψ, hψeq, hψanti, hψle, _, hψlim⟩ :=
    exists_decreasing_majorants_of_geometric_steps_of_tendsto omega θ hbig ui u
      hB hA hr0 hr1 hrC hstep hlim
  have hδψ (i : ℕ) : ENNReal.ofReal δ ≤ diagonalPotentialMass θ (ψ i).val (ψ i).property :=
    (hstage i).trans (diagonalPotentialMass_mono_of_kahler omega (ui i).property (ψ i).property
      (MoreSingularOn.of_le fun x _ => hψle i x))
  have hΨ (i : ℕ) : IsModelPotential θ (singularityEnvelope θ.val (ψ i).val) :=
    envelope_isModel_of_positive omega (ψ i).property
      ((ENNReal.ofReal_pos.mpr hδ).trans_le (hδψ i))
  let w : ℕ → ThetaPshL1 θ.val := fun i =>
    ⟨singularityEnvelope θ.val (ψ i).val, (hΨ i).plurisubharmonic⟩
  have hanti : Antitone fun i => (w i).val := by
    intro i j hij
    exact singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hψanti x hij)
  have hδw (i : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (w i).val (hΨ i).plurisubharmonic :=
    (hδψ i).trans_eq (singularityEnvelopeMassPreserving omega θ (ψ i).val
      (ψ i).property (hΨ i).plurisubharmonic).symm
  have hInf := isModelPotential_iInf_of_uniform_positive_stage_mass omega hΨ hanti hδ hδw
  let U : ThetaPshL1 θ.val := ⟨⨅ i, (w i).val, hInf.plurisubharmonic⟩
  have hlimInf : Tendsto w atTop (𝓝 U) :=
    tendsto_native_iInf_of_uniform_positive_stage_mass omega θ hbig w hΨ hanti hδ hδw
  have hzero (i : ℕ) : dist (w i) (ψ i) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (ψ i).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (w i).property (ψ i).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hwlim : Tendsto w atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hψdist := tendsto_iff_dist_tendsto_zero.mp hψlim
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hψdist
    have h := dist_triangle (w i) (ψ i) u
    simpa only [hzero, zero_add] using h)
  have hzReal : dist U u = 0 := by
    have h := hlimInf.dist hwlim
    simp only [dist_self] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig U.property u.property
  have hmzero : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm, EReal.toReal_coe] using hzReal
  have hz : singularityDistance omega θ hbig U.val u.val = 0 := by
    rw [hm, hmzero, EReal.coe_zero]
  have hsource := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
    U.property u.property).mp hz
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith omega θ U.property u.property
    hInf.positive_mass hup).mp hsource
  have heq : U.val = singularityEnvelope θ.val u.val :=
    hInf.envelope_eq.trans (pEquivalentWith_iff_envelope_eq.mp hfixed)
  refine ⟨hup, hPu, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [← hψeq i] using hΨ i
  · intro i
    refine ⟨?_, ?_⟩
    · simpa only [← hψeq i] using (hΨ i).plurisubharmonic
    · simpa only [← hψeq i] using hδw i
  · simpa only [w, hψeq] using hanti
  · simpa only [U, w, hψeq] using heq

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityUpperEnvelopeInfimum
