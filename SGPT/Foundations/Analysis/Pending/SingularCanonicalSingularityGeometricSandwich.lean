import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityTailRooftopModels
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityUpperEnvelopeInfimum

set_option autoImplicit false

/-! # Actual geometric monotone singularity sandwiches

SGPT PDF0228--0231 Proposition 6.2.3 on the natural geometric native-step
domain. Actual tails, increasing convergence, equal-mass comparison and
global P-classification internally produce both native limits. The target
is only genuine PSH, and no equality of the raw increasing supremum with
the target model is assumed or claimed. Fast subsequence extraction remains
separate from this geometric-domain consumer.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricSandwich

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  RelativeDarvasDistance DiagonalMass MixedMass ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularModelDarvasFiniteRooftopChains
  SingularCanonicalSingularityTailRooftopModels SingularCanonicalSingularityUpperEnvelopeInfimum
  SingularCanonicalSingularityTailSupremumMajorants SingularCanonicalSingularityMassLipschitz
  SingularCanonicalSingularityIncreasing SingularGlobalPOrder SingularCanonicalDistanceZeroPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual upper and lower tails form a genuine monotone native sandwich;
the lower regularized supremum has the actual target P-envelope. -/
theorem exists_monotone_sandwich_of_geometric_steps_of_tendsto
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ A r : ℝ}
    (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property)
    (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
    let D : ℝ := 3 * ((n : ℝ) + 1) * C
    let L : ℝ := D * A * (C / (1 - C * r) + 1)
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    L / (1 - r) < δ →
      (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) → Tendsto ui atTop (𝓝 u) →
      ∃ η ψ : ℕ → ThetaPshL1 θ.val,
        (∀ i, (η i).val = ⨅ k, finiteTailRooftop θ (fun j => (ui j).val) i k) ∧
        (∀ i, (ψ i).val = uscRegularization (⨆ j, (ui (i + j)).val)) ∧
        (∀ i, IsModelPotential θ (η i).val) ∧ Monotone (fun i => (η i).val) ∧
        (∀ x, Antitone fun i => (ψ i).val x) ∧
        (∀ i, (η i).val ≤ (ui i).val ∧ (ui i).val ≤ (ψ i).val) ∧
        Tendsto η atTop (𝓝 u) ∧ Tendsto ψ atTop (𝓝 u) ∧
        singularityEnvelope θ.val (uscRegularization (⨆ i, (η i).val)) =
          singularityEnvelope θ.val u.val := by
  dsimp only
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hsmall hstep hlim
  obtain ⟨η, hηeq, hηmodel, hηmono, hηle, _, _, hηmasslim⟩ :=
    exists_increasing_rooftop_models_of_geometric_steps_of_tendsto omega θ hbig ui u
      hmodels hδ hstage hA hr0 hr1 hrC hsmall hstep hlim
  have hB : ∀ i x, (ui i).val x ≤ (0 : EReal) := by
    intro i
    rw [(hmodels i).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (ui i).val
  obtain ⟨ψ, hψeq, hψanti, hψle, _, hψlim⟩ :=
    exists_decreasing_majorants_of_geometric_steps_of_tendsto omega θ hbig ui u
      hB hA hr0 hr1 hrC hstep hlim
  obtain ⟨hupos, hPu, _, _, _, hInf⟩ :=
    upper_envelope_models_iInf_eq_target_envelope omega θ hbig ui u hmodels hδ hstage
      hA hr0 hr1 hrC hstep hlim
  have hη0 : ∀ i x, (η i).val x ≤ (0 : EReal) :=
    fun i x => (hηle i x).trans (hB i x)
  have hS := IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
    (fun i => (η i).property) hη0
  let S : ThetaPshL1 θ.val := ⟨uscRegularization (⨆ i, (η i).val), hS⟩
  have hηSlim : Tendsto η atTop (𝓝 S) :=
    tendsto_native_of_monotone_uniformlyBounded omega θ hbig η hηmono hη0
  have hSmasslim := ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto S).comp hηSlim
  have hfinite (a : ThetaPshL1 θ.val) : diagonalPotentialMass θ a.val a.property ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => a.property.1)).ne
  have hmass : diagonalPotentialMass θ S.val S.property = diagonalPotentialMass θ u.val u.property :=
    (ENNReal.toReal_eq_toReal_iff' (hfinite S) (hfinite u)).mp
      (tendsto_nhds_unique hSmasslim hηmasslim)
  have hSpos : 0 < diagonalPotentialMass θ S.val S.property := hmass.symm ▸ hupos
  have htail (i j : ℕ) (hji : j ≤ i) : (ui i).val ≤ singularityEnvelope θ.val (ψ j).val := by
    have hle : (ui i).val ≤ (ψ j).val := fun x =>
      (hψle i x).trans (hψanti x hji)
    calc
      (ui i).val = singularityEnvelope θ.val (ui i).val := (hmodels i).envelope_eq
      _ ≤ _ := singularityEnvelope_mono (θ := θ.val) (MoreSingularOn.of_le fun x _ => hle x)
  have hcross (i j : ℕ) : (η i).val ≤ singularityEnvelope θ.val (ψ j).val := by
    by_cases hji : j ≤ i
    · exact (hηle i).trans (htail i j hji)
    · exact (hηmono (le_of_not_ge hji)).trans ((hηle j).trans (htail j j le_rfl))
  have hInf' : (⨅ j, singularityEnvelope θ.val (ψ j).val) = singularityEnvelope θ.val u.val := by
    simpa only [hψeq] using hInf
  have hSle : S.val ≤ singularityEnvelope θ.val u.val :=
    (le_iInf fun j => uscRegularization_le
      (upperSemicontinuous_singularityEnvelope θ.val (ψ j).val)
      (iSup_le fun i => hcross i j)).trans_eq hInf'
  have hmassP : diagonalPotentialMass θ S.val S.property =
      diagonalPotentialMass θ (singularityEnvelope θ.val u.val) hPu.plurisubharmonic :=
    hmass.trans (singularityEnvelopeMassPreserving omega θ u.val u.property hPu.plurisubharmonic).symm
  have hrev : singularityEnvelope θ.val u.val ≤ singularityEnvelope θ.val S.val :=
    equalMassLeSingularityEnvelope omega θ S.val (singularityEnvelope θ.val u.val)
      S.property hPu.plurisubharmonic hSpos (singularityEnvelope_le_zero θ.val u.val)
      (MoreSingularOn.of_le fun x _ => hSle x) hmassP
  have hPeq : singularityEnvelope θ.val S.val = singularityEnvelope θ.val u.val :=
    le_antisymm ((singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hSle x)).trans_eq hPu.envelope_eq.symm) hrev
  have hglobal := (sourcePEquivalent_iff_pEquivalentWith omega θ S.property u.property
    hSpos hupos).mpr (pEquivalentWith_iff_envelope_eq.mpr hPeq)
  have hzero : dist S u = 0 := by
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      S.property u.property).mpr hglobal
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hηlim : Tendsto η atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hηdist := tendsto_iff_dist_tendsto_zero.mp hηSlim
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hηdist
    have hi := dist_triangle (η i) S u
    simpa only [hzero, add_zero] using hi)
  exact ⟨η, ψ, hηeq, hψeq, hηmodel, hηmono, hψanti,
    fun i => ⟨hηle i, hψle i⟩, hηlim, hψlim, hPeq⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricSandwich
