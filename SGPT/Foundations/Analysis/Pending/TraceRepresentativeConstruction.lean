import SGPT.Foundations.Analysis.Pending.AnalyticRestrictedApproximantUniformMass
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # Actual trace representatives from genuine restricted QEA sequences -/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  DiagonalMass RelativeEnergy ThetaPshL1Topology
  SingularCanonicalSingularityDistance PluripolarCapacityDichotomy
  ActualDecreasingModelPositiveInfimum

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

private theorem native_limit_of_antitone_positive
    (omegaV β : KahlerBackground k V) {v : ℕ → V → EReal}
    (hv : ∀ j, IsThetaPshPotential β.form.val (v j)) (hanti : Antitone v)
    {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ j, ENNReal.ofReal δ ≤ diagonalPotentialMass β.form (v j) (hv j)) :
    ∃ τ : V → EReal, ∃ hτ : IsModelPotential β.form τ,
      Tendsto (fun j => (⟨v j, hv j⟩ : ThetaPshL1 β.form.val))
        atTop (@nhds (ThetaPshL1 β.form.val)
          (singularityPseudoMetricSpace omegaV β.form
            (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
          ⟨τ, hτ.plurisubharmonic⟩) := by
  let P : ℕ → V → EReal := fun j => singularityEnvelope β.form.val (v j)
  have hP (j : ℕ) : IsModelPotential β.form (P j) := by
    have hpos : 0 < diagonalPotentialMass β.form (v j) (hv j) :=
      (ENNReal.ofReal_pos.mpr hδ).trans_le (hbound j)
    have hp := singularityEnvelope_isThetaPshPotential β.form.val β.form.property.1
      β.form.property.2 (hv j).1.hasSmoothLocalPotentials (v j) (hv j)
    exact ⟨hp, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omegaV β.form (v j) (hv j) hpos).symm,
      (singularityEnvelopeMassPreserving omegaV β.form (v j) (hv j) hp).symm ▸ hpos⟩
  have hPanti : Antitone P := fun i j hij =>
    singularityEnvelope_mono (θ := β.form.val)
      (MoreSingularOn.of_le fun x _ => hanti hij x)
  have hPbound (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass β.form (P j) (hP j).plurisubharmonic :=
    (hbound j).trans_eq
      (singularityEnvelopeMassPreserving omegaV β.form (v j) (hv j)
        (hP j).plurisubharmonic).symm
  have hτ := isModelPotential_iInf_of_uniform_positive_stage_mass omegaV hP hPanti hδ hPbound
  refine ⟨⨅ j, P j, hτ, ?_⟩
  let := singularityPseudoMetricSpace omegaV β.form (isBigClass_kahler β)
  let : TopologicalSpace (ThetaPshL1 β.form.val) :=
    (singularityPseudoMetricSpace omegaV β.form
      (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
  let x : ℕ → ThetaPshL1 β.form.val := fun j => ⟨v j, hv j⟩
  let w : ℕ → ThetaPshL1 β.form.val := fun j => ⟨P j, (hP j).plurisubharmonic⟩
  let τ : ThetaPshL1 β.form.val := ⟨⨅ j, P j, hτ.plurisubharmonic⟩
  have hwlim : Tendsto w atTop (𝓝 τ) :=
    SingularCanonicalSingularityDecreasingModels.tendsto_native_iInf_of_uniform_positive_stage_mass
      omegaV β.form (isBigClass_kahler β) w hP hPanti hδ hPbound
  have hzero (j : ℕ) : dist (x j) (w j) = 0 := by
    rw [dist_eq_singularityDistance_toReal]
    have hd :=
      (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
        omegaV β.form (isBigClass_kahler β) (hv j) (hP j).plurisubharmonic).mpr
        (SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope
          omegaV β.form (hv j))
    change (singularityDistance omegaV β.form (isBigClass_kahler β) (v j) (P j)).toReal = 0
    rw [hd, EReal.toReal_zero]
  have hdist (j : ℕ) : dist (x j) τ = dist (w j) τ := by
    apply le_antisymm
    · simpa only [hzero j, zero_add] using dist_triangle (x j) (w j) τ
    · have hh := dist_triangle (w j) (x j) τ
      rw [dist_comm (w j) (x j), hzero j, zero_add] at hh
      exact hh
  change Tendsto x atTop (𝓝 τ)
  rw [tendsto_iff_dist_tendsto_zero] at hwlim ⊢
  simpa only [hdist] using hwlim

/-- Source Definition 8.1.1 with actual approximation, admissible Kähler
background, genuine restricted readers and the native canonical metric. -/
def IsTraceRepresentativeAlong {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (u : M → EReal) (τ : V → EReal) : Prop :=
  (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0 ∧
    ∃ (θ : ClosedRealOneOneForm n M) (ε : ℕ → ℝ) (uSeq : ℕ → M → EReal),
      IsQuasiEquisingularApproximation omega θ u ε uSeq ∧
      ∃ β : KahlerBackground k V,
        IsAdmissibleTraceBackground hι omega θ ε β.form ∧
        ∃ hτ : IsThetaPshPotential β.form.val τ,
          ∃ hterms : ∀ j, IsThetaPshPotential β.form.val (fun y => uSeq j (ι y)),
            Tendsto (fun j => (⟨fun y => uSeq j (ι y), hterms j⟩ : ThetaPshL1 β.form.val))
              atTop (@nhds (ThetaPshL1 β.form.val)
                (singularityPseudoMetricSpace omegaV β.form
                  (isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
                ⟨τ, hτ⟩)

/-- The actual QEA, generic infimum, and target geometry internally
produce a trace representative and its positive-mass model realization. -/
theorem exists_of_quasiEquisingularApproximation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ τ : V → EReal, IsTraceRepresentativeAlong omega omegaV hι u τ ∧
      ∃ β : KahlerBackground k V, IsModelPotential β.form τ := by
  obtain ⟨C, hC, hadm, hterms, δ, hδ, hbound⟩ :=
    AnalyticRestrictedApproximantUniformMass.exists_admissible_background_uniform_positive_restricted_mass
      omegaV happ hι hgeneric
  let β : KahlerBackground k V := ⟨C • omegaV.form, hadm.1⟩
  have hanti : Antitone (fun j y => uSeq j (ι y)) := fun i j hij y =>
    happ.term_antitone (ι y) hij
  obtain ⟨τ, hτ, hlim⟩ := native_limit_of_antitone_positive
    omegaV β hterms hanti hδ hbound
  refine ⟨τ, ?_, β, hτ⟩
  exact ⟨hgeneric, θ, ε, uSeq, happ, β, hadm, hτ.plurisubharmonic, hterms, hlim⟩

end

end SGPT.Foundations.Analysis.Pending.TraceRepresentativeConstruction
