import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricUpperTails
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # A genuine model limit internally constructed from geometric steps

SGPT PDF0229 upper tails and PDF0230--0231 Cauchy argument, on the
uniform-positive geometric sequence precursor. The actual envelopes of
internally produced upper tails form genuine positive decreasing models.
Contact-first infimum construction and native decreasing convergence give
an actual model limit. No target potential or incoming native limit is given.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricModelLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass MixedMass
  SingularCanonicalSingularityDistance SingularCanonicalSingularityGeometricUpperTails
  SingularCanonicalSingularityDecreasingModels ActualDecreasingModelPositiveInfimum
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Original uniform-positive models and geometric native steps internally
produce a genuine model limit, its mass lower bound, and its native limit. -/
theorem exists_model_limit_of_geometric_steps
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (hmodels : ∀ i, IsModelPotential θ (ui i).val)
    {δ A r : ℝ} (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property)
    (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) →
      ∃ U : ThetaPshL1 θ.val, IsModelPotential θ U.val ∧
        ENNReal.ofReal δ ≤ diagonalPotentialMass θ U.val U.property ∧
        Tendsto ui atTop (𝓝 U) ∧
        U.val = ⨅ i, singularityEnvelope θ.val (uscRegularization (⨆ j, (ui (i + j)).val)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hstep
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hB : ∀ i x, (ui i).val x ≤ (0 : EReal) := by
    intro i x
    rw [(hmodels i).envelope_eq]
    exact singularityEnvelope_le_zero θ.val _ x
  obtain ⟨ψ, hψeq, hψanti, hψle, hdist⟩ :=
    exists_decreasing_majorants_of_geometric_steps omega θ hbig ui hB hA hr0 hr1 hrC hstep
  have hδψ (i : ℕ) : ENNReal.ofReal δ ≤ diagonalPotentialMass θ (ψ i).val (ψ i).property :=
    (hstage i).trans (diagonalPotentialMass_mono_of_kahler omega (ui i).property (ψ i).property
      (MoreSingularOn.of_le fun x _ => hψle i x))
  have hΨ (i : ℕ) : IsModelPotential θ (singularityEnvelope θ.val (ψ i).val) := by
    have hpos : 0 < diagonalPotentialMass θ (ψ i).val (ψ i).property :=
      (ENNReal.ofReal_pos.mpr hδ).trans_le (hδψ i)
    have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
      θ.property.2 (ψ i).property.1.hasSmoothLocalPotentials (ψ i).val (ψ i).property
    exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (ψ i).val (ψ i).property hpos).symm,
      (singularityEnvelopeMassPreserving omega θ (ψ i).val (ψ i).property hP).symm ▸ hpos⟩
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
  have hδU : ENNReal.ofReal δ ≤ diagonalPotentialMass θ U.val U.property :=
    le_diagonalPotentialMass_iInf_of_le_stage_masses omega hΨ hanti hδw
  have hwlim : Tendsto w atTop (𝓝 U) :=
    tendsto_native_iInf_of_uniform_positive_stage_mass omega θ hbig w hΨ hanti hδ hδw
  have hzero (i : ℕ) : dist (ψ i) (w i) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (ψ i).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (ψ i).property (w i).property).mpr he
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hpow : Tendsto (fun i : ℕ => r ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hbound := ((tendsto_const_nhds (x := C * A)).mul hpow).div_const (1 - C * r)
  simp only [mul_zero, zero_div] at hbound
  have hlim : Tendsto ui atTop (𝓝 U) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp hwlim
    have hupper := hbound.add hd
    simp only [zero_add] at hupper
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hupper
    have htw := dist_triangle (ui i) (ψ i) (w i)
    rw [hzero, add_zero] at htw
    exact (dist_triangle (ui i) (w i) U).trans (add_le_add (htw.trans (hdist i)) le_rfl))
  refine ⟨U, hInf, hδU, hlim, ?_⟩
  simp only [U, w, hψeq]

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricModelLimit
