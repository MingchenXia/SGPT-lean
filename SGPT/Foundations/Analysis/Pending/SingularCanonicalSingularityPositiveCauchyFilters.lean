import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCompleteness
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive

set_option autoImplicit false

/-! # Actual limits of arbitrary uniformly positive PSH Cauchy filters

SGPT PDF0231--0232 Corollary 6.2.7, complete first Cauchy-net clause,
strengthened to arbitrary incoming filters. Genuine envelope projection
internally produces the actual fixed-threshold model carrier and preserves
all native distances. Its actual proved completeness supplies the model
limit. No NeBot, projected limit, or completeness certificate is an input.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityPositiveCauchyFilters

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularCanonicalSingularityModelMetricSpace SingularCanonicalSingularityModelCompleteness
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine uniformly positive PSH Cauchy image filters internally produce
an actual model limit and native convergence along the original filter. -/
theorem exists_model_limit_of_cauchy_map (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (ui : I → ThetaPshL1 θ.val) {δ : ℝ} (hδ : 0 < δ)
    (hstage : ∀ i, ENNReal.ofReal δ ≤ diagonalPotentialMass θ (ui i).val (ui i).property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Cauchy (map ui F) → ∃ U : ThetaPshL1 θ.val, IsModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ diagonalPotentialMass θ U.val U.property ∧ Tendsto ui F (𝓝 U) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hcauchy
  have : NeBot F := (map_neBot_iff ui).mp hcauchy.1
  have hP (i : I) : IsThetaPshPotential θ.val (singularityEnvelope θ.val (ui i).val) :=
    singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (ui i).property.1.hasSmoothLocalPotentials (ui i).val (ui i).property
  have hmodels (i : I) : IsModelPotential θ (singularityEnvelope θ.val (ui i).val) := by
    have hpos : 0 < diagonalPotentialMass θ (ui i).val (ui i).property :=
      (ENNReal.ofReal_pos.mpr hδ).trans_le (hstage i)
    exact ⟨hP i, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (ui i).val (ui i).property hpos).symm,
      (singularityEnvelopeMassPreserving omega θ (ui i).val (ui i).property (hP i)).symm ▸ hpos⟩
  have hδP (i : I) : ENNReal.ofReal δ ≤ diagonalPotentialMass θ
      (singularityEnvelope θ.val (ui i).val) (hP i) :=
    (hstage i).trans_eq (singularityEnvelopeMassPreserving omega θ
      (ui i).val (ui i).property (hP i)).symm
  let w : I → MassBoundedModelPotential θ δ := fun i =>
    ⟨⟨singularityEnvelope θ.val (ui i).val, hP i⟩, hmodels i, hδP i⟩
  let := modelMetricSpace omega θ hbig δ
  let : UniformSpace (MassBoundedModelPotential θ δ) :=
    (modelMetricSpace omega θ hbig δ).toUniformSpace
  let : TopologicalSpace (MassBoundedModelPotential θ δ) :=
    (modelMetricSpace omega θ hbig δ).toUniformSpace.toTopologicalSpace
  let := completeSpace_modelMetricSpace omega θ hbig hδ
  have hzero (i : I) : dist (ui i) (w i).val = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (ui i).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (ui i).property (w i).val.property).mpr he
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hdist (i j : I) : dist (w i) (w j) = dist (ui i) (ui j) := by
    change dist (w i).val (w j).val = dist (ui i) (ui j)
    apply le_antisymm
    · have h := (dist_triangle (w i).val (ui i) (w j).val).trans
        (add_le_add le_rfl (dist_triangle (ui i) (ui j) (w j).val))
      simpa only [dist_comm (w i).val (ui i), hzero, zero_add, add_zero] using h
    · have h := (dist_triangle (ui i) (w i).val (ui j)).trans
        (add_le_add le_rfl (dist_triangle (w i).val (w j).val (ui j)))
      simpa only [dist_comm (w j).val (ui j), hzero, zero_add, add_zero] using h
  have hwcauchy : Cauchy (map w F) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨t, ht, htdist⟩ := (Metric.cauchy_iff.mp hcauchy).2 ε hε
    change ui ⁻¹' t ∈ F at ht
    refine ⟨w '' (ui ⁻¹' t), image_mem_map ht, ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    rw [hdist]
    exact htdist _ hi _ hj
  obtain ⟨U, hUlim⟩ := cauchy_map_iff_exists_tendsto.mp hwcauchy
  have hlim : Tendsto (fun i => (w i).val) F (𝓝 U.val) :=
    ((model_inclusion_isometry omega θ hbig δ).continuous.tendsto U).comp hUlim
  have hZ : Tendsto (fun i => dist (ui i) (w i).val) F (𝓝 0) := by
    simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ℝ)) F (𝓝 0))
  exact ⟨U.val, U.property.1, U.property.2, (tendsto_iff_of_dist hZ).mpr hlim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityPositiveCauchyFilters
