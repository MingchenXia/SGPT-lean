import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

/-! # The native actual singularity metric on mass-bounded models

SGPT PDF0231--0232 positive-threshold model completeness argument,
with explicit independent native metric construction. The original actual
positive model fields and genuine positive-background classification
produce separation; no pointwise identification is inferred from a general
pseudometric zero. Completeness is separate and requires a fixed delta > 0.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelMetricSpace

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  DiagonalMass ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularGlobalPOrder SingularCanonicalDistanceZeroPEquivalence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual genuine models retaining a fixed actual top-mass lower bound. -/
abbrev MassBoundedModelPotential (θ : ClosedRealOneOneForm n M) (δ : ℝ) :=
  {u : ThetaPshL1 θ.val // IsModelPotential θ u.val ∧
    ENNReal.ofReal δ ≤ diagonalPotentialMass θ u.val u.property}

/-- Inducing the actual native singularity distance on true models gives
a genuine metric: their positive original masses justify fixed-envelope separation. -/
@[instance_reducible]
def modelMetricSpace (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) (δ : ℝ) :
    MetricSpace (MassBoundedModelPotential θ δ) := by
  let := singularityPseudoMetricSpace omega θ hbig
  refine { PseudoMetricSpace.induced (fun u : MassBoundedModelPotential θ δ => u.val)
      (singularityPseudoMetricSpace omega θ hbig) with eq_of_dist_eq_zero := ?_ }
  intro u v hd
  change dist u.val v.val = 0 at hd
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig
    u.val.property v.val.property
  have hmzero : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm, EReal.toReal_coe] using hd
  have hz : singularityDistance omega θ hbig u.val.val v.val.val = 0 := by
    rw [hm, hmzero, EReal.coe_zero]
  have hsource := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
    u.val.property v.val.property).mp hz
  have hfixed := (sourcePEquivalent_iff_pEquivalentWith omega θ
    u.val.property v.val.property u.property.1.positive_mass v.property.1.positive_mass).mp hsource
  have heq : u.val.val = v.val.val := u.property.1.envelope_eq.trans
    ((pEquivalentWith_iff_envelope_eq.mp hfixed).trans v.property.1.envelope_eq.symm)
  exact Subtype.ext (Subtype.ext heq)

/-- The actual model metric inclusion preserves the genuine native distance
and hence induces the actual generated uniformity and topology. -/
theorem model_inclusion_isometry (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (δ : ℝ) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI := modelMetricSpace omega θ hbig δ
    Isometry (fun u : MassBoundedModelPotential θ δ => u.val) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let := modelMetricSpace omega θ hbig δ
  intro u v
  rfl

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelMetricSpace
