import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay
import SGPT.Foundations.Analysis.Pending.SingularModelSourceRayDistance
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

set_option autoImplicit false

/-! # The actual canonical-ray singularity pseudometric, SGPT Definition 6.2.1

The actual minimal-reference canonical rays for all genuine theta-PSH inputs
give the existing defining extended radial distance. Genuine finite radial
limits precede realification, and actual native based rays produce the
native induced pseudometric. Separation and completeness remain separate.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses RelativePreceqRays RelativeGeodesicRays
  SingularMinimalCanonicalRay SingularModelDarvasMetricSpace SingularModelGeodesicRayDistance
  SingularModelSourceRayInitialEnergy ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual defining extended canonical-ray distance uses the produced
minimal model and the existing actual radial Darvas functional. -/
def singularityDistance (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : M → EReal) : EReal :=
  rayD1 θ (thetaPshSupremum θ.val) (isModelPotential_thetaPshSupremum omega θ hbig)
    (canonicalRay θ u) (canonicalRay θ v)

private theorem finiteEnergy_canonicalRay (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    IsFiniteEnergyRayFromModel θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) (canonicalRay θ u) := by
  have hR := isBoundedRayFromModel_canonicalRay omega θ hbig hu
  exact ⟨⟨hR.1.1, fun t ht =>
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      (hR.1.2 t ht.le)⟩, hR.2⟩

/-- All genuine PSH inputs have an internally produced finite real radial
limit of the actual defining singularity distance and its supremum bounds. -/
theorem exists_tendsto_singularityDistance (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u v : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    ∃ m : ℝ, 0 ≤ m ∧
      Tendsto (fun t : ℝ => relativeD1 θ (thetaPshSupremum θ.val)
        (isModelPotential_thetaPshSupremum omega θ hbig)
        (canonicalRay θ u t) (canonicalRay θ v t) / t) atTop (𝓝 m) ∧
      (∀ t : ℝ, 0 < t → relativeD1 θ (thetaPshSupremum θ.val)
        (isModelPotential_thetaPshSupremum omega θ hbig)
        (canonicalRay θ u t) (canonicalRay θ v t) / t ≤ m) ∧
      singularityDistance omega θ hbig u v = (m : EReal) := by
  have hRu := finiteEnergy_canonicalRay omega θ hbig hu
  have hRv := finiteEnergy_canonicalRay omega θ hbig hv
  exact SingularModelSourceRayDistance.exists_tendsto_rayD1 omega hRu.1 hRv.1
    (hRu.2.trans hRv.2.symm)

private def minimalModelBase (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    ModelFiniteEnergyPotential θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) :=
  ⟨thetaPshSupremum θ.val,
    RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
      ⟨(isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic,
        SameSingularityTypeOn.refl _ univ⟩⟩

private def basedCanonicalRay (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u : ThetaPshL1 θ.val) :
    BasedModelFiniteEnergyGeodesicRay θ (thetaPshSupremum θ.val)
      (isModelPotential_thetaPshSupremum omega θ hbig) (minimalModelBase omega θ hbig) := by
  let hR := finiteEnergy_canonicalRay omega θ hbig u.property
  refine ⟨nativeRay omega hR.1, ?_⟩
  apply Subtype.ext
  exact ((nativeRay omega hR.1).rawCurve_coe 0).symm.trans
    ((nativeRay_reader_eq omega hR.1 le_rfl).trans hR.2)

/-- The native metric of actual based rays induces a native pseudometric on
the full genuine PSH carrier, with its distance-generated uniformity. -/
@[instance_reducible]
def singularityPseudoMetricSpace (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) :
    PseudoMetricSpace (ThetaPshL1 θ.val) :=
  PseudoMetricSpace.induced (basedCanonicalRay omega θ hbig)
    (basedRayMetricSpace omega (minimalModelBase omega θ hbig)).toPseudoMetricSpace

/-- With the actual singularity pseudometric explicitly selected, its native
distance is exactly the finite real value of the defining canonical distance. -/
theorem dist_eq_singularityDistance_toReal (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    dist u v = (singularityDistance omega θ hbig u.val v.val).toReal := by
  let hRu := finiteEnergy_canonicalRay omega θ hbig u.property
  let hRv := finiteEnergy_canonicalRay omega θ hbig v.property
  change (rayD1 θ (thetaPshSupremum θ.val)
    (isModelPotential_thetaPshSupremum omega θ hbig)
    (nativeRay omega hRu.1).rawCurve (nativeRay omega hRv.1).rawCurve).toReal =
      (rayD1 θ (thetaPshSupremum θ.val)
        (isModelPotential_thetaPshSupremum omega θ hbig)
        (canonicalRay θ u.val) (canonicalRay θ v.val)).toReal
  exact congrArg EReal.toReal (SingularModelSourceRayDistance.rayD1_eq_native_readers
    omega hRu.1 hRv.1 (hRu.2.trans hRv.2.symm)).symm

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDistance
