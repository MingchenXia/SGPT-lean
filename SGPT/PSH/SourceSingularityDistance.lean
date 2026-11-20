import SGPT.PSH.SourceAssociatedRay
import SGPT.PSH.SourceSubgeodesicL1
import SGPT.PSH.SourcePIComparison
import SGPT.Envelopes.SourceRooftopMassCalculus
import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance

/-! # The literal original singularity pseudometric and mixed-mass criteria

The complete original-source route precedes this implementation in
`source-singularity-distance.tex`. The existing source PSH carrier, associated
ray and radial distance are reused, with the actual distance topology explicit.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Actual original R1 membership is produced from the already constructed
associated bounded ray, retaining the SAME original functions at every time. -/
def sourceAssociatedFiniteEnergyRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) :
    SourceFiniteEnergyRay ω θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) :=
  sourceBoundedRayToFiniteEnergyRay ω (sourceAssociatedBoundedRay ω θ hbig u.property)

/-- WHOLE original def:dS on the ENTIRE existing source PSH carrier:
the literal original radial Darvas distance of the actual associated rays. -/
def sourceSingularityDistance (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) : EReal :=
  sourceRadialDarvasDistance ω (sourceAssociatedFiniteEnergyRay ω θ hbig u)
    (sourceAssociatedFiniteEnergyRay ω θ hbig v)

/-- Every original defining ray, function, pole and minimal model is the
same as in the existing genuine native canonical-distance construction. -/
theorem sourceSingularityDistance_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityDistance ω θ hbig u v =
      SingularCanonicalSingularityDistance.singularityDistance ω (atlasClosedFormToNative θ)
        hbig u.val v.val := by
  rw [sourceSingularityDistance, sourceRadialDarvasDistance_eq_native]
  change RelativeGeodesicRays.rayD1 (atlasClosedFormToNative θ) (sourceMinimalEnvelope θ)
    (sourceMinimalEnvelope_model ω θ hbig).toNative
    (sourceRayExtension (sourceAssociatedRay ω θ u.val))
    (sourceRayExtension (sourceAssociatedRay ω θ v.val)) = _
  rw [sourceAssociatedRay_extension_eq_native, sourceAssociatedRay_extension_eq_native]
  have he (a b : M → EReal) :
      RelativeGeodesicRays.rayD1 (atlasClosedFormToNative θ) (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_model ω θ hbig).toNative
        (SingularMinimalCanonicalRay.canonicalRay (atlasClosedFormToNative θ) a)
        (SingularMinimalCanonicalRay.canonicalRay (atlasClosedFormToNative θ) b) =
      SingularCanonicalSingularityDistance.singularityDistance ω (atlasClosedFormToNative θ)
        hbig a b := by
    simp only [sourceMinimalEnvelope_eq_native, SingularCanonicalSingularityDistance.singularityDistance]
  exact he u.val v.val

/-- Genuine original radial convergence manufactures a finite nonnegative
real value BEFORE any realification of the source distance. -/
theorem sourceSingularityDistance_exists_real (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    ∃ m : ℝ, 0 ≤ m ∧ sourceSingularityDistance ω θ hbig u v = (m : EReal) := by
  obtain ⟨m, hm, _, _, he⟩ := exists_tendsto_sourceRadialDarvasDistance ω
    (sourceAssociatedFiniteEnergyRay ω θ hbig u) (sourceAssociatedFiniteEnergyRay ω θ hbig v)
  exact ⟨m, hm, he⟩

/-- The WHOLE original pseudometric is pulled back on the existing literal
PSH carrier. Its genuine distance-generated uniformity is explicit. -/
@[instance_reducible]
def sourceSingularityPseudoMetricSpace (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    PseudoMetricSpace (SourceThetaPotentialL1 θ) :=
  PseudoMetricSpace.induced (sourceThetaPotentialL1EquivNative θ)
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig)

/-- Selecting the actual source dS metric gives EXACTLY its finite real
value. The existing L1 or pointwise topology is not used for this instance. -/
theorem sourceSingularityPseudoMetricSpace_dist (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    dist u v = (sourceSingularityDistance ω θ hbig u v).toReal := by
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  change dist (sourceThetaPotentialL1EquivNative θ u) (sourceThetaPotentialL1EquivNative θ v) = _
  rw [SingularCanonicalSingularityDistance.dist_eq_singularityDistance_toReal ω,
    sourceSingularityDistance_eq_native]
  rfl

/-- Full source distance nonnegativity and BOTH excluded extended endpoints
are genuine outputs of finite radial convergence on all original inputs. -/
theorem sourceSingularityDistance_nonneg_finite (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    0 ≤ sourceSingularityDistance ω θ hbig u v ∧
      sourceSingularityDistance ω θ hbig u v ≠ ⊤ ∧ sourceSingularityDistance ω θ hbig u v ≠ ⊥ := by
  obtain ⟨m, hm, he⟩ := sourceSingularityDistance_exists_real ω θ hbig u v
  rw [he]
  exact ⟨EReal.coe_nonneg.mpr hm, EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- The actual source maximum packaged in the existing ENTIRE PSH carrier;
its genuineness is produced by the already proved source maximum theorem. -/
def sourceThetaPotentialMaximum
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (u v : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 θ :=
  ⟨fun x => max (u.val x) (v.val x), sourceThetaMaximum_genuine u.property v.property⟩

/-- The already defined ALL-competitor original ordinary singularity
envelope, with source PSH regularity manufactured by its existing producer. -/
def sourceThetaPotentialSingularityEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} (u : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 θ :=
  ⟨sourceSingularityEnvelope θ u.val, isThetaPSH_sourceSingularityEnvelope u.property⟩

/-- The original zero locus is exactly its existing global P-equivalence,
including either zero original mass and dimension zero. -/
theorem sourceSingularityDistance_eq_zero_iff_sourcePEquivalent (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityDistance ω θ hbig u v = 0 ↔
      GlobalPComparison.sourcePEquivalent (n := n) u.val v.val := by
  rw [sourceSingularityDistance_eq_native]
  exact SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
    ω (atlasClosedFormToNative θ) hbig
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)

/-- The ENTIRE printed positive-mass consequence uses the literal original
ordinary P-envelope and the existing genuine global equivalence proof. -/
theorem sourceSingularityDistance_pEnvelope_eq_zero (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    sourceSingularityDistance ω θ hbig u (sourceThetaPotentialSingularityEnvelope u) = 0 := by
  apply (sourceSingularityDistance_eq_zero_iff_sourcePEquivalent ω θ hbig _ _).mpr
  change GlobalPComparison.sourcePEquivalent (n := n) u.val (sourceSingularityEnvelope θ u.val)
  simpa only [sourceSingularityEnvelope_eq_native] using
    GlobalPComparison.sourcePEquivalent_singularityEnvelope ω (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property) hpos

/-- WHOLE original ordered source formula, under precisely the global
P-order; no pointwise order or positive input mass is added. -/
theorem sourceSingularityDistance_eq_mixedMass_sub_of_sourcePOrder (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u.val v.val) :
    sourceSingularityDistance ω θ hbig u v =
      (((∑ j : Fin (n + 1),
        ((sourceMinimalMixedMass ω θ hbig v.val v.property j).toReal -
          (sourceMinimalMixedMass ω θ hbig u.val u.property j).toReal)) / (n + 1 : ℝ) : ℝ) : EReal) := by
  rw [sourceSingularityDistance_eq_native]
  simpa only [sourceMinimalMixedMass_eq_native] using
    SingularCanonicalOrderedMixedMassDistance.singularityDistance_eq_mixedMass_sub_of_sourcePOrder
      ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property) huv

/-- Actual original P-chain distances telescope as finite real mixed sums,
using only the already proved exact ordered formula and true P-transitivity. -/
theorem sourceSingularityDistance_add_of_sourcePChain (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v w : SourceThetaPotentialL1 θ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u.val v.val)
    (hvw : GlobalPComparison.sourcePOrder (n := n) v.val w.val) :
    sourceSingularityDistance ω θ hbig u w =
      sourceSingularityDistance ω θ hbig u v + sourceSingularityDistance ω θ hbig v w := by
  rw [sourceSingularityDistance_eq_mixedMass_sub_of_sourcePOrder ω θ hbig u w
      (GlobalPComparison.sourcePOrder_trans ω huv hvw),
    sourceSingularityDistance_eq_mixedMass_sub_of_sourcePOrder ω θ hbig u v huv,
    sourceSingularityDistance_eq_mixedMass_sub_of_sourcePOrder ω θ hbig v w hvw,
    ← EReal.coe_add]
  congr 1
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- BOTH printed original three-term inequalities, with no input
monotonicity certificate beyond the two literal original P-order relations. -/
theorem sourceSingularityDistance_three_term (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v w : SourceThetaPotentialL1 θ)
    (huv : GlobalPComparison.sourcePOrder (n := n) u.val v.val)
    (hvw : GlobalPComparison.sourcePOrder (n := n) v.val w.val) :
    sourceSingularityDistance ω θ hbig u v ≤ sourceSingularityDistance ω θ hbig u w ∧
      sourceSingularityDistance ω θ hbig v w ≤ sourceSingularityDistance ω θ hbig u w := by
  rw [sourceSingularityDistance_add_of_sourcePChain ω θ hbig u v w huv hvw]
  exact ⟨le_add_of_nonneg_right (sourceSingularityDistance_nonneg_finite ω θ hbig v w).1,
    le_add_of_nonneg_left (sourceSingularityDistance_nonneg_finite ω θ hbig u v).1⟩

/-- The literal source associated ray of the maximum is the ACTUALLY
CONSTRUCTED original bounded join, at every original nonnegative time. -/
theorem sourceAssociatedRay_max_eq_joinFamily (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceAssociatedRay ω θ (sourceThetaPotentialMaximum u v).val =
      sourceBoundedRayJoinFamily ω θ (sourceMinimalEnvelope θ)
        (sourceAssociatedRay ω θ u.val) (sourceAssociatedRay ω θ v.val) := by
  funext s
  have he (a : M → EReal) : sourceAssociatedRay ω θ a s =
      SingularMinimalCanonicalRay.canonicalRay (atlasClosedFormToNative θ) a s.val := by
    rw [← sourceRayExtension_nonneg (sourceAssociatedRay ω θ a) s.val s.property,
      sourceAssociatedRay_extension_eq_native]
  rw [he, sourceBoundedRayJoinFamily_eq_native, sourceAssociatedRay_extension_eq_native,
    sourceAssociatedRay_extension_eq_native]
  simpa only [sourceMinimalEnvelope_eq_native, sourceThetaPotentialMaximum] using
    SingularCanonicalSingularityMassComparison.canonicalRay_max_eq_joinSlice
      ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property) s.property

/-- The same actual maximum/join identity on the full original bounded-ray
subtypes, changing only already produced proof witnesses. -/
theorem sourceAssociatedBoundedRay_max_eq_join (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceAssociatedBoundedRay ω θ hbig (sourceThetaPotentialMaximum u v).property =
      sourceBoundedRayJoin ω (sourceAssociatedBoundedRay ω θ hbig u.property)
        (sourceAssociatedBoundedRay ω θ hbig v.property) :=
  Subtype.ext (sourceAssociatedRay_max_eq_joinFamily ω θ hbig u v)

/-- WHOLE original almost-triangle lemma with BOTH inequalities and the
EXACT existing dimensional constant 3(n+1)2^(n+2), on ALL original inputs. -/
theorem sourceSingularityDistance_almost_triangle (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityDistance ω θ hbig u v ≤
      sourceSingularityDistance ω θ hbig u (sourceThetaPotentialMaximum u v) +
        sourceSingularityDistance ω θ hbig v (sourceThetaPotentialMaximum u v) ∧
    sourceSingularityDistance ω θ hbig u (sourceThetaPotentialMaximum u v) +
      sourceSingularityDistance ω θ hbig v (sourceThetaPotentialMaximum u v) ≤
      (sourceIThetaComparisonConstant n : EReal) * sourceSingularityDistance ω θ hbig u v := by
  have h := sourceBoundedRayJoin_distance_bounds ω
    (sourceAssociatedBoundedRay ω θ hbig u.property) (sourceAssociatedBoundedRay ω θ hbig v.property)
  rw [← sourceAssociatedBoundedRay_max_eq_join ω θ hbig u v] at h
  simpa only [sourceSingularityDistance, sourceAssociatedFiniteEnergyRay] using h

/-- Literal original finite mixed-mass expression, with no supplied
distance/gap identity or comparison certificate. -/
def sourceSingularityMassJoinGap (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) : ℝ :=
  (∑ j : Fin (n + 1),
    (2 * (sourceMinimalMixedMass ω θ hbig (sourceThetaPotentialMaximum u v).val
      (sourceThetaPotentialMaximum u v).property j).toReal -
      (sourceMinimalMixedMass ω θ hbig u.val u.property j).toReal -
      (sourceMinimalMixedMass ω θ hbig v.val v.property j).toReal)) / (n + 1 : ℝ)

/-- Every original mass and the same actual maximum give the existing
native mass expression, including zero input mass and the empty tuple. -/
theorem sourceSingularityMassJoinGap_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityMassJoinGap ω θ hbig u v =
      ActualMixedMassJoinGap.mixedMassJoinGap
        (SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum ω (atlasClosedFormToNative θ) hbig).plurisubharmonic
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property) := by
  simp only [sourceSingularityMassJoinGap, sourceMinimalMixedMass_eq_native,
    sourceThetaPotentialMaximum, ActualMixedMassJoinGap.mixedMassJoinGap]

/-- The displayed ORIGINAL two-sided mass comparison, with the literal
source distance and actual original masses, not a renamed conditional gap. -/
theorem sourceSingularityDistance_mass_comparison (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityDistance ω θ hbig u v ≤ (sourceSingularityMassJoinGap ω θ hbig u v : EReal) ∧
      (sourceSingularityMassJoinGap ω θ hbig u v : EReal) ≤
        (sourceIThetaComparisonConstant n : EReal) * sourceSingularityDistance ω θ hbig u v := by
  rw [sourceSingularityDistance_eq_native, sourceSingularityMassJoinGap_eq_native]
  exact SingularCanonicalSingularityMassComparison.singularityDistance_le_mixedMassJoinGap_le
    ω (atlasClosedFormToNative θ) hbig
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)

/-- The actual dS uniformity is named separately from the existing L1
uniformity; it is precisely the source pseudometric-generated uniformity. -/
@[instance_reducible]
def sourceSingularityUniformSpace (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    UniformSpace (SourceThetaPotentialL1 θ) :=
  (sourceSingularityPseudoMetricSpace ω θ hbig).toUniformSpace

/-- The actual source dS topology generated by that SAME uniformity. -/
@[instance_reducible]
def sourceSingularityTopology (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    TopologicalSpace (SourceThetaPotentialL1 θ) :=
  (sourceSingularityUniformSpace ω θ hbig).toTopologicalSpace

/-- The entire SAME-function source/native PSH equivalence is a genuine
homeomorphism for the explicitly selected actual dS uniformities/topologies. -/
def sourceSingularityHomeomorphNative (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    letI := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
    letI : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
      (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
    letI : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
      (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
    SourceThetaPotentialL1 θ ≃ₜ ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val := by
  letI := sourceSingularityPseudoMetricSpace ω θ hbig
  letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  letI := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  letI : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  letI : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  exact (sourceThetaPotentialL1EquivNative θ).toHomeomorphOfIsInducing (Topology.IsInducing.induced _)

/-- WHOLE arbitrary-net consequence, strengthened to EVERY filter, with
BOTH actual dS uniformities/topologies explicit. Original endpoint AND
maximum masses converge as actual ENNReal values, with finiteness internal. -/
theorem tendsto_sourceSingularityTopology_iff_mixedMass (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Tendsto w F (𝓝 v) ↔ ∀ j : Fin (n + 1),
      Tendsto (fun i => sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j)
        F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)) ∧
      Tendsto (fun i => sourceMinimalMixedMass ω θ hbig
        (sourceThetaPotentialMaximum (w i) v).val (sourceThetaPotentialMaximum (w i) v).property j)
        F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hread (a : SourceThetaPotentialL1 θ) :
      (sourceThetaPotentialL1EquivNative θ a).val = a.val := rfl
  rw [hmap.tendsto_nhds_iff]
  simpa only [Function.comp_def, sourceMinimalMixedMass_eq_native, sourceThetaPotentialMaximum, hread] using
    SingularCanonicalSingularityMassComparison.tendsto_native_iff_endpointMixedMass
      ω (atlasClosedFormToNative θ) hbig F
      (fun i => sourceThetaPotentialL1EquivNative θ (w i)) (sourceThetaPotentialL1EquivNative θ v)

/-- The actual real distance-zero criterion for EVERY filter, retaining
BOTH families of original finite real mass readbacks. No monotonicity,
limit-membership, positive input mass or countable-cofinality input. -/
theorem tendsto_sourceSingularityDistance_zero_iff_realMixedMass (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    Tendsto (fun i => (sourceSingularityDistance ω θ hbig (w i) v).toReal) F (𝓝 0) ↔
      ∀ j : Fin (n + 1),
        Tendsto (fun i => (sourceMinimalMixedMass ω θ hbig (w i).val (w i).property j).toReal)
          F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j).toReal) ∧
        Tendsto (fun i => (sourceMinimalMixedMass ω θ hbig
          (sourceThetaPotentialMaximum (w i) v).val (sourceThetaPotentialMaximum (w i) v).property j).toReal)
          F (𝓝 (sourceMinimalMixedMass ω θ hbig v.val v.property j).toReal) := by
  simp only [sourceSingularityDistance_eq_native, sourceMinimalMixedMass_eq_native,
    sourceThetaPotentialMaximum]
  exact SingularCanonicalSingularityMassComparison.tendsto_singularityDistance_toReal_zero_iff_endpointMixedMass
    ω (atlasClosedFormToNative θ) hbig F
    (fun i => (isThetaPSH_iff_nativeThetaPotential θ _).mp (w i).property)
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)

end SGPT.PSH.VariableComplexAtlas
