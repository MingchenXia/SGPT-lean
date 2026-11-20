import SGPT.PSH.SourcePMassCharacterization
import SGPT.PSH.SourceBoundedRayJoin
import SGPT.Foundations.Analysis.Pending.SingularMinimalCanonicalRay

/-! # The literal original associated-ray construction

The complete source-first route is in `source-associated-ray.tex`.
Real cutoff horizons and the original whole competitor supremum are retained.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending DiagonalMass RelativeEnergy
open SingularModelNormalizedMixedCutoff SingularCanonicalCutoffStages
  SingularCanonicalCutoffSlices SingularMinimalCanonicalRay

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original maximum of the input and the real cutoff of V_theta. -/
def sourceAssociatedCutoff (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (u : M → EReal) (C : ℝ) : M → EReal :=
  fun x => max (u x) (sourceMinimalEnvelope θ x - (C : EReal))

/-- Same functions, real horizon and literal minimal envelope in every slot. -/
theorem sourceAssociatedCutoff_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) (C : ℝ) :
    sourceAssociatedCutoff θ u C =
      realCutoff (thetaPshSupremum (atlasClosedFormToNative θ).val) u C := by
  unfold sourceAssociatedCutoff realCutoff
  rw [sourceMinimalEnvelope_eq_native]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The literal closed original Perron geodesic on physical time [0,C].
Outside that interval this only provides a normalized real-time reader. -/
def sourceAssociatedRayStage (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (C s : ℝ) : M → EReal :=
  sourcePerronClosedSlice ω θ (sourceMinimalEnvelope θ) (sourceAssociatedCutoff θ u C) (s / C)

/-- Both original closed endpoints and every interior potential are identical. -/
theorem sourceAssociatedRayStage_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (C s : ℝ) :
    sourceAssociatedRayStage ω θ u C s = cutoffStage (atlasClosedFormToNative θ)
      (thetaPshSupremum (atlasClosedFormToNative θ).val) u C s := by
  unfold sourceAssociatedRayStage
  rw [sourcePerronClosedSlice_eq_native, sourceAssociatedCutoff_eq_native,
    sourceMinimalEnvelope_eq_native]
  rfl

/-- The original neighborhood-USC supremum over ALL real C>t at every t≥0. -/
def sourceAssociatedCutoffRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) :
    SourceRayFamily M :=
  fun t => SGPT.PSH.uscSup (fun C : {C : ℝ // t.val < C} =>
    sourceAssociatedRayStage ω θ u C.val t.val)

/-- Only the native real-time API clamps negative times; every original time
and every actual real cutoff competitor remain exactly the original ones. -/
theorem sourceAssociatedCutoffRay_extension_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) :
    sourceRayExtension (sourceAssociatedCutoffRay ω θ u) =
      cutoffSlice (atlasClosedFormToNative θ)
        (thetaPshSupremum (atlasClosedFormToNative θ).val) u := by
  funext s
  simp only [sourceRayExtension, sourceAssociatedCutoffRay, sourceUscSup_eq_native,
    sourceAssociatedRayStage_eq_native, cutoffSlice]

variable [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- A genuine original nonpositive competitor lies below the literal V_theta. -/
theorem sourceAssociatedInput_le_minimal
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    u ≤ sourceMinimalEnvelope θ := by
  rw [sourceMinimalEnvelope_eq_native]
  exact le_thetaPshSupremum ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hu0

/-- Every actual closed stage has the original same singularity type,
including the two assigned endpoint values and all original poles. -/
theorem sourceAssociatedRayStage_sameType (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    SourceRelativeEInfinity θ (sourceMinimalEnvelope θ) (sourceAssociatedRayStage ω θ u C s) := by
  apply (sourceRelativeEInfinity_iff_native θ _ _).mpr
  rw [sourceAssociatedRayStage_eq_native, sourceMinimalEnvelope_eq_native]
  exact relativeEInfinity_cutoffStage ω (isModelPotential_thetaPshSupremum ω _ hbig)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (by simpa only [sourceMinimalEnvelope_eq_native] using sourceAssociatedInput_le_minimal hu hu0)
    hC hs

/-- The actual original lower and upper barriers hold on the entire closed
physical interval; no real-valued subtraction at a pole is substituted. -/
theorem sourceAssociatedRayStage_bounds (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    {C s : ℝ} (hC : 0 < C) (hs : s ∈ Icc (0 : ℝ) C) :
    (fun x => sourceMinimalEnvelope θ x - (s : EReal)) ≤ sourceAssociatedRayStage ω θ u C s ∧
      sourceAssociatedRayStage ω θ u C s ≤ sourceMinimalEnvelope θ := by
  rw [sourceAssociatedRayStage_eq_native, sourceMinimalEnvelope_eq_native]
  exact cutoffStage_bounds (isModelPotential_thetaPshSupremum ω _ hbig).plurisubharmonic
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (by simpa only [sourceMinimalEnvelope_eq_native] using sourceAssociatedInput_le_minimal hu hu0)
    hC hs

/-- Genuine Perron restriction produces monotonicity in the REAL horizon. -/
theorem sourceAssociatedRayStage_mono_horizon (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    {C D s : ℝ} (hC : 0 < C) (hCD : C ≤ D) (hs : s ∈ Icc (0 : ℝ) C) :
    sourceAssociatedRayStage ω θ u C s ≤ sourceAssociatedRayStage ω θ u D s := by
  rw [sourceAssociatedRayStage_eq_native, sourceAssociatedRayStage_eq_native]
  exact SingularCanonicalCutoffStageOrder.cutoffStage_mono_horizon ω
    (isModelPotential_thetaPshSupremum ω _ hbig)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (by simpa only [sourceMinimalEnvelope_eq_native] using sourceAssociatedInput_le_minimal hu hu0)
    hC hCD hs

/-- The original all-real-horizon construction is a WHOLE original bounded
ray. Every closed interval, including a=b, and the initial value are produced. -/
theorem sourceAssociatedCutoffRay_mem_boundedRays (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    sourceAssociatedCutoffRay ω θ u ∈ sourceBoundedRays ω θ (sourceMinimalEnvelope θ)
      (sourceMinimalEnvelope_model ω θ hbig) := by
  apply (mem_sourceBoundedRays_iff_native ω θ _ _ _).mpr
  rw [sourceAssociatedCutoffRay_extension_eq_native]
  simpa only [sourceMinimalEnvelope_eq_native] using
    SingularCanonicalCutoffRay.isBoundedRayFromModel_cutoffSlice ω
      (isModelPotential_thetaPshSupremum ω _ hbig)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      (by simpa only [sourceMinimalEnvelope_eq_native] using sourceAssociatedInput_le_minimal hu hu0)

/-- Same-type stages internally supply their genuine original E1 classes,
so the source distance below has its actual domain without a supplied certificate. -/
def sourceAssociatedRayStagePotential (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (s : Ici (0 : ℝ)) (C : {C : ℝ // s.val < C}) :
    SourceFiniteEnergyPotential θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) := by
  refine ⟨sourceAssociatedRayStage ω θ u C.val s.val, ?_⟩
  apply (sourceRelativeFiniteEnergy_iff_native θ _ _ _).mpr
  exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity ω
    ((sourceRelativeEInfinity_iff_native θ _ _).mp
      (sourceAssociatedRayStage_sameType ω θ hbig hu hu0
        (lt_of_le_of_lt s.property C.property) ⟨s.property, C.property.le⟩))

/-- The actual cutoff ray, packaged only after its whole original bounded
contract has been produced, for reuse of the existing same-function E1 reader. -/
def sourceAssociatedCutoffBoundedRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    SourceBoundedGeodesicRay ω θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) :=
  ⟨sourceAssociatedCutoffRay ω θ u, sourceAssociatedCutoffRay_mem_boundedRays ω θ hbig hu hu0⟩

/-- The ENTIRE real-horizon tail tends to the actual slice in the original
Darvas metric, with genuine original E1 memberships produced internally. -/
theorem tendsto_sourceAssociatedRayStage_distance (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (s : Ici (0 : ℝ)) :
    Tendsto (fun C : {C : ℝ // s.val < C} =>
      sourceDarvasDistance θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig)
        (sourceAssociatedRayStagePotential ω θ hbig hu hu0 s C)
        (sourceFiniteEnergyRaySlice ω (sourceBoundedRayToFiniteEnergyRay ω
          (sourceAssociatedCutoffBoundedRay ω θ hbig hu hu0)) s)) atTop (𝓝 0) := by
  have hn := (SingularCanonicalCutoffTailLimits.tendsto_cutoffStage_common_tail ω
    (isModelPotential_thetaPshSupremum ω _ hbig)
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
    (by simpa only [sourceMinimalEnvelope_eq_native] using sourceAssociatedInput_le_minimal hu hu0)
    s.property le_rfl).1
  have hslice : sourceAssociatedCutoffRay ω θ u s = cutoffSlice (atlasClosedFormToNative θ)
      (thetaPshSupremum (atlasClosedFormToNative θ).val) u s.val := by
    rw [← sourceAssociatedCutoffRay_extension_eq_native ω θ u,
      sourceRayExtension_nonneg _ s.val s.property]
  simpa only [sourceDarvasDistance_eq_native ω, sourceAssociatedRayStagePotential,
    sourceFiniteEnergyRaySlice, sourceBoundedRayToFiniteEnergyRay,
    sourceAssociatedCutoffBoundedRay, sourceAssociatedRayStage_eq_native,
    sourceMinimalEnvelope_eq_native, hslice] using hn

/-- Normalizing only the unused initial horizon interval gives a literal
REAL C→infinity limit. For C≥s+1 its stage is exactly the original stage. -/
theorem tendsto_sourceAssociatedRayStage_real_horizon (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0)
    (s : Ici (0 : ℝ)) :
    Tendsto (fun C : ℝ =>
      sourceDarvasDistance θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig)
        (sourceAssociatedRayStagePotential ω θ hbig hu hu0 s
          ⟨max C (s.val + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩)
        (sourceFiniteEnergyRaySlice ω (sourceBoundedRayToFiniteEnergyRay ω
          (sourceAssociatedCutoffBoundedRay ω θ hbig hu hu0)) s)) atTop (𝓝 0) := by
  apply (tendsto_sourceAssociatedRayStage_distance ω θ hbig hu hu0 s).comp
  apply tendsto_atTop.2
  intro C
  filter_upwards [eventually_ge_atTop C.val] with D hD
  exact hD.trans (le_max_left _ _)

omit [BorelSpace M] [ConnectedSpace M] in
/-- The real-horizon normalization changes no actual sufficiently large
source stage; this records the exact reader used in the preceding limit. -/
theorem sourceAssociatedRayStage_real_horizon_readback (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    (s C : ℝ) (hC : s + 1 ≤ C) :
    sourceAssociatedRayStage ω θ u (max C (s + 1)) s =
      sourceAssociatedRayStage ω θ u C s := by
  rw [max_eq_left hC]

/-- The actual original normalization of an arbitrary genuine input uses
its own global supremum. No ray or normalization certificate is supplied. -/
def sourceAssociatedRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) : SourceRayFamily M :=
  sourceAssociatedCutoffRay ω θ (fun x => u x - ((⨆ y, u y).toReal : EReal))

omit [ConnectedSpace M] in
/-- The entire original normalized family is the genuine native canonical
ray on the SAME input, original minimal reference and every original pole. -/
theorem sourceAssociatedRay_extension_eq_native (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal) :
    sourceRayExtension (sourceAssociatedRay ω θ u) = canonicalRay (atlasClosedFormToNative θ) u := by
  exact sourceAssociatedCutoffRay_extension_eq_native ω θ _

/-- The genuinely produced native minimal model and actual normalization
manufacture the whole bounded-ray contract for EVERY genuine source input. -/
theorem sourceAssociatedRay_mem_boundedRays (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceAssociatedRay ω θ u ∈ sourceBoundedRays ω θ (sourceMinimalEnvelope θ)
      (sourceMinimalEnvelope_model ω θ hbig) := by
  apply (mem_sourceBoundedRays_iff_native ω θ _ _ _).mpr
  rw [sourceAssociatedRay_extension_eq_native]
  simpa only [sourceMinimalEnvelope_eq_native] using
    isBoundedRayFromModel_canonicalRay ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- The arbitrary-input ray agrees identically with the literal cutoff
construction when the ORIGINAL input is nonpositive. -/
theorem sourceAssociatedRay_eq_cutoff_of_nonpositive (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    sourceAssociatedRay ω θ u = sourceAssociatedCutoffRay ω θ u := by
  have he : sourceRayExtension (sourceAssociatedRay ω θ u) =
      sourceRayExtension (sourceAssociatedCutoffRay ω θ u) := by
    rw [sourceAssociatedRay_extension_eq_native, sourceAssociatedCutoffRay_extension_eq_native]
    exact canonicalRay_eq_cutoffSlice_of_nonpositive ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) hu0
  funext t
  simpa only [sourceRayExtension_nonneg _ t.val t.property] using congrFun he t.val

/-- Actual finite-constant invariance is equality at EVERY original time,
proved from genuine native normalization, not an assumed equivalence class. -/
theorem sourceAssociatedRay_sub_const_eq (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ) :
    sourceAssociatedRay ω θ (fun x => u x - (c : EReal)) = sourceAssociatedRay ω θ u := by
  have he : sourceRayExtension (sourceAssociatedRay ω θ (fun x => u x - (c : EReal))) =
      sourceRayExtension (sourceAssociatedRay ω θ u) := by
    rw [sourceAssociatedRay_extension_eq_native, sourceAssociatedRay_extension_eq_native]
    exact canonicalRay_sub_const_eq (atlasClosedFormToNative θ)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) c
  funext t
  simpa only [sourceRayExtension_nonneg _ t.val t.property] using congrFun he t.val

/-- The actual arbitrary-input original ray, retaining the entire original
R-infinity contract for the existing source radial-energy definition. -/
def sourceAssociatedBoundedRay (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    SourceBoundedGeodesicRay ω θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_model ω θ hbig) :=
  ⟨sourceAssociatedRay ω θ u, sourceAssociatedRay_mem_boundedRays ω θ hbig hu⟩

/-- The literal original EReal LIMSUP equals the UNNORMALIZED original
mixed-mass deficit. Zero input mass and dimension zero are retained. -/
theorem sourceAssociatedRay_radialEnergy_eq_mixed_mass_deficit (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceRadialEnergy ω (sourceBoundedRayToGeodesicRay ω (sourceAssociatedBoundedRay ω θ hbig hu)) =
      (((∑ j : Fin (n + 1), ((sourceMinimalMixedMass ω θ hbig u hu j).toReal -
        (sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
          (sourceMinimalEnvelope_thetaPSH ω θ hbig) univ).toReal)) / (n + 1 : ℝ) : ℝ) : EReal) := by
  rw [sourceRadialEnergy_eq_native]
  change RelativeGeodesicRays.radialEnergy (atlasClosedFormToNative θ) (sourceMinimalEnvelope θ)
    (sourceMinimalEnvelope_model ω θ hbig).toNative (sourceRayExtension (sourceAssociatedRay ω θ u)) = _
  rw [sourceAssociatedRay_extension_eq_native]
  simpa only [sourceMinimalMixedMass_eq_native, sourcePotentialNonPluripolarMeasure,
    sourceMinimalEnvelope_eq_native, DiagonalMass.diagonalPotentialMass] using
    radialEnergy_canonicalRay_eq_mixed_mass_deficit ω (atlasClosedFormToNative θ) hbig
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

omit [ConnectedSpace M] in
/-- The literal physical closed geodesic has BOTH assigned original
endpoints, including its actual noninteger real cutoff horizon. -/
theorem sourceAssociatedRayStage_endpoints (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : M → EReal)
    {C : ℝ} (hC : 0 < C) :
    sourceAssociatedRayStage ω θ u C 0 = sourceMinimalEnvelope θ ∧
      sourceAssociatedRayStage ω θ u C C = sourceAssociatedCutoff θ u C := by
  simp only [sourceAssociatedRayStage_eq_native, sourceAssociatedCutoff_eq_native,
    sourceMinimalEnvelope_eq_native]
  exact ⟨cutoffStage_zero _ _ _ C, cutoffStage_terminal _ _ _ hC⟩

/-- The original reference mass is genuinely finite before the real
mass-deficit encoding; every other mass is covered by the reused mixed guard. -/
theorem sourceAssociatedReferenceMass_lt_top (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
      (sourceMinimalEnvelope_thetaPSH ω θ hbig) univ < ⊤ := by
  rw [← sourceMinimalMixedMass_last ω θ hbig (sourceMinimalEnvelope θ)
    (sourceMinimalEnvelope_thetaPSH ω θ hbig)]
  exact sourceMinimalMixedMass_lt_top ω θ hbig _ _ _

/-- The original nonpositive cutoff construction has the same literal
radial LIMSUP formula, through actual equality of the two full rays. -/
theorem sourceAssociatedCutoffRay_radialEnergy_eq_mixed_mass_deficit (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) (hu0 : u ≤ 0) :
    sourceRadialEnergy ω (sourceBoundedRayToGeodesicRay ω
      (sourceAssociatedCutoffBoundedRay ω θ hbig hu hu0)) =
      (((∑ j : Fin (n + 1), ((sourceMinimalMixedMass ω θ hbig u hu j).toReal -
        (sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
          (sourceMinimalEnvelope_thetaPSH ω θ hbig) univ).toReal)) / (n + 1 : ℝ) : ℝ) : EReal) := by
  have he : sourceAssociatedBoundedRay ω θ hbig hu =
      sourceAssociatedCutoffBoundedRay ω θ hbig hu hu0 :=
    Subtype.ext (sourceAssociatedRay_eq_cutoff_of_nonpositive ω θ hbig hu hu0)
  simpa only [he] using sourceAssociatedRay_radialEnergy_eq_mixed_mass_deficit ω θ hbig hu

/-- The whole arbitrary-input normalization conclusion: actual R-infinity,
literal original origin, invariance under EVERY real constant, and agreement
with the unnormalized construction for original nonpositive inputs. The
preceding source-distance and literal mass theorems give the other clauses. -/
theorem sourceAssociatedRay_normalization_properties (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {u : M → EReal} (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    (sourceAssociatedRay ω θ u ∈ sourceBoundedRays ω θ (sourceMinimalEnvelope θ)
      (sourceMinimalEnvelope_model ω θ hbig)) ∧
    sourceAssociatedRay ω θ u ⟨0, by simp⟩ = sourceMinimalEnvelope θ ∧
    (∀ c : ℝ, sourceAssociatedRay ω θ (fun x => u x - (c : EReal)) = sourceAssociatedRay ω θ u) ∧
    (u ≤ 0 → sourceAssociatedRay ω θ u = sourceAssociatedCutoffRay ω θ u) :=
  ⟨sourceAssociatedRay_mem_boundedRays ω θ hbig hu,
    (sourceAssociatedRay_mem_boundedRays ω θ hbig hu).2,
    sourceAssociatedRay_sub_const_eq ω θ hu,
    sourceAssociatedRay_eq_cutoff_of_nonpositive ω θ hbig hu⟩

end SGPT.PSH.VariableComplexAtlas
