import SGPT.PSH.SourceCapacity
import SGPT.PSH.ThetaDecreasingNets
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyDecreasingNets
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedDiamond
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyConcavity

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Every actual original ordinary P-envelope competitor is exactly a native one.
The whole supremum and original neighborhood regularization are retained. -/
theorem sourceSingularityEnvelope_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal) :
    sourceSingularityEnvelope θ φ = singularityEnvelope (atlasClosedFormToNative θ).val φ := by
  apply congrArg uscRegularization
  funext x
  change (⨆ v : sourceSingularityCompetitors θ φ, v.1 x) =
    singularitySupremum (atlasClosedFormToNative θ).val φ x
  simp only [singularitySupremum, sSup_apply, iSup_subtype]
  apply le_antisymm
  · apply iSup_le
    intro v
    exact le_iSup_of_le v.1 (le_iSup_of_le
      ⟨⟨(isThetaPSH_iff_nativeThetaPotential θ v.1).mp v.2.1, v.2.2.1⟩, v.2.2.2⟩ le_rfl)
  · apply iSup_le
    intro v
    apply iSup_le
    rintro ⟨⟨hv, hv0⟩, hvφ⟩
    exact le_iSup (fun w : sourceSingularityCompetitors θ φ => w.1 x)
      ⟨v, (isThetaPSH_iff_nativeThetaPotential θ v).mpr hv, hv0, hvφ⟩

variable [MeasurableSpace M] [CompactSpace M]

/-- The original fixed point and strictly positive actual mass, with genuine
universal source theta-PSH. The reference need not be bounded. -/
def SourceModelPotential (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ : M → EReal) : Prop :=
  ∃ hφ : (ofFixedModel n M).IsThetaPSH θ φ,
    φ = sourceSingularityEnvelope θ φ ∧
      0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ

/-- The same original model and same actual whole-space mass give precisely
the native model; this does not replace the fixed-point equation by a premise. -/
theorem sourceModelPotential_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal) :
    SourceModelPotential θ φ ↔ IsModelPotential (atlasClosedFormToNative θ) φ := by
  constructor
  · rintro ⟨hφ, heq, hmass⟩
    refine ⟨(isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ,
      heq.trans (sourceSingularityEnvelope_eq_native θ φ), ?_⟩
    exact hmass
  · intro hφ
    refine ⟨(isThetaPSH_iff_nativeThetaPotential θ φ).mpr hφ.plurisubharmonic,
      hφ.envelope_eq.trans (sourceSingularityEnvelope_eq_native θ φ).symm, ?_⟩
    exact hφ.positive_mass

/-- Exact source-to-native model dictionary for downstream consumers. -/
theorem SourceModelPotential.toNative
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) : IsModelPotential (atlasClosedFormToNative θ) φ :=
  (sourceModelPotential_iff_native θ φ).mp hφ


/-- The genuine original potential belonging to a source model. -/
theorem SourceModelPotential.thetaPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : SourceModelPotential θ φ) : (ofFixedModel n M).IsThetaPSH θ φ := hφ.choose

/-- The full original additive-constant singularity-order class. -/
def SourceRelativePSH (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ u : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH θ u ∧ SGPT.PSH.SingularityLE u φ

/-- The original relatively minimal class, without pointwise normalization. -/
def SourceRelativeEInfinity (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ u : M → EReal) : Prop :=
  (ofFixedModel n M).IsThetaPSH θ u ∧ SGPT.PSH.SingularityEquiv u φ

/-- Full mass means equality of the same actual diagonal measures. -/
def SourceRelativeFullMass (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ u : M → EReal) (hφ : SourceModelPotential θ φ) : Prop :=
  ∃ hu : (ofFixedModel n M).IsThetaPSH θ u, SGPT.PSH.SingularityLE u φ ∧
    sourcePotentialNonPluripolarMeasure θ u hu univ =
      sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ

/-- The original absolute gap integral against the potential's own measure. -/
def sourceRelativeFiniteEnergyIntegral
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) : ENNReal :=
  ∫⁻ x, canonicalERealAbsDiff (φ x) (u x) ∂sourcePotentialNonPluripolarMeasure θ u hu

/-- The source finite-energy class retains actual mass and integrability. -/
def SourceRelativeFiniteEnergy (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (φ u : M → EReal) (hφ : SourceModelPotential θ φ) : Prop :=
  SourceRelativeFullMass θ φ u hφ ∧
    ∃ hu : (ofFixedModel n M).IsThetaPSH θ u,
      sourceRelativeFiniteEnergyIntegral θ φ u hu < ⊤

omit [MeasurableSpace M] [CompactSpace M] in
/-- Exact dictionary for the entire singularity-order PSH class. -/
theorem sourceRelativePSH_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal) :
    SourceRelativePSH θ φ u ↔
      RelativePreceqClasses.RelativePSHPreceq (atlasClosedFormToNative θ) φ u := by
  exact and_congr (isThetaPSH_iff_nativeThetaPotential θ u) Iff.rfl

omit [MeasurableSpace M] [CompactSpace M] in
/-- Exact dictionary for the entire minimal-singularity class. -/
theorem sourceRelativeEInfinity_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal) :
    SourceRelativeEInfinity θ φ u ↔ RelativeEInfinity (atlasClosedFormToNative θ) φ u := by
  exact and_congr (isThetaPSH_iff_nativeThetaPotential θ u) Iff.rfl

/-- Exact full-mass dictionary retains unbounded model references. -/
theorem sourceRelativeFullMass_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    SourceRelativeFullMass θ φ u hφ ↔
      RelativePreceqClasses.RelativeFullMassPreceq (atlasClosedFormToNative θ) φ u hφ.toNative := by
  constructor
  · rintro ⟨hu, hle, hm⟩
    exact ⟨(isThetaPSH_iff_nativeThetaPotential θ u).mp hu, hle, hm⟩
  · rintro ⟨hu, hle, hm⟩
    exact ⟨(isThetaPSH_iff_nativeThetaPotential θ u).mpr hu, hle, hm⟩

/-- The gap integrals have literally the same measure and integrand. -/
theorem sourceRelativeFiniteEnergyIntegral_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceRelativeFiniteEnergyIntegral θ φ u hu = relativeFiniteEnergyIntegral
      (atlasClosedFormToNative θ) φ u ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) := rfl

/-- Exact finite-energy dictionary on the full source preceq class. -/
theorem sourceRelativeFiniteEnergy_iff_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    SourceRelativeFiniteEnergy θ φ u hφ ↔
      RelativePreceqClasses.RelativeFiniteEnergyPreceq (atlasClosedFormToNative θ) φ u hφ.toNative := by
  constructor
  · rintro ⟨hfull, hu, hint⟩
    exact ⟨(sourceRelativeFullMass_iff_native θ φ u hφ).mp hfull,
      (isThetaPSH_iff_nativeThetaPotential θ u).mp hu, hint⟩
  · rintro ⟨hfull, hu, hint⟩
    exact ⟨(sourceRelativeFullMass_iff_native θ φ u hφ).mpr hfull,
      (isThetaPSH_iff_nativeThetaPotential θ u).mpr hu, hint⟩

variable [BorelSpace M]

/-- Actual endpoint wedge with j copies of u and n-j of phi. -/
def sourceEndpointMixedMeasure
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (j : Fin (n + 1)) : Measure M :=
  GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => atlasClosedFormToNative θ)
    (fun i : Fin n => if i.val < j.val then u else φ)
    (RelativeEnergy.endpointMixedPotential_thetaPlurisubharmonic
      (atlasClosedFormToNative θ) j u φ
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ))

omit [BorelSpace M] in
/-- The source wedge is the actual native endpoint mixed measure. -/
theorem sourceEndpointMixedMeasure_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (j : Fin (n + 1)) :
    sourceEndpointMixedMeasure θ φ u hφ hu j = RelativeEnergy.endpointMixedMeasure
      (atlasClosedFormToNative θ) φ u
      ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) j := rfl

/-- The printed finite formula, with all n+1 actual endpoint integrals. -/
def sourceRelativeEnergyOfMinimalType
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hu : (ofFixedModel n M).IsThetaPSH θ u) : ℝ :=
  (∑ j : Fin (n + 1), ∫ x, canonicalERealDiffToReal (u x) (φ x)
    ∂sourceEndpointMixedMeasure θ φ u hφ hu j) / (n + 1 : ℝ)

omit [BorelSpace M] in
/-- Literal equality of the whole finite formula. -/
theorem sourceRelativeEnergyOfMinimalType_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (hu : (ofFixedModel n M).IsThetaPSH θ u) :
    sourceRelativeEnergyOfMinimalType θ φ u hφ hu =
      RelativeEnergy.relativeEnergyOfMinimalType (atlasClosedFormToNative θ) φ u
        ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hφ)
        ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu) := rfl

/-- ALL actual source minimal-type majorants enter the extension. -/
def sourceRelativeEnergyMajorantValues
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) : Set EReal :=
  {e | ∃ (v : M → EReal) (hv : SourceRelativeEInfinity θ φ v), u ≤ v ∧
    e = (sourceRelativeEnergyOfMinimalType θ φ v hφ.thetaPSH hv.1 : EReal)}

/-- The original infimum over the whole printed majorant set. -/
def sourceRelativeEnergy
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) : EReal :=
  sInf (sourceRelativeEnergyMajorantValues θ φ u hφ)

omit [BorelSpace M] in
/-- Exact reindexing of every energy majorant, in both directions. -/
theorem sourceRelativeEnergyMajorantValues_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    sourceRelativeEnergyMajorantValues θ φ u hφ =
      RelativeEnergy.relativeEnergyMajorantValues (atlasClosedFormToNative θ) φ u hφ.toNative := by
  ext e
  constructor
  · rintro ⟨v, hv, hle, he⟩
    exact ⟨v, (sourceRelativeEInfinity_iff_native θ φ v).mp hv, hle, he⟩
  · rintro ⟨v, hv, hle, he⟩
    exact ⟨v, (sourceRelativeEInfinity_iff_native θ φ v).mpr hv, hle, he⟩

omit [BorelSpace M] in
/-- The actual source inf-majorant energy equals the native energy. -/
theorem sourceRelativeEnergy_eq_native
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ u : M → EReal)
    (hφ : SourceModelPotential θ φ) :
    sourceRelativeEnergy θ φ u hφ =
      RelativeDarvasDistance.energy (atlasClosedFormToNative θ) φ hφ.toNative u := by
  exact congrArg sInf (sourceRelativeEnergyMajorantValues_eq_native θ φ u hφ)


variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ u v : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- The finite formula increases on the whole original minimal-type class. -/
theorem sourceRelativeEnergyOfMinimalType_mono (ω : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) (hu : SourceRelativeEInfinity θ φ u)
    (hv : SourceRelativeEInfinity θ φ v) (huv : u ≤ v) :
    sourceRelativeEnergyOfMinimalType θ φ u hφ.thetaPSH hu.1 ≤
      sourceRelativeEnergyOfMinimalType θ φ v hφ.thetaPSH hv.1 := by
  exact SingularModelEnergyCocycle.relativeEnergyOfMinimalType_mono ω _
    hφ.toNative.plurisubharmonic
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) hu.2 hv.2 huv

/-- The source extended energy agrees with its finite formula on E-infinity. -/
theorem sourceRelativeEnergy_eq_of_eInfinity (ω : KahlerBackground n M)
    (hu : SourceRelativeEInfinity θ φ u) :
    sourceRelativeEnergy θ φ u hφ =
      (sourceRelativeEnergyOfMinimalType θ φ u hφ.thetaPSH hu.1 : EReal) := by
  rw [sourceRelativeEnergy_eq_native]
  exact SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity ω _ hφ.toNative
    ((sourceRelativeEInfinity_iff_native θ φ u).mp hu)

omit [BorelSpace M] in
/-- Inclusion of all actual majorant sets makes the extended source energy increasing. -/
theorem sourceRelativeEnergy_mono (huv : u ≤ v) :
    sourceRelativeEnergy θ φ u hφ ≤ sourceRelativeEnergy θ φ v hφ := by
  rw [sourceRelativeEnergy_eq_native, sourceRelativeEnergy_eq_native]
  exact RelativePreceqClasses.energy_mono_of_le huv

omit [BorelSpace M] in
/-- An actual source preceq potential has a finite-type majorant. -/
theorem sourceRelativeEnergy_ne_top (hu : SourceRelativePSH θ φ u) :
    sourceRelativeEnergy θ φ u hφ ≠ ⊤ := by
  rw [sourceRelativeEnergy_eq_native]
  exact RelativePreceqClasses.energy_ne_top_of_preceq
    ((sourceRelativePSH_iff_native θ φ u).mp hu)

/-- Both original endpoint integral bounds on the whole minimal-type class. -/
theorem sourceRelativeEnergy_endpoint_bounds (ω : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) (hu : SourceRelativeEInfinity θ φ u)
    (hv : SourceRelativeEInfinity θ φ v) :
    (∫ x, canonicalERealDiffToReal (u x) (v x)
      ∂sourcePotentialNonPluripolarMeasure θ u hu.1) ≤
        sourceRelativeEnergyOfMinimalType θ φ u hφ.thetaPSH hu.1 -
          sourceRelativeEnergyOfMinimalType θ φ v hφ.thetaPSH hv.1 ∧
    sourceRelativeEnergyOfMinimalType θ φ u hφ.thetaPSH hu.1 -
      sourceRelativeEnergyOfMinimalType θ φ v hφ.thetaPSH hv.1 ≤
        ∫ x, canonicalERealDiffToReal (u x) (v x)
          ∂sourcePotentialNonPluripolarMeasure θ v hv.1 := by
  exact SingularModelEnergyCocycle.integral_le_relativeEnergyOfMinimalType_sub_le ω _
    hφ.toNative.plurisubharmonic
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) hu.2 hv.2

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The actual extended-real convex combination has its original zero endpoint. -/
theorem sourceConvexComb_zero (u v : M → EReal) :
    ThetaPshConvexCombination.convexComb (0 : ℝ) u v = v := by
  funext x
  change (0 : EReal) * u x + ((1 - 0 : ℝ) : EReal) * v x = v x
  simp

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The actual extended-real convex combination has its original one endpoint. -/
theorem sourceConvexComb_one (u v : M → EReal) :
    ThetaPshConvexCombination.convexComb (1 : ℝ) u v = u := by
  funext x
  change (1 : EReal) * u x + ((1 - 1 : ℝ) : EReal) * v x = u x
  simp

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- Closed-interval convex combinations stay in the actual source E-infinity class;
the two endpoints are retained explicitly. -/
theorem sourceRelativeEInfinity_convexComb
    (hu : SourceRelativeEInfinity θ φ u) (hv : SourceRelativeEInfinity θ φ v)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SourceRelativeEInfinity θ φ (ThetaPshConvexCombination.convexComb t u v) := by
  rcases eq_or_lt_of_le ht0 with hzero | ht0'
  · subst t
    rw [sourceConvexComb_zero]
    exact hv
  rcases eq_or_lt_of_le ht1 with hone | ht1'
  · subst t
    rw [sourceConvexComb_one]
    exact hu
  exact (sourceRelativeEInfinity_iff_native θ φ _).mpr
    ⟨ThetaPshConvexCombination.isThetaPshPotential_convexComb
      ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
      ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) ht0' ht1',
      SingularModelEnergyConcavity.sameSingularityTypeOn_convexComb hu.2 hv.2 ht0' ht1'⟩

/-- Whole original concavity on the CLOSED interval [0,1], including its identities. -/
theorem sourceRelativeEnergy_concave (ω : KahlerBackground n M)
    (hφ : SourceModelPotential θ φ) (hu : SourceRelativeEInfinity θ φ u)
    (hv : SourceRelativeEInfinity θ φ v) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sourceRelativeEnergyOfMinimalType θ φ u hφ.thetaPSH hu.1 +
      (1 - t) * sourceRelativeEnergyOfMinimalType θ φ v hφ.thetaPSH hv.1 ≤
      sourceRelativeEnergyOfMinimalType θ φ (ThetaPshConvexCombination.convexComb t u v)
        hφ.thetaPSH (sourceRelativeEInfinity_convexComb hu hv ht0 ht1).1 := by
  rcases eq_or_lt_of_le ht0 with hzero | ht0'
  · subst t
    simp [sourceConvexComb_zero]
  rcases eq_or_lt_of_le ht1 with hone | ht1'
  · subst t
    simp [sourceConvexComb_one]
  exact SingularModelEnergyConcavity.relativeEnergyOfMinimalType_concave ω _
    hφ.toNative.plurisubharmonic
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu.1)
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv.1) hu.2 hv.2 ht0' ht1'

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The literal non-bottom directed infimum is internally proved source PSH/preceq. -/
theorem sourceRelativePSH_iInf_of_antitone [ConnectedSpace M]
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {ui : I → M → EReal} (hui : ∀ i, SourceRelativePSH θ φ (ui i))
    (hanti : ∀ x, Antitone (fun i => ui i x))
    (hne : ∃ x, (⨅ i, ui i x) ≠ ⊥) :
    SourceRelativePSH θ φ (fun x => ⨅ i, ui i x) := by
  have hraw := SGPT.PSH.thetaPlurisubharmonic_iInf_of_antitone
    (fun i => ((isThetaPSH_iff_nativeThetaPotential θ (ui i)).mp (hui i).1).1) hanti
  have hstrong := ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot hraw hne
  refine ⟨(isThetaPSH_iff_nativeThetaPotential θ _).mpr hstrong, ?_⟩
  exact (MoreSingularOn.of_le fun x _ => iInf_le (fun i => ui i x)
    (Classical.arbitrary I)).trans (hui (Classical.arbitrary I)).2

/-- Full source decreasing-net continuity: genuine limit class, energy infimum,
and convergence; no countable cofinality or bounded-reference assumption. -/
theorem sourceRelativeEnergy_directed_decreasing_net [ConnectedSpace M]
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ω : KahlerBackground n M) {ui : I → M → EReal}
    (hui : ∀ i, SourceRelativePSH θ φ (ui i))
    (hanti : ∀ x, Antitone (fun i => ui i x))
    (hne : ∃ x, (⨅ i, ui i x) ≠ ⊥) :
    SourceRelativePSH θ φ (fun x => ⨅ i, ui i x) ∧
      (⨅ i, sourceRelativeEnergy θ φ (ui i) hφ) =
        sourceRelativeEnergy θ φ (fun x => ⨅ i, ui i x) hφ ∧
      Tendsto (fun i => sourceRelativeEnergy θ φ (ui i) hφ) atTop
        (nhds (sourceRelativeEnergy θ φ (fun x => ⨅ i, ui i x) hφ)) := by
  refine ⟨sourceRelativePSH_iInf_of_antitone hui hanti hne, ?_, ?_⟩
  · simp only [sourceRelativeEnergy_eq_native]
    exact SingularModelEnergyDecreasingNets.energy_iInf_of_directed_antitone ω _ hφ.toNative
      (fun i => ((isThetaPSH_iff_nativeThetaPotential θ (ui i)).mp (hui i).1))
      (Classical.arbitrary I) (hui (Classical.arbitrary I)).2 hanti
      (fun x => tendsto_atTop_iInf (hanti x))
  · simp only [sourceRelativeEnergy_eq_native]
    exact SingularModelEnergyDecreasingNets.energy_tendsto_of_directed_antitone ω _ hφ.toNative
      (fun i => ((isThetaPSH_iff_nativeThetaPotential θ (ui i)).mp (hui i).1))
      (Classical.arbitrary I) (hui (Classical.arbitrary I)).2 hanti
      (fun x => tendsto_atTop_iInf (hanti x))

/-- Whole original E1 characterization on the original FULL-MASS domain. -/
theorem sourceRelativeFiniteEnergy_iff_bot_lt_energy (ω : KahlerBackground n M)
    (hfull : SourceRelativeFullMass θ φ u hφ) :
    SourceRelativeFiniteEnergy θ φ u hφ ↔ ⊥ < sourceRelativeEnergy θ φ u hφ := by
  rw [sourceRelativeFiniteEnergy_iff_native, sourceRelativeEnergy_eq_native]
  exact SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy ω
    ((sourceRelativeFullMass_iff_native θ φ u hφ).mp hfull)

/-- Both infinities are excluded before any finite-energy real readback. -/
theorem sourceRelativeFiniteEnergy_coe_toReal (ω : KahlerBackground n M)
    (hu : SourceRelativeFiniteEnergy θ φ u hφ) :
    ((sourceRelativeEnergy θ φ u hφ).toReal : EReal) = sourceRelativeEnergy θ φ u hφ := by
  rw [sourceRelativeEnergy_eq_native]
  exact SingularModelFiniteEnergyPreceq.coe_toReal_energy ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)

/-- Actual mixed endpoint integrability is produced for source E1 endpoints. -/
theorem sourceRelativeFiniteEnergy_endpoint_integrable [ConnectedSpace M]
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) (k : Fin (n + 1)) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (sourceEndpointMixedMeasure θ v u hv.1.choose hu.1.choose k) := by
  exact SingularModelFiniteEnergyMixedCocycle.integrable_endpoint_canonicalDiff_of_preceq ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv) k

/-- Exact original E1 mixed cocycle, retaining the printed factor and all integrals. -/
theorem sourceRelativeFiniteEnergy_mixed_cocycle [ConnectedSpace M]
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    ((n : ℝ) + 1) * ((sourceRelativeEnergy θ φ u hφ).toReal -
      (sourceRelativeEnergy θ φ v hφ).toReal) =
      ∑ k : Fin (n + 1), ∫ x, canonicalERealDiffToReal (u x) (v x)
        ∂sourceEndpointMixedMeasure θ v u hv.1.choose hu.1.choose k := by
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelFiniteEnergyMixedCocycle.mul_toReal_energy_sub_eq_sum_endpoint_integrals ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv)

/-- The original difference-of-real-energies form, after actual integrability and
finite real readback have been produced above. -/
theorem sourceRelativeFiniteEnergy_cocycle [ConnectedSpace M]
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    (sourceRelativeEnergy θ φ u hφ).toReal - (sourceRelativeEnergy θ φ v hφ).toReal =
      sourceRelativeEnergyOfMinimalType θ v u hv.1.choose hu.1.choose := by
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelFiniteEnergyMixedCocycle.toReal_energy_sub_eq_relativeEnergyOfMinimalType_of_preceq ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv)

omit [MeasurableSpace M] [CompactSpace M] [BorelSpace M] in
/-- The literal raw source rooftop equals the native envelope whenever the latter
is genuine; the full E1 consumer below manufactures this premise. -/
theorem sourceThetaRooftop_eq_native
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (hr : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u v)) :
    thetaRooftop θ u v = RelativeDarvasDistance.rooftop (atlasClosedFormToNative θ) u v := by
  have hnu := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
  have hnv := (isThetaPSH_iff_nativeThetaPotential θ v).mp hv
  apply le_antisymm
  · intro x
    apply iSup_le
    intro f
    exact ((RelativeDarvasDistance.le_rooftop_iff hnu hnv
      ((isThetaPSH_iff_nativeThetaPotential θ f.1).mp f.2.1)).mpr f.2.2) x
  · exact le_thetaRooftop ((isThetaPSH_iff_nativeThetaPotential θ _).mpr hr)
      (RelativeDarvasDistance.rooftop_le_left hnu hnv)
      (RelativeDarvasDistance.rooftop_le_right hnu hnv)

/-- Genuine original E1 rooftop closure is produced for unbounded model references. -/
theorem sourceRelativeFiniteEnergy_rooftop [ConnectedSpace M]
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    SourceRelativeFiniteEnergy θ φ (thetaRooftop θ u v) hφ := by
  have hr := RelativePreceqClasses.relativeFiniteEnergyPreceq_rooftop ω
    ((sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu)
    ((sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv)
  rw [sourceThetaRooftop_eq_native hu.1.choose hv.1.choose hr.1.plurisubharmonic]
  exact (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr hr

/-- Whole source diamond inequality on the genuine E1 class; the actual raw
source rooftop is identified using internally produced closure. -/
theorem sourceRelativeFiniteEnergy_diamond [ConnectedSpace M]
    (ω : KahlerBackground n M) (hu : SourceRelativeFiniteEnergy θ φ u hφ)
    (hv : SourceRelativeFiniteEnergy θ φ v hφ) :
    (sourceRelativeEnergy θ φ u hφ).toReal + (sourceRelativeEnergy θ φ v hφ).toReal ≤
      (sourceRelativeEnergy θ φ (fun x => max (u x) (v x)) hφ).toReal +
      (sourceRelativeEnergy θ φ (thetaRooftop θ u v) hφ).toReal := by
  have hnu := (sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mp hu
  have hnv := (sourceRelativeFiniteEnergy_iff_native θ φ v hφ).mp hv
  have hr := RelativePreceqClasses.relativeFiniteEnergyPreceq_rooftop ω hnu hnv
  rw [sourceThetaRooftop_eq_native hu.1.choose hv.1.choose hr.1.plurisubharmonic]
  simp only [sourceRelativeEnergy_eq_native]
  exact SingularModelEnergyExtendedDiamond.toReal_energy_add_le_max_add_rooftop ω _
    hφ.toNative hnu hnv

end SGPT.PSH.VariableComplexAtlas
