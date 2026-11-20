import SGPT.PSH.SourceGeodesicRays
import SGPT.PSH.SourceDarvasSupremum
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicRayDistance

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Precisely the original model-origin R1 class. E1 is required only at
positive times; genuine E1 of the initial model is manufactured below. -/
abbrev SourceFiniteEnergyRay (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (φ : M → EReal)
    (hφ : SourceModelPotential θ φ) :=
  {ℓ : SourceRayFamily M // ℓ ∈ sourceFiniteEnergyRays omega θ φ hφ}

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ}

/-- The actual native ray is produced from the complete original ray
contract, using genuine finite-type inclusion for the initial model. -/
def sourceFiniteEnergyRayToNative (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) :
    SingularModelGeodesicRays.ModelFiniteEnergyGeodesicRay
      (atlasClosedFormToNative θ) φ hφ.toNative :=
  SingularModelGeodesicRays.ModelFiniteEnergyGeodesicRay.ofFiniteEnergyRayFromModel omega
    ((mem_sourceFiniteEnergyRays_iff_native omega θ φ hφ L.val).mp L.property)

omit [ConnectedSpace M] in
/-- The native reader retains the SAME entire original clamped function,
not merely an AE representative, and retains every original pole. -/
theorem sourceFiniteEnergyRayToNative_rawCurve (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) (t : ℝ) :
    (sourceFiniteEnergyRayToNative omega L).rawCurve t = sourceRayExtension L.val t := by
  change L.val ⟨max (max t 0) 0, _⟩ = L.val ⟨max t 0, _⟩
  exact congrArg L.val (Subtype.ext (by simp only [max_assoc, max_self]))

/-- EVERY original slice, including time zero, is internally a member
of the actual original preceq E1 class, with exactly its original value. -/
def sourceFiniteEnergyRaySlice (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) (t : Ici (0 : ℝ)) :
    SourceFiniteEnergyPotential θ φ hφ := by
  refine ⟨L.val t, (sourceRelativeFiniteEnergy_iff_native θ φ _ hφ).mpr ?_⟩
  have h := (sourceFiniteEnergyRayToNative omega L).finiteEnergy_rawCurve t.val
  simpa only [sourceFiniteEnergyRayToNative_rawCurve,
    sourceRayExtension_nonneg L.val t.val t.property] using h

/-- The literal original slice distance; the real-time reader clamps
negative times only to normalize the atTop API. -/
def sourceRaySliceDistance (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) (t : ℝ) : ℝ :=
  sourceDarvasDistance θ φ hφ
    (sourceFiniteEnergyRaySlice omega L ⟨max t 0, le_max_right t 0⟩)
    (sourceFiniteEnergyRaySlice omega K ⟨max t 0, le_max_right t 0⟩)

/-- The actual E1/rooftop source metric equals the native metric on the
SAME original potentials, for the entire normalized real-time reader. -/
theorem sourceRaySliceDistance_eq_native (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) (t : ℝ) :
    sourceRaySliceDistance omega L K t =
      RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative
        (sourceRayExtension L.val t) (sourceRayExtension K.val t) := by
  unfold sourceRaySliceDistance
  rw [sourceDarvasDistance_eq_native omega]
  rfl

omit [ConnectedSpace M] in
/-- At EVERY original nonnegative time this is exactly its original
source Darvas distance, with no off-time hypothesis or changed potential. -/
theorem sourceRaySliceDistance_nonnegTime (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) (t : Ici (0 : ℝ)) :
    sourceRaySliceDistance omega L K t.val = sourceDarvasDistance θ φ hφ
      (sourceFiniteEnergyRaySlice omega L t) (sourceFiniteEnergyRaySlice omega K t) := by
  have ht : (0 : ℝ) ≤ t.val := t.property
  have heq : (⟨max t.val 0, le_max_right t.val 0⟩ : Ici (0 : ℝ)) = t :=
    Subtype.ext (max_eq_left ht)
  simp only [sourceRaySliceDistance, heq]

/-- The WHOLE original radial-distance definition is the literal extended
limit of the actual ORIGINAL slice distances divided by time. -/
def sourceRadialDarvasDistance (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) : EReal :=
  Filter.limUnder atTop (fun t : ℝ => ((sourceRaySliceDistance omega L K t / t : ℝ) : EReal))

/-- Exact original/native radial dictionary follows from equality of the
whole actual defining ratio, rather than a named proxy or specialization. -/
theorem sourceRadialDarvasDistance_eq_native (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) :
    sourceRadialDarvasDistance omega L K =
      RelativeGeodesicRays.rayD1 (atlasClosedFormToNative θ) φ hφ.toNative
        (sourceRayExtension L.val) (sourceRayExtension K.val) := by
  simp only [sourceRadialDarvasDistance, RelativeGeodesicRays.rayD1,
    sourceRaySliceDistance_eq_native]

/-- Genuine monotone-ratio and internally produced finite-speed bounds
give the actual finite real source limit and EVERY positive-time bound.
BOTH extended endpoints are excluded by the displayed real value. -/
theorem exists_tendsto_sourceRadialDarvasDistance (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) :
    ∃ m : ℝ, 0 ≤ m ∧
      Tendsto (fun t : ℝ => sourceRaySliceDistance omega L K t / t) atTop (𝓝 m) ∧
      (∀ t : ℝ, 0 < t → sourceRaySliceDistance omega L K t / t ≤ m) ∧
      sourceRadialDarvasDistance omega L K = (m : EReal) := by
  have h0 : (sourceFiniteEnergyRayToNative omega L).rawCurve 0 =
      (sourceFiniteEnergyRayToNative omega K).rawCurve 0 := by
    rw [sourceFiniteEnergyRayToNative_rawCurve, sourceFiniteEnergyRayToNative_rawCurve,
      sourceRayExtension_nonneg L.val 0 le_rfl, sourceRayExtension_nonneg K.val 0 le_rfl,
      L.property.2, K.property.2]
  obtain ⟨m, hm, hT, hle, _⟩ :=
    SingularModelGeodesicRayDistance.exists_tendsto_rayD1 omega
      (sourceFiniteEnergyRayToNative omega L) (sourceFiniteEnergyRayToNative omega K) h0
  have hD (t : ℝ) : sourceRaySliceDistance omega L K t =
      RelativeDarvasDistance.relativeD1 (atlasClosedFormToNative θ) φ hφ.toNative
        ((sourceFiniteEnergyRayToNative omega L).rawCurve t)
        ((sourceFiniteEnergyRayToNative omega K).rawCurve t) := by
    rw [sourceRaySliceDistance_eq_native, sourceFiniteEnergyRayToNative_rawCurve,
      sourceFiniteEnergyRayToNative_rawCurve]
  have hs : Tendsto (fun t : ℝ => sourceRaySliceDistance omega L K t / t) atTop (𝓝 m) := by
    simpa only [hD] using hT
  exact ⟨m, hm, hs, fun t ht ↦ by simpa only [hD] using hle t ht,
    (EReal.tendsto_coe.mpr hs).limUnder_eq⟩

/-- The native based-ray target uses the actual genuine E1 model; the
source supplies only its prescribed initial value, not an E1 certificate. -/
def sourceFiniteEnergyRayToNativeBased (omega : KahlerBackground n M)
    (L : SourceFiniteEnergyRay omega θ φ hφ) :
    SingularModelGeodesicRayDistance.BasedModelFiniteEnergyGeodesicRay
      (atlasClosedFormToNative θ) φ hφ.toNative
      (sourceFiniteEnergyPotentialEquivNative θ φ hφ
        (sourceModelFiniteEnergyPotential omega θ φ hφ)) := by
  refine ⟨sourceFiniteEnergyRayToNative omega L, ?_⟩
  apply Subtype.ext
  change sourceRayExtension L.val 0 = φ
  rw [sourceRayExtension_nonneg L.val 0 le_rfl]
  exact L.property.2

omit [ConnectedSpace M] in
/-- Actual native equality identifies every ORIGINAL nonnegative-time
potential and hence the entire original ray; poles are retained literally. -/
theorem sourceFiniteEnergyRayToNativeBased_injective (omega : KahlerBackground n M) :
    Function.Injective (sourceFiniteEnergyRayToNativeBased (θ := θ) (φ := φ) (hφ := hφ) omega) := by
  intro L K h
  apply Subtype.ext
  funext t
  have heq := congrArg (fun R ↦ R.val.rawCurve t.val) h
  change (sourceFiniteEnergyRayToNative omega L).rawCurve t.val =
    (sourceFiniteEnergyRayToNative omega K).rawCurve t.val at heq
  simpa only [sourceFiniteEnergyRayToNative_rawCurve,
    sourceRayExtension_nonneg L.val t.val t.property,
    sourceRayExtension_nonneg K.val t.val t.property] using heq

/-- WHOLE original radial metric theorem as an actual MetricSpace on ALL
original R1 rays, through the injective SAME-function native construction.
The source theorem does not assert completeness despite its label. -/
@[instance_reducible]
def sourceRadialDarvasMetricSpace (omega : KahlerBackground n M) :
    MetricSpace (SourceFiniteEnergyRay omega θ φ hφ) :=
  MetricSpace.induced (sourceFiniteEnergyRayToNativeBased omega)
    (sourceFiniteEnergyRayToNativeBased_injective omega)
    (SingularModelGeodesicRayDistance.basedRayMetricSpace omega
      (sourceFiniteEnergyPotentialEquivNative θ φ hφ
        (sourceModelFiniteEnergyPotential omega θ φ hφ)))

/-- The actual induced metric has EXACTLY the finite real readback of the
literal ORIGINAL radial limit, whose finiteness was produced above. -/
theorem sourceRadialDarvasMetricSpace_dist (omega : KahlerBackground n M)
    (L K : SourceFiniteEnergyRay omega θ φ hφ) :
    letI := sourceRadialDarvasMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    dist L K = (sourceRadialDarvasDistance omega L K).toReal := by
  change (RelativeGeodesicRays.rayD1 (atlasClosedFormToNative θ) φ hφ.toNative
    (sourceFiniteEnergyRayToNative omega L).rawCurve
    (sourceFiniteEnergyRayToNative omega K).rawCurve).toReal = _
  rw [sourceRadialDarvasDistance_eq_native]
  congr 1
  unfold RelativeGeodesicRays.rayD1
  congr 1
  funext t
  rw [sourceFiniteEnergyRayToNative_rawCurve, sourceFiniteEnergyRayToNative_rawCurve]

end SGPT.PSH.VariableComplexAtlas
