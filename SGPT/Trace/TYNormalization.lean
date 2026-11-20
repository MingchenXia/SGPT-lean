import SGPT.Trace.TYDescentInterface
import SGPT.Unibranch.NativeNov16NormalizationExistence
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift
import SGPT.Unibranch.HironakaG11PresPresentation
import SGPT.Unibranch.NativeNov16AmbientFormRestriction
import SGPT.Unibranch.ComplexSpaceFormPullbackClosed

/-!
# The normalization `Ỹ` of `Y` as a `TildeY`

Source: `chapter_trace.tex`, Section "The definition of the trace operator": `Ỹ` is the
normalization of the irreducible analytic subset `Y` of the compact Kähler manifold `X`.

The normalization of the complex space `(Y, 𝒪_X/𝓘_Y)` is `NativeNov16NormalizationSpace.source`
with its projection `p : Ỹ → Y` (finite, proper, surjective, normal source, an isomorphism over
the intrinsic regular locus: `NativeNov16NormalizationSpace`, `NativeNov16NormalizationExistence`),
with the names `KSNormalizedSubvariety.normalization`, `normalizationMap`, `restrictForm`.
This file packages it as a `TildeY Y` (`normalizationTildeY`):

* the point map `Ỹ → X` is `p` followed by the inclusion `Y ⊆ X`;
* it is injective over `Y_reg` and the preimage of `Y_reg` is dense: the intrinsic singular
  locus of `(Y, 𝒪_X/𝓘_Y)` is the embedded singular set of `Y` (`HironakaG11PresPresentation`),
  which is `singularLocus Y` (`Trace2Resolution.singularSet_eq_singularLocus`), and `p` is an
  isomorphism over the intrinsic regular locus, whose preimage is dense;
* `θ|_Ỹ` is `KSNormalizedSubvariety.restrictForm Y θ = SpaceForm.pullback (SpaceForm.ofClosedAnalytic Y θ) p`
  (closed and `(1,1)`);
* the resolution of `Ỹ`: the strict transform `Y'` of `Y` under its embedded resolution (a
  resolution target of `Y`, as in `Trace2Resolution.exists_resolutionTarget`) with the lift
  `Y' → Ỹ` of the resolution morphism through the normalization (universal property,
  `PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift.resolutionLift`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.TY

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace
  SGPT.Foundations.Analysis.Pending.HironakaResolutionSpaceComplex
  SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
  SGPT.Foundations.Analysis.Pending.HironakaIntrinsicComplexAnalyticRegularLocus
  SGPT.Trace.Trace2Resolution SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open HironakaEmbeddedAnalytic (singularSet)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! The normalization `Ỹ` of `(C, 𝒪/𝓘_C)`, its map to `(C, 𝒪/𝓘_C)` and `θ|_Ỹ`: local notations
for the objects of lane KS (`KSNormalizedSubvariety.normalization`, `normalizationMap`,
`restrictForm`, which are these terms). -/

local notation "normalization" C:max hC:max =>
  NativeNov16NormalizationSpace.source (ofClosedAnalytic C hC)

local notation "normalizationMap" C:max hC:max =>
  NativeNov16NormalizationSpace.projection (ofClosedAnalytic C hC)

local notation "restrictForm" C:max hC:max θ:max =>
  SpaceForm.pullback (SpaceForm.ofClosedAnalytic C hC θ) (normalizationMap C hC)

namespace Normalization

private theorem ofClosedAnalytic_isClosed (C : Set X) (hC : IsComplexAnalyticSubset (n := n) C)
    (θ : ClosedRealOneOneForm n X) : (SpaceForm.ofClosedAnalytic C hC θ.val).IsClosed := by
  intro c
  exact ⟨LocalEmbedding.ofChart C hC c.val, mem_range_chartModelMap (n := n) C c.property,
    θ.val.coeff (complexChartAt c.val), θ.val.smooth (complexChartAt c.val),
    θ.property.1 (complexChartAt c.val), SpaceForm.ofClosedAnalytic_restrictsTo C hC θ.val c.val⟩

private theorem ofClosedAnalytic_isOneOne (C : Set X) (hC : IsComplexAnalyticSubset (n := n) C)
    (θ : ClosedRealOneOneForm n X) : (SpaceForm.ofClosedAnalytic C hC θ.val).IsOneOne := by
  intro c
  exact ⟨LocalEmbedding.ofChart C hC c.val, mem_range_chartModelMap (n := n) C c.property,
    θ.val.coeff (complexChartAt c.val), θ.val.smooth (complexChartAt c.val),
    fun z hz a b => θ.property.2 (complexChartAt c.val) z hz a b,
    SpaceForm.ofClosedAnalytic_restrictsTo C hC θ.val c.val⟩

variable (Y : ClosedIrreducibleAnalyticSubvariety n X)


/-- The point map `Ỹ → X`. -/
def toX (y : (normalization Y.carrier Y.analytic).obj.left) : X :=
  ((normalizationMap Y.carrier Y.analytic).hom.left.base y).val

/-- Points of `Ỹ` over `Y_reg` map to the intrinsic regular locus of `(Y, 𝒪_X/𝓘_Y)`. -/
theorem mem_intrinsicRegularLocus_iff (y : (normalization Y.carrier Y.analytic).obj.left) :
    (normalizationMap Y.carrier Y.analytic).hom.left.base y ∈
        intrinsicRegularLocus (ofClosedAnalytic Y.carrier Y.analytic).obj ↔
      toX Y y ∉ singularLocus Y := by
  have h := HironakaG11PresPresentation.mem_intrinsicSingularLocus_ofClosedAnalytic_iff
    Y.analytic ((normalizationMap Y.carrier Y.analytic).hom.left.base y)
  rw [singularSet_eq_singularLocus] at h
  constructor
  · intro hr hs
    exact (h.mpr hs) hr
  · intro hn
    by_contra hr
    exact hn (h.mp hr)

/-- The normalization map is injective over the intrinsic regular locus. -/
theorem injOn_regular : InjOn (toX Y) (toX Y ⁻¹' (singularLocus Y)ᶜ) := by
  obtain ⟨V, j, hj, hrange, hjp, -⟩ :=
    NativeNov16NormalizationExistence.isIsoOver_intrinsicRegularLocus (ofClosedAnalytic Y.carrier Y.analytic)
  intro y₁ hy₁ y₂ hy₂ heq
  have hm₁ : y₁ ∈ range j.base := by
    rw [hrange]
    exact (mem_intrinsicRegularLocus_iff Y y₁).mpr hy₁
  have hm₂ : y₂ ∈ range j.base := by
    rw [hrange]
    exact (mem_intrinsicRegularLocus_iff Y y₂).mpr hy₂
  obtain ⟨a₁, rfl⟩ := hm₁
  obtain ⟨a₂, rfl⟩ := hm₂
  have hp : (normalizationMap Y.carrier Y.analytic).hom.left.base (j.base a₁) =
      (normalizationMap Y.carrier Y.analytic).hom.left.base (j.base a₂) :=
    Subtype.ext heq
  have hinj := hjp.base_open.injective
  have : a₁ = a₂ := hinj (by
    change (normalizationMap Y.carrier Y.analytic).hom.left.base (j.base a₁) =
      (normalizationMap Y.carrier Y.analytic).hom.left.base (j.base a₂)
    exact hp)
  rw [this]

/-- The preimage of `Y_reg` in the normalization is dense. -/
theorem dense_regular : Dense (toX Y ⁻¹' (singularLocus Y)ᶜ) := by
  refine (NativeNov16NormalizationExistence.dense_preimage_intrinsicRegularLocus
    (ofClosedAnalytic Y.carrier Y.analytic)).mono ?_
  intro y hy
  exact (mem_intrinsicRegularLocus_iff Y y).mp hy

/-- `Ỹ` has a resolution by a resolution target of `Y`: the strict transform of `Y` in its
embedded resolution, lifted to the normalization. -/
theorem exists_lift [CompactSpace X] (omega : KahlerBackground n X) :
    ∃ (R : ResolutionTarget Y) (ν : R.V → (normalization Y.carrier Y.analytic).obj.left), Continuous ν ∧
      ∀ v, toX Y (ν v) = R.ι v := by
  have hWa : IsComplexAnalyticSubset (n := n) Y.carrier := Y.analytic
  have hpure : AnalyticDimensionBasics.IsPureDim (n := n) Y.carrier Y.dim :=
    fun _ _ hy => PureDimension.eq_dim_of_regularAtDim Y hy
  obtain ⟨M', _, _, _, σ, E, h, hreg, _omega', hCM, hcpt, omegaW, -, hval⟩ :=
    HironakaResolutionKahler.exists_kahler_strictTransform_resolution hWa hpure Y.dim_le omega
  let := SubmanifoldChartedSpace.chartedSpace Y.dim_le hreg
  have hExcS : σ '' exceptionalLocus n σ ⊆ singularLocus Y := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hx
    have hc : σ y ∈ (singularSet (n := n) Y.carrier)ᶜ := by
      rw [singularSet_eq_singularLocus]
      exact hx
    exact Set.disjoint_left.mp h.isIsomorphismOver.2 hc hy
  have hconn := StrictTransformSubvarietySequence.isConnected_strictTransform_of_isBlowupSequence
    h.isBlowupSequence Y hExcS
  have : ConnectedSpace (strictTransform n σ Y.carrier) :=
    isConnected_iff_connectedSpace.mp hconn
  have hres : IsResolutionOf Y (σ ∘ (Subtype.val : strictTransform n σ Y.carrier → M')) := by
    refine ⟨?_, singularSet (n := n) Y.carrier,
      HironakaResolutionSpaceSingular.isComplexAnalyticSubset_singularSet hWa,
      (singularSet_eq_singularLocus Y).symm.subset, ?_, ?_⟩
    · rw [range_comp, Subtype.range_coe]
      exact h.image_eq
    · intro y₁ hy₁ y₂ hy₂ heq
      exact Subtype.ext (h.isIsomorphismOver.1.injOn hy₁ hy₂ heq)
    · rw [dense_iff_closure_eq, eq_univ_iff_forall]
      intro x
      rw [closure_subtype]
      have hx : x.1 ∈ closure (σ ⁻¹' (Y.carrier \ singularSet (n := n) Y.carrier)) := by
        rw [← h.eq_closure]
        exact x.2
      refine closure_mono ?_ hx
      intro z hz
      have hz' : z ∈ strictTransform n σ Y.carrier ∩ σ ⁻¹' (singularSet (n := n) Y.carrier)ᶜ := by
        rw [h.inter_preimage_compl]
        exact hz
      exact ⟨⟨z, hz'.1⟩, hz'.2, rfl⟩
  let R : ResolutionTarget Y :=
    { V := strictTransform n σ Y.carrier
      ι := σ ∘ Subtype.val
      contMDiff := h.contMDiff.comp hval
      isResolutionOf := hres
      kahler := omegaW }
  let f := resolutionMorphism hWa h
  have hf : IsResolution f := isResolution_resolutionMorphism hWa h
  let L := PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift.resolutionLift f hf
  have hL := PrimeNov16AnalyticNormalizationOriginalResolutionNormalizationLift.resolutionLift_projection
    f hf
  refine ⟨R, fun v => L.hom.left.base v, L.hom.left.base.hom.continuous, fun v => ?_⟩
  have hb : (normalizationMap Y.carrier Y.analytic).hom.left.base (L.hom.left.base v) =
      f.hom.left.base v := by
    rw [← hL]
    rfl
  change ((normalizationMap Y.carrier Y.analytic).hom.left.base (L.hom.left.base v)).val =
    σ v.val
  rw [hb]
  rfl

end Normalization

/-- **The normalization `Ỹ` of `Y`** (`chapter_trace.tex`, `sec:trace_def`), as a `TildeY`. -/
def normalizationTildeY [CompactSpace X] (omega : KahlerBackground n X)
    (Y : ClosedIrreducibleAnalyticSubvariety n X) : TildeY Y where
  space := normalization Y.carrier Y.analytic
  toX := Normalization.toX Y
  continuous_toX :=
    continuous_subtype_val.comp (normalizationMap Y.carrier Y.analytic).hom.left.base.hom.continuous
  toX_mem y := ((normalizationMap Y.carrier Y.analytic).hom.left.base y).property
  injOn_regular := Normalization.injOn_regular Y
  dense_regular := Normalization.dense_regular Y
  restrict θ := restrictForm Y.carrier Y.analytic θ.val
  restrict_isClosed θ := (Normalization.ofClosedAnalytic_isClosed Y.carrier Y.analytic θ).pullback _
  restrict_isOneOne θ := (Normalization.ofClosedAnalytic_isOneOne Y.carrier Y.analytic θ).pullback _
  exists_lift := Normalization.exists_lift Y omega

end SGPT.Trace.TY
