import SGPT.PSH.LogResFinModification
import SGPT.PSH.LogResFinSigma
import SGPT.PSH.AtlasLogModification
import SGPT.PSH.AtlasOpenQCoefficientReadback
import SGPT.PSH.NativeLogBiholomorphicEquivalence
import SGPT.PSH.LocalIntrinsicAnalyticPullback
import SGPT.Foundations.Analysis.Pending.BlowupConnected

/-!
# Log resolutions on complex manifolds whose components have different dimensions

Source: `chapter_pshfunctions.tex`, `def:logres` and `thm:resolvelogsing`; `def:modif`
(`appendix_unibranch.tex`) and `conventions.tex` for modifications.  The book's complex
manifolds may have connected components of different dimensions; they are formalized by
`VariableComplexAtlas` (charts of varying dimension), whose connected components carry native
pure-dimensional structures (`actualComponentPoint A c`, `actualComponentChartedSpace`).

* `IsAtlasOpenBiholomorphism A' B β V`: `β` is a biholomorphism of a (native) manifold onto the
  open subset `V` of a varying-dimension manifold.
* `IsBlowupSequenceOverComponent A B π c`: over the connected component `c` of `X` (a
  pure-dimensional compact manifold when `X` is compact), `π` is a finite composition of
  blow-ups with smooth centres, up to a biholomorphism of `π⁻¹(c)`.  A blow-up of `X` along a
  smooth centre is the blow-up of each component along the trace of the centre, so a finite
  composition of blow-ups of a compact `X` (finitely many components) is the same as a finite
  composition of blow-ups of each component: `IsAtlasBlowupModification` (`def:modif`).
* `IsBlowupSequenceOverOpen`, `IsAtlasConventionModification` (`conventions.tex`): proper
  bimeromorphic (`IsAtlasAnalyticModification`) and locally a finite composition of blow-ups.
* `IsAtlasSourceModification`: `def:modif` for compact `X`, the conventions' notion otherwise.
* `AtlasIsSNC D`: simple normal crossing effective `ℚ`-divisor (`EffectiveGeometricQDivisor.IsSNC`
  on the native structure of every connected component; SNC is local).
* `IsAtlasLogResolution A B φ π` (`def:logres`): a modification such that `φ ∘ π` has log
  singularities (`SourceHasLogSingularitiesAlong`, the verified varying-dimension form of
  `def:pshfunctions:L1393`) along a simple normal crossing divisor.
* `exists_isAtlasLogResolution` (`thm:resolvelogsing`): on a compact complex manifold whose
  components may have different dimensions, every quasi-psh `φ` with analytic singularities
  (`HasRationalAnalyticType`, the source's local notion) has a log resolution.  The resolution is
  assembled from the native log resolutions of the (finitely many) components, on the disjoint
  union `Σ c, Y_c` with its varying-dimension atlas `sigmaNativeAtlas`.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas.LogResFin

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff

universe u

/-! ### Definitions -/

section Definitions

variable {W : Type u} [TopologicalSpace W] {X : Type u} [TopologicalSpace X] {Y : Type u}
  [TopologicalSpace Y]

/-- `β : W → Y` is a biholomorphism onto the open subset `V`: `V` is open, `β` maps onto `V`, is
holomorphic, and has a left inverse which is holomorphic on `V`. -/
def IsAtlasOpenBiholomorphism (A' : VariableComplexAtlas W) (B : VariableComplexAtlas Y)
    (β : W → Y) (V : Set Y) : Prop :=
  IsOpen V ∧ range β = V ∧ A'.IsHolomorphic B β ∧
    ∃ β' : Y → W, (∀ w, β' (β w) = w) ∧ B.IsHolomorphicOn A' β' V

variable [T2Space X] [ParacompactSpace X]

/-- `def:modif`, over one connected component: over the component `c` of `X` (with its native
pure-dimensional structure), `π` is a finite composition `σ` of blow-ups with smooth centres, up
to a biholomorphism `β` of a manifold `W` onto `π⁻¹(c)`: `π ∘ β = σ`. -/
def IsBlowupSequenceOverComponent (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (π : Y → X) (c : ConnectedComponents X) : Prop :=
  letI := actualComponentChartedSpace A c
  letI := actualComponentComplexManifold A c
  ∃ (W : Type u) (_ : TopologicalSpace W)
    (_ : ChartedSpace (ComplexModel (actualComponentDimension A c)) W)
    (_ : IsComplexManifold (actualComponentDimension A c) W)
    (σ : W → actualComponentPoint A c) (β : W → Y),
    IsBlowupSequence (actualComponentDimension A c) (actualComponentPoint A c) W σ ∧
    IsAtlasOpenBiholomorphism (ofFixedModel (actualComponentDimension A c) W) B β
      (π ⁻¹' (A.componentOpen (componentAnchor c) : Set X)) ∧
    ∀ w, π (β w) = (σ w).val

/-- `def:modif` for a manifold whose components may have different dimensions: a finite
composition of blow-ups with smooth centres, i.e. over every connected component a finite
composition of blow-ups of that component. -/
def IsAtlasBlowupModification (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (π : Y → X) : Prop :=
  ∀ c : ConnectedComponents X, IsBlowupSequenceOverComponent A B π c

/-- `conventions.tex`, local clause: over the open subset `U` of the component `c`, `π` is a
finite composition of blow-ups with smooth centres of `U`, up to a biholomorphism onto `π⁻¹ U`. -/
def IsBlowupSequenceOverOpen (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (π : Y → X) (c : ConnectedComponents X) (U : Opens (actualComponentPoint A c)) : Prop :=
  letI := actualComponentChartedSpace A c
  letI := actualComponentComplexManifold A c
  ∃ (W : Type u) (_ : TopologicalSpace W)
    (_ : ChartedSpace (ComplexModel (actualComponentDimension A c)) W)
    (_ : IsComplexManifold (actualComponentDimension A c) W)
    (σ : W → U) (β : W → Y),
    IsBlowupSequence (actualComponentDimension A c) U W σ ∧
    IsAtlasOpenBiholomorphism (ofFixedModel (actualComponentDimension A c) W) B β
      (π ⁻¹' (Subtype.val '' (U : Set (actualComponentPoint A c)))) ∧
    ∀ w, π (β w) = (σ w).val.val

/-- `conventions.tex`: a modification is a proper bimeromorphic morphism which is, over a
neighbourhood of every point, a finite composition of blow-ups with smooth centres. -/
def IsAtlasConventionModification (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (π : Y → X) : Prop :=
  B.IsAtlasAnalyticModification A π ∧
    ∀ (c : ConnectedComponents X) (p : actualComponentPoint A c),
      ∃ U : Opens (actualComponentPoint A c), p ∈ U ∧ IsBlowupSequenceOverOpen A B π c U

/-- The modifications of `def:logres`: `def:modif` for compact `X`, `conventions.tex` otherwise. -/
def IsAtlasSourceModification (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (π : Y → X) : Prop :=
  (CompactSpace X → IsAtlasBlowupModification A B π) ∧
    (¬ CompactSpace X → IsAtlasConventionModification A B π)

theorem isAtlasSourceModification_iff_of_compact [CompactSpace X] {A : VariableComplexAtlas X}
    {B : VariableComplexAtlas Y} {π : Y → X} :
    IsAtlasSourceModification A B π ↔ IsAtlasBlowupModification A B π :=
  ⟨fun h => h.1 inferInstance,
    fun h => ⟨fun _ => h, fun hc => absurd (inferInstance : CompactSpace X) hc⟩⟩

theorem isAtlasSourceModification_iff_of_not_compact (hX : ¬ CompactSpace X)
    {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y} {π : Y → X} :
    IsAtlasSourceModification A B π ↔ IsAtlasConventionModification A B π :=
  ⟨fun h => h.2 hX, fun h => ⟨fun hc => absurd hc hX, fun _ => h⟩⟩

variable [T2Space Y] [ParacompactSpace Y]

/-- A simple normal crossing effective `ℚ`-divisor on a manifold whose components may have
different dimensions: on every connected component (with its native structure) the divisor is
simple normal crossing (`EffectiveGeometricQDivisor.IsSNC`). -/
def AtlasIsSNC {B : VariableComplexAtlas Y} (D : AtlasEffectiveGeometricQDivisor B) : Prop :=
  ∀ y : Y,
    letI := B.componentChartedSpace y
    letI := B.componentComplexManifold_of_paracompact y
    (D.nativeComponent y).IsSNC

/-- Source `def:logres` on complex manifolds whose components may have different dimensions: a
log resolution of `φ` is a modification `π : Y → X` (`IsAtlasSourceModification`) such that
`φ ∘ π` has log singularities (`SourceHasLogSingularitiesAlong`) along a simple normal crossing
effective `ℚ`-divisor. -/
def IsAtlasLogResolution (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (φ : X → EReal) (π : Y → X) : Prop :=
  IsAtlasSourceModification A B π ∧
    ∃ D : AtlasEffectiveGeometricQDivisor B, AtlasIsSNC D ∧ SourceHasLogSingularitiesAlong D (φ ∘ π)

end Definitions

/-! ### Existence: componentwise assembly -/

section Existence

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- Native data on each component: a native log resolution of the restriction of `φ`. -/
private theorem exists_component_logResolution [CompactSpace X] (A : VariableComplexAtlas X)
    {φ : X → EReal} (hφ : A.IsQPSH φ) (ha : A.HasRationalAnalyticType φ)
    (c : ConnectedComponents X) :
    letI := A.componentChartedSpace (componentAnchor c)
    letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
    ∃ (Yc : Type u) (_ : TopologicalSpace Yc)
      (_ : ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c))) Yc)
      (_ : IsComplexManifold (A.pointDimension (componentAnchor c)) Yc)
      (πc : Yc → A.componentOpen (componentAnchor c))
      (D : EffectiveGeometricQDivisor (A.pointDimension (componentAnchor c)) Yc),
      CompactSpace Yc ∧ ConnectedSpace Yc ∧
      IsBlowupSequence (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c))
        Yc πc ∧
      D.IsSNC ∧
      NativeHasLogSingularitiesAlongAnyDimension D ((fun p => φ p.val) ∘ πc) := by
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  have : CompactSpace (A.componentOpen (componentAnchor c)) :=
    isCompact_iff_compactSpace.mp (isClosed_connectedComponent.isCompact)
  have : ConnectedSpace (A.componentOpen (componentAnchor c)) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hφc := IsQPSH.nativeComponent hφ (componentAnchor c)
  have hac := ha.comp_atlasHolomorphic (A.nativeComponentInclusion_isHolomorphic (componentAnchor c))
  obtain ⟨Yc, tY, cY, mY, πc, hY, hseq, D, hD, hlog⟩ :=
    exists_isLogResolution_of_hasRationalAnalyticType hφc hac
  exact ⟨Yc, tY, cY, mY, πc, D, hY,
    Pending.BlowupConnected.connectedSpace_of_isBlowupSequence πc hseq, hseq, hD, hlog⟩

/-- Source `thm:resolvelogsing` for complex manifolds whose connected components may have
different dimensions: on a compact complex manifold `X` (`VariableComplexAtlas`), every quasi-psh
`φ` with analytic singularities (`HasRationalAnalyticType`) has a log resolution in the sense of
`def:logres` (`IsAtlasLogResolution`), with `Y` compact.  `Y` is the disjoint union of native log
resolutions of the finitely many components (TN's Hironaka principalization, componentwise). -/
theorem exists_isAtlasLogResolution [CompactSpace X] (A : VariableComplexAtlas X)
    {φ : X → EReal} (hφ : A.IsQPSH φ) (ha : A.HasRationalAnalyticType φ) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : ParacompactSpace Y)
      (B : VariableComplexAtlas Y) (π : Y → X),
      CompactSpace Y ∧ IsAtlasLogResolution A B φ π := by
  classical
  choose Yc tY cY mY πc Dc hcpt hconn hseq hsnc hlog using
    exists_component_logResolution A hφ ha
  let d : ConnectedComponents X → ℕ := fun c => A.pointDimension (componentAnchor c)
  let : ∀ c, TopologicalSpace (Yc c) := tY
  let : ∀ c, ChartedSpace (ComplexModel (d c)) (Yc c) := cY
  let : ∀ c, IsComplexManifold (d c) (Yc c) := mY
  have : ∀ c, CompactSpace (Yc c) := hcpt
  have : ∀ c, ConnectedSpace (Yc c) := hconn
  have := A.locallyConnectedSpace_of_variableAtlas
  have : Finite (ConnectedComponents X) := inferInstance
  let Y := (c : ConnectedComponents X) × Yc c
  have hYc : CompactSpace Y := inferInstance
  have : T2Space Y := inferInstance
  have : ParacompactSpace Y := inferInstance
  let B : VariableComplexAtlas Y := sigmaNativeAtlas (n := d) (C := Yc)
  let π : Y → X := fun p => (πc p.1 p.2).val
  -- the pieces over the components
  have hpre : ∀ c, π ⁻¹' (A.componentOpen (componentAnchor c) : Set X) = range (Sigma.mk c) := by
    intro c
    ext ⟨e, w⟩
    constructor
    · intro h
      have he : ConnectedComponents.mk (πc e w).val = e :=
        actualComponentPoint_index A e (πc e w)
      have hc : ConnectedComponents.mk (πc e w).val = c :=
        ((ConnectedComponents.coe_eq_coe').mpr h).trans (componentAnchor_spec c)
      rw [← he.symm.trans hc]
      exact ⟨w, rfl⟩
    · rintro ⟨w', hw'⟩
      cases hw'
      exact (πc c w').property
  have hmod : IsAtlasBlowupModification A B π := by
    intro c
    let := actualComponentChartedSpace A c
    let := actualComponentComplexManifold A c
    obtain ⟨y₀⟩ := (hconn c).toNonempty
    refine ⟨Yc c, tY c, cY c, mY c, πc c, Sigma.mk c, hseq c, ?_, fun _ => rfl⟩
    rw [hpre c]
    exact ⟨isOpen_range_sigmaMk, rfl, sigmaMk_isHolomorphic (n := d) c, sigmaProj c y₀,
      sigmaProj_mk c y₀, sigmaProj_isHolomorphicOn (n := d) c y₀⟩
  -- holomorphy of `π` and quasi-plurisubharmonicity of `φ ∘ π`
  have hπhol : B.IsHolomorphic A π := by
    apply isHolomorphic_sigma_of_forall A π
    intro c
    let := A.componentChartedSpace (componentAnchor c)
    let := A.componentComplexManifold_of_paracompact (componentAnchor c)
    change (ofFixedModel (d c) (Yc c)).IsHolomorphic A (Subtype.val ∘ πc c)
    exact isHolomorphic_comp (nativeHolomorphicMap_isHolomorphic (hseq c).contMDiff)
      (A.nativeComponentInclusion_isHolomorphic (componentAnchor c))
  have hQ : B.IsQPSH (φ ∘ π) := by
    apply (hφ.comp_holomorphic_iff_component_nonbot hπhol).mpr
    rintro ⟨c, y⟩
    obtain ⟨w, -, hw⟩ := (hlog c).1.locallyNondegenerate y univ isOpen_univ (mem_univ y)
    exact ⟨⟨c, w⟩, sigma_mk_mem_connectedComponent c y w, hw⟩
  -- the native divisors on the components of `Y`
  have hdim : ∀ (c : ConnectedComponents X) (y : Yc c),
      B.pointDimension ⟨c, y⟩ = d c := fun c y => sigma_pointDimension (n := d) c y
  let F : ∀ γ : ConnectedComponents Y, B.componentNativeDivisor γ := fun γ =>
    letI := B.componentChartedSpace (componentAnchor γ)
    letI := B.componentComplexManifold_of_paracompact (componentAnchor γ)
    geometricQDivisorBiholomorphicPreimageOfDimensionEq
      (hdim (componentAnchor γ).1 (componentAnchor γ).2) (Dc (componentAnchor γ).1)
      (sigmaComponentHomeomorph (n := d) (componentAnchor γ).1 (componentAnchor γ).2)
      (sigmaComponentHomeomorph_contMDiff (n := d) (componentAnchor γ).1 (componentAnchor γ).2)
      (sigmaComponentHomeomorph_symm_contMDiff (n := d) (componentAnchor γ).1
        (componentAnchor γ).2)
  let D : AtlasEffectiveGeometricQDivisor B := divisorOfNativeComponents (A := B) F
  have hDγ : ∀ γ : ConnectedComponents Y,
      letI := B.componentChartedSpace (componentAnchor γ)
      letI := B.componentComplexManifold_of_paracompact (componentAnchor γ)
      D.nativeComponent (componentAnchor γ) = F γ := fun γ =>
    nativeComponent_divisorOfNativeComponents F γ
  -- simple normal crossings
  have hSNC : AtlasIsSNC D := by
    intro y
    let := B.componentChartedSpace y
    let := B.componentComplexManifold_of_paracompact y
    let a := componentAnchor (ConnectedComponents.mk y)
    let := B.componentChartedSpace a
    let := B.componentComplexManifold_of_paracompact a
    have ha : a ∈ connectedComponent y :=
      (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec (ConnectedComponents.mk y))
    rw [D.nativeComponent_reanchor y a ha]
    apply isSNC_geometricQDivisorBiholomorphicPreimageOfDimensionEq
    rw [hDγ (ConnectedComponents.mk y)]
    exact isSNC_geometricQDivisorBiholomorphicPreimageOfDimensionEq _ _ _ _ _ (hsnc a.1)
  -- log singularities
  have hlocal : ∀ (c : ConnectedComponents X) (y : Yc c),
      letI := B.componentChartedSpace ⟨c, y⟩
      letI := B.componentComplexManifold_of_paracompact ⟨c, y⟩
      NativeHasLogSingularitiesAlongAnyDimension
        (geometricQDivisorBiholomorphicPreimageOfDimensionEq (hdim c y) (Dc c)
          (sigmaComponentHomeomorph (n := d) c y)
          (sigmaComponentHomeomorph_contMDiff (n := d) c y)
          (sigmaComponentHomeomorph_symm_contMDiff (n := d) c y))
        (fun q : B.componentOpen ⟨c, y⟩ => (φ ∘ π) q.val) := by
    intro c y
    let := B.componentChartedSpace ⟨c, y⟩
    let := B.componentComplexManifold_of_paracompact ⟨c, y⟩
    have hfun : (fun q : B.componentOpen ⟨c, y⟩ => (φ ∘ π) q.val) =
        ((fun p => φ p.val) ∘ πc c) ∘ sigmaComponentHomeomorph (n := d) c y := by
      funext q
      obtain ⟨w, hw⟩ := sigma_connectedComponent_subset_range c y q.property
      change φ (π q.val) = φ (πc c (sigmaProj c y q.val)).val
      rw [← hw, sigmaProj_mk]
    rw [hfun]
    exact (native_log_preimage_of_dimensionEq_iff (hdim c y) (Dc c) _ _ _ _).mpr (hlog c)
  have hLog : SourceHasLogSingularitiesAlong D (φ ∘ π) := by
    apply original_log_of_selected_native_components hQ
    intro γ
    let := B.componentChartedSpace (componentAnchor γ)
    let := B.componentComplexManifold_of_paracompact (componentAnchor γ)
    rw [hDγ γ]
    exact hlocal (componentAnchor γ).1 (componentAnchor γ).2
  exact ⟨Y, inferInstance, inferInstance, inferInstance, B, π, hYc,
    (isAtlasSourceModification_iff_of_compact).mpr hmod, D, hSNC, hLog⟩

end Existence

end SGPT.PSH.VariableComplexAtlas.LogResFin
