import SGPT.PSH.AtlasLogNativeEquivalence
import SGPT.PSH.AtlasComponentwiseQPullback

/-! Actual original varying-atlas proper modification preserves the literal
source logarithmic condition along its independently defined geometric pullback. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff Classical
universe u

/-- Honest pure model-index substitution of the existing actual native
modification logarithmic theorem. The output is the literal existing pure
index pullback construction, without any output logarithmic certificate. -/
private theorem native_log_pullback_index_transport
    {a b n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [csM : ChartedSpace (ComplexModel a) M] [cmM : IsComplexManifold a M]
    [csN : ChartedSpace (ComplexModel b) N] [cmN : IsComplexManifold b N]
    (D : EffectiveGeometricQDivisor b N) (u : N → EReal)
    (hu : NativeHasLogSingularitiesAlongAnyDimension D u)
    (hn : n=a) (hm : n=b) {F : M → N}
    (hF :
      letI csM' : ChartedSpace (ComplexModel n) M := hn.symm ▸ csM
      letI cmM' : IsComplexManifold n M := by cases hn;exact cmM
      letI csN' : ChartedSpace (ComplexModel n) N := hm.symm ▸ csN
      letI cmN' : IsComplexManifold n N := by cases hm;exact cmN
      @IsAnalyticModification n N _ csN' cmN' M _ csM' cmM' F) :
    NativeHasLogSingularitiesAlongAnyDimension
      (show EffectiveGeometricQDivisor a M from by
        clear hu u
        subst a
        subst b
        exact geometricQDivisorModificationPullbackAnyDimension D hF) (u ∘ F) := by
  subst a
  subst b
  exact hu.comp_native_analyticModification hF

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- The actual native predicates on internally selected original components
suffice, via the SAME assembled divisor's genuine whole-divisor reanchor.
All arbitrary-point native data are manufactured before source reconstruction. -/
theorem original_log_of_selected_native_components
    {D : AtlasEffectiveGeometricQDivisor A} {u : X → EReal} (hu : A.IsQPSH u)
    (hnat : ∀ c : ConnectedComponents X,
      letI := A.componentChartedSpace (componentAnchor c)
      letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
      NativeHasLogSingularitiesAlongAnyDimension (D.nativeComponent (componentAnchor c))
        (fun q : A.componentOpen (componentAnchor c) => u q.val)) :
    SourceHasLogSingularitiesAlong D u := by
  apply original_log_of_native_components hu
  intro x
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let c := ConnectedComponents.mk x
  let a := componentAnchor c
  have ha : a∈connectedComponent x := (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec c)
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  rw [D.nativeComponent_reanchor x a ha]
  exact (native_log_preimage_of_dimensionEq_iff
    (A.pointDimension_eq_on_connectedComponent x ha).symm (D.nativeComponent a)
    (fun q : A.componentOpen a => u q.val) (A.componentReanchorHomeomorph x a ha)
    (A.componentReanchorHomeomorph_contMDiff x a ha)
    (A.componentReanchorHomeomorph_symm_contMDiff x a ha)).mpr (hnat c)

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  {B : VariableComplexAtlas Y} {π : X → Y}

/-- ORIGINAL source logarithms and an ACTUAL original modification alone
produce complete logarithms along its genuine component geometric pullback.
Every native map, common dimension and pullback field is manufactured. -/
theorem componentGeometricQPullback_hasLog
    {D : AtlasEffectiveGeometricQDivisor B} {u : Y → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (hπ : A.IsAtlasAnalyticModification B π) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    NativeHasLogSingularitiesAlongAnyDimension (componentGeometricQPullback D hπ x)
      (fun q : A.componentOpen x => u (π q.val)) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let := B.componentChartedSpace (π x)
  let := B.componentComplexManifold_of_paracompact (π x)
  let H := hπ.exists_native_component_modification x
  let n := Classical.choose H
  let hn : n=A.pointDimension x := Classical.choose (Classical.choose_spec H)
  let hm : n=B.pointDimension (π x) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec H))
  let hF := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  dsimp only [componentGeometricQPullback]
  exact native_log_pullback_index_transport (D.nativeComponent (π x))
    (fun p : B.componentOpen (π x) => u p.val) (original_log_nativeComponent hu (π x)) hn hm hF

/-- ORIGINAL complete source logarithms pull back along the ACTUAL original
proper bimeromorphic modification to the SAME independently defined entire
geometric rational divisor pullback. No native, coefficient or type flag
premise and no compactness or globally fixed native dimension is added. -/
theorem original_log_comp_atlasAnalyticModification
    {D : AtlasEffectiveGeometricQDivisor B} {u : Y → EReal}
    (hu : SourceHasLogSingularitiesAlong D u) (hπ : A.IsAtlasAnalyticModification B π) :
    SourceHasLogSingularitiesAlong (atlasComponentwiseGeometricQPullback D hπ) (u ∘ π) := by
  apply original_log_of_selected_native_components (hu.1.comp_atlasAnalyticModification hπ)
  intro c
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  let F : ∀ c : ConnectedComponents X,A.componentNativeDivisor c :=
    fun c => componentGeometricQPullback D hπ (componentAnchor c)
  have heq := nativeComponent_divisorOfNativeComponents (A := A) F c
  change (atlasComponentwiseGeometricQPullback D hπ).nativeComponent (componentAnchor c)=
    componentGeometricQPullback D hπ (componentAnchor c) at heq
  rw [heq]
  exact componentGeometricQPullback_hasLog hu hπ (componentAnchor c)

omit [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y] in
/-- The original analytic clause retains its actual original QPSH field and
same original local rational analytic type along the genuine modification. -/
theorem original_analytic_comp_atlasAnalyticModification
    {u : Y → EReal} (hu : B.IsQPSH u) (han : B.HasRationalAnalyticType u)
    (hπ : A.IsAtlasAnalyticModification B π) :
    A.IsQPSH (u ∘ π) ∧ A.HasRationalAnalyticType (u ∘ π) :=
  ⟨hu.comp_atlasAnalyticModification hπ,han.comp_atlasAnalyticModification hπ⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
