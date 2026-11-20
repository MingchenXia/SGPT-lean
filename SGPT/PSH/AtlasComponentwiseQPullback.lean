import SGPT.PSH.AtlasNativeComponentModification
import SGPT.PSH.AtlasComponentDivisorAssembly
import SGPT.PSH.GeometricQPullbackAnyDimension

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

/-- Pure substitution in model indices ONLY. The original-input producer below
internally manufactures every genuine native geometric input. -/
private def native_q_pullback_index_transport
    {a b n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [csM : ChartedSpace (ComplexModel a) M] [cmM : IsComplexManifold a M]
    [csN : ChartedSpace (ComplexModel b) N] [cmN : IsComplexManifold b N]
    (D : EffectiveGeometricQDivisor b N) (hn : n = a) (hm : n = b) {F : M → N}
    (hF :
      letI csM' : ChartedSpace (ComplexModel n) M := hn.symm ▸ csM
      letI cmM' : IsComplexManifold n M := by cases hn; exact cmM
      letI csN' : ChartedSpace (ComplexModel n) N := hm.symm ▸ csN
      letI cmN' : IsComplexManifold n N := by cases hm; exact cmN
      @IsAnalyticModification n N _ csN' cmN' M _ csM' cmM' F) :
    EffectiveGeometricQDivisor a M := by
  subst a
  subst b
  exact geometricQDivisorModificationPullbackAnyDimension D hF

private theorem native_q_pullback_index_transport_support
    {a b n : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [csM : ChartedSpace (ComplexModel a) M] [cmM : IsComplexManifold a M]
    [csN : ChartedSpace (ComplexModel b) N] [cmN : IsComplexManifold b N]
    (D : EffectiveGeometricQDivisor b N) (hn : n = a) (hm : n = b) {F : M → N}
    (hF :
      letI csM' : ChartedSpace (ComplexModel n) M := hn.symm ▸ csM
      letI cmM' : IsComplexManifold n M := by cases hn; exact cmM
      letI csN' : ChartedSpace (ComplexModel n) N := hm.symm ▸ csN
      letI cmN' : IsComplexManifold n N := by cases hm; exact cmN
      @IsAnalyticModification n N _ csN' cmN' M _ csM' cmM' F) :
    (native_q_pullback_index_transport D hn hm hF).support = F ⁻¹' D.support := by
  subst a
  subst b
  exact geometricQDivisorModificationPullbackAnyDimension_support D hF

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}
  [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y]
  {π : X → Y}

/-- ORIGINAL D, actual original modification and x ALONE manufacture the genuine
native component pullback. Native dimensions/models/modification are internal
outputs of the existing original-input producer, never incoming certificates. -/
def componentGeometricQPullback (D : AtlasEffectiveGeometricQDivisor B)
    (hπ : A.IsAtlasAnalyticModification B π) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    EffectiveGeometricQDivisor (A.pointDimension x) (A.componentOpen x) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let := B.componentChartedSpace (π x)
  let := B.componentComplexManifold_of_paracompact (π x)
  let H := hπ.exists_native_component_modification x
  let n := Classical.choose H
  let hn : n = A.pointDimension x := Classical.choose (Classical.choose_spec H)
  let hm : n = B.pointDimension (π x) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec H))
  let hF := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec H))
  exact native_q_pullback_index_transport (D.nativeComponent (π x)) hn hm hF

/-- ENTIRE literal original support preimage on SAME actual source component. -/
theorem componentGeometricQPullback_support (D : AtlasEffectiveGeometricQDivisor B)
    (hπ : A.IsAtlasAnalyticModification B π) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (componentGeometricQPullback D hπ x).support =
      Subtype.val ⁻¹' (π ⁻¹' D.support) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let := B.componentChartedSpace (π x)
  let := B.componentComplexManifold_of_paracompact (π x)
  dsimp only [componentGeometricQPullback]
  rw [native_q_pullback_index_transport_support, D.nativeComponent_support]
  rfl

/-- ORIGINAL D and actual original modification internally supply EVERY
component divisor for genuine global assembly. No component-family certificate
is an input. Reanchoring/all-open logarithmic compatibility is separate. -/
def atlasComponentwiseGeometricQPullback (D : AtlasEffectiveGeometricQDivisor B)
    (hπ : A.IsAtlasAnalyticModification B π) : AtlasEffectiveGeometricQDivisor A :=
  divisorOfNativeComponents (fun c => componentGeometricQPullback D hπ (componentAnchor c))

/-- Exact coefficient at EVERY native prime on EACH SAME internally represented
actual component. The right side is the internally produced genuine pullback. -/
theorem atlasComponentwiseGeometricQPullback_coefficient
    (D : AtlasEffectiveGeometricQDivisor B) (hπ : A.IsAtlasAnalyticModification B π)
    (c : ConnectedComponents X) :
    letI := A.componentChartedSpace (componentAnchor c)
    letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
    ∀ P : GeometricPrimeCarrier (A.pointDimension (componentAnchor c))
        (A.componentOpen (componentAnchor c)),
      (atlasComponentwiseGeometricQPullback D hπ).coefficient
        (A.nativePrimeOriginalCarrier (componentAnchor c) P) =
      (componentGeometricQPullback D hπ (componentAnchor c)).coefficient P := by
  let := A.componentChartedSpace (componentAnchor c)
  let := A.componentComplexManifold_of_paracompact (componentAnchor c)
  intro P
  exact divisorOfNativeComponents_coefficient
    (fun c => componentGeometricQPullback D hπ (componentAnchor c)) ⟨c, P⟩

/-- Full original support preimage, including exceptional/singular points and
all zero-dimensional components. No coefficient or ideal is inferred from it. -/
theorem atlasComponentwiseGeometricQPullback_support
    (D : AtlasEffectiveGeometricQDivisor B) (hπ : A.IsAtlasAnalyticModification B π) :
    (atlasComponentwiseGeometricQPullback D hπ).support = π ⁻¹' D.support := by
  have hs := divisorOfNativeComponents_support
    (fun c => componentGeometricQPullback D hπ (componentAnchor c))
  refine hs.trans ?_
  ext x
  constructor
  · intro hx
    obtain ⟨c, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    let := A.componentChartedSpace (componentAnchor c)
    let := A.componentComplexManifold_of_paracompact (componentAnchor c)
    rw [componentGeometricQPullback_support] at hp
    exact hp
  · intro hx
    let c := ConnectedComponents.mk x
    let := A.componentChartedSpace (componentAnchor c)
    let := A.componentComplexManifold_of_paracompact (componentAnchor c)
    have hxc : x ∈ connectedComponent (componentAnchor c) :=
      (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec c).symm
    let p : A.componentOpen (componentAnchor c) := ⟨x, hxc⟩
    have hp : p ∈ (componentGeometricQPullback D hπ (componentAnchor c)).support := by
      rw [componentGeometricQPullback_support]
      exact hx
    exact Set.mem_iUnion.mpr ⟨c, ⟨p, hp, rfl⟩⟩

end SGPT.PSH.VariableComplexAtlas
