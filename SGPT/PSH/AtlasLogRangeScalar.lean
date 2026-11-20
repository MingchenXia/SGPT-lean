import SGPT.PSH.AtlasLogNativeComponent
import SGPT.PSH.GeometricPrimeClopenRestriction

/-! Genuine original/native scalar germ dictionaries on the actual range
of an arbitrary original-component open, with no atlas-identification input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u

private theorem native_holomorphic_germ_congr {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {f g : M → ℂ} {q : M} (heq : f =ᶠ[𝓝 q] g) :
    HolomorphicAt n f q ↔ HolomorphicAt n g q := by
  constructor
  · intro h
    have ho : (ofFixedModel n M).AtlasHolomorphicAt f q := atlasHolomorphicAt_iff_native.mpr h
    exact atlasHolomorphicAt_iff_native.mp (ho.congr heq)
  · intro h
    have ho : (ofFixedModel n M).AtlasHolomorphicAt g q := atlasHolomorphicAt_iff_native.mpr h
    exact atlasHolomorphicAt_iff_native.mp (ho.congr heq.symm)

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (A : VariableComplexAtlas X) (x : X)

/-- Every scalar holomorphic germ on the SAME actual original range open
has exactly its native scalar germ; both original and native atlas structures
are manufactured internally, and original opens may be disconnected. -/
theorem range_atlasHolomorphicAt_iff
    (O : Opens (A.componentOpen x)) (q : O)
    (g : flattenOpen (A.componentOpen x) O → ℂ) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (A.openRestriction (flattenOpen (A.componentOpen x) O)).AtlasHolomorphicAt g
      (flattenHomeomorph (A.componentOpen x) O q) ↔
    HolomorphicAt (A.pointDimension x) (g ∘ flattenHomeomorph (A.componentOpen x) O) q := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let C := A.componentOpen x
  let U := flattenOpen C O
  let e := flattenHomeomorph C O
  let G : C → ℂ := extendOpens U g ∘ Subtype.val
  have heq : G =ᶠ[𝓝 q.val] extendOpens O (g ∘ e) := by
    filter_upwards [eventually_mem_opens O q] with y hy
    change extendOpens U g y.val=extendOpens O (g ∘ e) y
    rw [extendOpens_val O (g ∘ e) ⟨y,hy⟩]
    exact extendOpens_val U g (e ⟨y,hy⟩)
  calc
    _ ↔ A.AtlasHolomorphicAt (extendOpens U g) q.val.val :=
      atlasHolomorphicAt_openRestriction_iff_extend A U
    _ ↔ (A.openRestriction C).AtlasHolomorphicAt G q.val :=
      (atlasHolomorphicAt_comp_open_val_iff A C).symm
    _ ↔ HolomorphicAt (A.pointDimension x) G q.val :=
      atlasHolomorphicAt_component_iff_native A x G q.val
    _ ↔ HolomorphicAt (A.pointDimension x) (extendOpens O (g ∘ e)) q.val :=
      native_holomorphic_germ_congr heq
    _ ↔ _ := (holomorphicAt_iff_extendOpens O).symm

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
