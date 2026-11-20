import SGPT.PSH.AtlasLogRangeIdeals

/-! The ACTUAL original range component and native open component are
biholomorphic, retaining their independently derived native dimensions. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u

/-- The actual homeomorphism between the two corresponding WHOLE connected
components, restricted from the actual inverse homeomorphism. -/
def connectedComponentHomeomorph {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (e : M ≃ₜ N) (q : M) :
    {z : N // z∈connectedComponent (e q)} ≃ₜ {z : M // z∈connectedComponent q} :=
  e.symm.subtype (fun z => by
    constructor
    · intro hz
      simpa only [e.symm_apply_apply] using e.symm.continuous.mapsTo_connectedComponent (e q) hz
    · intro hz
      have h := e.continuous.mapsTo_connectedComponent q hz
      simpa only [e.apply_symm_apply] using h)

/-- The actual native connected component is an open with no additional
connectedness or coordinate witness supplied by the caller. -/
def nativeConnectedOpen {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (q : M) : Opens M :=
  (ofFixedModel n M).componentOpen q

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (A : VariableComplexAtlas X) (x : X)

omit [T2Space X] [ParacompactSpace X] in
/-- The native dimensions of the SAME actual range component agree, derived
only from the original open and original ambient component constancy. -/
theorem range_component_dimension (O : Opens (A.componentOpen x)) (q : O) :
    (A.openRestriction (flattenOpen (A.componentOpen x) O)).pointDimension
      (flattenHomeomorph (A.componentOpen x) O q)=A.pointDimension x :=
  (A.openRestriction_pointDimension _ _).trans
    (A.pointDimension_eq_on_connectedComponent x q.val.property)

/-- Forward holomorphy of the SAME actual component homeomorphism, lifted
through the native open O and its actual whole connected component. -/
theorem range_component_contMDiff (O : Opens (A.componentOpen x)) (q : O) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    let B := A.openRestriction U
    let p := flattenHomeomorph (A.componentOpen x) O q
    letI := A.openRestriction_paracompactSpace U
    letI := B.componentChartedSpace p
    letI := B.componentComplexManifold_of_paracompact p
    let C := nativeConnectedOpen (n := A.pointDimension x) q
    let r : B.componentOpen p ≃ₜ C :=
      connectedComponentHomeomorph (flattenHomeomorph (A.componentOpen x) O) q
    ContMDiff 𝓘(ℂ,ComplexModel (B.pointDimension p)) 𝓘(ℂ,ComplexModel (A.pointDimension x)) ∞
      r := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let p := e q
  let := A.openRestriction_paracompactSpace U
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
  let F := (A.openRestriction_inclusion_isHolomorphic U).componentMap p
  have hpx : p.val∈connectedComponent x := q.val.property
  let a := A.componentReanchorHomeomorph x p.val hpx
  have hfun : (fun s : B.componentOpen p => (r s).val.val)=a.symm ∘ F := by
    funext s
    apply Subtype.ext
    change (r s).val.val.val=(F s).val
    exact congrArg (fun z : U => z.val) (e.apply_symm_apply s.val)
  have hbase : ContMDiff 𝓘(ℂ,ComplexModel (B.pointDimension p))
      𝓘(ℂ,ComplexModel (A.pointDimension x)) ∞ (fun s : B.componentOpen p => (r s).val.val) := by
    rw [hfun]
    exact (A.componentReanchorHomeomorph_symm_contMDiff x p.val hpx).comp
      ((A.openRestriction_inclusion_isHolomorphic U).componentMap_contMDiff p)
  have hmid : ContMDiff 𝓘(ℂ,ComplexModel (B.pointDimension p))
      𝓘(ℂ,ComplexModel (A.pointDimension x)) ∞ (fun s : B.componentOpen p => (r s).val) := by
    apply (ContMDiff.iff_comp_isImmersionOfComplement
      (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} O)).mpr
    exact ⟨continuous_subtype_val.comp r.continuous,hbase⟩
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} C)).mpr
  exact ⟨r.continuous,hmid⟩

/-- Inverse holomorphy of the SAME actual range-component map, obtained
from the existing genuine original component/open biholomorphism. -/
theorem range_component_symm_contMDiff (O : Opens (A.componentOpen x)) (q : O) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    let U := flattenOpen (A.componentOpen x) O
    let B := A.openRestriction U
    let p := flattenHomeomorph (A.componentOpen x) O q
    letI := A.openRestriction_paracompactSpace U
    letI := B.componentChartedSpace p
    letI := B.componentComplexManifold_of_paracompact p
    let C := nativeConnectedOpen (n := A.pointDimension x) q
    let r : B.componentOpen p ≃ₜ C :=
      connectedComponentHomeomorph (flattenHomeomorph (A.componentOpen x) O) q
    ContMDiff 𝓘(ℂ,ComplexModel (A.pointDimension x)) 𝓘(ℂ,ComplexModel (B.pointDimension p)) ∞
      r.symm := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let p := e q
  let := A.openRestriction_paracompactSpace U
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let := A.componentChartedSpace p.val
  let := A.componentComplexManifold_of_paracompact p.val
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
  have hpx : p.val∈connectedComponent x := q.val.property
  let a := A.componentReanchorHomeomorph x p.val hpx
  obtain ⟨_hd,Oa,k,hkval⟩ := A.exists_native_open_component_biholomorphism U p
  have hfun : (fun z : C => (k (r.symm z)).val)=
      a ∘ (fun z : C => z.val.val) := by
    funext z
    apply Subtype.ext
    rw [hkval (r.symm z)]
    rfl
  have hbase : ContMDiff 𝓘(ℂ,ComplexModel (A.pointDimension x))
      𝓘(ℂ,ComplexModel (A.pointDimension p.val)) ∞ (fun z : C => (k (r.symm z)).val) := by
    rw [hfun]
    exact (A.componentReanchorHomeomorph_contMDiff x p.val hpx).comp
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
  have hmid : ContMDiff 𝓘(ℂ,ComplexModel (A.pointDimension x))
      𝓘(ℂ,ComplexModel (A.pointDimension p.val)) ∞ (fun z : C => k (r.symm z)) := by
    apply (ContMDiff.iff_comp_isImmersionOfComplement
      (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} Oa)).mpr
    exact ⟨k.contMDiff.continuous.comp r.symm.continuous,hbase⟩
  have h := k.symm.contMDiff.comp hmid
  simpa only [Function.comp_def,k.symm_apply_apply] using h

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
