import SGPT.Unibranch.ComplexSpaceThinChartGerm
import SGPT.Unibranch.ComplexSpaceAnalyticSubsets

/-! Actual connected analytic-complement neighborhoods in the ORIGINAL
unibranch topology. Blueprint: complex-space-unibranch-complement.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch
namespace LocalEmbedding

/-- Original unibranchness and actual trace thinness manufacture the
actual connected neighborhood and its LITERAL connected complement. -/
theorem exists_connected_neighborhood_diff {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (e : LocalEmbedding X) (c : e.carrier)
    {Z : Set X.obj.left} (hZ : interior Z = ∅) (B : Set e.ambient)
    (hB : IsComplexAnalyticSubset (n := e.dim) B)
    (hrep : e.toPoint ⁻¹' Z = Subtype.val ⁻¹' B)
    {N : Set X.obj.left} (hN : IsOpen N) (hcN : e.toPoint c ∈ N) :
    ∃ V : Set X.obj.left,IsOpen V ∧ e.toPoint c ∈ V ∧ V ⊆ N ∧
      IsConnected V ∧ IsConnected (V \ Z) := by
  have hpreN : IsOpen (e.toPoint ⁻¹' N) := hN.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O,hO,hOpre⟩ := isOpen_induced_iff.mp hpreN
  have hcO : c.val ∈ O := by
    have h : c ∈ e.toPoint ⁻¹' N := hcN
    rw [← hOpre] at h
    exact h
  let E := (complexChartAt (n := e.dim) c.val).val
  let q := E c.val
  let A := AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val
  let T := AnalyticDescendingChain.chartGerm (n := e.dim) B c.val
  have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
  let W : Set (ComplexModel e.dim) := (fun w => w+q) ⁻¹' (E.target ∩ E.symm ⁻¹' O)
  have hW : IsOpen W := (E.isOpen_inter_preimage_symm hO).preimage (continuous_id.add_const q)
  have hW0 : (0 : ComplexModel e.dim) ∈ W := by
    change 0+q ∈ E.target ∩ E.symm ⁻¹' O
    rw [zero_add]
    exact ⟨E.map_source hp,by simpa only [q,mem_preimage,E.left_inv hp] using hcO⟩
  obtain ⟨Δ,hΔ,hΔ0,hAN,hconn,hconnDiff⟩ := e.exists_connected_chartGerm_diff hX c B hB
    (e.not_eventually_chartGerm_le_of_interior_empty c hZ B hrep) (hW.mem_nhds hW0)
  let K : Set e.carrier := {a | a.val ∈ E.source ∧ E a.val-q ∈ Δ}
  have hK : IsOpen K := by
    exact ((E.continuousOn.sub continuousOn_const).isOpen_inter_preimage E.open_source hΔ).preimage
      continuous_subtype_val
  let V : Set X.obj.left := e.toPoint '' K
  have hV : IsOpen V := e.isOpenEmbedding_toPoint.isOpenMap K hK
  have hcV : e.toPoint c ∈ V := ⟨c,⟨hp,by simpa only [q,sub_self] using hΔ0⟩,rfl⟩
  have hcoord (a : e.carrier) (ha : a.val ∈ E.source) : E a.val-q ∈ A := by
    change E a.val-q+q ∈ E.target ∩ E.symm ⁻¹' e.carrier
    rw [sub_add_cancel]
    exact ⟨E.map_source ha,by simpa only [mem_preimage,E.left_inv ha] using a.property⟩
  have hVN : V ⊆ N := by
    rintro y ⟨a,ha,rfl⟩
    have hWm := hAN ⟨hcoord a ha.1,ha.2⟩
    change E a.val-q+q ∈ E.target ∩ E.symm ⁻¹' O at hWm
    rw [sub_add_cancel] at hWm
    have haO : a.val ∈ O := by simpa only [mem_preimage,E.left_inv ha.1] using hWm.2
    have haN : a ∈ e.toPoint ⁻¹' N := by rw [← hOpre];exact haO
    exact haN
  let R : ↥(A ∩ Δ) → e.carrier := fun s => ⟨E.symm (s.val+q),s.property.1.2⟩
  have hR : Continuous R := by
    have hL : Continuous (fun s : ↥(A ∩ Δ) => s.val+q) := continuous_subtype_val.add_const q
    exact (E.continuousOn_symm.comp_continuous hL (fun s => s.property.1.1)).subtype_mk _
  have hRK (s : ↥(A ∩ Δ)) : R s ∈ K := by
    refine ⟨E.map_target s.property.1.1,?_⟩
    change E (E.symm (s.val+q))-q ∈ Δ
    rw [E.right_inv s.property.1.1,add_sub_cancel_right]
    exact s.property.2
  have hRsurj (a : e.carrier) (ha : a ∈ K) : ∃ s : ↥(A ∩ Δ),R s = a := by
    refine ⟨⟨E a.val-q,hcoord a ha.1,ha.2⟩,?_⟩
    apply Subtype.ext
    change E.symm (E a.val-q+q) = a.val
    rw [sub_add_cancel,E.left_inv ha.1]
  let F : ↥(A ∩ Δ) → X.obj.left := e.toPoint ∘ R
  have hF : Continuous F := e.isOpenEmbedding_toPoint.continuous.comp hR
  have hrF : range F = V := by
    ext y
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨R s,hRK s,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨s,hs⟩ := hRsurj a ha
      exact ⟨s,congrArg e.toPoint hs⟩
  have hVc : IsConnected V := by
    let singularActualCarrierWindowConnected : ConnectedSpace ↥(A ∩ Δ) :=
      isConnected_iff_connectedSpace.mp hconn
    rw [← hrF]
    exact isConnected_range hF
  let J : ↥((A ∩ Δ) \ T) → ↥(A ∩ Δ) := fun t => ⟨t.val,t.property.1⟩
  have hJ : Continuous J := continuous_subtype_val.subtype_mk _
  have hrJ : range (F ∘ J) = V \ Z := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨?_,?_⟩
      · rw [← hrF]
        exact ⟨J t,rfl⟩
      · intro hyZ
        have hyB : (R (J t)).val ∈ B := (Set.ext_iff.mp hrep (R (J t))).mp hyZ
        apply t.property.2
        exact ⟨t.property.1.1.1,hyB⟩
    · rintro ⟨⟨a,ha,hpa⟩,hyZ⟩
      obtain ⟨s,hs⟩ := hRsurj a ha
      have hsT : s.val ∉ T := by
        intro hsB
        have haB : a.val ∈ B := by
          have h : (R s).val ∈ B := hsB.2
          rwa [hs] at h
        exact hyZ (hpa ▸ (Set.ext_iff.mp hrep a).mpr haB)
      refine ⟨⟨s.val,s.property,hsT⟩,?_⟩
      exact (congrArg e.toPoint hs).trans hpa
  have hVdiff : IsConnected (V \ Z) := by
    let singularActualCarrierComplementConnected : ConnectedSpace ↥((A ∩ Δ) \ T) :=
      isConnected_iff_connectedSpace.mp hconnDiff
    rw [← hrJ]
    exact isConnected_range (hF.comp hJ)
  exact ⟨V,hV,hcV,hVN,hVc,hVdiff⟩

end LocalEmbedding
namespace SourceReducedComplexSpace

/-- Genuine connected-complement original neighborhood basis from the
actual intrinsic unibranch condition and original analytic thinness. -/
theorem IsUnibranch.exists_connected_neighborhood_diff {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) {Z : Set X.obj.left} (hZa : X.IsAnalyticSubset Z) (hZ : interior Z = ∅)
    (x : X.obj.left) {N : Set X.obj.left} (hN : IsOpen N) (hxN : x ∈ N) :
    ∃ V : Set X.obj.left,IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ IsConnected V ∧ IsConnected (V \ Z) := by
  obtain ⟨e,⟨c,hc⟩,B,hB,hrep⟩ := hZa x
  have hcN : e.toPoint c ∈ N := hc.symm ▸ hxN
  obtain ⟨V,hV,hcV,hVN,hconn,hconnDiff⟩ :=
    e.exists_connected_neighborhood_diff hX c hZ B hB hrep hN hcN
  exact ⟨V,hV,hc ▸ hcV,hVN,hconn,hconnDiff⟩

end SourceReducedComplexSpace
end SGPT.Unibranch
