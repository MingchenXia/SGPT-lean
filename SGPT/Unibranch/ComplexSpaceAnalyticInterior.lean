import SGPT.Unibranch.ComplexSpaceThinChartGerm
import SGPT.Unibranch.ComplexSpaceAnalyticSubsets
import SGPT.Foundations.Analysis.Pending.IrreducibleGermLocal

/-! Genuine identity theorem in the ORIGINAL unibranch singular topology.
Blueprint: complex-space-analytic-interior.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch
namespace LocalEmbedding

/-- The original interior point is produced from actual carrier-germ
containment, using the SAME original trace and actual open embedding. -/
theorem mem_interior_of_eventually_chartGerm_le
    {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (c : e.carrier)
    {Z : Set X.obj.left} (B : Set e.ambient)
    (hrep : e.toPoint ⁻¹' Z = Subtype.val ⁻¹' B)
    (hAB : AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := e.dim) B c.val) :
    e.toPoint c ∈ interior Z := by
  let E := (complexChartAt (n := e.dim) c.val).val
  let q := E c.val
  have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
  have ht : Tendsto (fun y : e.ambient => E y-q) (𝓝 c.val) (𝓝 0) := by
    have h := ((E.continuousAt hp).sub (continuousAt_const : ContinuousAt (fun _ : e.ambient => q) c.val)).tendsto
    change Tendsto (fun y : e.ambient => E y-q) (𝓝 c.val) (𝓝 (E c.val-q)) at h
    simpa only [q,sub_self] using h
  have hev : ∀ᶠ y in 𝓝 c.val,y ∈ e.carrier → y ∈ B := by
    filter_upwards [ht.eventually hAB,E.open_source.mem_nhds hp] with y hy hys hyC
    have hyA : E y-q ∈ AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val := by
      change E y-q+q ∈ E.target ∩ E.symm ⁻¹' e.carrier
      rw [sub_add_cancel]
      exact ⟨E.map_source hys,by simpa only [mem_preimage,E.left_inv hys] using hyC⟩
    have hyB := hy hyA
    change E y-q+q ∈ E.target ∩ E.symm ⁻¹' B at hyB
    rw [sub_add_cancel] at hyB
    simpa only [mem_preimage,E.left_inv hys] using hyB.2
  have hcB : ∀ᶠ d : e.carrier in 𝓝 c,d.val ∈ B := by
    filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hev] with d hd
    exact hd d.property
  have hcZ : ∀ᶠ d : e.carrier in 𝓝 c,e.toPoint d ∈ Z := by
    filter_upwards [hcB] with d hd
    exact (Set.ext_iff.mp hrep d).mpr hd
  have hnhds : Z ∈ 𝓝 (e.toPoint c) := by
    rw [← e.isOpenEmbedding_toPoint.map_nhds_eq c]
    exact eventually_map.mpr hcZ
  exact mem_interior_iff_mem_nhds.mpr hnhds

/-- Original interior membership supplies actual translated germ containment. -/
theorem eventually_chartGerm_le_of_mem_interior
    {X : SourceReducedComplexSpace} (e : LocalEmbedding X) (c : e.carrier)
    {Z : Set X.obj.left} (B : Set e.ambient)
    (hrep : e.toPoint ⁻¹' Z = Subtype.val ⁻¹' B) (hcZ : e.toPoint c ∈ interior Z) :
    AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := e.dim) B c.val := by
  have hS : IsOpen (e.toPoint ⁻¹' interior Z) := isOpen_interior.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O,hO,hOpre⟩ := isOpen_induced_iff.mp hS
  have hcO : c.val ∈ O := by
    have h : c ∈ e.toPoint ⁻¹' interior Z := hcZ
    rw [← hOpre] at h
    exact h
  let E := (complexChartAt (n := e.dim) c.val).val
  let q := E c.val
  have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
  have hq : q ∈ E.target := E.map_source hp
  have htAdd : Tendsto (fun w : ComplexModel e.dim => w+q) (𝓝 0) (𝓝 q) :=
    (continuous_add_const q).tendsto' 0 q (zero_add q)
  have htInv : Tendsto E.symm (𝓝 q) (𝓝 c.val) := by
    have h := (E.continuousAt_symm hq).tendsto
    simpa only [q,E.left_inv hp] using h
  filter_upwards [(htInv.comp htAdd).eventually (hO.mem_nhds hcO),
    htAdd.eventually (E.open_target.mem_nhds hq)] with w hwO hwt hwA
  let a : e.carrier := ⟨E.symm (w+q),hwA.2⟩
  have haZ : e.toPoint a ∈ interior Z := by
    change a ∈ e.toPoint ⁻¹' interior Z
    rw [← hOpre]
    exact hwO
  exact ⟨hwt,(Set.ext_iff.mp hrep a).mp (interior_subset (s := Z) haZ)⟩

end LocalEmbedding
namespace SourceReducedComplexSpace

/-- Analytic continuation on the ORIGINAL unibranch singular space, from
actual intrinsic irreducible germs and the SAME original analytic subset. -/
theorem IsUnibranch.isClosed_interior_of_isAnalyticSubset
    {X : SourceReducedComplexSpace} (hX : X.IsUnibranch) {Z : Set X.obj.left}
    (hZa : X.IsAnalyticSubset Z) : IsClosed (interior Z) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨e,⟨c,hc⟩,B,hB,hrep⟩ := hZa x
  have hxc : e.toPoint c ∈ closure (interior Z) := hc.symm ▸ hx
  suffices h : e.toPoint c ∈ interior Z by exact hc ▸ h
  by_contra hnot
  have hAB : ¬ AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := e.dim) B c.val :=
    fun h => hnot (e.mem_interior_of_eventually_chartGerm_le c B hrep h)
  let E := (complexChartAt (n := e.dim) c.val).val
  let q := E c.val
  let A := AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val
  let T := AnalyticDescendingChain.chartGerm (n := e.dim) B c.val
  have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
  obtain ⟨Ω,hΩ,hΩ0,hthin⟩ := IrreducibleGermLocal.exists_thin_nhds
    (e.isIrreducibleGerm_of_isUnibranch hX c)
    (AnalyticDescendingChain.isAnalyticGerm_chartGerm hB c.val) hAB
  let K : Set e.carrier := {a | a.val ∈ E.source ∧ E a.val-q ∈ Ω}
  have hK : IsOpen K :=
    ((E.continuousOn.sub continuousOn_const).isOpen_inter_preimage E.open_source hΩ).preimage
      continuous_subtype_val
  have hV : IsOpen (e.toPoint '' K) := e.isOpenEmbedding_toPoint.isOpenMap K hK
  have hcV : e.toPoint c ∈ e.toPoint '' K :=
    ⟨c,⟨hp,by simpa only [q,sub_self] using hΩ0⟩,rfl⟩
  obtain ⟨z,⟨a,ha,haz⟩,hzint⟩ := mem_closure_iff.mp hxc _ hV hcV
  have haint : e.toPoint a ∈ interior Z := haz.symm ▸ hzint
  have hS : IsOpen (e.toPoint ⁻¹' interior Z) := isOpen_interior.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O,hO,hOpre⟩ := isOpen_induced_iff.mp hS
  have haO : a.val ∈ O := by
    have h : a ∈ e.toPoint ⁻¹' interior Z := haint
    rw [← hOpre] at h
    exact h
  let L : Set (ComplexModel e.dim) := (fun w => w+q) ⁻¹' (E.target ∩ E.symm ⁻¹' O)
  have hL : IsOpen L := (E.isOpen_inter_preimage_symm hO).preimage (continuous_id.add_const q)
  have hcoord : E a.val-q ∈ A := by
    change E a.val-q+q ∈ E.target ∩ E.symm ⁻¹' e.carrier
    rw [sub_add_cancel]
    exact ⟨E.map_source ha.1,by simpa only [mem_preimage,E.left_inv ha.1] using a.property⟩
  have hcoordL : E a.val-q ∈ L := by
    change E a.val-q+q ∈ E.target ∩ E.symm ⁻¹' O
    rw [sub_add_cancel]
    exact ⟨E.map_source ha.1,by simpa only [mem_preimage,E.left_inv ha.1] using haO⟩
  obtain ⟨w,⟨hwL,hwA,_hwΩ⟩,hwB⟩ := hthin L hL ⟨E a.val-q,hcoordL,hcoord,ha.2⟩
  let b : e.carrier := ⟨E.symm (w+q),hwA.2⟩
  have hbint : e.toPoint b ∈ interior Z := by
    change b ∈ e.toPoint ⁻¹' interior Z
    rw [← hOpre]
    exact hwL.2
  apply hwB
  exact ⟨hwA.1,(Set.ext_iff.mp hrep b).mp (interior_subset (s := Z) hbint)⟩

end SourceReducedComplexSpace
end SGPT.Unibranch
