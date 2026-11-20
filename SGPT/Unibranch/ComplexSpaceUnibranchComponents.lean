import SGPT.Unibranch.ComplexSpaceAnalyticInterior
import SGPT.Unibranch.ComplexSpaceUnibranchComplement

/-! Actual original connected/irreducible component geometry under intrinsic
unibranchness. Blueprint: complex-space-unibranch-components.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch
namespace LocalEmbedding

/-- Actual restriction of the PRESCRIBED original embedding to an ambient
ball inside any original point neighborhood. -/
theorem exists_restrict_to_open {X : SourceReducedComplexSpace} (e : LocalEmbedding X)
    (c : e.carrier) {N : Set X.obj.left} (hN : IsOpen N) (hcN : e.toPoint c ∈ N) :
    ∃ (T : Opens (ComplexModel e.dim)) (hT : T ≤ e.ambient),
      e.toPoint c ∈ range (e.restrict T hT).toPoint ∧ range (e.restrict T hT).toPoint ⊆ N := by
  have hS : IsOpen (e.toPoint ⁻¹' N) := hN.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨O,hO,hOpre⟩ := isOpen_induced_iff.mp hS
  have hcO : c.val ∈ O := by
    have h : c ∈ e.toPoint ⁻¹' N := hcN
    rw [← hOpre] at h
    exact h
  have hopen : IsOpen ((Subtype.val : e.ambient → ComplexModel e.dim) '' O) :=
    e.ambient.isOpen.isOpenMap_subtype_val O hO
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen c.val.val ⟨c.val,hcO,rfl⟩
  let T : Opens (ComplexModel e.dim) := ⟨Metric.ball c.val.val r,Metric.isOpen_ball⟩
  have hT : T ≤ e.ambient := by
    intro z hz
    obtain ⟨u,-,rfl⟩ := hball hz
    exact u.property
  refine ⟨T,hT,?_,?_⟩
  · refine ⟨⟨⟨c.val.val,Metric.mem_ball_self hr⟩,c.property⟩,?_⟩
    rw [restrict_toPoint]
    rfl
  · rintro _ ⟨z,rfl⟩
    rw [restrict_toPoint]
    have hzO : Opens.inclusion hT z.val ∈ O := by
      obtain ⟨u,hu,huz⟩ := hball z.val.property
      have hEq : u = Opens.inclusion hT z.val := Subtype.ext huz
      rwa [← hEq]
    have hzN : (⟨Opens.inclusion hT z.val,z.property⟩ : e.carrier) ∈ e.toPoint ⁻¹' N := by
      rw [← hOpre]
      exact hzO
    exact hzN

end LocalEmbedding
namespace OriginalAnalyticClopen

/-- Clopen cutting preserves actual original analyticity on ANY singular space. -/
theorem isAnalyticSubset_inter {X : SourceReducedComplexSpace} {A W : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hW : IsClopen W) : X.IsAnalyticSubset (A ∩ W) := by
  intro x
  by_cases hxW : x ∈ W
  · obtain ⟨e,⟨c,hc⟩,B,hB,hrep⟩ := hA x
    obtain ⟨T,hT,hcT,hTW⟩ := e.exists_restrict_to_open c hW.isOpen (hc.symm ▸ hxW)
    let g : T → e.ambient := Opens.inclusion hT
    have hg : ContMDiff 𝓘(ℂ,ComplexModel e.dim) 𝓘(ℂ,ComplexModel e.dim) ∞ g := by
      apply (ContMDiff.subtypeVal_comp_iff e.ambient g).mp
      exact contMDiff_subtype_val
    refine ⟨e.restrict T hT,hc ▸ hcT,g ⁻¹' B,
      AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg hB,?_⟩
    ext d
    have hdW := hTW ⟨d,rfl⟩
    rw [LocalEmbedding.restrict_toPoint] at hdW
    change (e.restrict T hT).toPoint d ∈ A ∩ W ↔ g d.val ∈ B
    rw [LocalEmbedding.restrict_toPoint]
    have hiff := Set.ext_iff.mp hrep (⟨Opens.inclusion hT d.val,d.property⟩ : e.carrier)
    change e.toPoint _ ∈ A ∩ W ↔ Opens.inclusion hT d.val ∈ B
    exact ⟨fun h => hiff.mp h.1,fun h => ⟨hiff.mpr h,hdW⟩⟩
  · obtain ⟨e,he,hsub,-⟩ := LocalEmbedding.exists_domain (X := X) x hW.isClosed.isOpen_compl hxW
    refine ⟨e,he,∅,isComplexAnalyticSubset_empty,?_⟩
    ext d
    change e.toPoint d ∈ A ∩ W ↔ False
    exact ⟨fun h => (hsub ⟨d,rfl⟩) h.2,False.elim⟩

/-- Every literal original clopen subset is genuinely analytic. -/
theorem isAnalyticSubset {X : SourceReducedComplexSpace} {W : Set X.obj.left} (hW : IsClopen W) :
    X.IsAnalyticSubset W := by
  simpa only [univ_inter] using isAnalyticSubset_inter SourceReducedComplexSpace.isAnalyticSubset_univ hW

end OriginalAnalyticClopen
namespace SourceReducedComplexSpace

/-- Local connectedness of the SAME actual unibranch topology is produced
from internally manufactured connected original neighborhoods. -/
theorem IsUnibranch.locallyConnectedSpace {X : SourceReducedComplexSpace} (hX : X.IsUnibranch) :
    LocallyConnectedSpace X.obj.left := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x N hN
  obtain ⟨O,hON,hO,hxO⟩ := mem_nhds_iff.mp hN
  obtain ⟨V,hV,hxV,hVO,hconn,-⟩ := hX.exists_connected_neighborhood_diff
    isAnalyticSubset_empty (by simp) x hO hxO
  exact ⟨V,hVO.trans hON,hV,hxV,hconn⟩

/-- Actual connected components are ORIGINAL irreducible analytic components;
this supplies the original PSH component reader without a manifold proxy. -/
theorem IsUnibranch.isIrreducibleComponent_connectedComponent {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (x : X.obj.left) : X.IsIrreducibleComponent (connectedComponent x) := by
  let singularOriginalUnibranchLocallyConnected := hX.locallyConnectedSpace
  have hK : IsClopen (connectedComponent x) :=
    ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  have hirr : X.IsIrreducibleAnalyticSubset (connectedComponent x) := by
    refine ⟨OriginalAnalyticClopen.isAnalyticSubset hK, ⟨x, mem_connectedComponent⟩, ?_⟩
    intro B C hB hC hBK hCK hBC
    by_cases h : connectedComponent x ⊆ B
    · exact Or.inl (Subset.antisymm h hBK)
    · right
      obtain ⟨p, hpK, hpB⟩ := not_subset.mp h
      have hpint : p ∈ interior C := by
        refine mem_interior.mpr ⟨connectedComponent x ∩ Bᶜ, fun z hz => ?_,
          hK.isOpen.inter hB.isClosed.isOpen_compl, hpK, hpB⟩
        have : z ∈ B ∪ C := hBC ▸ hz.1
        exact this.resolve_left hz.2
      have hint : IsClopen (interior C) :=
        ⟨hX.isClosed_interior_of_isAnalyticSubset hC, isOpen_interior⟩
      have hsub := hint.connectedComponent_subset hpint
      rw [← connectedComponent_eq hpK] at hsub
      exact Subset.antisymm (hsub.trans interior_subset) hCK
  refine ⟨hirr, fun D hD hKD => ?_⟩
  have hD1 := OriginalAnalyticClopen.isAnalyticSubset_inter hD.1 hK
  have hD2 := OriginalAnalyticClopen.isAnalyticSubset_inter hD.1 hK.compl
  have hunion : D = D ∩ connectedComponent x ∪ D ∩ (connectedComponent x)ᶜ := by
    rw [← inter_union_distrib_left, union_compl_self, inter_univ]
  rcases hD.2.2 _ _ hD1 hD2 inter_subset_left inter_subset_left hunion with h | h
  · have hDK : D ⊆ connectedComponent x := by
      rw [h]
      exact inter_subset_right
    exact Subset.antisymm hDK hKD
  · exfalso
    have hx : x ∈ D := hKD mem_connectedComponent
    rw [h] at hx
    exact hx.2 mem_connectedComponent


end SourceReducedComplexSpace
end SGPT.Unibranch
