import SGPT.Unibranch.ComplexSpacePSHPullbackFinite

/-! Genuine original local PSH pullback at actual finite-locus closure
points, including poles. Blueprint: complex-space-psh-dense-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- Actual source finite-locus closure internally manufactures a finite
witness on the SAME source chart, hence genuine original local PSH. -/
theorem IsLocallyAmbientPSHAt.pullback_of_mem_closure_finite
    {X Y : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (f : Y ⟶ X) (y : Y.obj.left)
    (hφ : X.IsLocallyAmbientPSHAt φ (f.hom.left.base y))
    (hy : y ∈ closure {z : Y.obj.left | φ (f.hom.left.base z) ≠ ⊥}) :
    Y.IsLocallyAmbientPSHAt (fun z => φ (f.hom.left.base z)) y := by
  obtain ⟨e,he,-,ψ,hψ,hrep⟩ := hφ
  let a := LocalEmbedding.ofPoint Y y
  obtain ⟨c,hcy⟩ := LocalEmbedding.mem_range_ofPoint Y y
  have hover : (a.map ≫ f.hom.left) ≫ X.obj.hom = (modelOver a.ambient a.carrier).hom := by
    rw [Category.assoc,Over.w f.hom,a.overPoint]
  have hc : (a.map ≫ f.hom.left).base c ∈ range e.toPoint := by
    change f.hom.left.base (a.toPoint c) ∈ _
    rwa [hcy]
  obtain ⟨W,hW,hcW,hWU,G,hG,hmaps,hfac⟩ :=
    LocalEmbedding.exists_differentiableOn_factor (a.map ≫ f.hom.left) hover e c hc
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hW c.val.val hcW
  let T : Opens (ComplexModel a.dim) := ⟨Metric.ball c.val.val r,Metric.isOpen_ball⟩
  have hT : T ≤ a.ambient := fun z hz => hWU (hball hz)
  let b := a.restrict T hT
  have hyb : y ∈ range b.toPoint := by
    refine ⟨⟨⟨c.val.val,Metric.mem_ball_self hr⟩,c.property⟩,?_⟩
    rw [LocalEmbedding.restrict_toPoint]
    exact hcy
  have hvalue (z : a.carrier) (hz : z.val.val ∈ W) :
      φ (f.hom.left.base (a.toPoint z)) = ψ (G z.val.val) := by
    obtain ⟨q,hq,hpq⟩ := hfac z hz
    change e.toPoint q = f.hom.left.base (a.toPoint z) at hpq
    rw [← hpq,hrep q,hq]
  have hne := (mem_closure_iff.mp hy) (range b.toPoint) b.isOpenEmbedding_toPoint.isOpen_range hyb
  obtain ⟨z,⟨q,hq⟩,hzfin⟩ := hne
  have hqfin : φ (f.hom.left.base (b.toPoint q)) ≠ ⊥ := hq ▸ hzfin
  have hcomp := SGPT.PSH.discPshOn_comp_holomorphic hW e.ambient.isOpen hG hmaps hψ
  refine ⟨b,hyb,?_,fun z => ψ (G z),⟨hcomp.mono hball,?_,?_,?_⟩,?_⟩
  · exact convex_ball _ _ |>.isConnected ⟨c.val.val,Metric.mem_ball_self hr⟩
  · exact q.val.val
  · exact q.val.property
  · rw [← hvalue ⟨⟨q.val.val,hT q.val.property⟩,q.property⟩ (hball q.val.property)]
    exact hqfin
  · intro z
    rw [LocalEmbedding.restrict_toPoint]
    exact hvalue _ (hball z.val.property)

/-- All ORIGINAL local ambient PSH witnesses follow from actual source
finite-locus density. This does not assume or claim component nondegeneracy. -/
theorem locallyAmbientPSH_pullback_of_dense_finite {X Y : SourceReducedComplexSpace}
    {φ : X.obj.left → EReal} (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x) (f : Y ⟶ X)
    (hdense : Dense {z : Y.obj.left | φ (f.hom.left.base z) ≠ ⊥}) :
    ∀ y,Y.IsLocallyAmbientPSHAt (fun z => φ (f.hom.left.base z)) y := by
  intro y
  exact (hφ _).pullback_of_mem_closure_finite f y (hdense y)

end SGPT.Unibranch.SourceReducedComplexSpace
