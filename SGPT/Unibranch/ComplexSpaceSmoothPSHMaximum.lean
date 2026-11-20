import SGPT.Unibranch.ComplexBallMaximum
import SGPT.Unibranch.MiscMFornaessNarasimhanManifold
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceManifoldCharts

/-! Original smooth-local-model conversion and actual finite maximum locus.
Blueprint: complex-space-maximum-principle.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceManifoldCharts
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The ORIGINAL varying-dimensional smoothness predicate supplies actual
whole-domain model charts inside any original open neighborhood. -/
theorem IsSmooth.hasDomainCharts {X : SourceReducedComplexSpace} (hX : X.IsSmooth) :
    X.HasDomainCharts := by
  intro x N hN hxN
  obtain ⟨d,V,i,hi,hp,v,hv⟩ := hX x
  let e₀ : LocalEmbedding X := {
    dim := d
    ambient := V
    carrier := univ
    analytic := isComplexAnalyticSubset_univ
    map := (actualSubspaceUnivIso (n := d) (M := V)).hom ≫ i
    isOpenImmersion := by
      let singularSmoothChartOpenImmersion : LocallyRingedSpace.IsOpenImmersion i := hi
      infer_instance
    overPoint := by
      rw [Category.assoc,hp]
      rfl }
  let c : e₀.carrier := ⟨v,trivial⟩
  have hc : e₀.toPoint c = x := hv
  have hS : IsOpen (e₀.toPoint ⁻¹' N) := hN.preimage e₀.isOpenEmbedding_toPoint.continuous
  obtain ⟨t,ht,hts⟩ := isOpen_induced_iff.mp hS
  have hct : c.val ∈ t := by
    have hcN : c ∈ e₀.toPoint ⁻¹' N := by rwa [mem_preimage,hc]
    rw [← hts] at hcN
    exact hcN
  have hopen : IsOpen ((Subtype.val : e₀.ambient → ComplexModel e₀.dim) '' t) :=
    e₀.ambient.isOpen.isOpenMap_subtype_val t ht
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen c.val.val ⟨c.val,hct,rfl⟩
  let T : Opens (ComplexModel e₀.dim) := ⟨Metric.ball c.val.val r,Metric.isOpen_ball⟩
  have hT : T ≤ e₀.ambient := by
    intro z hz
    obtain ⟨q,-,rfl⟩ := hball hz
    exact q.property
  have hC' : ∀ z,z ∈ (univ : Set T) ↔ Opens.inclusion hT z ∈ e₀.carrier :=
    fun _ => iff_of_true trivial trivial
  refine ⟨e₀.dim,T,(e₀.restrictWith T hT univ hC').map,
    (e₀.restrictWith T hT univ hC').isOpenImmersion,
    (e₀.restrictWith T hT univ hC').overPoint,
    (convex_ball _ _).isConnected ⟨c.val.val,Metric.mem_ball_self hr⟩,?_,?_⟩
  · refine ⟨⟨⟨c.val.val,Metric.mem_ball_self hr⟩,trivial⟩,?_⟩
    change (e₀.restrictWith T hT univ hC').toPoint _ = x
    rw [LocalEmbedding.restrictWith_toPoint]
    exact hc
  · rintro _ ⟨z,rfl⟩
    change (e₀.restrictWith T hT univ hC').toPoint z ∈ N
    rw [LocalEmbedding.restrictWith_toPoint]
    have hz : Opens.inclusion hT z.val ∈ t := by
      obtain ⟨q,hq,hqz⟩ := hball z.val.property
      have hq' : q = Opens.inclusion hT z.val := Subtype.ext hqz
      rwa [← hq']
    have hzN : (⟨Opens.inclusion hT z.val,(hC' z.val).mp z.property⟩ : e₀.carrier) ∈
        e₀.toPoint ⁻¹' N := by
      rw [← hts]
      exact hz
    exact hzN

/-- Genuine local PSH on a possibly singular target has an open finite
maximum locus on every actual ORIGINAL smooth source. -/
theorem IsSmooth.isOpen_maximumLocus {X Y : SourceReducedComplexSpace}
    (hY : Y.IsSmooth) (f : Y ⟶ X) {φ : X.obj.left → EReal}
    (hφ : ∀ x,X.IsLocallyAmbientPSHAt φ x) (C : ℝ)
    (hbound : ∀ y,φ (f.hom.left.base y) ≤ (C : EReal)) :
    IsOpen {y : Y.obj.left | φ (f.hom.left.base y) = (C : EReal)} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨d,U,F,hFo,hF,_hU,hcy,_hFU⟩ := hY.hasDomainCharts y univ isOpen_univ trivial
  obtain ⟨c,hc⟩ := hcy
  have hover : (F ≫ f.hom.left) ≫ X.obj.hom = (modelOver U (univ : Set U)).hom := by
    rw [Category.assoc,Over.w f.hom,hF]
  have hdisc := discPshOn_modelPullback hφ (F ≫ f.hom.left) hover
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp U.isOpen c.val.val c.val.property
  have hmax (w : ComplexModel d) (hw : w ∈ Metric.ball c.val.val r) :
      modelPullback (F ≫ f.hom.left) φ w ≤ (C : EReal) := by
    simp only [modelPullback]
    split_ifs with hwU
    · exact hbound _
    · exact False.elim (hwU (hball hw))
  have heq : modelPullback (F ≫ f.hom.left) φ c.val.val = (C : EReal) := by
    simp only [modelPullback,dif_pos c.val.property]
    change φ (f.hom.left.base (F.base c)) = _
    rwa [hc]
  have hconst := SingularMaximum.discPshOn_eqOn_ball_of_le_of_eq hdisc c.val.val hball hmax heq
  let B : Set (univ : Set U) := {z | z.val.val ∈ Metric.ball c.val.val r}
  have hB : IsOpen B := Metric.isOpen_ball.preimage
    (continuous_subtype_val.comp continuous_subtype_val)
  have hFB : IsOpen (F.base '' B) := hFo.base_open.isOpenMap B hB
  refine Filter.mem_of_superset (hFB.mem_nhds ⟨c,Metric.mem_ball_self hr,hc⟩) ?_
  rintro z ⟨q,hq,rfl⟩
  have hq' := hconst hq
  simp only [modelPullback,dif_pos q.val.property] at hq'
  exact hq'

end SGPT.Unibranch.SourceReducedComplexSpace
