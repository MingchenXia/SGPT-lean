import SGPT.Unibranch.NativeNov16AmbientPSHStabilizationProduct
import SGPT.Unibranch.PrimeNov16StabilizedAnalyticModel
import SGPT.Unibranch.ComplexSpacePSHPullbackFinite

/-! Full original local ambient PSH pullback, including arbitrary pole points.
Blueprint: native-nov16-psh-pole-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16LocalAmbientPSHPullback
open SourceReducedComplexSpace
namespace S
export PrimeNov16StabilizedAnalyticModel
  (domain carrier carrier_analytic projection inclusion modelIso split split_carrier_coordinates
   domain_connected domain_eq_split_preimage)
end S

def stabilizedEmbedding {Y : SourceReducedComplexSpace} (a : LocalEmbedding Y) : LocalEmbedding Y where
  dim := a.dim+1
  ambient := S.domain a.ambient
  carrier := S.carrier a.ambient a.carrier
  analytic := S.carrier_analytic a.ambient a.carrier a.analytic
  map := (S.projection a.ambient a.carrier a.analytic).hom.left ≫ a.map
  isOpenImmersion := by
    let : LocallyRingedSpace.IsOpenImmersion a.map := a.isOpenImmersion
    infer_instance
  overPoint := by
    rw [Category.assoc,a.overPoint]
    exact PrimeNov16StabilizedAnalyticModel.projection_scalar a.ambient a.carrier a.analytic

theorem stabilized_toPoint {Y : SourceReducedComplexSpace} (a : LocalEmbedding Y)
    (z : S.carrier a.ambient a.carrier) :
    (stabilizedEmbedding a).toPoint z = a.toPoint ((S.projection a.ambient a.carrier a.analytic).hom.left.base z) := rfl

theorem projection_inclusion_point {Y : SourceReducedComplexSpace} (a : LocalEmbedding Y) (c : a.carrier) :
    (S.projection a.ambient a.carrier a.analytic).hom.left.base
      ((S.inclusion a.ambient a.carrier a.analytic).hom.left.base c)=c :=
  congrArg (fun f : sourceReducedComplexSpaceModel a.ambient a.carrier a.analytic ⟶
    sourceReducedComplexSpaceModel a.ambient a.carrier a.analytic => f.hom.left.base c)
    (S.modelIso a.ambient a.carrier a.analytic).inv_hom_id

theorem pullback {X Y : SourceReducedComplexSpace} {φ : X.obj.left → EReal}
    (f : Y ⟶ X) (y : Y.obj.left)
    (hφ : X.IsLocallyAmbientPSHAt φ (f.hom.left.base y)) :
    Y.IsLocallyAmbientPSHAt (fun z => φ (f.hom.left.base z)) y := by
  obtain ⟨e,he,_heconn,ψ,hψ,hrep⟩ := hφ
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
  let T : Opens (ComplexModel a.dim) := ⟨ball c.val.val r,isOpen_ball⟩
  have hT : T ≤ a.ambient := fun z hz => hWU (hball hz)
  let b := a.restrict T hT
  let u : ComplexModel a.dim → EReal := fun z => ψ (G z)
  have hu : SGPT.Foundations.Analysis.DiscPshOn u T :=
    (SGPT.PSH.discPshOn_comp_holomorphic hW e.ambient.isOpen hG hmaps hψ).mono hball
  have hconn : IsConnected (T : Set (ComplexModel a.dim)) :=
    (convex_ball _ _).isConnected ⟨c.val.val,mem_ball_self hr⟩
  let F : ComplexModel (a.dim+1) → EReal := fun z =>
    NativeNov16AmbientPSHStabilization.potential u (S.split a.dim z)
  have hF : SGPT.PSH.PSHOn F (S.domain T) := by
    rw [S.domain_eq_split_preimage]
    exact NativeNov16AmbientPSHStabilization.psh_comp_equiv
      (NativeNov16AmbientPSHStabilization.psh_univ hu hconn.nonempty) (S.split a.dim)
  have hvalue (z : a.carrier) (hz : z.val.val ∈ W) :
      φ (f.hom.left.base (a.toPoint z)) = ψ (G z.val.val) := by
    obtain ⟨q,hq,hpq⟩ := hfac z hz
    change e.toPoint q = f.hom.left.base (a.toPoint z) at hpq
    rw [← hpq,hrep q,hq]
  let cT : b.carrier := ⟨⟨c.val.val,mem_ball_self hr⟩,c.property⟩
  have hbc : b.toPoint cT=y := by
    rw [LocalEmbedding.restrict_toPoint]
    exact hcy
  refine ⟨stabilizedEmbedding b,?_,S.domain_connected T hconn,F,hF,?_⟩
  · refine ⟨(S.inclusion b.ambient b.carrier b.analytic).hom.left.base cT,?_⟩
    rw [stabilized_toPoint,projection_inclusion_point]
    exact hbc
  · intro z
    let q : b.carrier := (S.projection b.ambient b.carrier b.analytic).hom.left.base z
    have hz : S.split a.dim z.val.val = (q.val.val,0) :=
      S.split_carrier_coordinates b.ambient b.carrier b.analytic z
    rw [stabilized_toPoint]
    change φ (f.hom.left.base (b.toPoint q)) =
      NativeNov16AmbientPSHStabilization.potential u (S.split a.dim z.val.val)
    rw [hz,NativeNov16AmbientPSHStabilization.zero]
    rw [LocalEmbedding.restrict_toPoint]
    exact hvalue _ (hball q.val.property)

end SGPT.Unibranch.NativeNov16LocalAmbientPSHPullback
