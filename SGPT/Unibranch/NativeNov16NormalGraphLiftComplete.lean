import SGPT.Unibranch.NativeNov16NormalGraphCoordinates
import SGPT.Unibranch.NativeNov16NormalGraphFactor

/-! Normal source sections construct a UNIQUE full original graph lift.
Actual pullback section/value manufacture is a separate source-facing input producer.
Blueprint: native-nov16-normal-graph-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16NormalGraphLift
open SourceReducedComplexSpace HironakaActualAnalyticSubspace
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalSectionDensity

theorem graph_lift_eq_of_dense {n : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (A : SourceReducedComplexSpace) (f : A ⟶ d.target)
    (hdense : Dense {x : A.obj.left | d.denominator (f.hom.left.base x).val.val.val ≠ 0})
    (L K : A ⟶ d.source) (hL : L ≫ d.map=f) (hK : K ≫ d.map=f) : L=K := by
  let : T2Space d.source.obj.left.toPresheafedSpace := d.source.property.1
  have hgood : {x : A.obj.left | d.denominator (f.hom.left.base x).val.val.val ≠ 0} ⊆
      {x | L.hom.left.base x=K.hom.left.base x} := by
    intro x hx
    let p : d.graph.obj.left := d.sourceInclusion.hom.left.base (L.hom.left.base x)
    let q : d.graph.obj.left := d.sourceInclusion.hom.left.base (K.hom.left.base x)
    have hLp : L ≫ d.sourceInclusion ≫ d.projection=f ≫ d.baseInclusion := by
      rw [← d.map_square,← Category.assoc,hL]
    have hKp : K ≫ d.sourceInclusion ≫ d.projection=f ≫ d.baseInclusion := by
      rw [← d.map_square,← Category.assoc,hK]
    have hbP : baseProjection n d.arity p.val.val=(f.hom.left.base x).val.val.val := by
      have he := congrArg (fun t : A ⟶ d.base => (t.hom.left.base x).val.val) hLp
      have hp := congrArg Subtype.val (projection_apply
        (PrimeNov16AnalyticNormalizationLocalGraph.ballDomain (n := n) d.radius)
        d.carrier_analytic d.denominator d.numerator d.denominator_holo d.numerator_holo p)
      exact hp.symm.trans he
    have hbQ : baseProjection n d.arity q.val.val=(f.hom.left.base x).val.val.val := by
      have he := congrArg (fun t : A ⟶ d.base => (t.hom.left.base x).val.val) hKp
      have hp := congrArg Subtype.val (projection_apply
        (PrimeNov16AnalyticNormalizationLocalGraph.ballDomain (n := n) d.radius)
        d.carrier_analytic d.denominator d.numerator d.denominator_holo d.numerator_holo q)
      exact hp.symm.trans he
    have hpoint : p=q := by
      apply Subtype.ext
      apply Subtype.ext
      apply coordinates_injective
      · exact hbP.trans hbQ.symm
      · ext i
        have hp := ((mem_denominatorSet _ _ _ _ p.val).mp
          (graphClosure_subset_denominatorSet _ d.carrier_analytic d.denominator d.numerator
            d.denominator_holo d.numerator_holo p.property)).2 i
        have hq := ((mem_denominatorSet _ _ _ _ q.val).mp
          (graphClosure_subset_denominatorSet _ d.carrier_analytic d.denominator d.numerator
            d.denominator_holo d.numerator_holo q.property)).2 i
        rw [hbP] at hp
        rw [hbQ] at hq
        exact mul_left_cancel₀ hx (hp.trans hq.symm)
    have hj : LocallyRingedSpace.IsOpenImmersion d.sourceInclusion.hom.left := inferInstance
    exact hj.base_open.injective hpoint
  have hclosed : IsClosed {x : A.obj.left | L.hom.left.base x=K.hom.left.base x} :=
    isClosed_eq L.hom.left.base.hom.continuous K.hom.left.base.hom.continuous
  apply morphism_eq_of_pointwise_eq
  intro x
  exact (closure_minimal hgood hclosed) (hdense x)

theorem exists_unique_normal_graph_lift {m n : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (P : Opens (ComplexModel m)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target)
    (hnormal : ∀ x ∈ W, IsDomain ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier)
    (b : Fin n → sectionRing P C W) (h : sectionRing P C W)
    (g : Fin d.arity → sectionRing P C W)
    (hb : ∀ (x : W) (i : Fin n),evaluate P C W x (b i)=(f.hom.left.base x).val.val.val i)
    (hh : ∀ x : W,evaluate P C W x h=d.denominator (f.hom.left.base x).val.val.val)
    (hg : ∀ (x : W) (i : Fin d.arity),evaluate P C W x (g i)=d.numerator i (f.hom.left.base x).val.val.val)
    (hreg : ∀ (x : C) (hx : x ∈ W),
      (actualSubspaceSheaf (n := m) C).presheaf.germ W x hx h ≠ 0)
    (deg : Fin d.arity → ℕ) (c : ∀ i,Fin (deg i) → sectionRing P C W)
    (hrel : ∀ i,(g i)^(deg i)+∑ j : Fin (deg i),c i j*h^(deg i-j.val)*(g i)^j.val=0) :
    ∃! L : coordinateSource P C hC W ⟶ d.source,L ≫ d.map=f := by
  obtain ⟨q,F,hq,hbF,hqF⟩ := exists_normal_graph_coordinates d P C hC W f hnormal b h g hb hreg deg c hrel
  have hH (x : W) : d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val)=
      evaluate P C W x h := by
    rw [hbF x]
    exact (hh x).symm
  have hrelation (x : W) (i : Fin d.arity) :
      d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) *
          fibreProjection n d.arity (F.hom.left.base x).val.val i =
        d.numerator i (baseProjection n d.arity (F.hom.left.base x).val.val) := by
    rw [hH x,hqF x i,hbF x]
    have he := congrArg (evaluate P C W x) (hq i)
    rw [map_mul] at he
    exact he.symm.trans (hg x i)
  have hsourceDense := original_section_nonzero_dense C W h hreg
  have hdenseF : Dense {x : (coordinateSource P C hC W).obj.left |
      d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) ≠ 0} := by
    change Dense {x : W | d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) ≠ 0}
    have he : {x : W | d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) ≠ 0}=
        {x : W | evaluate P C W x h ≠ 0} := by
      ext x
      exact iff_of_eq (congrArg (fun z : ℂ => z ≠ 0) (hH x))
    rw [he]
    exact hsourceDense
  obtain ⟨L,hL⟩ := exists_graph_lift_of_coordinates d (coordinateSource P C hC W) f F hbF hrelation hdenseF
  have hdense : Dense {x : (coordinateSource P C hC W).obj.left |
      d.denominator (f.hom.left.base x).val.val.val ≠ 0} := by
    change Dense {x : W | d.denominator (f.hom.left.base x).val.val.val ≠ 0}
    have he : {x : W | d.denominator (f.hom.left.base x).val.val.val ≠ 0}=
        {x : W | evaluate P C W x h ≠ 0} := by
      ext x
      exact iff_of_eq (congrArg (fun z : ℂ => z ≠ 0) (hh x).symm)
    rw [he]
    exact hsourceDense
  refine ⟨L,hL,?_⟩
  intro K hK
  exact graph_lift_eq_of_dense d (coordinateSource P C hC W) f hdense K L hK hL

end SGPT.Unibranch.NativeNov16NormalGraphLift
