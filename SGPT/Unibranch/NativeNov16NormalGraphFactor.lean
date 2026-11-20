import SGPT.Unibranch.NativeNov16NormalGraphLift

/-! Actual coordinate morphisms factor through the SAME original denominator graph.
Blueprint: native-nov16-normal-graph-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16NormalGraphLift
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation

theorem exists_graph_lift_of_coordinates {n : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (A : SourceReducedComplexSpace) (f : A ⟶ d.target)
    (F : A ⟶ domainSpace (⊤ : Opens (ComplexModel (n+d.arity))))
    (hb : ∀ x : A.obj.left,baseProjection n d.arity (F.hom.left.base x).val.val=
      (f.hom.left.base x).val.val.val)
    (hrel : ∀ (x : A.obj.left) (i : Fin d.arity),
      d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) *
          fibreProjection n d.arity (F.hom.left.base x).val.val i =
        d.numerator i (baseProjection n d.arity (F.hom.left.base x).val.val))
    (hdense : Dense {x : A.obj.left |
      d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) ≠ 0}) :
    ∃ L : A ⟶ d.source,L ≫ d.map=f := by
  let U := PrimeNov16AnalyticNormalizationLocalGraph.ballDomain (n := n) d.radius
  let C : Set U := {z | z.val ∈ Z}
  let M := wideDomain d.arity U
  have hland (x : A.obj.left) : (F.hom.left.base x).val.val ∈ M := by
    change baseProjection n d.arity (F.hom.left.base x).val.val ∈ U
    rw [hb x]
    exact (f.hom.left.base x).val.val.property
  obtain ⟨E,hE,_hEu⟩ := exists_unique_affine_open_lift M A F hland
  have hwide (x : A.obj.left) : (E.hom.left.base x).val.val=(F.hom.left.base x).val.val :=
    congrArg (fun q : A ⟶ affineSpace (n+d.arity) => (q.hom.left.base x).val) hE
  have hbase (x : A.obj.left) : basePoint U (E.hom.left.base x).val ∈ C := by
    have he : basePoint U (E.hom.left.base x).val=(f.hom.left.base x).val.val := by
      apply Subtype.ext
      exact (congrArg (baseProjection n d.arity) (hwide x)).trans (hb x)
    rw [he]
    exact (f.hom.left.base x).val.property
  have hrelation (x : A.obj.left) (i : Fin d.arity) :
      d.denominator (baseProjection n d.arity (E.hom.left.base x).val.val) *
          fibreProjection n d.arity (E.hom.left.base x).val.val i =
        d.numerator i (baseProjection n d.arity (E.hom.left.base x).val.val) := by
    rw [hwide x]
    exact hrel x i
  have hdenseE : Dense {x : A.obj.left |
      d.denominator (baseProjection n d.arity (E.hom.left.base x).val.val) ≠ 0} := by
    have he : {x : A.obj.left | d.denominator (baseProjection n d.arity (E.hom.left.base x).val.val) ≠ 0}=
        {x : A.obj.left | d.denominator (baseProjection n d.arity (F.hom.left.base x).val.val) ≠ 0} := by
      ext x
      exact iff_of_eq (congrArg (fun z : ComplexModel (n+d.arity) =>
        d.denominator (baseProjection n d.arity z) ≠ 0) (hwide x))
    rw [he]
    exact hdense
  have hpoint : ∀ x : A.obj.left,(E.hom.left.base x).val ∈
      graphClosure U C d.denominator d.numerator :=
    graph_landing_of_dense_denominator U C d.denominator d.numerator
      (fun x => (E.hom.left.base x).val)
      (continuous_subtype_val.comp E.hom.left.base.hom.continuous) hbase hrelation hdenseE
  let hΓ := graphClosure_analytic U d.carrier_analytic d.denominator d.numerator
    d.denominator_holo d.numerator_holo
  obtain ⟨K,hK,_hKu⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization hΓ
    (isComplexAnalyticSubset_univ (n := n+d.arity) (M := M)) (subset_univ _) A E hpoint
  let L0 : A ⟶ d.graph := K
  have hL0 (x : A.obj.left) : (L0.hom.left.base x).val.val=(F.hom.left.base x).val.val := by
    have he : (L0.hom.left.base x).val.val=(E.hom.left.base x).val.val :=
      congrArg (fun q : A ⟶ domainSpace M => (q.hom.left.base x).val.val) hK
    exact he.trans (hwide x)
  have hprojection : L0 ≫ d.projection=f ≫ d.baseInclusion := by
    apply morphism_eq_of_pointwise_eq
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg Subtype.val (projection_apply U d.carrier_analytic
      d.denominator d.numerator d.denominator_holo d.numerator_holo (L0.hom.left.base x))
    exact he.trans ((congrArg (baseProjection n d.arity) (hL0 x)).trans (hb x))
  have hr : range L0.hom.left.base ⊆ range d.sourceInclusion.hom.left.base := by
    rintro _ ⟨x,rfl⟩
    have he : d.projection.hom.left.base (L0.hom.left.base x)=(f.hom.left.base x).val :=
      congrArg (fun q : A ⟶ d.base => q.hom.left.base x) hprojection
    have hm : d.projection.hom.left.base (L0.hom.left.base x) ∈ d.baseOpen := by
      rw [he]
      exact (f.hom.left.base x).property
    exact ⟨⟨L0.hom.left.base x,hm⟩,rfl⟩
  let L := LocallyRingedSpace.IsOpenImmersion.lift d.sourceInclusion.hom.left L0.hom.left hr
  have hL : L ≫ d.sourceInclusion.hom.left=L0.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac d.sourceInclusion.hom.left L0.hom.left hr
  have hp : L ≫ d.source.obj.hom=A.obj.hom := by
    rw [← Over.w d.sourceInclusion.hom,← Category.assoc,hL,Over.w L0.hom]
  let L' : A ⟶ d.source := ObjectProperty.homMk (Over.homMk L hp)
  have hL' : L' ≫ d.sourceInclusion=L0 := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hL
  refine ⟨L',?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono d.baseInclusion.hom.left).mp
  change (L' ≫ d.map ≫ d.baseInclusion).hom.left=(f ≫ d.baseInclusion).hom.left
  rw [d.map_square,← Category.assoc,hL',hprojection]

end SGPT.Unibranch.NativeNov16NormalGraphLift
