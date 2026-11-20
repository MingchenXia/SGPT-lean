import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPresentation

/-! Exact full original graph point and coordinate readback, including the entire bad fibre.
Blueprint: prime-nov16-analytic-normalization-original-graph-coordinates.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationLocalGraph

variable {n : ℕ} {Z : Set (ComplexModel n)} (d : GraphPresentation n Z)

theorem map_point (p : d.source.obj.left) :
    ((d.map.hom.left.base p).val : d.base.obj.left)=d.projection.hom.left.base p.val :=
  congrArg (fun f : d.source ⟶ d.base => f.hom.left.base p) d.map_square

theorem map_ambient (p : d.source.obj.left) :
    (d.map.hom.left.base p).val.val.val=baseProjection n d.arity p.val.val.val :=
  congrArg (fun b : d.base.obj.left => b.val.val) (map_point d p)

theorem whole_denominator_identity (p : d.graph.obj.left) (i : Fin d.arity) :
    d.denominator (baseProjection n d.arity p.val.val)*fibreProjection n d.arity p.val.val i=
      d.numerator i (baseProjection n d.arity p.val.val) :=
  ((mem_denominatorSet _ _ _ _ p.val).mp
    (graphClosure_subset_denominatorSet (ballDomain (n := n) d.radius) d.carrier_analytic
      d.denominator d.numerator d.denominator_holo d.numerator_holo p.property)).2 i

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
