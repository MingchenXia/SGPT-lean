import SGPT.Unibranch.NativeNov16GraphPullbackScalarValues
import SGPT.Unibranch.NativeNov16NormalGraphLiftComplete
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRelations
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRegularity

/-! Actual normal-source graph lift from the computed denominator pullback regularity.
No good-isomorphism assumption on a selector piece is required.
Blueprint: native-nov16-regular-normal-graph-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16RegularNormalGraphLift
open SourceReducedComplexSpace HironakaActualAnalyticSubspace
open NativeNov16SectionCoordinateMorphism NativeNov16NormalGraphLift
open NativeNov16GraphPullbackScalarValues
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalSourceScalarRelations
open PrimeNov16AnalyticNormalizationOriginalSourceScalarRegularity

theorem exists_unique_graph_lift_of_regular_pullback {n m : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (P : Opens (ComplexModel m)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target)
    (hnormal : ∀ x ∈ W, IsDomain ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) C).presheaf.stalk x).carrier)
    (hreg : ∀ (x : C) (hx : x ∈ W),
      (actualSubspaceSheaf (n := m) C).presheaf.germ W x hx
        (pulledBaseScalar d P C hC W f d.denominator d.denominator_holo) ≠ 0)
    (deg : Fin d.arity → ℕ) (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius))
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0)
    (hs : Function.Surjective d.map.hom.left.base) :
    ∃! L : coordinateSource P C hC W ⟶ d.source,L ≫ d.map=f := by
  let coordHolo (i : Fin n) : DifferentiableOn ℂ (fun z : ComplexModel n => z i)
      (ballDomain (n := n) d.radius) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.differentiableOn
  let b := fun i : Fin n => pulledBaseScalar d P C hC W f (fun z => z i) (coordHolo i)
  let h := pulledBaseScalar d P C hC W f d.denominator d.denominator_holo
  let g := fun i => pulledBaseScalar d P C hC W f (d.numerator i) (d.numerator_holo i)
  let c := fun (i : Fin d.arity) (j : Fin (deg i)) =>
    pulledBaseScalar d P C hC W f (a i j.val) (ha i j.val j.isLt)
  refine exists_unique_normal_graph_lift d P C hC W f hnormal b h g ?_ ?_ ?_ ?_ deg c ?_
  · intro x i
    exact pulledBaseScalar_value d P C hC W f (fun z => z i) (coordHolo i) x
  · intro x
    exact pulledBaseScalar_value d P C hC W f d.denominator d.denominator_holo x
  · intro x i
    exact pulledBaseScalar_value d P C hC W f (d.numerator i) (d.numerator_holo i) x
  · exact hreg
  · intro i
    exact pulledBaseScalar_graph_monic d P C hC W f deg a ha hm hs i

end SGPT.Unibranch.NativeNov16RegularNormalGraphLift
