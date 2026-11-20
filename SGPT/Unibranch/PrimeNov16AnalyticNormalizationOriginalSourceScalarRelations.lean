import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections

/-! Literal whole source scalar relations and genuine original germ transport.
Blueprint: prime-nov16-analytic-normalization-original-source-scalar-relations.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRelations
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
open NativeNov16SectionCoordinateMorphism
open HironakaActualAnalyticSubspace

variable {n m : ℕ} {Z : Set (ComplexModel n)}

theorem pulledBaseScalar_graph_monic (d : GraphPresentation n Z)
    (P : Opens (ComplexModel m)) (C : Set P) (hC : IsComplexAnalyticSubset (n := m) C)
    (W : Opens (TopCat.of C)) (f : coordinateSource P C hC W ⟶ d.target)
    (deg : Fin d.arity → ℕ) (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius))
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (PrimeNov16AnalyticNormalizationDenominatorGraph.baseProjection n d.arity p.val.val)
      (PrimeNov16AnalyticNormalizationDenominatorGraph.fibreProjection n d.arity p.val.val i)=0)
    (hs : Function.Surjective d.map.hom.left.base) (i : Fin d.arity) :
    (pulledBaseScalar d P C hC W f (d.numerator i) (d.numerator_holo i))^(deg i)+
      ∑ j : Fin (deg i),pulledBaseScalar d P C hC W f (a i j.val) (ha i j.val j.isLt)*
        (pulledBaseScalar d P C hC W f d.denominator d.denominator_holo)^(deg i-j.val)*
        (pulledBaseScalar d P C hC W f (d.numerator i) (d.numerator_holo i))^j.val=0 := by
  let L := (openTopEquiv (sourceReducedComplexSpaceModel P C hC).obj.left W).toRingHom.comp
    (pullTopRingHom f.hom.left)
  have he := congrArg L (baseScalar_graph_monic d deg a ha hm hs i)
  simp only [map_add,map_pow,map_sum,map_mul,map_zero] at he
  exact he

theorem pulledBaseScalar_germ (d : GraphPresentation n Z)
    (P : Opens (ComplexModel m)) (C : Set P) (hC : IsComplexAnalyticSubset (n := m) C)
    (W : Opens (TopCat.of C)) (f : coordinateSource P C hC W ⟶ d.target)
    (F : ComplexModel n → ℂ) (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius))
    (p : W) :
    (actualSubspaceSheaf (n := m) C).presheaf.germ W p.val p.property
      (pulledBaseScalar d P C hC W f F hF)=
      ((sourceReducedComplexSpaceModel P C hC).obj.left.restrictStalkIso W.isOpenEmbedding p).hom
        (f.hom.left.stalkMap p
          (d.target.obj.left.presheaf.germ ⊤ (f.hom.left.base p) (by trivial)
            (baseScalarSection d F hF))) := by
  exact (openTopEquiv_germ (sourceReducedComplexSpaceModel P C hC).obj.left W _ p).trans
    (congrArg ((sourceReducedComplexSpaceModel P C hC).obj.left.restrictStalkIso W.isOpenEmbedding p).hom
      (pullTop_germ f.hom.left (baseScalarSection d F hF) p))

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSourceScalarRelations
