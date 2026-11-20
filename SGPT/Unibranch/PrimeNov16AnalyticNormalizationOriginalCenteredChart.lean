import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredAnalyticModel
import SGPT.Unibranch.ComplexSpaceLocalEmbedding
import SGPT.Unibranch.Resolution

/-! Centered full original analytic charts through arbitrary original points.
Blueprint: prime-nov16-analytic-normalization-original-centered-chart.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredChart
open PrimeNov16AnalyticNormalizationOriginalCenteredAnalyticModel

def localEmbeddingMorphism {X : SourceReducedComplexSpace} (e : LocalEmbedding X) :
    SourceReducedComplexSpace.ofClosedAnalytic e.carrier e.analytic ⟶ X :=
  ObjectProperty.homMk (Over.homMk e.map e.overPoint)

instance localEmbeddingMorphism_isOpenImmersion {X : SourceReducedComplexSpace}
    (e : LocalEmbedding X) :
    LocallyRingedSpace.IsOpenImmersion (localEmbeddingMorphism e).hom.left := e.isOpenImmersion

theorem exists_actual_centered_chart (X : SourceReducedComplexSpace) (x : X.obj.left) :
    ∃ (n : ℕ) (Z : Set (ComplexModel n)) (Ω : Opens (ComplexModel n))
      (hC : IsComplexAnalyticSubset (n := n) ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z)),
      AnalyticGermDecomposition.IsAnalyticGerm Z ∧ (0 : ComplexModel n) ∈ Z ∧
      (0 : ComplexModel n) ∈ Ω ∧
      ∃ j : sourceReducedComplexSpaceModel Ω ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z) hC ⟶ X,
        LocallyRingedSpace.IsOpenImmersion j.hom.left ∧
        ∃ b : ((Subtype.val : Ω → ComplexModel n) ⁻¹' Z),
          b.val.val = 0 ∧ j.hom.left.base b = x := by
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c,hc⟩ := LocalEmbedding.mem_range_ofPoint X x
  let Ω := centeredOpen (n := e.dim) c.val
  let Z := AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val
  have hC : IsComplexAnalyticSubset (n := e.dim) ((Subtype.val : Ω → ComplexModel e.dim) ⁻¹' Z) :=
    centeredCarrier_analytic e.analytic c.val
  let j0 : sourceReducedComplexSpaceModel Ω ((Subtype.val : Ω → ComplexModel e.dim) ⁻¹' Z) hC ⟶
      SourceReducedComplexSpace.ofClosedAnalytic e.carrier e.analytic :=
    ObjectProperty.homMk (Over.homMk (centeredMap (n := e.dim) e.carrier c.val)
      (centeredMap_point (n := e.dim) e.carrier c.val))
  let b : ((Subtype.val : Ω → ComplexModel e.dim) ⁻¹' Z) :=
    ⟨⟨0,zero_mem_centeredOpen (n := e.dim) c.val⟩,zero_mem_chartGerm (n := e.dim) e.carrier c⟩
  refine ⟨e.dim,Z,Ω,hC,centeredGerm_analytic e.analytic c.val,
    zero_mem_chartGerm (n := e.dim) e.carrier c,zero_mem_centeredOpen (n := e.dim) c.val,j0 ≫ localEmbeddingMorphism e,?_,b,rfl,?_⟩
  · change LocallyRingedSpace.IsOpenImmersion
      (centeredMap (n := e.dim) e.carrier c.val ≫ e.map)
    let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
    infer_instance
  · change e.map.base ((centeredMap (n := e.dim) e.carrier c.val).base b) = x
    rw [centeredMap_origin]
    exact hc
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCenteredChart
