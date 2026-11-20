import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodDensity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCommonGraphMap

/-! Primitive actual graph geometry internally manufactures dense preimages for new dense sets.
Blueprint: prime-nov16-analytic-normalization-original-graph-pullback-density.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPullbackDensity
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
open PrimeNov16AnalyticNormalizationOriginalGoodDensity
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

theorem graph_denominator_preimage_dense {n : ℕ} {B : Set (ComplexModel n)}
    (d : GraphPresentation n B) :
    Dense (d.map.hom.left.base ⁻¹' {b | d.denominator b.val.val.val ≠ 0}) := by
  have he : d.map.hom.left.base ⁻¹' {b | d.denominator b.val.val.val ≠ 0}=
      {p : d.source.obj.left | d.denominator (baseProjection n d.arity p.val.val.val) ≠ 0} := by
    ext p
    change d.denominator (d.map.hom.left.base p).val.val.val ≠ 0 ↔ _
    rw [map_ambient]
    rfl
  exact he.symm ▸ d.source_denominator_dense

theorem actual_graph_dense_preimage {n : ℕ} {B : Set (ComplexModel n)}
    (d : GraphPresentation n B) (E : Set d.target.obj.left) (hE : Dense E) :
    Dense (d.map.hom.left.base ⁻¹' E) :=
  dense_preimage_of_actual_good_inverse d.map _ d.map_isIsoOver
    (graph_denominator_preimage_dense d) E hE

theorem actual_common_graph_dense_preimage {n : ℕ} {B : Set (ComplexModel n)}
    (d : GraphPresentation n B) {X : SourceReducedComplexSpace} (g : d.target ⟶ X)
    (U : Opens X.obj.left) [ParacompactSpace U] (E : Set (restrictedBase U).obj.left)
    (hE : Dense ((commonComponent d g U).hom.left.base ⁻¹' E)) :
    Dense ((commonMap d g U).hom.left.base ⁻¹' E) :=
  actual_graph_dense_preimage (commonGraph d g U) _ hE

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPullbackDensity
