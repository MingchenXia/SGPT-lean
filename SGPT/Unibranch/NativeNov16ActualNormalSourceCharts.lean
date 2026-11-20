import SGPT.Unibranch.ComplexSpaceLocalEmbedding
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
import SGPT.Foundations.Analysis.Pending.HironakaIntrinsicMorphismGluingAnalytic

/-! Actual full original whole-source charts internally transport original normal stalks.
Blueprint: native-nov16-actual-normal-source-charts.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
namespace SGPT.Unibranch.NativeNov16ActualNormalSourceCharts
open SourceReducedComplexSpace NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalCoordinateWindowInclusion
open HironakaIntrinsicMorphismGluingAnalytic

def chartSource {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) : SourceReducedComplexSpace :=
  coordinateSource e.ambient e.carrier e.analytic ⊤

def chartInclusion {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) : chartSource e ⟶ Y :=
  coordinateInclusion e.ambient e.carrier e.analytic ⊤ ≫
    ObjectProperty.homMk (Over.homMk e.map e.overPoint)

instance chartInclusion_isOpenImmersion {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) :
    LocallyRingedSpace.IsOpenImmersion (chartInclusion e).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  change LocallyRingedSpace.IsOpenImmersion
    ((coordinateInclusion e.ambient e.carrier e.analytic ⊤).hom.left ≫ e.map)
  infer_instance

theorem chartInclusion_point {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y)
    (p : (chartSource e).obj.left) : (chartInclusion e).hom.left.base p=e.toPoint p.val := rfl

theorem point_cover (Y : SourceReducedComplexSpace) (x : Y.obj.left) :
    ∃ p : (chartSource (LocalEmbedding.ofPoint Y x)).obj.left,
      (chartInclusion (LocalEmbedding.ofPoint Y x)).hom.left.base p=x := by
  obtain ⟨c,hc⟩ := LocalEmbedding.mem_range_ofPoint Y x
  exact ⟨(⟨c,by trivial⟩ : (⊤ : Opens (TopCat.of (LocalEmbedding.ofPoint Y x).carrier))),hc⟩

theorem chart_analytic {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y) :
    hasAnalyticCharts (Over.mk ((chartInclusion e).hom.left ≫ Y.obj.hom)) := by
  rw [Over.w (chartInclusion e).hom]
  exact hasAnalyticCharts_of_openImmersion (chartSource e).obj.hom
    (sourceReducedComplexSpaceModel e.ambient e.carrier e.analytic).obj.hom
    (HironakaReducedComplexAnalyticSpaces.hasAnalyticCharts_model e.ambient e.carrier e.analytic)
    (coordinateInclusion e.ambient e.carrier e.analytic ⊤).hom.left
    (Over.w (coordinateInclusion e.ambient e.carrier e.analytic ⊤).hom)

theorem chart_normal_stalks {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y)
    (hn : ∀ y : Y.obj.left,IsDomain (Y.obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (Y.obj.left.presheaf.stalk y).carrier) :
    ∀ x ∈ (⊤ : Opens (TopCat.of e.carrier)),
      IsDomain ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := e.dim) e.carrier).presheaf.stalk x).carrier := by
  intro x hx
  let p : (chartSource e).obj.left := ⟨x,hx⟩
  obtain ⟨hdom,hclosed⟩ := hn ((chartInclusion e).hom.left.base p)
  let := hdom
  let := hclosed
  let E := (asIso ((chartInclusion e).hom.left.stalkMap p)).commRingCatIsoToRingEquiv
  let R := ((actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier).restrictStalkIso
    (⊤ : Opens (TopCat.of e.carrier)).isOpenEmbedding p).commRingCatIsoToRingEquiv
  let F := E.trans R
  exact ⟨Function.Injective.isDomain F.symm F.symm.injective,IsIntegrallyClosed.of_equiv F⟩

end SGPT.Unibranch.NativeNov16ActualNormalSourceCharts
