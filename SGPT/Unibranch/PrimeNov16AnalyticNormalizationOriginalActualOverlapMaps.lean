import SGPT.Unibranch.NativeNov16ConstructedLocalNormalization
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting
import SGPT.Unibranch.NativeNov16NormalizationOverlapUniqueness
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.EMetricSpace.Paracompact

/-! Actual original overlap comparison maps from ONLY the original space.
Blueprint: prime-nov16-analytic-normalization-original-actual-overlap-maps.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
open SourceReducedComplexSpace NativeNov16ConstructedLocalNormalization
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalOverlapRetargeting

/-- The one actual original-point choice used by every overlap below. -/
def atPoint (X : SourceReducedComplexSpace) (x : X.obj.left) : LocalNormalizer X x :=
  Classical.choice (exists_local_normalizer X x)

instance atPoint_into_open (X : SourceReducedComplexSpace) (x : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (atPoint X x).into.hom.left := (atPoint X x).into_open

def overlapBase (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    Opens (atPoint X i).base.obj.left :=
  ⟨(atPoint X i).into.hom.left.base ⁻¹' range (atPoint X j).into.hom.left.base,
    (atPoint X j).into_open.base_open.isOpen_range.preimage
      (atPoint X i).into.hom.left.base.hom.continuous⟩

instance overlapBase_paracompact (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    ParacompactSpace (overlapBase X i j) := by
  let : MetrizableSpace (atPoint X i).base.obj.left := (atPoint X i).base_metrizable
  let : MetricSpace (atPoint X i).base.obj.left :=
    TopologicalSpace.metrizableSpaceMetric (atPoint X i).base.obj.left
  infer_instance

def overlapSource (X : SourceReducedComplexSpace) (i j : X.obj.left) : SourceReducedComplexSpace :=
  restrictedSource (atPoint X i).projection (atPoint X i).proper (overlapBase X i j)

def overlapInclusion (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    overlapSource X i j ⟶ (atPoint X i).source :=
  sourceInclusion (atPoint X i).projection (atPoint X i).proper (overlapBase X i j)

instance overlapInclusion_open (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion X i j).hom.left := by
  dsimp only [overlapInclusion]
  infer_instance

theorem overlapSource_normal (X : SourceReducedComplexSpace) (i j : X.obj.left)
    (y : (overlapSource X i j).obj.left) :
    IsDomain ((overlapSource X i j).obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed ((overlapSource X i j).obj.left.presheaf.stalk y).carrier :=
  restrictedSource_normal_stalks (atPoint X i).projection (atPoint X i).proper
    (overlapBase X i j) (fun p _hp => (atPoint X i).normal p) y

theorem exists_actual_comparison (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    ∃ L : overlapSource X i j ⟶ (atPoint X j).source,
      L ≫ (atPoint X j).projection ≫ (atPoint X j).into =
        overlapInclusion X i j ≫ (atPoint X i).projection ≫ (atPoint X i).into := by
  obtain ⟨f,hf,G,hG,hDense⟩ := exists_actual_overlap_retargeting
    (atPoint X i).projection (atPoint X i).proper (atPoint X i).good
    (atPoint X i).good_inverse (atPoint X i).good_source_dense
    (atPoint X i).into (atPoint X j).into (overlapBase X i j) (fun _b hb => hb)
  obtain ⟨L,hL,_hunique⟩ := (atPoint X j).good_map_lift (overlapSource X i j)
    (overlapSource_normal X i j) f G hG hDense
  exact ⟨L,(Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ (atPoint X j).into) hL).trans hf)⟩

def comparison (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    overlapSource X i j ⟶ (atPoint X j).source :=
  Classical.choose (exists_actual_comparison X i j)

theorem comparison_triangle (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    comparison X i j ≫ (atPoint X j).projection ≫ (atPoint X j).into =
      overlapInclusion X i j ≫ (atPoint X i).projection ≫ (atPoint X i).into :=
  Classical.choose_spec (exists_actual_comparison X i j)

private theorem comparison_lands (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    range (comparison X i j).hom.left.base ⊆ range (overlapInclusion X j i).hom.left.base := by
  rintro _ ⟨s,rfl⟩
  have ht := congrArg (fun f : overlapSource X i j ⟶ X => f.hom.left.base s)
    (comparison_triangle X i j)
  refine ⟨⟨(comparison X i j).hom.left.base s,?_⟩,rfl⟩
  change (atPoint X j).into.hom.left.base
    ((atPoint X j).projection.hom.left.base ((comparison X i j).hom.left.base s)) ∈
      range (atPoint X i).into.hom.left.base
  exact ⟨(atPoint X i).projection.hom.left.base ((overlapInclusion X i j).hom.left.base s),ht.symm⟩

def overlapMap (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    overlapSource X i j ⟶ overlapSource X j i := by
  let K := overlapInclusion X j i
  let L := LocallyRingedSpace.IsOpenImmersion.lift K.hom.left (comparison X i j).hom.left
    (comparison_lands X i j)
  have hL : L ≫ K.hom.left = (comparison X i j).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hs : L ≫ (overlapSource X j i).obj.hom = (overlapSource X i j).obj.hom := by
    rw [← Over.w K.hom,← Category.assoc,hL]
    exact Over.w (comparison X i j).hom
  exact ObjectProperty.homMk (Over.homMk L hs)

theorem overlapMap_inclusion (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    overlapMap X i j ≫ overlapInclusion X j i = comparison X i j := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (comparison_lands X i j)

theorem overlapMap_projection (X : SourceReducedComplexSpace) (i j : X.obj.left) :
    overlapMap X i j ≫ overlapInclusion X j i ≫ (atPoint X j).projection ≫ (atPoint X j).into =
      overlapInclusion X i j ≫ (atPoint X i).projection ≫ (atPoint X i).into := by
  rw [← Category.assoc,← Category.assoc,overlapMap_inclusion]
  exact comparison_triangle X i j
end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalActualOverlapMaps
