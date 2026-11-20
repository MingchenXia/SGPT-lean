import SGPT.Unibranch.ComplexLocalFiberRelation

/-! Actual original maps internally produce the local disk-relation charts.
Blueprint: complex-space-disk-relation-chart.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch
open SourceReducedComplexSpace

/-- Primitive ORIGINAL embeddings and actual holomorphic lifts only.
The relation, its projections and ramified lifts are NOT input fields. -/
structure DiskRelationChart {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (f : unitDisc ⟶ X) where
  target : LocalEmbedding X
  source : SpaceForm.MorphismChartLift π target
  window : Opens (ComplexModel 1)
  window_subset : window ≤ unitDiscOpens
  diskLift : ComplexModel 1 → ComplexModel target.dim
  diskHolomorphic : ContDiffOn ℂ ∞ diskLift window
  diskMaps : MapsTo diskLift window target.ambient
  diskFactor : ∀ t : (univ : Set unitDiscOpens),t.val.val ∈ window →
    ∃ b : target.carrier,b.val.val = diskLift t.val.val ∧ target.toPoint b = f.hom.left.base t

/-- Actual original matching points manufacture the SAME prescribed target
chart and actual local holomorphic lifts internally. -/
theorem exists_diskRelationChart {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (f : unitDisc ⟶ X) (t : (univ : Set unitDiscOpens)) (y : Y.obj.left)
    (hmatch : π.hom.left.base y = f.hom.left.base t) :
    ∃ A : DiskRelationChart π f,t.val.val ∈ A.window ∧ y ∈ range A.source.source.toPoint := by
  let e := LocalEmbedding.ofPoint X (π.hom.left.base y)
  have heπ : π.hom.left.base y ∈ range e.toPoint := LocalEmbedding.mem_range_ofPoint _ _
  have hef : f.hom.left.base t ∈ range e.toPoint := hmatch ▸ heπ
  obtain ⟨B,hyB,_hconn⟩ := SpaceForm.morphismChartLift_connected_cover π e y heπ
  obtain ⟨W,hW,htW,hWU,F,hF,hFm,hfac⟩ :=
    LocalEmbedding.exists_contDiffOn_factor f.hom.left (Over.w f.hom) e t hef
  exact ⟨⟨e,B,⟨W,hW⟩,hWU,F,hF,hFm,hfac⟩,htW,hyB⟩

namespace DiskRelationChart
variable {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} {f : unitDisc ⟶ X}

/-- The actual coordinate equation is exactly the SAME original point equation. -/
theorem coordinate_match_iff (A : DiskRelationChart π f)
    (t : (univ : Set unitDiscOpens)) (ht : t.val.val ∈ A.window)
    (y : A.source.source.carrier) :
    A.source.lift y.val.val = A.diskLift t.val.val ↔
      π.hom.left.base (A.source.source.toPoint y) = f.hom.left.base t := by
  obtain ⟨b,hb,hpb⟩ := A.source.factor y
  obtain ⟨c,hc,hpc⟩ := A.diskFactor t ht
  constructor
  · intro heq
    have hbc : b = c := Subtype.ext (Subtype.ext (hb.trans (heq.trans hc.symm)))
    exact hpb.symm.trans ((congrArg A.target.toPoint hbc).trans hpc)
  · intro heq
    have hbc : b = c := A.target.toPoint_injective (hpb.trans (heq.trans hpc.symm))
    exact hb.symm.trans ((congrArg (fun z : A.target.carrier => z.val.val) hbc).trans hc)

/-- The computed actual ORIGINAL analytic relation object; no supplied fiber product. -/
def model (A : DiskRelationChart π f) : SourceReducedComplexSpace :=
  sourceReducedComplexSpaceModel (LocalFiberRelation.ambient A.window A.source.source.ambient)
    (LocalFiberRelation.carrier A.window A.source.source.ambient A.source.source.carrier
      A.diskLift A.source.lift)
    (LocalFiberRelation.analytic A.window A.source.source.ambient A.source.source.carrier
      A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic)

private def windowMorphism (A : DiskRelationChart π f) : domainSpace A.window ⟶ unitDisc :=
  analyticModelMorphism isComplexAnalyticSubset_univ isComplexAnalyticSubset_univ
    (fun z : ComplexModel 1 => z) contDiffOn_id A.window_subset (fun _ => trivial)

/-- The SAME actual relation model's original disk projection. -/
def leftMorphism (A : DiskRelationChart π f) : A.model ⟶ unitDisc :=
  LocalFiberRelation.leftMorphism A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic ≫
      windowMorphism A

/-- The SAME actual relation model's original source projection. -/
def rightMorphism (A : DiskRelationChart π f) : A.model ⟶ Y :=
  LocalFiberRelation.rightMorphism A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic ≫
    ObjectProperty.homMk (Over.homMk A.source.source.map A.source.source.overPoint)

/-- Actual projection point maps satisfy the unchanged ORIGINAL square. -/
theorem projection_square (A : DiskRelationChart π f) (q : A.model.obj.left) :
    π.hom.left.base (A.rightMorphism.hom.left.base q) =
      f.hom.left.base (A.leftMorphism.hom.left.base q) := by
  let L := LocalFiberRelation.leftMorphism A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic
  let R := LocalFiberRelation.rightMorphism A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic
  have ht : (A.leftMorphism.hom.left.base q).val.val ∈ A.window := (L.hom.left.base q).val.property
  have heq : A.source.lift (R.hom.left.base q).val.val =
      A.diskLift (A.leftMorphism.hom.left.base q).val.val :=
    LocalFiberRelation.projection_relation A.window A.source.source.ambient A.source.source.carrier
      A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic q
  exact (A.coordinate_match_iff _ ht _).mp heq

/-- Every actual original matching pair in the SAME produced windows is
realized on the SAME computed analytic model. -/
theorem exists_point_of_matching_pair (A : DiskRelationChart π f)
    (t : (univ : Set unitDiscOpens)) (ht : t.val.val ∈ A.window)
    (y : Y.obj.left) (hy : y ∈ range A.source.source.toPoint)
    (hmatch : π.hom.left.base y = f.hom.left.base t) :
    ∃ q : A.model.obj.left,A.leftMorphism.hom.left.base q = t ∧
      A.rightMorphism.hom.left.base q = y := by
  obtain ⟨c,hcy⟩ := hy
  have hcoords := (A.coordinate_match_iff t ht c).mpr (by rw [hcy];exact hmatch)
  obtain ⟨q,hqL,hqR⟩ := LocalFiberRelation.exists_point_of_matching_pair
    A.window A.source.source.ambient A.source.source.carrier A.diskLift A.source.lift
    A.source.source.analytic A.diskHolomorphic A.source.holomorphic ⟨t.val.val,ht⟩ c hcoords
  refine ⟨q,Subtype.ext (Subtype.ext hqL),?_⟩
  let R := LocalFiberRelation.rightMorphism A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift A.source.source.analytic A.diskHolomorphic A.source.holomorphic
  have hRc : R.hom.left.base q = c := Subtype.ext (Subtype.ext hqR)
  change A.source.source.toPoint (R.hom.left.base q) = y
  rw [hRc,hcy]

end DiskRelationChart
end SGPT.Unibranch
