import SGPT.Unibranch.ComplexSpaceDiskRelationChart
import SGPT.Unibranch.ComplexFiberRelationTopology
import SGPT.Unibranch.ProperFiberRelation
import Mathlib.Topology.LocalAtTarget

/-! Genuine original local relation topology and literal closure readback.
Blueprint: complex-space-disk-relation-topology.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch
open SourceReducedComplexSpace
namespace DiskRelationChart
variable {X Y : SourceReducedComplexSpace} {π : Y ⟶ X} {f : unitDisc ⟶ X}

/-- Actual original product-window point map. -/
def windowPair (A : DiskRelationChart π f) :
    A.window × A.source.source.carrier → ↥(univ : Set unitDiscOpens) × Y.obj.left :=
  fun p => (⟨⟨p.1.val,A.window_subset p.1.property⟩,trivial⟩,A.source.source.toPoint p.2)

/-- Actual open embedding, including the original unit-disk outer subtype. -/
theorem windowPair_isOpenEmbedding (A : DiskRelationChart π f) :
    Topology.IsOpenEmbedding A.windowPair := by
  let e : A.window → unitDiscOpens := Opens.inclusion A.window_subset
  have he : Topology.IsOpenEmbedding e :=
    Topology.IsOpenEmbedding.of_comp e unitDiscOpens.isOpenEmbedding' A.window.isOpenEmbedding'
  have hunit : Topology.IsOpenEmbedding
      (fun t : A.window => (⟨e t,trivial⟩ : (univ : Set unitDiscOpens))) :=
    (Homeomorph.Set.univ unitDiscOpens).symm.isOpenEmbedding.comp he
  exact hunit.prodMap A.source.source.isOpenEmbedding_toPoint

/-- The actual coordinate relation is EXACTLY the literal original relation preimage. -/
theorem pairCarrier_eq_preimage (A : DiskRelationChart π f) :
    LocalFiberRelation.pairCarrier A.window A.source.source.ambient A.source.source.carrier
      A.diskLift A.source.lift = A.windowPair ⁻¹'
        ProperFiberRelation.relation π.hom.left.base f.hom.left.base := by
  ext p
  change A.source.lift p.2.val.val = A.diskLift p.1.val ↔
    f.hom.left.base (A.windowPair p).1 = π.hom.left.base (A.windowPair p).2
  exact (A.coordinate_match_iff (A.windowPair p).1 p.1.property p.2).trans eq_comm

/-- The explicit genuine topology, retaining the SAME original model carrier. -/
def pairHomeomorph (A : DiskRelationChart π f) : A.model.obj.left ≃ₜ
    (A.windowPair ⁻¹' ProperFiberRelation.relation π.hom.left.base f.hom.left.base) :=
  (LocalFiberRelation.carrierHomeomorph A.window A.source.source.ambient A.source.source.carrier
    A.diskLift A.source.lift).trans (Homeomorph.setCongr A.pairCarrier_eq_preimage)

/-- The SAME actual original model point as a literal original matching pair. -/
def pairMap (A : DiskRelationChart π f) : A.model.obj.left →
    ProperFiberRelation.relation π.hom.left.base f.hom.left.base :=
  (ProperFiberRelation.relation π.hom.left.base f.hom.left.base).restrictPreimage A.windowPair ∘
    A.pairHomeomorph

/-- Literal readback of BOTH actual original sheaf-morphism point maps. -/
theorem pairMap_apply (A : DiskRelationChart π f) (q : A.model.obj.left) :
    (A.pairMap q).val = (A.leftMorphism.hom.left.base q,A.rightMorphism.hom.left.base q) := rfl

/-- Actual open relation chart, with its topology manufactured internally. -/
theorem isOpenEmbedding_pairMap (A : DiskRelationChart π f) :
    Topology.IsOpenEmbedding A.pairMap :=
  (A.windowPair_isOpenEmbedding.restrictPreimage _).comp A.pairHomeomorph.isOpenEmbedding

/-- The actual original analytic relation chart pulls literal pair closures
back to actual closures, without an incoming open-image/density certificate. -/
theorem mem_closure_preimage_pairMap (A : DiskRelationChart π f)
    {S : Set (ProperFiberRelation.relation π.hom.left.base f.hom.left.base)}
    {q : A.model.obj.left} (hq : A.pairMap q ∈ closure S) :
    q ∈ closure (A.pairMap ⁻¹' S) :=
  A.isOpenEmbedding_pairMap.isOpenMap.preimage_closure_subset_closure_preimage hq

/-- EVERY original matching pair in a literal pair closure produces an
actual point AND nontrivial closure in the SAME computed analytic relation. -/
theorem exists_point_and_closure (A : DiskRelationChart π f)
    (t : (univ : Set unitDiscOpens)) (ht : t.val.val ∈ A.window)
    (y : Y.obj.left) (hy : y ∈ range A.source.source.toPoint)
    (hmatch : π.hom.left.base y = f.hom.left.base t)
    {S : Set (ProperFiberRelation.relation π.hom.left.base f.hom.left.base)}
    (hcl : (⟨(t,y),hmatch.symm⟩ : ProperFiberRelation.relation π.hom.left.base f.hom.left.base) ∈ closure S) :
    ∃ q : A.model.obj.left,A.leftMorphism.hom.left.base q = t ∧
      A.rightMorphism.hom.left.base q = y ∧ q ∈ closure (A.pairMap ⁻¹' S) := by
  obtain ⟨q,hqt,hqy⟩ := A.exists_point_of_matching_pair t ht y hy hmatch
  have heq : A.pairMap q = ⟨(t,y),hmatch.symm⟩ := by
    apply Subtype.ext
    rw [pairMap_apply,hqt,hqy]
  exact ⟨q,hqt,hqy,A.mem_closure_preimage_pairMap (by rw [heq];exact hcl)⟩

end DiskRelationChart
end SGPT.Unibranch
