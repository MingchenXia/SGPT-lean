import SGPT.Unibranch.ComplexSpaceDiskRelationTopology
import SGPT.Unibranch.ComplexSpaceUnibranchFibers

/-! Proper ORIGINAL geometry produces an actual nonconstant disk-parameter
germ on its computed analytic relation. Blueprint: complex-space-disk-nonzero-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The literal original disk zero point, with actual model coordinates. -/
def zeroDiscPoint : (univ : Set unitDiscOpens) :=
  ⟨⟨0,by change (0 : ComplexModel 1) ∈ Metric.ball 0 1;simp⟩,trivial⟩

/-- Literal nonzero scalar parameters in the SAME original disk object. -/
def nonzeroDiscParameters : Set (univ : Set unitDiscOpens) := {t | t.val.val 0 ≠ 0}

/-- Punctured parameter density is manufactured from the actual original
open coordinate embedding, not assumed as an analytic certificate. -/
theorem nonzeroDiscParameters_dense : Dense nonzeroDiscParameters := by
  let ι : ↥(univ : Set unitDiscOpens) → ComplexModel 1 := fun t => t.val.val
  have hι : Topology.IsOpenEmbedding ι :=
    unitDiscOpens.isOpenEmbedding'.comp (Homeomorph.Set.univ unitDiscOpens).isOpenEmbedding
  have hd := (dense_compl_singleton (0 : ComplexModel 1)).preimage hι.isOpenMap
  apply hd.mono
  intro t ht hzero
  apply ht
  change t.val.val = 0
  ext i
  fin_cases i
  exact hzero

/-- Original properness internally produces a TRUE nonconstant-base germ
on the SAME computed original analytic disk relation, even for constant f. -/
theorem exists_diskRelation_nonzero_germ {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (f : unitDisc ⟶ X) :
    ∃ (A : DiskRelationChart π f) (p : A.model.obj.left),
      A.leftMorphism.hom.left.base p = zeroDiscPoint ∧
      (A.leftMorphism.hom.left.base p).val.val 0 = 0 ∧
      p ∈ closure {q : A.model.obj.left | (A.leftMorphism.hom.left.base q).val.val 0 ≠ 0} ∧
      ¬ ∀ᶠ q in 𝓝 p,(A.leftMorphism.hom.left.base q).val.val 0 = 0 := by
  let singularDiskSeedTargetHausdorff : T2Space X.obj.left.toPresheafedSpace := X.property.1
  obtain ⟨q,hqzero,hqcl⟩ := ProperFiberRelation.exists_closure_lift hπ.1 hπ.surjective
    f.hom.left.base.hom.continuous (nonzeroDiscParameters_dense zeroDiscPoint)
  let y : Y.obj.left := q.val.2
  have hmatch : π.hom.left.base y = f.hom.left.base zeroDiscPoint :=
    q.property.symm.trans (congrArg f.hom.left.base hqzero)
  let S : Set (ProperFiberRelation.relation π.hom.left.base f.hom.left.base) :=
    {q | q.val.1 ∈ nonzeroDiscParameters}
  have hqeq : q = (⟨(zeroDiscPoint,y),hmatch.symm⟩ :
      ProperFiberRelation.relation π.hom.left.base f.hom.left.base) :=
    Subtype.ext (Prod.ext hqzero rfl)
  have hcl : (⟨(zeroDiscPoint,y),hmatch.symm⟩ :
      ProperFiberRelation.relation π.hom.left.base f.hom.left.base) ∈ closure S := by
    rw [← hqeq]
    exact hqcl
  obtain ⟨A,ht,hy⟩ := exists_diskRelationChart π f zeroDiscPoint y hmatch
  obtain ⟨p,hpt,_hpy,hpcl⟩ := A.exists_point_and_closure zeroDiscPoint ht y hy hmatch hcl
  have hset : A.pairMap ⁻¹' S =
      {r : A.model.obj.left | (A.leftMorphism.hom.left.base r).val.val 0 ≠ 0} := by
    ext r
    change (A.pairMap r).val.1.val.val 0 ≠ 0 ↔
      (A.leftMorphism.hom.left.base r).val.val 0 ≠ 0
    rw [A.pairMap_apply]
  rw [hset] at hpcl
  refine ⟨A,p,hpt,?_,hpcl,?_⟩
  · rw [hpt]
    rfl
  · intro hlocal
    obtain ⟨r,hrzero,hrnonzero⟩ := mem_closure_iff_nhds.mp hpcl _ hlocal
    exact hrnonzero hrzero

end SGPT.Unibranch.SourceReducedComplexSpace
