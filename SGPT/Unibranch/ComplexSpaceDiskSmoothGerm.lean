import SGPT.Unibranch.ComplexSpaceDiskNonzeroGerm
import SGPT.Unibranch.ResolutionLocal

/-! A genuine ORIGINAL smooth source of the nonconstant disk parameter.
Accepted local resolution is reused READ ONLY; no Hironaka development.
Blueprint: complex-space-disk-smooth-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace SGPT.Unibranch.SourceReducedComplexSpace

/-- The actual nonconstant scalar disk germ survives on an internally
produced ORIGINAL smooth source, with the SAME original projection square. -/
theorem exists_smooth_disk_nonzero_germ {X Y : SourceReducedComplexSpace}
    (π : Y ⟶ X) (hπ : IsProperBimeromorphic π) (f : unitDisc ⟶ X) :
    ∃ (T : SourceReducedComplexSpace) (a : T ⟶ unitDisc) (b : T ⟶ Y) (t : T.obj.left),
      T.IsSmooth ∧ a.hom.left.base t = zeroDiscPoint ∧
      t ∈ closure {q : T.obj.left | (a.hom.left.base q).val.val 0 ≠ 0} ∧
      (¬ ∀ᶠ q in 𝓝 t,(a.hom.left.base q).val.val 0 = 0) ∧
      ∀ q : T.obj.left,π.hom.left.base (b.hom.left.base q) = f.hom.left.base (a.hom.left.base q) := by
  obtain ⟨A,p,hp0,_hpScalar,hpcl,_hpNotLocal⟩ := exists_diskRelation_nonzero_germ π hπ f
  obtain ⟨V,j,hj,⟨v,hjv⟩,T,ρ,hρ⟩ := SGPT.Unibranch.exists_local_resolution A.model p
  let S : Set A.model.obj.left := {q | (A.leftMorphism.hom.left.base q).val.val 0 ≠ 0}
  have hvcl : v ∈ closure (j.hom.left.base ⁻¹' S) := by
    apply hj.base_open.isOpenMap.preimage_closure_subset_closure_preimage
    change j.hom.left.base v ∈ closure S
    rw [hjv]
    exact hpcl
  have hvI : v ∈ closure (ρ.hom.left.base '' (ρ.hom.left.base ⁻¹' (j.hom.left.base ⁻¹' S))) := by
    rw [hρ.2.surjective.image_preimage]
    exact hvcl
  obtain ⟨t,htcl,hρt⟩ := hρ.2.1.isClosedMap.closure_image_subset
    (ρ.hom.left.base ⁻¹' (j.hom.left.base ⁻¹' S)) hvI
  let a : T ⟶ unitDisc := ρ ≫ j ≫ A.leftMorphism
  let b : T ⟶ Y := ρ ≫ j ≫ A.rightMorphism
  have ha0 : a.hom.left.base t = zeroDiscPoint := by
    change A.leftMorphism.hom.left.base (j.hom.left.base (ρ.hom.left.base t)) = zeroDiscPoint
    rw [hρt,hjv,hp0]
  have htNonzero : t ∈ closure {q : T.obj.left | (a.hom.left.base q).val.val 0 ≠ 0} := htcl
  refine ⟨T,a,b,t,hρ.1,ha0,htNonzero,?_,?_⟩
  · intro hlocal
    obtain ⟨q,hqzero,hqnonzero⟩ := mem_closure_iff_nhds.mp htNonzero _ hlocal
    exact hqnonzero hqzero
  · intro q
    exact A.projection_square (j.hom.left.base (ρ.hom.left.base q))

end SGPT.Unibranch.SourceReducedComplexSpace
