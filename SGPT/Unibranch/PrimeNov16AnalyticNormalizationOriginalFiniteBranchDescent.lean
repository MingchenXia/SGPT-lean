import SGPT.Unibranch.HironakaG1NativeDisjointCoproduct

/-! Actual finite branch coproduct descent over the SAME possibly overlapping base.
Blueprint: prime-nov16-analytic-normalization-original-finite-branch-descent.tex. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent
open HironakaG1NativeDisjointCoproduct

variable {ι : Type} [Finite ι] (Z : ι → SourceReducedComplexSpace)
  {X : SourceReducedComplexSpace} (F : ∀ i,Z i ⟶ X)

omit [Finite ι] in
private theorem point_triangle (i : ι) (z : (Z i).obj.left) :
    (desc Z F).hom.left.base ((inclusion Z i).hom.left.base z)=(F i).hom.left.base z :=
  congrArg (fun f : Z i ⟶ X => f.hom.left.base z) (inclusion_desc Z F i)

omit [Finite ι] in
private theorem image_union (S : Set (coproduct Z).obj.left) :
    (desc Z F).hom.left.base '' S =
      ⋃ i,(F i).hom.left.base '' ((inclusion Z i).hom.left.base ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨i,z,rfl⟩ := inclusion_jointly_surjective Z p
    exact mem_iUnion.mpr ⟨i,z,hp,(point_triangle Z F i z).symm⟩
  · intro hx
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hx
    exact ⟨(inclusion Z i).hom.left.base z,hz,point_triangle Z F i z⟩

omit [Finite ι] in
private theorem fibre_union (x : X.obj.left) :
    (desc Z F).hom.left.base ⁻¹' {x}=
      ⋃ i,(inclusion Z i).hom.left.base '' ((F i).hom.left.base ⁻¹' {x}) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i,z,rfl⟩ := inclusion_jointly_surjective Z p
    refine mem_iUnion.mpr ⟨i,z,?_,rfl⟩
    change (F i).hom.left.base z=x
    exact (point_triangle Z F i z).symm.trans hp
  · intro hp
    obtain ⟨i,z,hz,rfl⟩ := mem_iUnion.mp hp
    exact (point_triangle Z F i z).trans hz

theorem desc_proper (hp : ∀ i,IsProperMap (F i).hom.left.base) :
    IsProperMap (desc Z F).hom.left.base := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨(desc Z F).hom.left.base.hom.continuous,?_,?_⟩
  · intro S hS
    rw [image_union]
    exact isClosed_iUnion_of_finite fun i =>
      (hp i).isClosedMap _ (hS.preimage (inclusion Z i).hom.left.base.hom.continuous)
  · intro x
    rw [fibre_union]
    exact isCompact_iUnion fun i => ((hp i).isCompact_preimage isCompact_singleton).image
      (inclusion Z i).hom.left.base.hom.continuous

theorem desc_fibres_finite
    (hf : ∀ i,∀ x : X.obj.left,((F i).hom.left.base ⁻¹' {x}).Finite) (x : X.obj.left) :
    ((desc Z F).hom.left.base ⁻¹' {x}).Finite := by
  rw [fibre_union]
  exact Set.finite_iUnion fun i => (hf i x).image _

omit [Finite ι] in
theorem coproduct_normal_stalks
    (hn : ∀ i,∀ z : (Z i).obj.left,
      IsDomain ((Z i).obj.left.presheaf.stalk z).carrier ∧
      IsIntegrallyClosed ((Z i).obj.left.presheaf.stalk z).carrier)
    (p : (coproduct Z).obj.left) :
    IsDomain ((coproduct Z).obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((coproduct Z).obj.left.presheaf.stalk p).carrier := by
  obtain ⟨i,z,rfl⟩ := inclusion_jointly_surjective Z p
  obtain ⟨hd,hc⟩ := hn i z
  let := hd
  let := hc
  let : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (inclusion Z i).hom.left :=
    inclusion_isOpenImmersion Z i
  let E := (asIso ((inclusion Z i).hom.left.stalkMap z)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain E E.injective,IsIntegrallyClosed.of_equiv E.symm⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent
