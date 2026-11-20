import SGPT.Foundations.Schemes.BundleDualSheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Descent of genuine module-sheaf morphisms

Maps on restrictions to a genuine open cover, with their literal overlap
equalities, glue to native maps of module sheaves. The sheaf of Hom retains
all subordinate opens and its module linearity descends by separation.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {X : Scheme.{u}}

/-- Genuine morphisms between the two module sheaves restricted to an open. -/
abbrev bundleHomSections (L N : X.Modules) (U : X.Opens) : Type u :=
  L.over U ⟶ N.over U

/-- Restriction of a genuine module map, using the native comparison functors. -/
def bundleHomRestriction (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) : bundleHomSections L N U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app L).inv ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map α ≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N).hom

/-- Restriction keeps the literal component at every subordinate open. -/
theorem bundleHomRestriction_app (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) (W : (Over U)ᵒᵖ) (x : (L.over U).val.obj W) :
    (bundleHomRestriction L N i α).val.app W x =
      α.val.app ((Over.map i).op.obj W) x := by
  rfl

private def additiveHom (L N : X.Modules) : X.Opensᵒᵖ ⥤ Type u :=
  CategoryTheory.presheafHom L.val.presheaf N.val.presheaf

private def scalarValue (N : X.Modules) (U : X.Opensᵒᵖ)
    (r : X.ringCatSheaf.obj.obj U) (x : N.val.obj U) : N.val.obj U := r • x

private theorem scalarValue_restrict (N : X.Modules) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (r : X.ringCatSheaf.obj.obj U) (x : N.val.obj U) :
    N.val.map i (scalarValue N U r x) =
      scalarValue N V (X.ringCatSheaf.obj.map i r) (N.val.map i x) :=
  N.val.map_smul i r x

private def linearHom (L N : X.Modules) : Subfunctor (additiveHom L N) where
  obj U := { α | ∀ (W : (Over U.unop)ᵒᵖ)
    (r : X.ringCatSheaf.obj.obj ((Over.forget U.unop).op.obj W))
    (x : L.val.obj ((Over.forget U.unop).op.obj W)), α.app W (r • x) =
      scalarValue N ((Over.forget U.unop).op.obj W) r (α.app W x) }
  map {U V} i α hα := by
    intro W r x
    exact hα ((Over.map i.unop).op.obj W) r x

private def underlyingHom (L N : X.Modules) (U : X.Opens)
    (α : bundleHomSections L N U) : (additiveHom L N).obj (.op U) :=
  (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map α.val

private def linearHomEquiv (L N : X.Modules) (U : X.Opens) :
    bundleHomSections L N U ≃ (linearHom L N).toFunctor.obj (.op U) where
  toFun α := ⟨underlyingHom L N U α, fun W r x ↦ (α.val.app W).hom.map_smul r x⟩
  invFun α :=
    { val :=
      { app := fun W ↦ ModuleCat.ofHom (X := (L.over U).val.obj W)
          (Y := (N.over U).val.obj W)
          { toFun := α.1.app W
            map_add' := (α.1.app W).hom.map_add
            map_smul' := α.2 W }
        naturality := fun {V W} i ↦ by
          apply ModuleCat.hom_ext
          ext x
          exact congr($(α.1.naturality i).hom x) } }
  left_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv α := by
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

/-- The actual restricted module-Hom presheaf of types. -/
def bundleHomTypePresheaf (L N : X.Modules) : X.Opensᵒᵖ ⥤ Type u where
  obj U := bundleHomSections L N U.unop
  map i := ↾(bundleHomRestriction L N i.unop)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (linearHomEquiv L N U.unop).injective
    apply Subtype.ext
    change (additiveHom L N).map (𝟙 U) (underlyingHom L N U.unop α) =
      underlyingHom L N U.unop α
    exact ConcreteCategory.congr_hom ((additiveHom L N).map_id U) _
  map_comp {U V W} i j := by
    apply ConcreteCategory.hom_ext
    intro α
    apply (linearHomEquiv L N W.unop).injective
    apply Subtype.ext
    change (additiveHom L N).map (i ≫ j) (underlyingHom L N U.unop α) =
      (additiveHom L N).map j ((additiveHom L N).map i (underlyingHom L N U.unop α))
    exact ConcreteCategory.congr_hom ((additiveHom L N).map_comp i j) _

private def linearHomIso (L N : X.Modules) :
    bundleHomTypePresheaf L N ≅ (linearHom L N).toFunctor :=
  NatIso.ofComponents (fun U ↦ (linearHomEquiv L N U.unop).toIso) (fun i ↦ by
    apply ConcreteCategory.hom_ext
    intro α
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl)

private theorem additiveHom_naturality (L N : X.Modules) (U : X.Opens)
    (α : (additiveHom L N).obj (.op U))
    {V W : (Over U)ᵒᵖ} (i : V ⟶ W) (x : L.val.obj ((Over.forget U).op.obj V)) :
    N.val.map ((Over.forget U).op.map i) (α.app V x) =
      α.app W (L.val.map ((Over.forget U).op.map i) x) := by
  exact (congr($(α.naturality i).hom x)).symm

private theorem linearHom_isSheaf (L N : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X) (linearHom L N).toFunctor := by
  let J := _root_.Opens.grothendieckTopology X
  have hH : Presieve.IsSheaf J (additiveHom L N) :=
    (isSheaf_iff_isSheaf_of_type J _).1 (N.isSheaf.hom L.val.presheaf)
  have hN : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      (Presheaf.isSheaf_comp_of_isSheaf J N.val.presheaf (forget AddCommGrpCat) N.isSheaf)
  apply (isSheaf_iff_isSheaf_of_type J _).2
  apply (Subfunctor.isSheaf_iff (linearHom L N) hH).2
  intro U α hS W r x
  apply (hN.isSeparated _ (J.pullback_stable W.unop.hom hS)).ext
  intro Z p hp
  have hlin : (additiveHom L N).map (p ≫ W.unop.hom).op α ∈
      (linearHom L N).obj (.op Z) := hp
  have hv := hlin (.op (Over.mk (𝟙 Z)))
    (X.ringCatSheaf.obj.map p.op r) (L.val.map p.op x)
  dsimp only [additiveHom] at hv
  erw [CategoryTheory.presheafHom_map_app_op_mk_id] at hv
  let i : Over.mk (p ≫ W.unop.hom) ⟶ W.unop := Over.homMk p
  change N.val.map p.op (α.app W (r • x)) =
    N.val.map p.op (scalarValue N ((Over.forget U.unop).op.obj W) r (α.app W x))
  erw [scalarValue_restrict,
    additiveHom_naturality L N U.unop α i.op,
    additiveHom_naturality L N U.unop α i.op,
    L.val.map_smul p.op r x]
  exact hv

/-- Actual module morphisms satisfy sheaf descent, including their module linearity. -/
theorem bundleHomTypePresheaf_isSheaf (L N : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X) (bundleHomTypePresheaf L N) :=
  (Presheaf.isSheaf_of_iso_iff (linearHomIso L N)).2 (linearHom_isSheaf L N)

/-- The genuine sheaf of native restricted module morphisms. -/
def bundleHomTypeSheaf (L N : X.Modules) : TopCat.Sheaf (Type u) X :=
  ⟨bundleHomTypePresheaf L N, bundleHomTypePresheaf_isSheaf L N⟩

/-- On the largest open, native restricted morphisms identify with native global morphisms. -/
def bundleHomTopEquiv (L N : X.Modules) : bundleHomSections L N ⊤ ≃ (L ⟶ N) where
  toFun α :=
    { val :=
      { app := fun U ↦ α.val.app (.op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
        naturality := fun {U V} i ↦ by
          exact α.val.naturality
            (Over.homMk i.unop :
              Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
                Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))).op } }
  invFun α := (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map α
  left_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    ext x
    rfl
  right_inv α := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rfl

/-- Restricting the global morphism obtained from top Hom gives literal local restriction. -/
theorem bundleHomTopEquiv_restrict (L N : X.Modules) (α : bundleHomSections L N ⊤)
    (U : X.Opens) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).map (bundleHomTopEquiv L N α) =
      bundleHomRestriction L N (homOfLE (show U ≤ ⊤ from le_top)) α := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem cover_top {ι : Type*} (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) : (⊤ : X.Opens) ≤ iSup U := by
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr (hc x)

/-- Compatible native module maps on an actual open cover glue uniquely. -/
theorem bundleHom_existsUnique {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) :
    ∃! f : L ⟶ N, ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f = α i := by
  obtain ⟨f, hf, hu⟩ := (bundleHomTypeSheaf L N).existsUnique_gluing' U ⊤
    (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (cover_top U hc) α (by
      intro i j
      exact ha i j)
  refine ⟨bundleHomTopEquiv L N f, ?_, ?_⟩
  · intro i
    rw [bundleHomTopEquiv_restrict]
    exact hf i
  · intro g hg
    apply (bundleHomTopEquiv L N).symm.injective
    rw [Equiv.symm_apply_apply]
    apply hu
    intro i
    exact (bundleHomTopEquiv_restrict L N ((bundleHomTopEquiv L N).symm g) (U i)).symm.trans
      (by simpa using hg i)

/-- The native module morphism glued from genuine compatible local maps. -/
def bundleGlueHom {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) : L ⟶ N :=
  (bundleHom_existsUnique L N U hc α ha).choose

/-- The glued morphism has exactly the prescribed native restriction. -/
theorem bundleGlueHom_restrict {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (α : ∀ i, bundleHomSections L N (U i))
    (ha : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (α i) =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (α j)) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (bundleGlueHom L N U hc α ha) = α i :=
  (bundleHom_existsUnique L N U hc α ha).choose_spec.1 i

/-- Native global module maps are determined by restrictions to a genuine cover. -/
theorem bundleHom_ext {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) {f g : L ⟶ N}
    (h : ∀ i, (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g) : f = g := by
  apply (bundleHomTopEquiv L N).symm.injective
  apply (bundleHomTypeSheaf L N).eq_of_locally_eq' U ⊤
    (fun i ↦ homOfLE (show U i ≤ ⊤ from le_top)) (cover_top U hc)
  intro i
  change bundleHomRestriction L N (homOfLE (show U i ≤ ⊤ from le_top))
      ((bundleHomTopEquiv L N).symm f) =
    bundleHomRestriction L N (homOfLE (show U i ≤ ⊤ from le_top))
      ((bundleHomTopEquiv L N).symm g)
  rw [← bundleHomTopEquiv_restrict, ← bundleHomTopEquiv_restrict,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h i

/-- Restriction preserves the identity native module map. -/
theorem bundleHomRestriction_id (L : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    bundleHomRestriction L L i (𝟙 (L.over V)) = 𝟙 (L.over U) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Restriction preserves composition of genuine native module maps. -/
theorem bundleHomRestriction_comp (L N M : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (α : bundleHomSections L N V) (β : bundleHomSections N M V) :
    bundleHomRestriction L M i (α ≫ β) =
      bundleHomRestriction L N i α ≫ bundleHomRestriction N M i β := by
  simp only [bundleHomRestriction, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- A genuine restricted isomorphism under the native restriction comparisons. -/
def bundleHomRestrictionIso (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) : L.over U ≅ N.over U :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app L).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app N)

/-- Its hom is exactly the literal restricted local map. -/
theorem bundleHomRestrictionIso_hom (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) :
    (bundleHomRestrictionIso L N i e).hom = bundleHomRestriction L N i e.hom := rfl

/-- Its inverse is exactly the literal restricted local inverse map. -/
theorem bundleHomRestrictionIso_inv (L N : X.Modules) {U V : X.Opens} (i : U ⟶ V)
    (e : L.over V ≅ N.over V) :
    (bundleHomRestrictionIso L N i e).inv = bundleHomRestriction N L i e.inv := by
  simp only [bundleHomRestrictionIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    bundleHomRestriction, Category.assoc]

/-- Actual overlap equality of local iso homs entails overlap equality of their inverses. -/
theorem bundleLocalIso_inv_compatible {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) :
    ∀ i j, bundleHomRestriction N L (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).inv =
      bundleHomRestriction N L (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).inv := by
  intro i j
  rw [← bundleHomRestrictionIso_inv, ← bundleHomRestrictionIso_inv]
  apply congrArg Iso.inv
  apply Iso.ext
  exact he i j

/-- Compatible genuine local isomorphisms produce a native global isomorphism.
The global inverse is derived by descent of the actual local inverses. -/
def bundleGlueIso {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) : L ≅ N where
  hom := bundleGlueHom L N U hc (fun i ↦ (e i).hom) he
  inv := bundleGlueHom N L U hc (fun i ↦ (e i).inv) (bundleLocalIso_inv_compatible L N U e he)
  hom_inv_id := by
    apply bundleHom_ext L L U hc
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, bundleGlueHom_restrict, bundleGlueHom_restrict]
    exact (e i).hom_inv_id
  inv_hom_id := by
    apply bundleHom_ext N N U hc
    intro i
    rw [Functor.map_comp, CategoryTheory.Functor.map_id, bundleGlueHom_restrict, bundleGlueHom_restrict]
    exact (e i).inv_hom_id

/-- The global isomorphism has exactly the prescribed native local isomorphisms. -/
theorem bundleGlueIso_restrict {ι : Type*} (L N : X.Modules) (U : ι → X.Opens)
    (hc : ∀ x : X, ∃ i, x ∈ U i) (e : ∀ i, L.over (U i) ≅ N.over (U i))
    (he : ∀ i j, bundleHomRestriction L N (TopologicalSpace.Opens.infLELeft (U i) (U j)) (e i).hom =
      bundleHomRestriction L N (TopologicalSpace.Opens.infLERight (U i) (U j)) (e j).hom) (i : ι) :
    (SheafOfModules.overFunctor X.ringCatSheaf (U i)).mapIso (bundleGlueIso L N U hc e he) = e i := by
  apply Iso.ext
  exact bundleGlueHom_restrict L N U hc (fun i ↦ (e i).hom) he i

end

end SGPT.Foundations.Schemes
