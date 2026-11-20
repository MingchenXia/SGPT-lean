import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Module
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Actual finite local module triviality and the given unit determine the
stalk action. The reduced analytic strict-transform and flattening constructions
are separate obligations. -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

universe u

namespace SGPT.Okounkov

namespace DenseDegreeOne

variable {X : TopCat.{u}} {R A : X.Sheaf CommRingCat.{u}}

/-- The actual unit on the original ring stalks. -/
def stalkUnit (u : R ⟶ A) (x : X) : (TopCat.Presheaf.stalk (X := X) R.obj) x →+* (TopCat.Presheaf.stalk (X := X) A.obj) x :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat x).map u.hom).hom

/-- Forget the given commutative ring sheaf, with its original sections. -/
abbrev ringSheaf (R : X.Sheaf CommRingCat.{u}) : X.Sheaf RingCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- The module sheaf whose action is induced by this same given unit. -/
def unitModule (u : R ⟶ A) : SheafOfModules.{u} (ringSheaf R) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map u)).obj
    (SheafOfModules.unit (ringSheaf A))

private def unitAdditiveIso (u : R ⟶ A) :
    (unitModule u).val.presheaf ≅ A.obj ⋙ (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext a; rfl)

/-- The preserved filtered-colimit comparison, retaining every actual germ. -/
private def unitStalkComparison (u : R ⟶ A) (x : X) :
    (TopCat.Presheaf.stalk (X := X) (unitModule u).val.presheaf) x ≅
      ((forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).obj ((TopCat.Presheaf.stalk (X := X) A.obj) x) :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso (unitAdditiveIso u) ≪≫
    (preservesColimitIso ((forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
      ((OpenNhds.inclusion x).op ⋙ A.obj)).symm

private lemma unitStalkComparison_germ (u : R ⟶ A) (x : X)
    (U : Opens X) (hx : x ∈ U) (a : A.obj.obj (op U)) :
    (unitStalkComparison u x).hom
      ((TopCat.Presheaf.germ (X := X) (unitModule u).val.presheaf) U x hx a) = (TopCat.Presheaf.germ (X := X) A.obj) U x hx a := by
  simp only [unitStalkComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change ((preservesColimitIso ((forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
    ((OpenNhds.inclusion x).op ⋙ A.obj)).inv)
      ((TopCat.Presheaf.germ (X := X) (A.obj ⋙ (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))) U x hx a) =
    (TopCat.Presheaf.germ (X := X) A.obj) U x hx a
  exact CategoryTheory.congr_fun
    (ι_preservesColimitIso_inv ((forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
      ((OpenNhds.inclusion x).op ⋙ A.obj) (op ⟨U, hx⟩)) a

/-- The comparison is linear for the actual unit, rather than an unrelated
choice of algebra or module structure. -/
private def unitStalkLinearEquiv (u : R ⟶ A) (x : X) :
    let _ := (stalkUnit u x).toAlgebra
    (TopCat.Presheaf.stalk (X := X) (unitModule u).val.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) x] (TopCat.Presheaf.stalk (X := X) A.obj) x := by
  dsimp only [TopCat.Sheaf] at R A
  let _ := (stalkUnit u x).toAlgebra
  let e : (TopCat.Presheaf.stalk (X := X) (unitModule u).val.presheaf) x ≃+
      (TopCat.Presheaf.stalk (X := X) A.obj) x :=
    (unitStalkComparison u x).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro r a
  obtain ⟨U, hxU, rU, hr⟩ := (TopCat.Presheaf.exists_germ_eq (X := X) R.obj) r
  obtain ⟨V, hxV, aV, ha⟩ := (TopCat.Presheaf.exists_germ_eq (X := X) (unitModule u).val.presheaf) a
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW := R.obj.map (homOfLE (show W ≤ U from inf_le_left)).op rU
  let aW : (unitModule u).val.obj (op W) := (unitModule u).val.map (homOfLE (show W ≤ V from inf_le_right)).op aV
  have hrW : (TopCat.Presheaf.germ (X := X) R.obj) W x hxW rW = r :=
    ((TopCat.Presheaf.germ_res_apply (X := X) R.obj) (homOfLE inf_le_left) x hxW rU).trans hr
  have haW : (TopCat.Presheaf.germ (X := X) (unitModule u).val.presheaf) W x hxW aW = a :=
    ((TopCat.Presheaf.germ_res_apply (X := X) (unitModule u).val.presheaf)
      (homOfLE inf_le_right) x hxW aV).trans ha
  change e (r • a) = stalkUnit u x r * e a
  rw [← hrW, ← haW, ← PresheafOfModules.germ_smul]
  have heW (b : (unitModule u).val.obj (op W)) :
      e ((TopCat.Presheaf.germ (X := X) (unitModule u).val.presheaf) W x hxW b) =
        (TopCat.Presheaf.germ (X := X) A.obj) W x hxW b :=
    unitStalkComparison_germ u x W hxW b
  rw [heW, heW]
  let aWA : A.obj.obj (op W) := aW
  change (TopCat.Presheaf.germ (X := X) A.obj) W x hxW (u.hom.app (op W) rW * aWA) =
    stalkUnit u x ((TopCat.Presheaf.germ (X := X) R.obj) W x hxW rW) * (TopCat.Presheaf.germ (X := X) A.obj) W x hxW aWA
  rw [map_mul]
  have hg : stalkUnit u x ((TopCat.Presheaf.germ (X := X) R.obj) W x hxW rW) =
      (TopCat.Presheaf.germ (X := X) A.obj) W x hxW (u.hom.app (op W) rW) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW u.hom rW
  exact congrArg (fun z => z * (TopCat.Presheaf.germ (X := X) A.obj) W x hxW aWA) hg.symm

section ModuleStalkMaps

variable {B : X.Presheaf CommRingCat.{u}}
  {M N P : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)}

/-- The already existing additive stalk map is linear. -/
private def moduleStalkMap (f : M ⟶ N) (x : X) :
    (TopCat.Presheaf.stalk (X := X) M.presheaf) x →ₗ[(TopCat.Presheaf.stalk (X := X) B) x] (TopCat.Presheaf.stalk (X := X) N.presheaf) x where
  toFun := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map f)
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, rU, hr⟩ := (TopCat.Presheaf.exists_germ_eq (X := X) B) r
    obtain ⟨V, hxV, mV, hm⟩ := (TopCat.Presheaf.exists_germ_eq (X := X) M.presheaf) m
    let W := U ⊓ V
    have hxW : x ∈ W := ⟨hxU, hxV⟩
    let rW := B.map (homOfLE (show W ≤ U from inf_le_left)).op rU
    let mW : M.obj (op W) := M.map (homOfLE (show W ≤ V from inf_le_right)).op mV
    have hrW : (TopCat.Presheaf.germ (X := X) B) W x hxW rW = r :=
      ((TopCat.Presheaf.germ_res_apply (X := X) B) (homOfLE inf_le_left) x hxW rU).trans hr
    have hmW : (TopCat.Presheaf.germ (X := X) M.presheaf) W x hxW mW = m :=
      ((TopCat.Presheaf.germ_res_apply (X := X) M.presheaf) (homOfLE inf_le_right) x hxW mV).trans hm
    rw [← hrW, ← hmW, ← PresheafOfModules.germ_smul]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (TopCat.Presheaf.germ (X := X) N.presheaf) W x hxW (f.app (op W) (rW • mW)) = _
    rw [map_smul, PresheafOfModules.germ_smul]
    rfl

private lemma moduleStalkMap_comp (f : M ⟶ N) (g : N ⟶ P) (x : X) :
    moduleStalkMap (f ≫ g) x = (moduleStalkMap g x).comp (moduleStalkMap f x) := by
  ext a
  exact CategoryTheory.congr_fun
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
      ((PresheafOfModules.toPresheaf _).map f)
      ((PresheafOfModules.toPresheaf _).map g)) a

private lemma moduleStalkMap_id (x : X) :
    moduleStalkMap (𝟙 M) x = LinearMap.id := by
  ext a
  simp [moduleStalkMap]

private def moduleStalkIso (e : M ≅ N) (x : X) :
    (TopCat.Presheaf.stalk (X := X) M.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) B) x] (TopCat.Presheaf.stalk (X := X) N.presheaf) x :=
  LinearEquiv.ofLinearMap (moduleStalkMap e.hom x) (moduleStalkMap e.inv x)
    (by rw [← moduleStalkMap_comp, e.inv_hom_id, moduleStalkMap_id])
    (by rw [← moduleStalkMap_comp, e.hom_inv_id, moduleStalkMap_id])

end ModuleStalkMaps

private def moduleSheafStalkIso (M N : SheafOfModules.{u} (ringSheaf R))
    (e : M ≅ N) (x : X) : (TopCat.Presheaf.stalk (X := X) M.val.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) x]
      (TopCat.Presheaf.stalk (X := X) N.val.presheaf) x :=
  moduleStalkIso ((SheafOfModules.forget _).mapIso e) x

/-- The actual finite product, before taking any stalk or computing a rank. -/
def finiteUnitProduct (R : X.Sheaf CommRingCat.{u}) (n : ℕ) :
    SheafOfModules.{u} (ringSheaf R) :=
  ∏ᶜ fun _ : Fin n => SheafOfModules.unit (ringSheaf R)

private abbrev moduleStalkFunctor (R : X.Sheaf CommRingCat.{u}) (x : X) :
    SheafOfModules.{u} (ringSheaf R) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget (ringSheaf R) ⋙
    (PresheafOfModules.toPresheaf (ringSheaf R).obj ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)

private instance moduleStalkFunctor_preservesFiniteProducts
    (R : X.Sheaf CommRingCat.{u}) (x : X) :
    PreservesFiniteProducts (moduleStalkFunctor R x) := by
  dsimp only [moduleStalkFunctor]
  let : PreservesFiniteProducts (SheafOfModules.forget.{u} (ringSheaf R)) :=
    inferInstance
  let : PreservesFiniteProducts (PresheafOfModules.toPresheaf.{u} (ringSheaf R).obj) :=
    inferInstance
  let : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive :=
    inferInstance
  let : PreservesFiniteProducts (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    CategoryTheory.Functor.preservesFiniteProductsOfAdditive _
  let : PreservesFiniteProducts
      (PresheafOfModules.toPresheaf.{u} (ringSheaf R).obj ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
    CategoryTheory.Limits.comp_preservesFiniteProducts _ _
  exact CategoryTheory.Limits.comp_preservesFiniteProducts _ _

private def finiteProductStalkAddIso (R : X.Sheaf CommRingCat.{u}) (n : ℕ) (x : X) :
    (TopCat.Presheaf.stalk (X := X) (finiteUnitProduct R n).val.presheaf) x ≅
      AddCommGrpCat.of (Fin n → (TopCat.Presheaf.stalk (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) x) := by
  let G := moduleStalkFunctor R x
  letI : PreservesFiniteProducts G := moduleStalkFunctor_preservesFiniteProducts R x
  let f := fun _ : Fin n => SheafOfModules.unit (ringSheaf R)
  exact PreservesProduct.iso G f ≪≫
    IsLimit.conePointUniqueUpToIso (productIsProduct (fun i => G.obj (f i)))
      (AddCommGrpCat.HasLimit.productLimitCone (fun i => G.obj (f i))).isLimit

private lemma finiteProductStalkAddIso_apply (R : X.Sheaf CommRingCat.{u})
    (n : ℕ) (x : X) (a : (TopCat.Presheaf.stalk (X := X) (finiteUnitProduct R n).val.presheaf) x) (i : Fin n) :
    (finiteProductStalkAddIso R n x).hom a i =
      moduleStalkMap
        ((Pi.π (fun _ : Fin n => SheafOfModules.unit (ringSheaf R)) i).val) x a := by
  let G := moduleStalkFunctor R x
  let f := fun _ : Fin n => SheafOfModules.unit (ringSheaf R)
  let c := IsLimit.conePointUniqueUpToIso (productIsProduct (fun j => G.obj (f j)))
    (AddCommGrpCat.HasLimit.productLimitCone (fun j => G.obj (f j))).isLimit
  let ev : AddCommGrpCat.of (Fin n → G.obj (SheafOfModules.unit (ringSheaf R))) ⟶
      G.obj (f i) := AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => G.obj (f j)) i)
  have hc : c.hom ≫ ev = Pi.π (fun j => G.obj (f j)) i :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (productIsProduct (fun j => G.obj (f j)))
      (AddCommGrpCat.HasLimit.productLimitCone (fun j => G.obj (f j))).isLimit ⟨i⟩
  have h : (finiteProductStalkAddIso R n x).hom ≫ ev = G.map (Pi.π f i) := by
    change ((PreservesProduct.iso G f).hom ≫ c.hom) ≫ ev = G.map (Pi.π f i)
    rw [Category.assoc, hc, PreservesProduct.iso_hom, piComparison_comp_π]
  exact CategoryTheory.congr_fun h a

private def finiteProductStalkLinearEquiv (R : X.Sheaf CommRingCat.{u})
    (n : ℕ) (x : X) :
    (TopCat.Presheaf.stalk (X := X) (finiteUnitProduct R n).val.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) x]
      (Fin n → (TopCat.Presheaf.stalk (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) x) := by
  let e := (finiteProductStalkAddIso R n x).addCommGroupIsoToAddEquiv
  refine { e with map_smul' := ?_ }
  intro r a
  ext i
  change (finiteProductStalkAddIso R n x).hom (r • a) i =
    r • (finiteProductStalkAddIso R n x).hom a i
  rw [finiteProductStalkAddIso_apply, finiteProductStalkAddIso_apply, map_smul]

private def unitSelfStalkLinearEquiv (R : X.Sheaf CommRingCat.{u}) (x : X) :
    (TopCat.Presheaf.stalk (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) x]
      (TopCat.Presheaf.stalk (X := X) R.obj) x := by
  dsimp only [TopCat.Sheaf] at R
  let e' : (TopCat.Presheaf.stalk (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) x ≃+
      (TopCat.Presheaf.stalk (X := X) R.obj) x :=
    (unitStalkComparison (𝟙 R) x).addCommGroupIsoToAddEquiv
  refine { e' with map_smul' := ?_ }
  intro r a
  obtain ⟨U, hxU, rU, hr⟩ := (TopCat.Presheaf.exists_germ_eq (X := X) R.obj) r
  obtain ⟨V, hxV, aV, ha⟩ :=
    (TopCat.Presheaf.exists_germ_eq (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) a
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW := R.obj.map (homOfLE (show W ≤ U from inf_le_left)).op rU
  let aW : (SheafOfModules.unit (ringSheaf R)).val.obj (op W) :=
    (SheafOfModules.unit (ringSheaf R)).val.map (homOfLE (show W ≤ V from inf_le_right)).op aV
  have hrW : (TopCat.Presheaf.germ (X := X) R.obj) W x hxW rW = r :=
    ((TopCat.Presheaf.germ_res_apply (X := X) R.obj) (homOfLE inf_le_left) x hxW rU).trans hr
  have haW : (TopCat.Presheaf.germ (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) W x hxW aW = a :=
    ((TopCat.Presheaf.germ_res_apply (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf)
      (homOfLE inf_le_right) x hxW aV).trans ha
  change e' (r • a) = r * e' a
  rw [← hrW, ← haW, ← PresheafOfModules.germ_smul]
  have heW (b : (SheafOfModules.unit (ringSheaf R)).val.obj (op W)) :
      e' ((TopCat.Presheaf.germ (X := X) (SheafOfModules.unit (ringSheaf R)).val.presheaf) W x hxW b) =
        (TopCat.Presheaf.germ (X := X) R.obj) W x hxW b :=
    unitStalkComparison_germ (𝟙 R) x W hxW b
  rw [heW, heW]
  let aWR : R.obj.obj (op W) := aW
  change (TopCat.Presheaf.germ (X := X) R.obj) W x hxW (rW * aWR) =
    (TopCat.Presheaf.germ (X := X) R.obj) W x hxW rW *
      (TopCat.Presheaf.germ (X := X) R.obj) W x hxW aWR
  exact map_mul _ rW aWR

private def finiteProductStalkCoordinates (R : X.Sheaf CommRingCat.{u})
    (n : ℕ) (x : X) :
    (TopCat.Presheaf.stalk (X := X) (finiteUnitProduct R n).val.presheaf) x ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) x]
      (Fin n → (TopCat.Presheaf.stalk (X := X) R.obj) x) :=
  (finiteProductStalkLinearEquiv R n x).trans
    (LinearEquiv.piCongrRight fun _ => unitSelfStalkLinearEquiv R x)

/-- The finite local hypothesis is a genuine module-sheaf isomorphism on an
open subspace. It contains no prescribed rank, stalk inverse or unit inverse. -/
def HasFiniteLocalUnitTrivializations (u : R ⟶ A) : Prop :=
  ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (n : ℕ),
    Nonempty (unitModule (X := TopCat.of V) ((V.sheafRestrict (C := CommRingCat)).map u) ≅
      finiteUnitProduct (X := TopCat.of V) ((V.sheafRestrict (C := CommRingCat)).obj R) n)

private abbrev openInclusion (V : Opens X) : TopCat.of V ⟶ X :=
  V.inclusion'

/-- The actual open-restriction stalk comparison from the existing pullback
and naive open-pullback isomorphisms. -/
private def restrictionStalkIso (R : X.Sheaf CommRingCat.{u})
    (V : Opens X) (y : V) :
    (TopCat.Presheaf.stalk (X := X) R.obj) y.val ≅ (TopCat.Presheaf.stalk (X := TopCat.of V) ((V.sheafRestrict (C := CommRingCat)).obj R).obj) y :=
  TopCat.Presheaf.stalkPullbackIso CommRingCat (openInclusion V) R.obj y ≪≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).mapIso
      (V.isOpenEmbedding.isOpenMap.pullbackIso.app R.obj)

private lemma restrictionStalkIso_natural (u : R ⟶ A) (V : Opens X) (y : V) :
    ((TopCat.Presheaf.stalkFunctor CommRingCat y.val).map u.hom) ≫
        (restrictionStalkIso A V y).hom =
      (restrictionStalkIso R V y).hom ≫
        ((TopCat.Presheaf.stalkFunctor CommRingCat y).map
          ((V.sheafRestrict (C := CommRingCat)).map u).hom) := by
  let up : R.obj ⟶ A.obj := u.hom
  dsimp only [TopCat.Sheaf] at R A
  have hpb :
      ((TopCat.Presheaf.stalkFunctor CommRingCat y.val).map up) ≫
          TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) A.obj y =
        TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) R.obj y ≫
          ((TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
            ((TopCat.Presheaf.pullback CommRingCat (openInclusion V)).map up)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hy
    have ha := TopCat.Presheaf.germ_stalkPullbackHom
      CommRingCat (openInclusion V) A.obj y U hy
    change (TopCat.Presheaf.germ (X := X) A.obj) U y.val hy ≫
      TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) A.obj y = _ at ha
    have hr := TopCat.Presheaf.germ_stalkPullbackHom
      CommRingCat (openInclusion V) R.obj y U hy
    change (TopCat.Presheaf.germ (X := X) R.obj) U y.val hy ≫
      TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) R.obj y = _ at hr
    have hr' := congrArg (fun q => q ≫
      ((TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
        ((TopCat.Presheaf.pullback CommRingCat (openInclusion V)).map up))) hr
    simp only [Category.assoc] at hr'
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
    dsimp only [TopCat.Presheaf.stalk]
    rw [ha, hr']
    erw [TopCat.Presheaf.stalkFunctor_map_germ]
    have hn := NatTrans.congr_app
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat (openInclusion V)).unit.naturality
        up) (op U)
    dsimp only [TopCat.Presheaf, NatTrans.comp_app, Functor.id_map, Functor.id_obj,
      Functor.comp_map, TopCat.Presheaf.pushforward, Functor.whiskeringLeft,
      Functor.whiskerLeft, Functor.op] at hn
    simpa only [Category.assoc, TopCat.Presheaf.stalk] using congrArg (fun q => q ≫
      TopCat.Presheaf.germ (X := TopCat.of V)
        ((TopCat.Presheaf.pullback CommRingCat (openInclusion V)).obj A.obj)
          ((Opens.map (openInclusion V)).obj U) y hy) hn
  have hn := congrArg
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
      (V.isOpenEmbedding.isOpenMap.pullbackIso.hom.naturality up)
  simp only [Functor.map_comp] at hn
  change
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
        ((TopCat.Presheaf.pullback CommRingCat (openInclusion V)).map up) ≫
      (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
        (V.isOpenEmbedding.isOpenMap.pullbackIso.app A.obj).hom =
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
        (V.isOpenEmbedding.isOpenMap.pullbackIso.app R.obj).hom ≫
      (TopCat.Presheaf.stalkFunctor (X := TopCat.of V) CommRingCat y).map
        ((V.sheafRestrict (C := CommRingCat)).map u).hom at hn
  change _ ≫ (TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) A.obj y ≫ _) =
    (TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) R.obj y ≫ _) ≫ _
  rw [← Category.assoc, hpb, Category.assoc, Category.assoc]
  simpa only [Functor.map_comp, Functor.mapIso_hom, Category.assoc] using congrArg
    (fun q => TopCat.Presheaf.stalkPullbackHom CommRingCat (openInclusion V) R.obj y ≫ q) hn

/-- Take the given local module isomorphism to the original ring stalks, with
the action of the same original unit. All coordinate and ring comparisons
are manufactured from the actual local isomorphism. -/
private def localStalkCoordinates (u : R ⟶ A) (V : Opens X) (n : ℕ)
    (e : unitModule (X := TopCat.of V) ((V.sheafRestrict (C := CommRingCat)).map u) ≅
      finiteUnitProduct (X := TopCat.of V) ((V.sheafRestrict (C := CommRingCat)).obj R) n)
    (y : V) :
    let _ := (stalkUnit u y.val).toAlgebra
    (TopCat.Presheaf.stalk (X := X) A.obj) y.val ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) y.val] (Fin n → (TopCat.Presheaf.stalk (X := X) R.obj) y.val) := by
  let Rv : (TopCat.of V).Sheaf CommRingCat.{u} := (V.sheafRestrict (C := CommRingCat)).obj R
  let Av : (TopCat.of V).Sheaf CommRingCat.{u} := (V.sheafRestrict (C := CommRingCat)).obj A
  let uv : Rv ⟶ Av := (V.sheafRestrict (C := CommRingCat)).map u
  let _ := (stalkUnit u y.val).toAlgebra
  let _ := (stalkUnit (X := TopCat.of V) uv y).toAlgebra
  let eR := (restrictionStalkIso R V y).commRingCatIsoToRingEquiv
  let eA := (restrictionStalkIso A V y).commRingCatIsoToRingEquiv
  let q : (TopCat.Presheaf.stalk (X := TopCat.of V) Av.obj) y ≃ₗ[(TopCat.Presheaf.stalk (X := TopCat.of V) Rv.obj) y] (Fin n → (TopCat.Presheaf.stalk (X := TopCat.of V) Rv.obj) y) :=
    (unitStalkLinearEquiv (X := TopCat.of V) uv y).symm.trans
      ((moduleSheafStalkIso (X := TopCat.of V) _ _ e y).trans
        (finiteProductStalkCoordinates (X := TopCat.of V) Rv n y))
  have hunit (r : (TopCat.Presheaf.stalk (X := X) R.obj) y.val) :
      eA (stalkUnit u y.val r) = stalkUnit uv y (eR r) :=
    CategoryTheory.congr_fun (restrictionStalkIso_natural u V y) r
  exact
    { toFun := fun a i => eR.symm (q (eA a) i)
      invFun := fun f => eA.symm (q.symm (fun i => eR (f i)))
      map_add' := by
        intro a b
        ext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro r a
        ext i
        change eR.symm (q (eA (stalkUnit u y.val r * a)) i) =
          r * eR.symm (q (eA a) i)
        rw [map_mul, hunit]
        change eR.symm (q (eR r • eA a) i) = _
        rw [map_smul]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := by
        intro a
        simp only [RingEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply,
          RingEquiv.symm_apply_apply]
      right_inv := by
        intro f
        funext i
        simp only [RingEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
          RingEquiv.symm_apply_apply] }

end DenseDegreeOne

open DenseDegreeOne

variable {X : TopCat.{u}} {R A : X.Sheaf CommRingCat.{u}}

/-- Genuine finite local module-sheaf trivializations and a dense bijective
unit locus manufacture rank one and bijectivity on every original stalk. -/
theorem rank_one_of_dense_unit_locus
    [∀ x : X, IsLocalRing ((TopCat.Presheaf.stalk (X := X) R.obj) x)]
    (u : R ⟶ A) (hfinite : HasFiniteLocalUnitTrivializations u)
    (D : Set X) (hD : Dense D)
    (huD : ∀ x ∈ D, Function.Bijective (stalkUnit u x)) :
    ∀ x : X, let _ := (stalkUnit u x).toAlgebra
      Module.finrank ((TopCat.Presheaf.stalk (X := X) R.obj) x) ((TopCat.Presheaf.stalk (X := X) A.obj) x) = 1 ∧
        Function.Bijective (stalkUnit u x) := by
  intro x
  obtain ⟨V, hxV, n, he⟩ := hfinite x
  obtain ⟨e⟩ := he
  obtain ⟨y, hyD, hyV⟩ := hD.exists_mem_open V.isOpen ⟨x, hxV⟩
  let _ := (stalkUnit u x).toAlgebra
  let _ := (stalkUnit u y).toAlgebra
  let ex := DenseDegreeOne.localStalkCoordinates u V n e ⟨x, hxV⟩
  let ey := DenseDegreeOne.localStalkCoordinates u V n e ⟨y, hyV⟩
  let ed : (TopCat.Presheaf.stalk (X := X) R.obj) y ≃ₗ[(TopCat.Presheaf.stalk (X := X) R.obj) y] (TopCat.Presheaf.stalk (X := X) A.obj) y :=
    LinearEquiv.ofBijective (Algebra.linearMap ((TopCat.Presheaf.stalk (X := X) R.obj) y) ((TopCat.Presheaf.stalk (X := X) A.obj) y))
      (huD y hyD)
  have hny : Module.finrank ((TopCat.Presheaf.stalk (X := X) R.obj) y) ((TopCat.Presheaf.stalk (X := X) A.obj) y) = n :=
    ey.finrank_eq.trans (by simp)
  have hyone : Module.finrank ((TopCat.Presheaf.stalk (X := X) R.obj) y) ((TopCat.Presheaf.stalk (X := X) A.obj) y) = 1 :=
    ed.finrank_eq.symm.trans (Module.finrank_self ((TopCat.Presheaf.stalk (X := X) R.obj) y))
  have hn : n = 1 := hny.symm.trans hyone
  have hxone : Module.finrank ((TopCat.Presheaf.stalk (X := X) R.obj) x) ((TopCat.Presheaf.stalk (X := X) A.obj) x) = 1 :=
    ex.finrank_eq.trans (by simp [hn])
  let _ : Module.Free ((TopCat.Presheaf.stalk (X := X) R.obj) x) ((TopCat.Presheaf.stalk (X := X) A.obj) x) :=
    Module.Free.of_equiv ex.symm
  exact ⟨hxone, Module.Free.bijective_algebraMap_of_finrank_eq_one hxone⟩

/-- The actual given unit has a unique natural ring-sheaf inverse. Every
section and stalk identity and every actual commuting-square readback follows
from the manufactured whole inverse. -/
theorem exists_unique_sheaf_inverse_of_dense_unit_locus
    [∀ x : X, IsLocalRing ((TopCat.Presheaf.stalk (X := X) R.obj) x)]
    (u : R ⟶ A) (hfinite : HasFiniteLocalUnitTrivializations u)
    (D : Set X) (hD : Dense D)
    (huD : ∀ x ∈ D, Function.Bijective (stalkUnit u x)) :
    ∃! v : A ⟶ R,
      u ≫ v = 𝟙 R ∧ v ≫ u = 𝟙 A ∧
      (∀ U : Opens X,
        Function.LeftInverse (v.hom.app (op U)) (u.hom.app (op U)) ∧
          Function.RightInverse (v.hom.app (op U)) (u.hom.app (op U))) ∧
      (∀ x : X,
        Function.LeftInverse (stalkUnit v x) (stalkUnit u x) ∧
          Function.RightInverse (stalkUnit v x) (stalkUnit u x)) ∧
      (∀ (R' A' : X.Sheaf CommRingCat.{u}) (u' : R' ⟶ A') (v' : A' ⟶ R')
        (α : R ⟶ R') (β : A ⟶ A'),
        u' ≫ v' = 𝟙 R' → v' ≫ u' = 𝟙 A' →
          u ≫ β = α ≫ u' → v ≫ α = β ≫ v') := by
  dsimp only [TopCat.Sheaf] at R A
  have hstalk := rank_one_of_dense_unit_locus u hfinite D hD huD
  have hb (U : Opens X) : Function.Bijective (u.hom.app (op U)) :=
    TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective u U
      (fun x _ => (hstalk x).2)
  let E (U : (Opens X)ᵒᵖ) : R.obj.obj U ≃+* A.obj.obj U :=
    RingEquiv.ofBijective (u.hom.app U).hom (hb U.unop)
  let v : A ⟶ R :=
    { hom :=
      { app := fun U => CommRingCat.ofHom (E U).symm.toRingHom
        naturality := by
          intro U W f
          ext a
          apply (hb W.unop).injective
          change u.hom.app W ((E W).symm (A.obj.map f a)) =
            u.hom.app W (R.obj.map f ((E U).symm a))
          have hleft : u.hom.app W ((E W).symm (A.obj.map f a)) = A.obj.map f a :=
            (E W).apply_symm_apply _
          have hright : u.hom.app W (R.obj.map f ((E U).symm a)) = A.obj.map f a := by
            calc
              _ = A.obj.map f (u.hom.app U ((E U).symm a)) :=
                u.hom.naturality_apply f _
              _ = _ := congrArg (fun z => A.obj.map f z) ((E U).apply_symm_apply a)
          exact hleft.trans hright.symm } }
  have huv : u ≫ v = 𝟙 R := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U a
    exact (E U).symm_apply_apply a
  have hvu : v ≫ u = 𝟙 A := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U a
    exact (E U).apply_symm_apply a
  refine ⟨v, ⟨huv, hvu, ?_, ?_, ?_⟩, ?_⟩
  · intro U
    exact ⟨fun a => (E (op U)).symm_apply_apply a,
      fun a => (E (op U)).apply_symm_apply a⟩
  · intro x
    let F := TopCat.Sheaf.forget CommRingCat X ⋙
      TopCat.Presheaf.stalkFunctor CommRingCat x
    constructor
    · intro a
      have h : F.map u ≫ F.map v = 𝟙 (F.obj R) := by
        rw [← F.map_comp, huv, F.map_id]
      exact CategoryTheory.congr_fun h a
    · intro a
      have h : F.map v ≫ F.map u = 𝟙 (F.obj A) := by
        rw [← F.map_comp, hvu, F.map_id]
      exact CategoryTheory.congr_fun h a
  · intro R' A' u' v' α β hu'v' _ hcomm
    calc
      v ≫ α = (v ≫ α) ≫ (u' ≫ v') := by rw [hu'v']; simp
      _ = v ≫ (α ≫ u') ≫ v' := by simp only [Category.assoc]
      _ = v ≫ (u ≫ β) ≫ v' := by rw [hcomm]
      _ = β ≫ v' := by simp only [← Category.assoc, hvu, Category.id_comp]
  · intro w hw
    calc
      w = (v ≫ u) ≫ w := by rw [hvu]; simp
      _ = v ≫ (u ≫ w) := Category.assoc _ _ _
      _ = v := by rw [hw.1]; simp

end SGPT.Okounkov
