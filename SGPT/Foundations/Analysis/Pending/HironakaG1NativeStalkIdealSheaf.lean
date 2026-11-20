import SGPT.Foundations.Analysis.Pending.HironakaNativePulledIdealStalk
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Genuine native ideal gluing from ordinary local stalk models

All original sections with germs in a family P form an actual native ideal
subsheaf. Exact stalk image is proved ONLY from local realizability or genuine
native open-chart ideal models. Full original sheaf/scalar inclusions remain.
Blueprint first: `hironaka-g1-native-stalk-ideal-sheaf.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace SGPT.Foundations.Analysis.Pending.HironakaG1NativeStalkIdealSheaf

open HironakaSingularModuleSheafStalk

noncomputable section
universe u
variable {X : LocallyRingedSpace.{u}} (P : (x : X) → Ideal (X.presheaf.stalk x).carrier)

/-- Literal original sections whose EVERY original germ belongs to P. -/
def sectionIdeal (U : Opens X.toTopCat) : Ideal (X.presheaf.obj (op U)).carrier where
  carrier := {s | ∀ (x : X) (hx : x ∈ U), X.presheaf.germ U x hx s ∈ P x}
  zero_mem' := by
    intro x hx
    rw [map_zero]
    exact Ideal.zero_mem _
  add_mem' := by
    intro s t hs ht x hx
    rw [map_add]
    exact Ideal.add_mem _ (hs x hx) (ht x hx)
  smul_mem' := by
    intro r s hs x hx
    change X.presheaf.germ U x hx (r * s) ∈ _
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (hs x hx)

private theorem sectionIdeal_restrict (U V : Opens X.toTopCat) (hUV : U ≤ V)
    (s : (X.presheaf.obj (op V)).carrier) (hs : s ∈ sectionIdeal P V) :
    X.presheaf.map (homOfLE hUV).op s ∈ sectionIdeal P U := by
  intro x hx
  rw [X.presheaf.germ_res_apply (homOfLE hUV) x hx s]
  exact hs x (hUV hx)

private def idealSubmodule :
    (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).Submodule where
  obj U := sectionIdeal P (unop U)
  map f := by
    intro s hs
    exact sectionIdeal_restrict P _ _ (leOfHom f.unop) s hs

private def idealPresheaf : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (idealSubmodule P).toPresheafOfModules

private theorem idealPresheaf_isSheaf :
    TopCat.Presheaf.IsSheaf (X := X.toTopCat) (idealPresheaf P).presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.toTopCat) _).mpr
  intro ι U sf hcpt
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hcpt i j)
  obtain ⟨s, hglue, huniq⟩ := X.toSheafedSpace.IsSheaf.isSheafUniqueGluing U
    (fun i => (sf i).val) hcompat
  have hs : s ∈ sectionIdeal P (iSup U) := by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    have hg := congrArg (X.presheaf.germ (U i) x hxi) (hglue i)
    rw [X.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (sf i).property x hxi
  refine ⟨⟨s, hs⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hglue i
  · intro t ht
    apply Subtype.ext
    apply huniq t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The actual native unit-module subsheaf, for any stalk-ideal family. -/
def idealModule : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf) where
  val := idealPresheaf P
  isSheaf := idealPresheaf_isSheaf P

/-- The literal original section-subtype inclusion into the original unit. -/
def idealInclusion : idealModule P ⟶ SheafOfModules.unit _ := ⟨(idealSubmodule P).ι⟩

@[simp] theorem idealInclusion_app (U : Opens X.toTopCat) (s : sectionIdeal P U) :
    (idealInclusion P).val.app (op U) s = s.val := rfl

instance idealInclusion_mono : Mono (idealInclusion P) := by
  have hmono : Mono ((SheafOfModules.forget _).map (idealInclusion P)) := by
    change Mono (idealSubmodule P).ι
    infer_instance
  exact (SheafOfModules.forget _).mono_of_mono_map hmono

/-- Ordinary local ORIGINAL germ representatives whose ALL germs lie in P. -/
def LocallyRealizable : Prop :=
  ∀ (x : X) (r : (X.presheaf.stalk x).carrier), r ∈ P x →
    ∃ (U : Opens X.toTopCat) (hx : x ∈ U) (s : (X.presheaf.obj (op U)).carrier),
      X.presheaf.germ U x hx s = r ∧
      ∀ (y : X) (hy : y ∈ U), X.presheaf.germ U y hy s ∈ P y

private abbrev idealNativeStalkModule (x : X) :
    Module (X.presheaf.stalk x).carrier
      ↑(TopCat.Presheaf.stalk (idealModule P).val.presheaf x) :=
  nativeSheafStalkModule X.toSheafedSpace.sheaf (idealModule P) x

attribute [instance] idealNativeStalkModule

/-- The actual native linear inclusion on the original module stalk. -/
def stalkInclusion (x : X) :
    ↑(TopCat.Presheaf.stalk (idealModule P).val.presheaf x) →ₗ[
      (X.presheaf.stalk x).carrier] (X.presheaf.stalk x).carrier :=
  stalkInclusionLinearMap X.toSheafedSpace.sheaf (idealModule P) (idealInclusion P) x

@[simp] theorem stalkInclusion_germ (x : X) (U : Opens X.toTopCat) (hx : x ∈ U)
    (s : sectionIdeal P U) :
    stalkInclusion P x (TopCat.Presheaf.germ (idealModule P).val.presheaf U x hx s) =
      X.presheaf.germ U x hx s.val :=
  stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf (idealModule P) (idealInclusion P) x U hx s

theorem stalkInclusion_injective (x : X) : Function.Injective (stalkInclusion P x) :=
  stalkInclusionLinearMap_injective X.toSheafedSpace.sheaf (idealModule P)
    (idealInclusion P) (fun _ => Subtype.val_injective) x

/-- Arbitrary families give ONLY this inclusion, not equality of stalk ideals. -/
theorem stalkInclusion_range_le (x : X) : LinearMap.range (stalkInclusion P x) ≤ P x := by
  rintro r ⟨m, rfl⟩
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (idealModule P).val.presheaf m
  exact (stalkInclusion_germ P x U hxU s).symm ▸ s.property x hxU

/-- BOTH entire ideal directions, proved only with genuine local realizability. -/
theorem stalkInclusion_range (hP : LocallyRealizable P) (x : X) :
    LinearMap.range (stalkInclusion P x) = P x := by
  apply le_antisymm (stalkInclusion_range_le P x)
  intro r hr
  obtain ⟨U, hxU, s, hs, hlocal⟩ := hP x r hr
  refine ⟨TopCat.Presheaf.germ (idealModule P).val.presheaf U x hxU ⟨s, hlocal⟩, ?_⟩
  exact (stalkInclusion_germ P x U hxU ⟨s, hlocal⟩).trans hs

/-- A genuine local original open-chart module IMAGE model at an actual point.
No global ideal object, realization, or output isomorphism is assumed. -/
def LocalModelAt (x : X) : Prop :=
  ∃ (L : LocallyRingedSpace.{u}) (f : L ⟶ X) (z : L),
    LocallyRingedSpace.IsOpenImmersion f ∧ f.base z = x ∧
    ∃ (B : SheafOfModules.{u} (forgetRing L.toSheafedSpace.sheaf))
      (b : B ⟶ SheafOfModules.unit (forgetRing L.toSheafedSpace.sheaf)),
      ∀ w : L, Ideal.map (f.stalkMap w).hom (P (f.base w)) =
        LinearMap.range (stalkInclusionLinearMap L.toSheafedSpace.sheaf B b w)

private theorem openImmersion_invApp_germ {L : LocallyRingedSpace.{u}}
    (f : L ⟶ X) [LocallyRingedSpace.IsOpenImmersion f] (U : Opens L.toTopCat)
    (s : (L.presheaf.obj (op U)).carrier) (w : L) (hw : w ∈ U) :
    f.stalkMap w (X.presheaf.germ ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj U)
      (f.base w) (show f.base w ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj U from
        ⟨w, hw, rfl⟩) (LocallyRingedSpace.IsOpenImmersion.invApp f U s)) =
      L.presheaf.germ U w hw s := by
  rw [LocallyRingedSpace.stalkMap_germ_apply]
  have hsec := ConcreteCategory.congr_hom (LocallyRingedSpace.IsOpenImmersion.invApp_app f U) s
  change f.c.app (op ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj U))
    (LocallyRingedSpace.IsOpenImmersion.invApp f U s) = _ at hsec
  rw [hsec]
  let i : (Opens.map f.base).obj ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj U) ⟶ U :=
    homOfLE (by
      intro v hv
      change f.base v ∈ f.base '' U.1 at hv
      obtain ⟨a, ha, hea⟩ := hv
      have hf : LocallyRingedSpace.IsOpenImmersion f := inferInstance
      exact hf.base_open.injective hea ▸ ha)
  change L.presheaf.germ _ w _ (L.presheaf.map i.op s) = _
  exact L.presheaf.germ_res_apply i w _ s

/-- Genuine local native ideal modules and their WHOLE stalk images internally
construct ordinary local original section realizations. -/
theorem locallyRealizable_of_localModels (h : ∀ x : X, LocalModelAt P x) : LocallyRealizable P := by
  intro x r hr
  obtain ⟨L, f, z, hf, hz, B, b, hmodel⟩ := h x
  let := hf
  subst x
  have hmap : (f.stalkMap z).hom r ∈ Ideal.map (f.stalkMap z).hom (P (f.base z)) :=
    Ideal.mem_map_of_mem (f.stalkMap z).hom hr
  rw [hmodel z] at hmap
  obtain ⟨m, hm⟩ := hmap
  obtain ⟨U, hzU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf m
  let V := (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj U
  let s := LocallyRingedSpace.IsOpenImmersion.invApp f U (b.val.app (op U) t)
  have hzV : f.base z ∈ V := ⟨z, hzU, rfl⟩
  refine ⟨V, hzV, s, ?_, ?_⟩
  · apply (ConcreteCategory.bijective_of_isIso (f.stalkMap z)).1
    exact (openImmersion_invApp_germ f U (b.val.app (op U) t) z hzU).trans
      ((stalkInclusionLinearMap_germ L.toSheafedSpace.sheaf B b z U hzU t).symm.trans hm)
  · intro y hy
    change y ∈ f.base '' U.1 at hy
    obtain ⟨w, hw, rfl⟩ := hy
    have hg : (f.stalkMap w).hom (X.presheaf.germ V (f.base w)
        (show f.base w ∈ V from ⟨w, hw, rfl⟩) s) ∈
        LinearMap.range (stalkInclusionLinearMap L.toSheafedSpace.sheaf B b w) :=
      ⟨TopCat.Presheaf.germ B.val.presheaf U w hw t,
        (stalkInclusionLinearMap_germ L.toSheafedSpace.sheaf B b w U hw t).trans
          (openImmersion_invApp_germ f U (b.val.app (op U) t) w hw).symm⟩
    rw [← hmodel w] at hg
    have hg' : X.presheaf.germ V (f.base w) (show f.base w ∈ V from ⟨w, hw, rfl⟩) s ∈
        (Ideal.map (f.stalkMap w).hom (P (f.base w))).comap (f.stalkMap w).hom := hg
    simpa only [Ideal.comap_map_of_bijective _
      (ConcreteCategory.bijective_of_isIso (f.stalkMap w))] using hg'

/-- Exact original stalk image from genuine ordinary local chart models. -/
theorem stalkInclusion_range_of_localModels (h : ∀ x : X, LocalModelAt P x) (x : X) :
    LinearMap.range (stalkInclusion P x) = P x :=
  stalkInclusion_range P (locallyRealizable_of_localModels P h) x

section Uniqueness

variable (B : SheafOfModules.{u} (forgetRing X.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))

private theorem locallyRealizable_of_nativeIdeal
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x) :
    LocallyRealizable P := by
  intro x r hr
  rw [← hB x] at hr
  obtain ⟨m, hm⟩ := hr
  obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf m
  refine ⟨U, hx, b.val.app (op U) t,
    (stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf B b x U hx t).symm.trans hm, ?_⟩
  intro y hy
  rw [← hB y]
  exact ⟨TopCat.Presheaf.germ B.val.presheaf U y hy t,
    stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf B b y U hy t⟩

private def toIdealModule
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x) :
    B ⟶ idealModule P where
  val :=
    { app := fun U => ModuleCat.ofHom ((b.val.app U).hom.codRestrict
        (sectionIdeal P (unop U)) (fun t x hx => by
          rw [← hB x]
          exact ⟨TopCat.Presheaf.germ B.val.presheaf (unop U) x hx t,
            stalkInclusionLinearMap_germ X.toSheafedSpace.sheaf B b x (unop U) hx t⟩))
      naturality := by
        intro U V i
        ext t
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply b.val i t }

private theorem toIdealModule_comp
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x) :
    toIdealModule P B b hB ≫ idealInclusion P = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  rfl

private theorem toIdealModule_stalk_bijective
    (hb : ∀ U : Opens X.toTopCat, Function.Injective (b.val.app (op U)))
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x)
    (x : X) : Function.Bijective (stalkLinearMap (toIdealModule P B b hB).val x) := by
  have hcomm : (stalkInclusion P x).comp (stalkLinearMap (toIdealModule P B b hB).val x) =
      stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x := by
    ext m
    obtain ⟨U, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf m
    simp only [LinearMap.comp_apply]
    erw [stalkLinearMap_germ, stalkInclusion_germ, stalkInclusionLinearMap_germ]
    rfl
  constructor
  · intro a c he
    apply stalkInclusionLinearMap_injective X.toSheafedSpace.sheaf B b hb x
    exact (LinearMap.congr_fun hcomm a).symm.trans
      ((congrArg (stalkInclusion P x) he).trans (LinearMap.congr_fun hcomm c))
  · intro z
    have hz : stalkInclusion P x z ∈
        LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) := by
      rw [hB x, ← stalkInclusion_range P (locallyRealizable_of_nativeIdeal P B b hB) x]
      exact ⟨z, rfl⟩
    obtain ⟨m, hm⟩ := hz
    exact ⟨m, (stalkInclusion_injective P x) ((LinearMap.congr_fun hcomm m).trans hm)⟩

private theorem toIdealModule_isIso
    (hb : ∀ U : Opens X.toTopCat, Function.Injective (b.val.app (op U)))
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x) :
    IsIso (toIdealModule P B b hB) := by
  let f := toIdealModule P B b hB
  have hbij (x : X) := toIdealModule_stalk_bijective P B b hb hB x
  have happ (U : Opens X.toTopCat) : Function.Bijective (f.val.app (op U)) :=
    TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
      ((SheafOfModules.toSheaf _).map f) U (fun x _ => hbij x)
  let (U : (Opens X.toTopCat)ᵒᵖ) : IsIso (f.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (happ (unop U))
  let e : B.val ≅ (idealModule P).val :=
    PresheafOfModules.isoMk (fun U => asIso (f.val.app U)) (by
      intro U V i
      exact f.val.naturality i)
  have he : e.hom = f.val := by
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  let : IsIso ((SheafOfModules.forget (forgetRing X.toSheafedSpace.sheaf)).map f) :=
    show IsIso f.val from he ▸ (inferInstance : IsIso e.hom)
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/-- The entire native ideal subsheaf is uniquely determined by its actual
whole stalk image, retaining the SAME full original unit-sheaf inclusion. -/
theorem existsUnique_idealIso
    (hb : ∀ U : Opens X.toTopCat, Function.Injective (b.val.app (op U)))
    (hB : ∀ x : X, LinearMap.range (stalkInclusionLinearMap X.toSheafedSpace.sheaf B b x) = P x) :
    ∃! e : B ≅ idealModule P, e.hom ≫ idealInclusion P = b := by
  let f := toIdealModule P B b hB
  let : IsIso f := toIdealModule_isIso P B b hb hB
  refine ⟨asIso f, toIdealModule_comp P B b hB, ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_mono (idealInclusion P)).mp
  exact he.trans (toIdealModule_comp P B b hB).symm

end Uniqueness

end
end SGPT.Foundations.Analysis.Pending.HironakaG1NativeStalkIdealSheaf
