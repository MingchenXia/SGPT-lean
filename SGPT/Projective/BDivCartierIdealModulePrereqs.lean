/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange

/-! The ideal module, its affine section identifications and localization, and the regular
principal cover used to construct the original Cartier line and its canonical section.
The affine comparison lemmas are adapted from Hironaka's ideal-module development.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Membership in `I(U)` is local**: a function on an affine open `U` lies in `I(U)` if every
point of `U` has an open neighbourhood `V` such that the restriction of the function to every affine
open inside `V ∩ U` lies in the ideal of that open. -/
theorem mem_ideal_of_locally_mem (U : X.affineOpens) (s : Γ(X, U))
    (h : ∀ x ∈ (U : X.Opens), ∃ V : X.Opens, x ∈ V ∧ ∀ (U' : X.affineOpens)
      (hU' : (U' : X.Opens) ≤ U), (U' : X.Opens) ≤ V →
        X.presheaf.map (homOfLE hU').op s ∈ I.ideal U') :
    s ∈ I.ideal U := by
  let S : Set Γ(X, U) := {g | X.presheaf.map (homOfLE (X.basicOpen_le g)).op s ∈
    I.ideal (X.affineBasicOpen g)}
  have hspan : Ideal.span S = ⊤ := by
    refine (U.2.iSup_basicOpen_eq_self_iff).mp (le_antisymm (iSup_le fun g => X.basicOpen_le _)
      fun x hxU => ?_)
    obtain ⟨V, hxV, hV⟩ := h x hxU
    obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hxU
    exact Opens.mem_iSup.mpr ⟨⟨g, hV (X.affineBasicOpen g) (X.basicOpen_le g) hgV⟩, hxg⟩
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S hspan s fun g => ?_
  have := U.2.isLocalization_basicOpen (g : Γ(X, U))
  have hg := g.2
  change X.presheaf.map (homOfLE (X.basicOpen_le _)).op s ∈ I.ideal (X.affineBasicOpen _) at hg
  rw [← I.map_ideal_basicOpen] at hg
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ham⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Submonoid.powers (g : Γ(X, U))) Γ(X, X.basicOpen (g : Γ(X, U)))).mp hg
  have ham' : algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) (s * (g : Γ(X, U)) ^ n) =
      algebraMap Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) a := by
    rw [map_mul]
    exact ham
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (g : Γ(X, U)))
    Γ(X, X.basicOpen (g : Γ(X, U)))).mp ham'
  refine ⟨n + k, ?_⟩
  change (g : Γ(X, U)) ^ (n + k) * s ∈ I.ideal U
  rw [pow_add, mul_comm ((g : Γ(X, U)) ^ n), mul_assoc, mul_comm _ s, hc]
  exact Ideal.mul_mem_left _ _ a.2

/-- The condition defining the sections of the ideal sheaf `I` over an open `W`: the restriction to
every affine open `U ⊆ W` lies in `I(U)`. -/
def IsLocallyMem (W : X.Opens) (s : Γ(X, W)) : Prop :=
  ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W), X.presheaf.map (homOfLE hU).op s ∈ I.ideal U

theorem isLocallyMem_map {W W' : X.Opens} (h : W' ≤ W) {s : Γ(X, W)} (hs : I.IsLocallyMem W s) :
    I.IsLocallyMem W' (X.presheaf.map (homOfLE h).op s) := fun U hU => by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact hs U (hU.trans h)

/-- The submodules of sections of the ideal sheaf `I` inside `𝒪_X`: over an open `W`, the
functions whose restriction to every affine open `U ⊆ W` lies in `I(U)`. -/
noncomputable def toSubmodule : (SheafOfModules.unit X.ringCatSheaf).val.Submodule where
  obj W :=
    { carrier := {s | I.IsLocallyMem W.unop (s : Γ(X, W.unop))}
      add_mem' := fun {a b} ha hb U hU =>
        (congrArg (· ∈ I.ideal U) (map_add (X.presheaf.map (homOfLE hU).op).hom
          (a : Γ(X, W.unop)) (b : Γ(X, W.unop)))).mpr (add_mem (ha U hU) (hb U hU))
      zero_mem' := fun U hU =>
        (congrArg (· ∈ I.ideal U) (map_zero (X.presheaf.map (homOfLE hU).op).hom)).mpr
          (zero_mem _)
      smul_mem' := fun c s hs U hU =>
        (congrArg (· ∈ I.ideal U) (map_mul (X.presheaf.map (homOfLE hU).op).hom
          (c : Γ(X, W.unop)) (s : Γ(X, W.unop)))).mpr (Ideal.mul_mem_left _ _ (hs U hU)) }
  map f _ hs := I.isLocallyMem_map f.unop.le hs

/-- The sheaf condition of `toSubmodule`, from the locality of membership in `I(U)`
(`mem_ideal_of_locally_mem`). -/
theorem isSheaf_toSubmodule :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) I.toSubmodule.toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.presheaf ⋙ CategoryTheory.forget CommRingCat) := by
    rw [← isSheaf_iff_isSheaf_of_type, ← Presheaf.isSheaf_iff_isSheaf_forget]
    exact X.IsSheaf
  let G : Subfunctor (X.presheaf ⋙ CategoryTheory.forget CommRingCat) :=
    { obj W := {s | I.IsLocallyMem W.unop s}
      map {W W'} f s hs := I.isLocallyMem_map f.unop.le hs }
  have hG : Presieve.IsSheaf (Opens.grothendieckTopology X) G.toFunctor := by
    refine (G.isSheaf_iff hF).mpr fun W s hs U hU => ?_
    refine I.mem_ideal_of_locally_mem U _ fun x hxU => ?_
    obtain ⟨V, f, hf, hxV⟩ := hs x (hU hxU)
    refine ⟨V, hxV, fun U' hU' hU'V => ?_⟩
    have := hf U' hU'V
    change X.presheaf.map (homOfLE hU'V).op (X.presheaf.map (homOfLE f.le).op s) ∈ I.ideal U'
      at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact this
  refine Presieve.isSheaf_iso (Opens.grothendieckTopology X) ?_ hG
  exact NatIso.ofComponents (fun W =>
    { hom := TypeCat.ofHom fun x => ⟨x.1, x.2⟩
      inv := TypeCat.ofHom fun x => ⟨x.1, x.2⟩ }) (fun _ => rfl)

/-- **The ideal sheaf `I` as a sheaf of `𝒪_X`-modules**: the subsheaf of `𝒪_X` of the functions
whose restriction to every affine open `U` lies in `I(U)`. -/
noncomputable def toModules : X.Modules where
  val := I.toSubmodule.toPresheafOfModules
  isSheaf := I.isSheaf_toSubmodule

/-- Over an affine open `U`, the sections of `I.toModules` are the elements of `I(U)`. -/
theorem isLocallyMem_iff (U : X.affineOpens) (s : Γ(X, U)) :
    I.IsLocallyMem U s ↔ s ∈ I.ideal U := by
  refine ⟨fun hs => ?_, fun hs U' hU' => ?_⟩
  · have := hs U le_rfl
    rwa [show homOfLE (le_refl (U : X.Opens)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id] at this
  · exact I.ideal_le_comap_ideal hU' hs

/-- Over an affine open `U`, the sections of `I.toModules` are the elements of `I(U)`, as modules
over `Γ(X, U)`. -/
noncomputable def toModulesSectionsEquiv (U : X.affineOpens) :
    Γ(I.toModules, U) ≃ₗ[Γ(X, U)] I.ideal U where
  toFun s := ⟨(s : I.toSubmodule.obj (op (U : X.Opens))).1,
    (I.isLocallyMem_iff U _).mp (s : I.toSubmodule.obj (op (U : X.Opens))).2⟩
  invFun a := (⟨a.1, (I.isLocallyMem_iff U a.1).mpr a.2⟩ : I.toSubmodule.obj (op (U : X.Opens)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_toModulesSectionsEquiv (U : X.affineOpens) (s : Γ(I.toModules, U)) :
    ((I.toModulesSectionsEquiv U s : I.ideal U) : Γ(X, U)) =
      (s : I.toSubmodule.obj (op (U : X.Opens))).1 :=
  rfl

/-- The restriction maps of `I.toModules` are the restrictions of functions. -/
theorem coe_toModulesSectionsEquiv_restrictionMap {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(I.toModules, V)) :
    ((I.toModulesSectionsEquiv U (I.toModules.presheaf.map (homOfLE h).op s) : I.ideal U) :
        Γ(X, U)) =
      X.presheaf.map (homOfLE h).op (I.toModulesSectionsEquiv V s : Γ(X, V)) :=
  rfl

/-- The effective Cartier ideal predicate: each point has an affine neighborhood
on which a nonzerodivisor generates the ideal. -/
def IsInvertible (J : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
    ∃ f ∈ nonZeroDivisors Γ(X, U), J.ideal U = Ideal.span {f}

/-- The actual ideal module includes in the original actual structure module. -/
def toModulesInclusion (I : X.IdealSheafData) :
    I.toModules ⟶ SheafOfModules.unit X.ringCatSheaf where
  val := I.toSubmodule.ι

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The ring identity behind the restriction to an affine open: the `Γ(X, V)`-action on the
sections of `F.restrict hV.fromSpec` over `W` is the restriction. -/
theorem fromSpec_appIso_inv {V : X.Opens} (hV : IsAffineOpen V) (W : (Spec Γ(X, V)).Opens)
    (h : hV.fromSpec ''ᵁ W ≤ V) (r : Γ(X, V)) :
    (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, V)).inv r)) = X.presheaf.map (homOfLE h).op r := by
  apply (ConcreteCategory.bijective_of_isIso (hV.fromSpec.appIso W).hom).1
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    Scheme.Hom.appIso_hom, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.naturality_assoc, hV.fromSpec_app_self, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 3


/-- The restriction `Γ(F, V) → Γ(F, U)` as a `Γ(X, V)`-linear map, `Γ(F, U)` a `Γ(X, V)`-module
through the restriction of functions. -/
noncomputable def resₗ {U V : X.Opens} (h : U ≤ V) :
    letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
    Γ(F, V) →ₗ[Γ(X, V)] Γ(F, U) :=
  letI := Module.compHom Γ(F, U) (X.presheaf.map (homOfLE h).op).hom
  { toFun := F.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r x => F.val.map_smul (homOfLE h).op r x }

theorem resₗ_apply {U V : X.Opens} (h : U ≤ V) (x : Γ(F, V)) :
    F.resₗ h x = F.presheaf.map (homOfLE h).op x := rfl

omit F in
theorem fromSpec_image_top {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ''ᵁ ⊤ = V :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec

/-- The sections of `F` over an affine open `V` are the global sections of the restriction of `F`
to `Spec Γ(X, V) ≅ V`, as `Γ(X, V)`-modules. -/
noncomputable def topSectionsEquiv {V : X.Opens} (hV : IsAffineOpen V) :
    Γ(F, V) ≃ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, ⊤) :=
  LinearEquiv.ofBijective (M₂ := Γ(F.restrict hV.fromSpec, ⊤))
    { toFun := F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op (c • x) =
          (hV.fromSpec.appIso ⊤).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) •
              F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x
        rw [fromSpec_appIso_inv hV ⊤ (fromSpec_image_top hV).le]
        exact F.val.map_smul (homOfLE (fromSpec_image_top hV).le).op c x }
    (by
      have : IsIso (homOfLE (fromSpec_image_top hV).le).op := by
        rw [show (homOfLE (fromSpec_image_top hV).le).op = (eqToHom (fromSpec_image_top hV)).op
          from rfl]
        infer_instance
      exact ConcreteCategory.bijective_of_isIso
        (F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op))

theorem topSectionsEquiv_apply {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(F, V)) :
    F.topSectionsEquiv hV x = F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x :=
  rfl

set_option linter.style.haveILetI false in
/-- The restriction to a basic open `D(r)` of an affine open `V` is a localization on `X` if and
only if it is one for the restriction of `F` to `Spec Γ(X, V) ≅ V`, the condition of Mathlib's
`isIso_fromTildeΓ_iff_isLocalizing`: the two restriction maps are identified by the restrictions
of `F` along `Spec Γ(X, V) ≅ V`, and the actions of `Γ(X, V)` by `fromSpec_appIso_inv`. -/
theorem isLocalizedModule_restrict_fromSpec_iff {V : X.Opens} (hV : IsAffineOpen V)
    (r : Γ(X, V)) :
    letI := Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r)
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map
        (PrimeSpectrum.basicOpen r : (Spec Γ(X, V)).Opens).leTop.op).hom ↔
      IsLocalizedModule (Submonoid.powers r) (F.resₗ (X.basicOpen_le r)) := by
  letI := Module.compHom Γ(F, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  set W : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen r with hW
  have h2 : hV.fromSpec ''ᵁ W = X.basicOpen r := hV.fromSpec_image_basicOpen r
  let e1 := (F.topSectionsEquiv hV).toLinearMap
  let e2 : Γ(F, X.basicOpen r) →ₗ[Γ(X, V)] Γ(F.restrict hV.fromSpec, W) :=
    { toFun := F.presheaf.map (homOfLE h2.le).op
      map_add' := map_add _
      map_smul' := fun c x => by
        change F.presheaf.map (homOfLE h2.le).op
            (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c • x) =
          (hV.fromSpec.appIso W).inv ((Spec Γ(X, V)).presheaf.map (homOfLE le_top).op
            ((Scheme.ΓSpecIso Γ(X, V)).inv c)) • F.presheaf.map (homOfLE h2.le).op x
        rw [fromSpec_appIso_inv hV _ (h2.le.trans (X.basicOpen_le r)),
          show X.presheaf.map (homOfLE (h2.le.trans (X.basicOpen_le r))).op c =
            X.presheaf.map (homOfLE h2.le).op
              (X.presheaf.map (homOfLE (X.basicOpen_le r)).op c) by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl]
        exact F.val.map_smul (homOfLE h2.le).op _ x }
  have he1 : Function.Bijective e1 := (F.topSectionsEquiv hV).bijective
  have he2 : Function.Bijective e2 := by
    have : IsIso (homOfLE h2.le).op := by
      rw [show (homOfLE h2.le).op = (eqToHom h2).op from rfl]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (F.presheaf.map (homOfLE h2.le).op)
  have hcomm : e2 ∘ₗ F.resₗ (X.basicOpen_le r) =
      ((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1 := by
    ext x
    change F.presheaf.map (homOfLE h2.le).op (F.presheaf.map (homOfLE (X.basicOpen_le r)).op x) =
      F.presheaf.map _ (F.presheaf.map (homOfLE (fromSpec_image_top hV).le).op x)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : IsLocalizedModule (Submonoid.powers r) (e2 ∘ₗ F.resₗ (X.basicOpen_le r)) := by
      rw [hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mp h'
  · have h' : IsLocalizedModule (Submonoid.powers r)
        (((modulesSpecToSheaf.obj (F.restrict hV.fromSpec)).obj.map W.leTop.op).hom ∘ₗ e1) := by
      rw [← hcomm]
      exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e2 he2).mpr h
    exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e1 he1).mp h'

/-- The restriction of `F` to an open `U` along `U.ι` is the restriction to `Spec Γ(X, U)` pushed
along `U ≅ Spec Γ(X, U)`. -/
noncomputable def restrictιIso {U : X.Opens} (hU : IsAffineOpen U) :
    (F.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ F.restrict U.ι :=
  ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app F).symm ≪≫
    (restrictFunctorCongr (by rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc])).app F

/-- `F.over U` is the restriction of `F` along `U.ι`, through `overEquiv U`. -/
noncomputable def overIso (U : X.Opens) :
    (overEquiv U).inverse.obj (F.restrict U.ι) ≅ F.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app F).symm ≪≫
    ((overEquiv U).unitIso.app _).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

theorem coe_toModulesSectionsEquiv_smul (U : X.affineOpens) (c : Γ(X, U))
    (s : Γ(I.toModules, U)) :
    ((I.toModulesSectionsEquiv U (c • s) : I.ideal U) : Γ(X, U)) =
      c * (I.toModulesSectionsEquiv U s : Γ(X, U)) := by
  rw [LinearEquiv.map_smul]
  rfl

set_option linter.style.haveILetI false in
/-- Over a basic open `D(r)` of an affine open `U`, the sections of `I.toModules` are the
localization of those over `U`: `I(D(r)) = I(U)_r`. -/
theorem isLocalizedModule_toModules_resₗ (U : X.affineOpens) (r : Γ(X, U)) :
    letI := Module.compHom Γ(I.toModules, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    IsLocalizedModule (Submonoid.powers r) (I.toModules.resₗ (X.basicOpen_le r)) := by
  letI := Module.compHom Γ(I.toModules, X.basicOpen r)
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have := U.2.isLocalization_basicOpen r
  set ρ := X.presheaf.map (homOfLE (X.basicOpen_le r)).op
  set eU := I.toModulesSectionsEquiv U
  set eD := I.toModulesSectionsEquiv (X.affineBasicOpen r)
  -- The values in `Γ(X, D(r))` of the sections over `D(r)`.
  let v : Γ(I.toModules, X.basicOpen r) → Γ(X, X.basicOpen r) := fun w => (eD w).1
  have hv : Function.Injective v := fun w w' h => eD.injective (Subtype.ext h)
  have hres (s : Γ(I.toModules, U)) :
      v (I.toModules.resₗ (X.basicOpen_le r) s) = ρ (eU s : Γ(X, U)) :=
    I.coe_toModulesSectionsEquiv_restrictionMap (U := X.affineBasicOpen r) (V := U)
      (X.basicOpen_le r) s
  have hsmul' (c : Γ(X, X.basicOpen r)) (y : Γ(I.toModules, X.basicOpen r)) :
      v (c • y) = c * v y :=
    I.coe_toModulesSectionsEquiv_smul (X.affineBasicOpen r) c y
  have hsmul (c : Γ(X, U)) (y : Γ(I.toModules, X.basicOpen r)) : v (c • y) = ρ c * v y :=
    hsmul' (ρ c) y
  have hunit (n : ℕ) : IsUnit (ρ (r ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen r)) r).pow n
  refine ⟨fun x => ?_, fun y => ?_, fun {a b} h => ?_⟩
  · obtain ⟨_, n, rfl⟩ := x
    rw [Module.End.isUnit_iff]
    obtain ⟨u, hu⟩ := hunit n
    refine ⟨fun y z hyz => hv ?_, fun y => ⟨(u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y, hv ?_⟩⟩
    · have := congrArg v hyz
      simp only [Module.algebraMap_end_apply] at this
      rw [hsmul, hsmul, ← hu] at this
      exact u.isUnit.mul_left_cancel this
    · change v ((r ^ n) • ((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) • y)) = v y
      rw [hsmul, ← hu, Units.smul_def, hsmul', ← mul_assoc, Units.mul_inv, one_mul]
  · have hmap : ∀ w : Γ(X, X.basicOpen r), w ∈ I.ideal (X.affineBasicOpen r) →
        w ∈ (I.ideal U).map ρ.hom := fun w hw => by rwa [← I.map_ideal_basicOpen] at hw
    have hy := hmap (v y) (eD y).2
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Submonoid.powers r) Γ(X, X.basicOpen r)).mp hy
    refine ⟨(eU.symm a, ⟨r ^ n, n, rfl⟩), hv ?_⟩
    change v ((r ^ n) • y) = _
    rw [hsmul, hres, LinearEquiv.apply_symm_apply, mul_comm]
    exact ha
  · have h' := congrArg v h
    simp only [hres] at h'
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r)
      Γ(X, X.basicOpen r)).mp h'
    refine ⟨c, eU.injective (Subtype.ext ?_)⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, LinearEquiv.map_smul, LinearEquiv.map_smul]
    exact hc

/-- Over an affine open `U`, the restriction of `I.toModules` to `Spec Γ(X, U)` is the sheaf
associated to its global sections: the restrictions to the basic opens are localizations
(`isLocalizedModule_toModules_resₗ`). -/
theorem isIso_fromTildeΓ_toModules {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (I.toModules.restrict hU.fromSpec).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).mpr fun r =>
    (I.toModules.isLocalizedModule_restrict_fromSpec_iff hU r).mpr
      (I.isLocalizedModule_toModules_resₗ ⟨U, hU⟩ r)

end AlgebraicGeometry.Scheme.IdealSheafData
