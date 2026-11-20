/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license; see LICENSES/derived-algebraic-geometry.md.
Adapted from chris-dare-dev/derived-alg-geo-lean commit
 ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788:
 DerivedAlgGeo/AlgebraicGeometry/Modules/Pushforward/BaseChange.lean lines 80–233,
 and Modules/Restriction/Sections.lean lines 64–73.
-/
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Actual module pushforward and restriction across an open square

The comparison transports genuine sections along the equality of actual opens.
Its linearity follows from the native restricted structural maps, with no
finiteness, coherence, or affine hypothesis.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace SGPT.Foundations.Schemes

noncomputable section

theorem modulePresheaf_map_square_eq {X : Scheme.{u}} (M : X.Modules) {A B C D : X.Opens}
    (α : op A ⟶ op B) (β : op B ⟶ op C) (γ : op A ⟶ op D) (δ : op D ⟶ op C) (x : Γ(M, A)) :
    (M.presheaf.map β).hom ((M.presheaf.map α).hom x)
      = (M.presheaf.map δ).hom ((M.presheaf.map γ).hom x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  exact congrArg (fun φ => (M.presheaf.map φ).hom x) (Subsingleton.elim _ _)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **The restriction square commutes on opens.** Going round by `U.ι` and then taking the
preimage under `f` is going round by `f ∣_ U` and then taking the image in `X`.

This is `image_morphismRestrict_preimage` packaged as an isomorphism of the two composite
functors `Opens U ⥤ Opens X`, which is the form the base-change comparison of pushforwards
consumes. -/
noncomputable def restrictSquareOpensIso :
    U.ι.opensFunctor ⋙ Opens.map f.base ≅
      Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor :=
  NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V).symm)


section Modules

variable (M : X.Modules)

/-- **The transport of sections across the restriction square.**

Both ways round the square have the same sections over `V` — `Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))` one way and
`Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))` the other, each `rfl`-equal to the composite — so the
comparison is the transport along `image_morphismRestrict_preimage`. -/
noncomputable def restrictSquareSections (V : U.toScheme.Opens) :
    Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) ⟶ Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) :=
  M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op

/-- The transport the other way. -/
noncomputable def restrictSquareSectionsInv (V : U.toScheme.Opens) :
    Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ⟶ Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) :=
  M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op

@[simp]
theorem restrictSquareSectionsInv_restrictSquareSections (V : U.toScheme.Opens)
    (x : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))) :
    (restrictSquareSectionsInv f U M V).hom ((restrictSquareSections f U M V).hom x) = x := by
  show (M.presheaf.map _ ≫ M.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem restrictSquareSections_restrictSquareSectionsInv (V : U.toScheme.Opens)
    (x : Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))) :
    (restrictSquareSections f U M V).hom ((restrictSquareSectionsInv f U M V).hom x) = x := by
  show (M.presheaf.map _ ≫ M.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The transport is linear**, which is the whole content of the module-level comparison.

Each side's action unfolds by `rfl` to an action through `Scheme.Hom.app`; `Scheme.Opens.ι_appIso`
removes the open immersion's `appIso`, which is the one step that is not definitional; and
`morphismRestrict_app` says the two structure-sheaf maps differ by exactly the transport being
compared. -/
theorem restrictSquareSections_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (x : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V)) :
    (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) from
        (restrictSquareSections f U M V).hom (r • x))
      = r • (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) from
        (restrictSquareSections f U M V).hom x) := by
  have hL : (r • x : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V))
      = (show Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) from
          (f.app (U.ι ''ᵁ V)).hom ((Scheme.Hom.appIso U.ι V).inv.hom r)) •
        (show Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) from x) := rfl
  have hR : (r • (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj
        (M.restrict (f ⁻¹ᵁ U).ι), V) from (restrictSquareSections f U M V).hom x))
      = (show Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
          (Scheme.Hom.appIso (f ⁻¹ᵁ U).ι ((f ∣_ U) ⁻¹ᵁ V)).inv.hom
            (((f ∣_ U).app V).hom r)) •
        (show Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
          (restrictSquareSections f U M V).hom x) := rfl
  have hι : (Scheme.Hom.appIso U.ι V).inv.hom r = (show Γ(Y, U.ι ''ᵁ V) from r) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have hmr := congrArg (fun φ : Γ(U.toScheme, V) ⟶ Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) =>
    φ.hom r) (morphismRestrict_app f U V)
  have hι' : (Scheme.Hom.appIso (f ⁻¹ᵁ U).ι ((f ∣_ U) ⁻¹ᵁ V)).inv.hom (((f ∣_ U).app V).hom r)
      = (show Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from ((f ∣_ U).app V).hom r) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  refine (congrArg (fun y : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) =>
    (restrictSquareSections f U M V).hom y) hL).trans ?_
  refine (Scheme.Modules.map_smul M _ _ _).trans ?_
  refine Eq.symm (hR.trans ?_)
  refine congrArg (fun s : Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) =>
    s • (show Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
      (restrictSquareSections f U M V).hom x)) ?_
  refine hι'.trans (hmr.trans ?_)
  exact congrArg (fun s : Γ(Y, U.ι ''ᵁ V) =>
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op).hom
      ((f.app (U.ι ''ᵁ V)).hom s)) hι.symm

/-- **The comparison on sections over one open, as a linear equivalence.**

Named at the `Γ` spelling: written through the unfolded pushforward the `Module` instance does not
synthesize, which is `references/instance-transparency.md` technique 5 in its usual form. -/
noncomputable def restrictSquareSectionsEquiv (V : U.toScheme.Opens) :
    Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V) ≃ₗ[Γ(U.toScheme, V)]
      Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) where
  toFun x := (restrictSquareSections f U M V).hom x
  map_add' x y := map_add _ x y
  map_smul' r x := restrictSquareSections_smul f U M V r x
  invFun x := (restrictSquareSectionsInv f U M V).hom x
  left_inv x := restrictSquareSectionsInv_restrictSquareSections f U M V x
  right_inv x := restrictSquareSections_restrictSquareSectionsInv f U M V x

/-- **The open-square comparison, object by object.**

Pushing forward along `f` and then restricting to `U` is restricting to `f ⁻¹ᵁ U` and then pushing
forward along `f ∣_ U`. The coherent-pushforward chart argument uses this
objectwise isomorphism to transport finite presentation.

The component on every open is `restrictSquareSections`, transporting along
`image_morphismRestrict_preimage`. -/
noncomputable def pushforwardRestrictIso :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => (restrictSquareSectionsEquiv f U M V.unop).toModuleIso)
      (fun {V W} i => by
        ext x
        exact modulePresheaf_map_square_eq M
          ((Opens.map f.base).map (U.ι.opensFunctor.map i.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
          ((f ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (f ∣_ U).base).map i.unop)).op x))

end Modules

/-- The independent comparison of pushforward and restriction around an open square.
Its component at `M` is `pushforwardRestrictIso f U M`, whose map on sections is
`restrictSquareSections f U M`. -/
noncomputable def pushforwardRestrictNatIso :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (f ∣_ U) :=
  NatIso.ofComponents (pushforwardRestrictIso f U) (fun {M N} g ↦ by
    apply Scheme.Modules.hom_ext
    intro W
    ext x
    exact (NatTrans.naturality_apply g.mapPresheaf
      (eqToHom (image_morphismRestrict_preimage f U W)).op x).symm)


end

end SGPT.Foundations.Schemes
