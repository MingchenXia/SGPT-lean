/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license; see LICENSES/derived-algebraic-geometry.md.
The restriction equivalence and isomorphism pushforward comparison are adapted
from derived-alg-geo-lean commit ef2cfbb0060bf98dae0a45f3ad1eecff9ee46788,
DerivedAlgGeo/AlgebraicGeometry/Modules/Pushforward/Iso.lean.
-/
import SGPT.Foundations.Schemes.ModulePushforwardRestriction
import SGPT.Foundations.Schemes.NativeClosedPushforwardSections

/-! # Native affine pushforward quasicoherence

Isomorphism transport and the genuine affine spectral pushforward comparison
produce actual quasicoherence on arbitrary affine schemes.
-/

universe u

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace SGPT.Foundations.Schemes

noncomputable section

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- **Restriction along an isomorphism, as an equivalence of module categories.**

Built with `CategoryTheory.Equivalence.mk` rather than by giving the structure's fields: that
constructor adjointifies the unit, so the triangle identity is discharged for us. See the module
docstring — both halves of that sentence cost time to learn. -/
noncomputable def restrictEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.inv) (restrictFunctor e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫
      restrictFunctorCongr (by simp) ≪≫ restrictFunctorId).symm
    ((restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr (by simp) ≪≫ restrictFunctorId)

/-- **Pushforward along an isomorphism is restriction along its inverse.**

Both are right adjoint to `restrictFunctor e.hom` — the first by `restrictAdjunction`, the second
because `restrictEquiv` makes it half of an equivalence — and right adjoints are unique. -/
noncomputable def pushforwardIsoRestrict :
    pushforward e.hom ≅ restrictFunctor e.inv :=
  (restrictAdjunction e.hom).rightAdjointUniq (restrictEquiv e).symm.toAdjunction


/-- Actual native quasicoherence transports under a genuine scheme isomorphism. -/
theorem isoPushforward_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward e.hom).obj M).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict e).app M).symm
    (inferInstance : (M.restrict e.inv).IsQuasicoherent)

/-- Actual affine morphisms between actual affine schemes preserve native quasicoherence. -/
theorem affineSchemePushforward_isQuasicoherent {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let ex := X.isoSpec
  let ey := Y.isoSpec
  let N := (pushforward ex.hom).obj M
  let : N.IsQuasicoherent := isoPushforward_isQuasicoherent ex M
  let := specPushforward_isQuasicoherent f.appTop N
  let P := (pushforward ey.inv).obj ((pushforward (Spec.map f.appTop)).obj N)
  let : P.IsQuasicoherent :=
    isoPushforward_isQuasicoherent ey.symm ((pushforward (Spec.map f.appTop)).obj N)
  have h : (ex.hom ≫ Spec.map f.appTop) ≫ ey.inv = f := by
    change (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let α : P ≅ (pushforward f).obj M :=
    (pushforward ey.inv).mapIso ((pushforwardComp ex.hom (Spec.map f.appTop)).app M) ≪≫
      (pushforwardComp (ex.hom ≫ Spec.map f.appTop) ey.inv).app M ≪≫
      (pushforwardCongr h).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso α
    (inferInstance : P.IsQuasicoherent)

end

end SGPT.Foundations.Schemes
