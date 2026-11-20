import SGPT.Foundations.Schemes.PolynomialProjectiveCanonical

/-! Native sheaf frames on open schemes and their literal over-site coefficients. -/
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
variable {X : Scheme} {L : X.Modules} (U : X.Opens)
/-- A genuine open-scheme frame transports to the actual over-site by the native equivalence. -/
def nativeFrameFromRestricted (E : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    LocalBundleFrame L U :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app L ≪≫ E)
/-- The transport retains the actual restricted sheaf morphism. -/
theorem nativeFrameFromRestricted_map
    (E : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (Scheme.Modules.overEquiv U).functor.map (nativeFrameFromRestricted U E).hom =
      ((Scheme.Modules.overFunctorEquiv U).app L ≪≫ E).hom :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage _
/-- This native full-faithful transport equals the actual unit/inverse-unit construction. -/
theorem nativeFrameFromRestricted_eq
    (E : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    nativeFrameFromRestricted U E =
      (Scheme.Modules.overEquiv U).unitIso.app (L.over U) ≪≫
        (Scheme.Modules.overEquiv U).inverse.mapIso
          ((Scheme.Modules.overFunctorEquiv U).app L ≪≫ E) ≪≫
            U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf := by
  apply Iso.ext
  simp only [nativeFrameFromRestricted, Functor.FullyFaithful.preimageIso_hom,
    Equivalence.fullyFaithfulFunctor, Iso.trans_hom,
    TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit,
    TopologicalSpace.Opens.sheafOfModulesEquivOverUnit, Iso.symm_hom,
    Functor.mapIso_hom, Iso.refl_inv]
  have h : (U.sheafOfModulesEquivOver X.ringCatSheaf).inverse.map
      (𝟙 ((U.sheafOfModulesEquivOver X.ringCatSheaf).functor.obj
        (SheafOfModules.unit (X.ringCatSheaf.over U)))) = 𝟙 _ :=
    (U.sheafOfModulesEquivOver X.ringCatSheaf).inverse.map_id _
  rw [h]
  exact (congrArg (fun t ↦
    (Scheme.Modules.overEquiv U).unitIso.hom.app (L.over U) ≫
      (Scheme.Modules.overEquiv U).inverse.map
        (((Scheme.Modules.overFunctorEquiv U).app L).hom ≫ E.hom) ≫ t)
    (Category.id_comp ((U.sheafOfModulesEquivOver X.ringCatSheaf).unitIso.app
      (SheafOfModules.unit (X.ringCatSheaf.over U))).inv)).symm

/-- The actual restricted-frame component is the original over-site coefficient. -/
theorem nativeFrameFromRestricted_coefficients
    (E : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : U.toScheme.Opens)
    (s : bundleSections L ((U.overEquivalence.inverse.obj V).left)) :
    (nativeFrameFromRestricted U E).coefficients (U.overEquivalence.inverse.obj V).hom s =
      E.hom.val.app (.op V) s := by
  have h := congr($(nativeFrameFromRestricted_map U E).val.app (.op V) |>.hom s)
  exact h

/-- Genuine affine coordinate pullback on every chart open is its actual top restriction. -/
theorem affineCoordinateMap_openImmersion_hom {A : CommRingCat} {Y : Scheme}
    (e : Y ⟶ Spec A) [IsOpenImmersion e] (V : Y.Opens) :
    affineCoordinateMap A (.op (e.opensFunctor.obj V)) ≫ (e.appIso V).hom =
      (Scheme.ΓSpecIso A).inv ≫ e.appTop ≫ Y.presheaf.map V.leTop.op := by
  rw [affineCoordinateMap, Scheme.Hom.appIso_hom', Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.Hom.appLE_map e (show ⊤ ≤ e ⁻¹ᵁ ⊤ by simp) V.leTop.op]
  simp only [Scheme.Hom.appLE, Opens.map_top, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The actual image of the entire open subscheme is the original open. -/
theorem nativeOpenTop_left :
    (U.overEquivalence.inverse.obj (⊤ : U.toScheme.Opens)).left = U := by
  ext x
  simp [Opens.overEquivalence]

/-- A genuine restricted-frame normalization gives the actual over-site
normalization, using the native equivalence and true isomorphic restriction. -/
theorem nativeFrameFromRestricted_top_normalization
    (E : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (s : bundleSections L U)
    (h : E.hom.val.app (.op ⊤)
      (L.val.map (eqToHom (nativeOpenTop_left U)).op s) =
        (1 : Γ(U.toScheme, ⊤))) :
    (nativeFrameFromRestricted U E).coefficients (𝟙 U) s = 1 := by
  let W := U.overEquivalence.inverse.obj (⊤ : U.toScheme.Opens)
  let j : W.left ⟶ U := eqToHom (nativeOpenTop_left U)
  have hj : j ≫ 𝟙 U = W.hom := Subsingleton.elim _ _
  have hr := LocalBundleFrame.coefficients_restrict (nativeFrameFromRestricted U E) (𝟙 U) j s
  rw [hj] at hr
  have ht := nativeFrameFromRestricted_coefficients U E ⊤ (L.val.map j.op s)
  have hOne : X.sheaf.obj.map j.op ((nativeFrameFromRestricted U E).coefficients (𝟙 U) s) = 1 :=
    hr.symm.trans (ht.trans h)
  have : IsIso j := inferInstanceAs (IsIso (eqToHom (nativeOpenTop_left U)))
  apply (ConcreteCategory.bijective_of_isIso (X.sheaf.obj.map j.op)).injective
  exact hOne.trans (map_one (X.sheaf.obj.map j.op).hom).symm
end
end SGPT.Foundations.Schemes
