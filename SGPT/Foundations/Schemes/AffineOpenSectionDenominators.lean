import SGPT.Foundations.Schemes.AffineChartSectionExtension

/-! Actual denominator clearing on arbitrary affine opens, retaining original
scalar and section restriction maps through the canonical affine chart. -/

universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme.{u}} {L : X.Modules}

theorem affineOpenChartScalars_apply {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    affineOpenChartScalars hU r = r := by
  let c := hU.fromSpec
  let h : c ''ᵁ ⊤ = U :=
    c.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have he : X.presheaf.map (eqToHom h).op ≫ (c.appIso ⊤).hom =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appIso_hom, c.naturality_assoc]
    rw [hU.fromSpec_app_self]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp]
    trans (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map (𝟙 (op (⊤ : (Spec Γ(X, U)).Opens)))
    · congr 2
    · rw [(Spec Γ(X, U)).presheaf.map_id, Category.comp_id]
  change X.presheaf.map (eqToHom h.symm).op
    ((c.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv r)) = r
  have hr := congrArg (fun f : Γ(X, U) ⟶ Γ(Spec Γ(X, U), ⊤) ↦ f r) he
  rw [← hr]
  simp [← Functor.map_comp_apply]

/-- Denominator clearing uses the actual sections and scalar restrictions on
an arbitrary affine open, without choosing a frame there. -/
theorem affineOpenSection_clearDenominator (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let c := hU.fromSpec
  let D : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen f
  let hi : c ''ᵁ ⊤ = U :=
    c.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let hj : c ''ᵁ D = X.basicOpen f := hU.fromSpec_image_basicOpen f
  let eT : Γ(M.restrict c, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso c ⊤ ≪≫ M.presheaf.mapIso (eqToIso hi.symm).op
  let eD : Γ(M.restrict c, D) ≅ Γ(M, X.basicOpen f) :=
    M.restrictAppIso c D ≪≫ M.presheaf.mapIso (eqToIso hj.symm).op
  have hnat : (M.restrict c).presheaf.map D.leTop.op ≫ eD.hom =
      eT.hom ≫ M.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
    dsimp [eD, eT]
    rw [Scheme.Modules.map_restrictAppIso_hom_assoc]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 2
  have hscalar (r : Γ(X, U)) :
      X.presheaf.map (eqToHom hj.symm).op
        ((c.appIso D).inv ((Spec Γ(X, U)).presheaf.map D.leTop.op
          ((Scheme.ΓSpecIso Γ(X, U)).inv r))) =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op r := by
    have hc := c.appIso_inv_naturality D.leTop.op
    have hc' := congrArg (fun g : Γ(Spec Γ(X, U), ⊤) ⟶ Γ(X, c ''ᵁ D) ↦
      g ((Scheme.ΓSpecIso Γ(X, U)).inv r)) hc
    simp only [ConcreteCategory.comp_apply] at hc'
    rw [hc']
    have ha := affineOpenChartScalars_apply hU r
    change X.presheaf.map (eqToHom hi.symm).op
      ((c.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv r)) = r at ha
    conv_rhs => rw [← ha]
    simp only [← Functor.map_comp_apply]
    congr 2
  obtain ⟨n, t, ht⟩ := affineSection_clearDenominator (M.restrict c) f (eD.inv s)
  refine ⟨n, eT.hom t, ?_⟩
  have he := congrArg (fun z ↦ eD.hom z) ht
  change eD.hom ((M.restrict c).presheaf.map D.leTop.op t) = _ at he
  rw [← ConcreteCategory.comp_apply, hnat, ConcreteCategory.comp_apply] at he
  rw [he]
  change M.presheaf.map (eqToHom hj.symm).op
    ((M.restrictAppIso c D).hom (f ^ n • eD.inv s)) = _
  rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.smul_restrictAppIso_hom_apply,
    M.map_smul, hscalar, map_pow]
  change _ • eD.hom (eD.inv s) = _
  rw [Iso.inv_hom_id_apply]

end
end SGPT.Foundations.Schemes
