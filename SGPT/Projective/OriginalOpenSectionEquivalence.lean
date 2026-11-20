import SGPT.Projective.OriginalOpenSectionZero

/-! Actual original open-section/pullback equivalence.
Blueprint: original-open-section-equivalence.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite
variable {X : Scheme.{0}} {L : X.Modules}

/-- Actual original section equivalence on every original open, including the empty open. -/
def originalOpenSectionEquiv (U : X.Opens) :
    Γ(L, U) ≃+ Γ((Scheme.Modules.pullback U.ι).obj L, ⊤) :=
  ((L.presheaf.mapIso (eqToIso U.ι_image_top).op) ≪≫
    (L.restrictAppIso U.ι ⊤).symm ≪≫
    ((Scheme.Modules.toPresheaf U.toScheme).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L)).app (op ⊤)).addCommGroupIsoToAddEquiv

/-- This equivalence reads the SAME original global section via its genuine adjunction unit. -/
theorem originalOpenSectionEquiv_restrict (U : X.Opens) (s : Γ(L, ⊤)) :
    originalOpenSectionEquiv U (L.presheaf.map U.leTop.op s) = originalPulledSection U.ι s := by
  have h := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι) (Scheme.Modules.pullbackPushforwardAdjunction U.ι) L
  have hs := congrArg (fun q : L ⟶ (Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj L) => q.val.app (.op ⊤) s) h
  have hr : L.presheaf.map (eqToHom U.ι_image_top).op (L.presheaf.map U.leTop.op s) =
      L.presheaf.map (U.ι ''ᵁ (⊤ : U.toScheme.Opens)).leTop.op s := by
    rw [← L.presheaf.map_comp_apply]
    rfl
  change (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).hom.val.app (op ⊤))
    (L.presheaf.map (eqToHom U.ι_image_top).op (L.presheaf.map U.leTop.op s)) = _
  rw [hr]
  exact hs

end SGPT.Projective.NumEq.AlgebraicCurveDegree
