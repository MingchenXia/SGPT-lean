import SGPT.Projective.WholeCurveZeroArtinian
import SGPT.Projective.OriginalOpenSectionZero

/-! True original section transport through actual original sheaf
isomorphisms and actual original all-component nonzero restrictions.
Blueprint: original-section-iso-transport.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- The SAME actual adjunction unit is natural in the actual original section/sheaf map. -/
theorem originalSectionIso_pullback {X Y : Scheme.{0}} (g : X ⟶ Y) {L N : Y.Modules}
    (e : L ≅ N) (s : Γ(L, ⊤)) :
    originalPulledSection g (e.hom.val.app (.op ⊤) s) =
      ((Scheme.Modules.pullback g).mapIso e).hom.val.app (.op ⊤) (originalPulledSection g s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality e.hom
  exact congr($(h).val.app (.op ⊤) |>.hom s)

/-- The actual inverse original sheaf map preserves ordinary original section nonzero. -/
theorem originalSectionIso_ne_zero {X : Scheme.{0}} {L N : X.Modules}
    (e : L ≅ N) (s : Γ(L, ⊤)) (hs : s ≠ 0) : e.hom.val.app (.op ⊤) s ≠ 0 := by
  intro hzero
  have h := congr($(e.hom_inv_id).val.app (.op ⊤) |>.hom s)
  change e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s at h
  exact hs (h.symm.trans ((congrArg (e.inv.val.app (.op ⊤)) hzero).trans (map_zero _)))

/-- ALL SAME original components retain nonzero ordinary section after actual sheaf isomorphism. -/
theorem originalSectionIso_nonzeroOnComponents {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ))
    (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L N : X.Modules} (e : L ≅ N) (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s) :
    SectionNonzeroOnComponents f E (e.hom.val.app (.op ⊤) s) := by
  intro C hzero
  let U := smoothProjectiveComponentOpen f 1 E C.val C.property
  have hn := originalSectionIso_ne_zero ((Scheme.Modules.pullback U.ι).mapIso e)
    (originalPulledSection U.ι s) (hs C)
  apply hn
  exact (originalSectionIso_pullback U.ι e s).symm.trans hzero

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
