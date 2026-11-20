import SGPT.Projective.OriginalOpenSectionZero
import SGPT.Projective.OriginalProjectiveTwistGeneration
import SGPT.Foundations.Envelope.AlgGeom.SchemeGeneratorFrameNeighborhoods
import SGPT.Foundations.Envelope.Vanishing.NadelBertiniRestrictionCover

/-! Actual original generating sections avoid every original scheme point.
Blueprint: original-generated-point-unit.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace
open SGPT.Foundations.Envelope.SchemeLineSectionEvaluation SGPT.Foundations.Envelope.SchemeGeneratingSectionsUnit
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

variable {X : Scheme.{0}} {L : X.Modules}

/-- The actual inverse section morphism gives one in EVERY original evaluation ideal. -/
theorem originalSectionZeroIdeal_eq_top_of_isIso (a : LineBundleAtlas L)
    (α : Scheme.Modules.unitObj X ⟶ L) [IsIso α] :
    sectionZeroIdealSheaf a (sectionAtOne α) = ⊤ := by
  let s : Γ(L,⊤) := sectionAtOne α
  let β : Γ(bundleDual L,⊤) :=
    (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map (inv α)
  have hβ : sectionZeroEvaluation L s ⊤ β = 1 := by
    change (inv α).val.app (op ⊤) (L.presheaf.map (⊤ : X.Opens).leTop.op s) = (1 : Γ(X,⊤))
    have ht : (⊤ : X.Opens).leTop.op = 𝟙 (op ⊤) := Subsingleton.elim _ _
    rw [ht,L.presheaf.map_id]
    change (inv α).val.app (op ⊤) (α.val.app (op ⊤) (1 : Γ(X,⊤))) = (1 : Γ(X,⊤))
    exact congrArg (fun q => q.val.app (op ⊤) (1 : Γ(X,⊤))) (IsIso.hom_inv_id α)
  apply Scheme.IdealSheafData.ext
  funext U
  change sectionZeroIdeal L s U.val = ⊤
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  refine ⟨(bundleDual L).presheaf.map U.val.leTop.op β,?_⟩
  have hr := sectionZeroEvaluation_restrict L s (show U.val ≤ (⊤ : X.Opens) from le_top) β
  change sectionZeroEvaluation L s U.val ((bundleDual L).presheaf.map U.val.leTop.op β) =
    X.presheaf.map U.val.leTop.op (sectionZeroEvaluation L s ⊤ β) at hr
  rw [hβ,map_one] at hr
  exact hr

/-- The genuine original pullback-unit section has the same actual native Hom reader. -/
theorem originalPulledSection_sectionAtOne {Y : Scheme.{0}} (g : Y ⟶ X)
    (α : Scheme.Modules.unitObj X ⟶ L) :
    originalPulledSection g (sectionAtOne α) = sectionAtOne (pullbackSectionHom g α) := by
  have h := SGPT.Foundations.Envelope.Vanishing.NadelBertiniRestrictionCover.pullback_sectionAtOne g α
  have he : Scheme.Modules.affinePullbackUnitTop g L (sectionAtOne α) =
      originalPulledSection g (sectionAtOne α) := by
    let N := (Scheme.Modules.pullback g).obj L
    change N.presheaf.map (𝟙 (op ⊤)) (originalPulledSection g (sectionAtOne α)) = _
    exact congrArg (fun q => q (originalPulledSection g (sectionAtOne α))) (N.presheaf.map_id (op ⊤))
  exact he.symm.trans h

/-- EVERY original point is avoided by one SAME actual original generator's whole zero support. -/
theorem exists_originalGenerator_avoids_point (a : LineBundleAtlas L)
    (G : L.GeneratingSections) (c : X) :
    ∃ i : G.I, c ∉ (sectionZeroIdealSheaf a (sectionAtOne (generatorHom G i))).support := by
  obtain ⟨U,hcU,i,hi⟩ :=
    SGPT.Foundations.Envelope.SchemeGeneratorFrameNeighborhoods.exists_affine_generator_frame
      (originalAtlas_isInvertible a) G c
  let α := generatorHom G i
  let s : Γ(L,⊤) := sectionAtOne α
  let : IsIso (pullbackSectionHom U.1.ι α) := hi
  have hzero : (sectionZeroIdealSheaf a s).comap U.1.ι = ⊤ := by
    rw [← originalOpenSection_zeroIdeal U.1 a s]
    rw [originalPulledSection_sectionAtOne]
    exact originalSectionZeroIdeal_eq_top_of_isIso (matePullbackAtlas U.1.ι a)
      (pullbackSectionHom U.1.ι α)
  refine ⟨i,?_⟩
  intro hc
  have hlocal : (⟨c,hcU⟩ : U.1.toScheme) ∈ ((sectionZeroIdealSheaf a s).comap U.1.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hc
  rw [hzero] at hlocal
  change False at hlocal
  exact hlocal

/-- A genuine ordinary original section avoiding the prescribed actual scheme point. -/
theorem exists_originalGeneratedSection_avoids_point (a : LineBundleAtlas L)
    (G : L.GeneratingSections) (c : X) :
    ∃ s : Γ(L,⊤), c ∉ (sectionZeroIdealSheaf a s).support := by
  obtain ⟨i,hi⟩ := exists_originalGenerator_avoids_point a G c
  exact ⟨sectionAtOne (generatorHom G i),hi⟩

end SGPT.Projective.NumEq.AlgebraicCurveDegree
