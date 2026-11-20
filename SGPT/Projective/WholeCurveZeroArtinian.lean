import SGPT.Projective.OriginalOpenSectionZero
import SGPT.Projective.OriginalZeroComponentLengths
import SGPT.Projective.AlgebraicCurveZeroArtinian
import SGPT.Projective.ArtinianSchemeIsoLength

/-! ENTIRE actual original smooth projective curve, all components retained:
componentwise ordinary nonzero section produces true original Artinian zero scheme.
Blueprint: whole-curve-zero-artinian.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped BigOperators
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (s : Γ(L, ⊤))

/-- SAME actual original ordinary section, pulled onto EACH actual whole original component. -/
def originalCurveComponentSection (C : ↥(irreducibleComponents X)) :
    Γ((Scheme.Modules.pullback (smoothProjectiveComponentOpen f 1 E C.val C.property).ι).obj L, ⊤) :=
  originalPulledSection (smoothProjectiveComponentOpen f 1 E C.val C.property).ι s

/-- The actual ordinary restricted section is nonzero on EACH original component. -/
def SectionNonzeroOnComponents : Prop :=
  ∀ C : ↥(irreducibleComponents X), originalCurveComponentSection f E s C ≠ 0

/-- EACH actual original whole component zero scheme is genuinely Artinian. -/
theorem curveComponentZero_isArtinian (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) :
    IsArtinianScheme (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C)) := by
  let := smoothProjective_component_isIntegral f 1 E C.val C.property
  let := smoothProjective_component_smoothDimension f 1 E C.val C.property
  exact sectionZero_isArtinian ((smoothProjectiveComponentOpen f 1 E C.val C.property).ι ≫ f)
    (smoothProjective_componentEmbedding f 1 E C.val C.property) _ _ (hs C)

/-- ACTUAL original inverse-image component zero open inherits local Artinianness by TRUE scheme iso. -/
theorem curveZeroComponent_isLocallyArtinian (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) :
    IsLocallyArtinian (originalZeroComponentOpen f 1 E a s C) := by
  let : IsArtinianScheme (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalPulledSection (smoothProjectiveComponentOpen f 1 E C.val C.property).ι s)) :=
    curveComponentZero_isArtinian f E a s hs C
  exact IsLocallyArtinian.of_isImmersion
    (originalOpenSection_zeroSchemeIso (smoothProjectiveComponentOpen f 1 E C.val C.property) a s).inv

/-- ENTIRE original zero scheme is genuinely Artinian, ALL actual components/empty curve retained. -/
theorem wholeCurveSectionZero_isArtinian (hs : SectionNonzeroOnComponents f E s) :
    IsArtinianScheme (sectionZeroSubscheme a s) := by
  let Z := sectionZeroSubscheme a s
  let := (E.sectionZero a s).isNoetherian
  let O : ↥(irreducibleComponents X) → Z.Opens := originalZeroComponentOpen f 1 E a s
  have hcover : IsOpenCover O := by
    apply top_unique
    intro z _
    obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f 1 E (sectionZeroι a s z)
    exact Opens.mem_iSup.mpr ⟨C, hC⟩
  let V := Z.openCoverOfIsOpenCover O hcover
  have hlocal (C : ↥(irreducibleComponents X)) : IsLocallyArtinian (V.X C) :=
    curveZeroComponent_isLocallyArtinian f E a s hs C
  have hz : IsLocallyArtinian Z := (isLocallyArtinian_iff_openCover V).mpr hlocal
  exact { toIsLocallyArtinian := hz, toCompactSpace := inferInstance }

/-- EVERY actual original inverse-image component zero OPEN is Artinian, with all its points. -/
theorem wholeCurveZeroComponent_isArtinian (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) : IsArtinianScheme (originalZeroComponentOpen f 1 E a s C) := by
  let := wholeCurveSectionZero_isArtinian f E a s hs
  let : Finite (originalZeroComponentOpen f 1 E a s C) := Finite.of_injective
    (fun z : originalZeroComponentOpen f 1 E a s C => z.val) Subtype.val_injective
  exact { toIsLocallyArtinian := inferInstance, toCompactSpace := inferInstance }

/-- SAME original component-zero full-length sum equals ACTUAL restricted-section zero full-length sum. -/
theorem wholeCurveZeroComponent_fullLength_sum (hs : SectionNonzeroOnComponents f E s)
    (C : ↥(irreducibleComponents X)) :
    let := wholeCurveSectionZero_isArtinian f E a s hs
    let := curveComponentZero_isArtinian f E a s hs C
    let := wholeCurveZeroComponent_isArtinian f E a s hs C
    let : Fintype (originalZeroComponentOpen f 1 E a s C) := Fintype.ofFinite _
    let : Fintype (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalCurveComponentSection f E s C)) := Fintype.ofFinite _
    (∑ z : originalZeroComponentOpen f 1 E a s C,
      Module.length ((originalZeroComponentOpen f 1 E a s C).toScheme.presheaf.stalk z)
        ((originalZeroComponentOpen f 1 E a s C).toScheme.presheaf.stalk z)) =
      ∑ z : sectionZeroSubscheme
        (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
        (originalCurveComponentSection f E s C),
        Module.length ((sectionZeroSubscheme
          (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
          (originalCurveComponentSection f E s C)).presheaf.stalk z)
          ((sectionZeroSubscheme
          (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
          (originalCurveComponentSection f E s C)).presheaf.stalk z) := by
  let := wholeCurveSectionZero_isArtinian f E a s hs
  let : IsArtinianScheme (sectionZeroSubscheme
      (matePullbackAtlas (smoothProjectiveComponentOpen f 1 E C.val C.property).ι a)
      (originalPulledSection (smoothProjectiveComponentOpen f 1 E C.val C.property).ι s)) :=
    curveComponentZero_isArtinian f E a s hs C
  let : IsArtinianScheme (sectionZeroι a s ⁻¹ᵁ smoothProjectiveComponentOpen f 1 E C.val C.property) :=
    wholeCurveZeroComponent_isArtinian f E a s hs C
  exact (artinian_selfLength_sum_eq_of_iso
    (originalOpenSection_zeroSchemeIso (smoothProjectiveComponentOpen f 1 E C.val C.property) a s)).symm

end SGPT.Projective.NumEq.AlgebraicCurveDegree
