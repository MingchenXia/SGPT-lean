import SGPT.Projective.OriginalOpenSectionEquivalence
import SGPT.Projective.WholeCurveZeroArtinian
import SGPT.Foundations.Envelope.AlgGeom.ClosedProjectiveGlobalGeneration

/-! Actual ordinary generated sections on ALL original clopen components.
Blueprint: original-clopen-generated-section.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open Scheme.Modules
local instance (X : Scheme.{0}) : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X

/-- A genuine nonzero ordinary section is manufactured from actual original invertibility and generation. -/
theorem exists_originalGeneratedSection_ne_zero {X : Scheme.{0}} [Nonempty X]
    (L : X.Modules) (hL : IsInvertible L) (G : L.GeneratingSections) :
    ∃ s : Γ(L, ⊤), s ≠ 0 := by
  classical
  have hgen : ∃ i : G.I, (L.unitHomEquiv.symm (G.s i) : unitObj X ⟶ L) ≠ 0 := by
    by_contra h
    push Not at h
    have hπ : (G.π : (SheafOfModules.free G.I : X.Modules) ⟶ L) = 0 := by
      apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I)
      intro i
      change SheafOfModules.ιFree i ≫ G.π = SheafOfModules.ιFree i ≫ 0
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simpa only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply, comp_zero] using h i
    let : Epi G.π := G.epi
    have hz : IsZero L := IsZero.of_epi_eq_zero G.π hπ
    let F := tensorRight (dualObj L)
    let : F.Full := hL.dual.tensorRightFullyFaithful.full
    have hT : IsZero (L ⊗ dualObj L) := F.map_isZero hz
    let e : L ⊗ dualObj L ≅ unitObj X :=
      hL.monoidalEvaluationIso ≪≫ SGPT.Support.ModularCurves.monoidalUnitObjIso X
    have hO : IsZero (unitObj X) := hT.of_iso e.symm
    have hid : (𝟙 (unitObj X)) = 0 := hO.eq_of_src _ _
    have ht := congrArg (fun q : unitObj X ⟶ unitObj X =>
      q.val.app (op ⊤) (1 : Γ(X, ⊤))) hid
    have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
    exact one_ne_zero (show (1 : Γ(X, ⊤)) = 0 from ht)
  obtain ⟨i, hi⟩ := hgen
  let α : unitObj X ⟶ L := L.unitHomEquiv.symm (G.s i)
  refine ⟨α.val.app (op ⊤) (1 : Γ(X, ⊤)), ?_⟩
  intro hz
  apply hi
  apply L.unitHomEquiv.injective
  ext V
  have hn := PresheafOfModules.naturality_apply α.val
    (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))
  change α.val.app V (1 : Γ(X, V.unop)) = 0
  change α.val.app V (X.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op 1) =
    L.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
      (α.val.app (op ⊤) (1 : Γ(X, ⊤))) at hn
  simpa only [map_one, hz, map_zero] using hn

/-- Actual original whole generated line has an ordinary section nonzero on EVERY original component. -/
theorem exists_originalGeneratedSection_nonzeroOnComponents
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    (L : X.Modules) (hL : IsInvertible L) (G : L.GeneratingSections) :
    ∃ s : Γ(L, ⊤), SectionNonzeroOnComponents f E s := by
  classical
  let U (C : ↥(irreducibleComponents X)) : X.Opens :=
    smoothProjectiveComponentOpen f 1 E C.val C.property
  have hc (C : ↥(irreducibleComponents X)) :
      ∃ s : Γ((Scheme.Modules.pullback (U C).ι).obj L, ⊤), s ≠ 0 := by
    let := smoothProjective_component_isIntegral f 1 E C.val C.property
    exact exists_originalGeneratedSection_ne_zero _ (hL.pullback (U C).ι)
      (SGPT.Foundations.Envelope.ClosedProjectiveGlobalGeneration.pullback_generatingSections (U C).ι G)
  choose s hs using hc
  let v (C : ↥(irreducibleComponents X)) : Γ(L, U C) := (originalOpenSectionEquiv (U C)).symm (s C)
  let S : TopCat.Sheaf AddCommGrpCat X := ⟨L.presheaf, L.isSheaf⟩
  have hv : ∀ C D, S.obj.map (Opens.infLELeft (U C) (U D)).op (v C) =
      S.obj.map (Opens.infLERight (U C) (U D)).op (v D) := by
    intro C D
    by_cases hCD : C = D
    · subst D; rfl
    · apply TopCat.Presheaf.IsSheaf.section_ext (F := L.presheaf) L.isSheaf
      intro x hx
      have hne : C.val ≠ D.val := fun h => hCD (Subtype.ext h)
      exact False.elim (Set.disjoint_left.mp
        (smoothScheme_components_pairwiseDisjoint f 1 C.property D.property hne) hx.1 hx.2)
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f 1 E x
    exact Opens.mem_iSup.mpr ⟨C, hC⟩
  obtain ⟨t, ht, _⟩ := S.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover v hv
  refine ⟨t, fun C => ?_⟩
  change originalPulledSection (U C).ι t ≠ 0
  have htC : L.presheaf.map (U C).leTop.op t = v C := ht C
  have he : originalPulledSection (U C).ι t = s C :=
    (originalOpenSectionEquiv_restrict (U C) t).symm.trans
      ((congrArg (originalOpenSectionEquiv (U C)) htC).trans
        ((originalOpenSectionEquiv (U C)).apply_symm_apply (s C)))
  exact he ▸ hs C

end SGPT.Projective.NumEq.AlgebraicCurveDegree
