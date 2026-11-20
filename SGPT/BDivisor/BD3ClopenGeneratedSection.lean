import SGPT.Projective.OriginalOpenSectionEquivalence
import SGPT.Projective.WholeCurveZeroArtinian
import SGPT.Foundations.Schemes.NativeLinePullbackFrames

/-!
# generated sections on all clopen components, without the earlier envelope formalization

Source: `rmk:bdiv:L749` (chapter_bdiv.tex, line 749), comparison of the book's intersection
numbers with the algebraic (Snapper–Kleiman) numbers of Dang–Favre.  This file is the EP-free
replacement of the only the earlier envelope formalization dependency of the complete-intersection cut chain
(`SGPT.Projective.OriginalMixedEulerCut` → `…WholeTower` → `…ChernPeriod` → `…Diagonal`):
the module `SGPT.Projective.OriginalClopenGeneratedSection` imported
the earlier projective global-generation interface (and, through it, the vendored
`ModularCurves` Picard API: `Scheme.Modules.IsInvertible`, duals, `pullbackUnitIso`).

* `pullbackGeneratingSections`: generating sections pull back along every morphism of schemes
  (restatement of the pullback theorem for generating sections;
  proof: Mathlib's `GeneratingSections.map` for the colimit-preserving left adjoint
  `Scheme.Modules.pullback f` and the structure-sheaf isomorphism
  `SGPT.Foundations.Schemes.nativeSchemePullbackUnitIso`, which uses that `Opens.map f.base` is final).
* `not_isZero_restrict_of_atlas`: a sheaf with a rank-one atlas (`SGPT.Foundations.Schemes.LineBundleAtlas`)
  restricts to a nonzero module on every nonempty open (replaces the `IsInvertible`/dual argument).
* `exists_generatedSection_ne_zero`, `exists_generatedSection_nonzeroOnComponents`: the two
  statements of `OriginalClopenGeneratedSection`, with the invertibility hypothesis replaced by the
  native atlas actually available at the call site (`OriginalSerreCurveSections`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace SGPT.BDivisor.BD3

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace Opposite
open SGPT.Projective.NumEq.AlgebraicCurveDegree

/-- Generating sections pull back along an arbitrary morphism of schemes, with the same index set
(EP-free restatement of `ClosedProjectiveGlobalGeneration.pullback_generatingSections`). -/
def pullbackGeneratingSections {X Y : Scheme.{u}} (f : X ⟶ Y) {N : Y.Modules}
    (G : N.GeneratingSections) : ((Scheme.Modules.pullback f).obj N).GeneratingSections := by
  let : PreservesColimitsOfSize.{u, u} (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  exact G.map (Scheme.Modules.pullback f) (nativeSchemePullbackUnitIso f).symm

/-- The pulled-back family has the same (finite) index set. -/
theorem pullbackGeneratingSections_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N : Y.Modules} (G : N.GeneratingSections) [G.IsFiniteType] :
    (pullbackGeneratingSections f G).IsFiniteType := by
  unfold pullbackGeneratingSections
  infer_instance

/-- Every section of a zero module vanishes. -/
theorem section_eq_zero_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M)
    (U : X.Opens) (t : Γ(M, U)) : t = 0 := by
  have h : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
  have := congrArg (fun φ : M ⟶ M => φ.val.app (op U) t) h
  exact this

/-- A sheaf with a native rank-one atlas has nonzero restriction to every nonempty open. -/
theorem not_isZero_restrict_of_atlas {X : Scheme.{u}} {L : X.Modules} (a : LineBundleAtlas L)
    (U : X.Opens) (x : X) (hx : x ∈ U) : ¬ IsZero (L.restrict U.ι) := by
  intro hZ
  obtain ⟨j, hj⟩ := a.covers x
  let W := a.opens j
  have h1 : ∀ t : Γ(L, U ⊓ W), t = 0 := by
    have h : ∀ t : Γ(L, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)), t = 0 :=
      fun t => section_eq_zero_of_isZero hZ (U.ι ⁻¹ᵁ W) t
    have hUW : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = U ⊓ W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [hUW] at h
    exact h
  let V : W.toScheme.Opens := W.ι ⁻¹ᵁ U
  have h2 : ∀ t : Γ(L.restrict W.ι, V), t = 0 := by
    have hWU : W.ι ''ᵁ V = U ⊓ W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    intro t
    have h' : ∀ t : Γ(L, W.ι ''ᵁ V), t = 0 := by
      rw [hWU]
      exact h1
    exact h' t
  have hV : Nonempty V := ⟨⟨⟨x, hj⟩, by
    change W.ι ⟨x, hj⟩ ∈ U
    simpa using hx⟩⟩
  let e := (a.frame j).nativeRestriction
  have hu : e.inv.val.app (op V) (1 : Γ(W.toScheme, V)) = 0 := h2 _
  have h3 : (e.inv ≫ e.hom).val.app (op V) (1 : Γ(W.toScheme, V)) =
      ((1 : Γ(W.toScheme, V)) : Γ(W.toScheme, V)) := by
    rw [e.inv_hom_id]
    rfl
  change e.hom.val.app (op V) (e.inv.val.app (op V) (1 : Γ(W.toScheme, V))) =
    ((1 : Γ(W.toScheme, V)) : Γ(W.toScheme, V)) at h3
  rw [hu, map_zero] at h3
  exact (zero_ne_one (α := Γ(W.toScheme, V))) h3

/-- The pull-back to an open subscheme of a sheaf with a native atlas is nonzero when the open is
nonempty. -/
theorem not_isZero_pullback_of_atlas {X : Scheme.{u}} {L : X.Modules} (a : LineBundleAtlas L)
    (U : X.Opens) (x : X) (hx : x ∈ U) : ¬ IsZero ((Scheme.Modules.pullback U.ι).obj L) :=
  fun h => not_isZero_restrict_of_atlas a U x hx
    (h.of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L))

/-- A nonzero module with generating sections has a nonzero global section. -/
theorem exists_generatedSection_ne_zero {X : Scheme.{0}} [Nonempty X]
    (M : X.Modules) (hM : ¬ IsZero M) (G : M.GeneratingSections) :
    ∃ s : Γ(M, ⊤), s ≠ 0 := by
  classical
  have hgen : ∃ i : G.I,
      (M.unitHomEquiv.symm (G.s i) : SheafOfModules.unit X.ringCatSheaf ⟶ M) ≠ 0 := by
    by_contra h
    push Not at h
    have hπ : (G.π : (SheafOfModules.free G.I : X.Modules) ⟶ M) = 0 := by
      apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan G.I)
      intro i
      change SheafOfModules.ιFree i ≫ G.π = SheafOfModules.ιFree i ≫ 0
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simpa only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply, comp_zero] using h i
    let : Epi G.π := G.epi
    exact hM (IsZero.of_epi_eq_zero G.π hπ)
  obtain ⟨i, hi⟩ := hgen
  let α : SheafOfModules.unit X.ringCatSheaf ⟶ M := M.unitHomEquiv.symm (G.s i)
  refine ⟨α.val.app (op ⊤) (1 : Γ(X, ⊤)), ?_⟩
  intro hz
  apply hi
  apply M.unitHomEquiv.injective
  ext V
  have hn := PresheafOfModules.naturality_apply α.val
    (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op (1 : Γ(X, ⊤))
  change α.val.app V (1 : Γ(X, V.unop)) = 0
  change α.val.app V (X.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op 1) =
    M.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : X.Opens))).op
      (α.val.app (op ⊤) (1 : Γ(X, ⊤))) at hn
  simpa only [map_one, hz, map_zero] using hn

/-- On a smooth projective curve, a sheaf with a native rank-one atlas and generating sections has
a global section that is nonzero on EVERY irreducible (= connected) component.  EP-free version of
`SGPT.Projective.NumEq.AlgebraicCurveDegree.exists_originalGeneratedSection_nonzeroOnComponents`,
whose invertibility hypothesis is replaced by the atlas. -/
theorem exists_generatedSection_nonzeroOnComponents
    {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L : X.Modules} (a : LineBundleAtlas L) (G : L.GeneratingSections) :
    ∃ s : Γ(L, ⊤), SectionNonzeroOnComponents f E s := by
  classical
  let U (C : ↥(irreducibleComponents X)) : X.Opens :=
    smoothProjectiveComponentOpen f 1 E C.val C.property
  have hc (C : ↥(irreducibleComponents X)) :
      ∃ s : Γ((Scheme.Modules.pullback (U C).ι).obj L, ⊤), s ≠ 0 := by
    let := smoothProjective_component_isIntegral f 1 E C.val C.property
    obtain ⟨y⟩ : Nonempty (U C).toScheme := inferInstance
    exact exists_generatedSection_ne_zero _ (not_isZero_pullback_of_atlas a (U C) y.1 y.2)
      (pullbackGeneratingSections (U C).ι G)
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

end SGPT.BDivisor.BD3
