import SGPT.Checks.Comparison.BJProjPullback
import SGPT.Foundations.Envelope.Vanishing.AmpleScalarBaseChange
import SGPT.Foundations.Envelope.AlgGeom.SchemeAmpleClosedRestriction
import SGPT.Foundations.Envelope.AlgGeom.SchemeAmpleCoherentSerreVanishing
import SGPT.Foundations.Envelope.AlgGeom.AmpleTensorLines
import SGPT.Foundations.Envelope.AlgGeom.BundleTensorPowerPullback
import SGPT.Support.ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections

/-!
# Relative Serre vanishing and coherence of direct images (lane BJ-PROJ, R3 step 1)

Let `p_X : X ⟶ Spec k` be separated with `X` locally Noetherian, `π : Y ⟶ X` a morphism and `A` an
ample invertible sheaf on `Y` relative to `π ≫ p_X` (e.g. `Y` projective over `k`). For an affine
open `U ⊆ X` with ring `R = Γ(X, U)`, the open subscheme `π⁻¹ U` is a closed subscheme of
`Y ×_k Spec R` (`preimageEmbedding`, a base change of the diagonal of `X`), so `A|_{π⁻¹ U}` is
ample over `Spec R` (`isAmple_preimage`). Hence:

* **relative Serre vanishing**: for every coherent `M` on `Y`, `H^{>0}(π⁻¹ U, A^m ⊗ M) = 0` for
  `m ≫ 0` (`exists_preimage_cohomology_bound`);
* **coherence of direct images**: `π_* F` is of finite type for every coherent `F` on `Y`
  (`isFiniteType_pushforward`), since `Γ(π⁻¹ U, F)` is a finite `R`-module (projective
  finiteness over a Noetherian ring, SGPT.Foundations.Envelope/aintlib).

We also prove that restrictions of finite-type sheaves to open subschemes are of finite type
(`isFiniteType_restrict`).

Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:relative-serre`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Opposite

universe u

namespace SGPT.NAPotential.BJProj

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SchemeLineAmpleness

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-! ### Finite type is preserved by restriction to opens -/

section restrict

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of a finite-type quasi-coherent sheaf along an open immersion is of finite
type. -/
theorem isFiniteType_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : (M.restrict f).IsFiniteType := by
  apply isFiniteType_of_sections_module_finite
  intro W
  have hW' : IsAffineOpen (f ''ᵁ W.1) := W.2.image_of_isOpenImmersion f
  let : Module.Finite Γ(Y, f ''ᵁ W.1) Γ(M, f ''ᵁ W.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen M ⟨_, hW'⟩
  let : Algebra Γ(Y, f ''ᵁ W.1) Γ(X, W.1) := (f.appIso W.1).hom.hom.toAlgebra
  let : Module Γ(Y, f ''ᵁ W.1) Γ(M.restrict f, W.1) :=
    inferInstanceAs (Module Γ(Y, f ''ᵁ W.1) Γ(M, f ''ᵁ W.1))
  have : IsScalarTower Γ(Y, f ''ᵁ W.1) Γ(X, W.1) Γ(M.restrict f, W.1) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change ((f.appIso W.1).inv.hom ((f.appIso W.1).hom.hom r)) • (x : Γ(M, f ''ᵁ W.1)) = r • x
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  have : Module.Finite Γ(Y, f ''ᵁ W.1) Γ(M.restrict f, W.1) :=
    inferInstanceAs (Module.Finite Γ(Y, f ''ᵁ W.1) Γ(M, f ''ᵁ W.1))
  exact Module.Finite.of_restrictScalars_finite Γ(Y, f ''ᵁ W.1) Γ(X, W.1) Γ(M.restrict f, W.1)

/-- Global sections that are finite over the base along some morphism are finite over the ring
of global functions. -/
theorem globalSections_finite_of_baseSections_finite {T S : Scheme.{u}} (e : T ⟶ S)
    (N : T.Modules) (h : Module.Finite Γ(S, ⊤) (baseSections e N)) :
    Module.Finite Γ(T, ⊤) Γ(N, ⊤) := by
  have hD : Module.Finite Γ(S, ⊤)
      ((ModuleCat.restrictScalars e.appTop.hom).obj (ModuleCat.of Γ(T, ⊤) Γ(N, ⊤))) :=
    Module.Finite.equiv (baseSectionsIsoRestrictScalarsTop e N).toLinearEquiv
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := e.appTop.hom.toAlgebra
  let : Module Γ(T, ⊤)
      ((ModuleCat.restrictScalars e.appTop.hom).obj (ModuleCat.of Γ(T, ⊤) Γ(N, ⊤))) :=
    inferInstanceAs (Module Γ(T, ⊤) Γ(N, ⊤))
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤)
      ((ModuleCat.restrictScalars e.appTop.hom).obj (ModuleCat.of Γ(T, ⊤) Γ(N, ⊤))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.of_restrictScalars_finite Γ(S, ⊤) Γ(T, ⊤)
    ((ModuleCat.restrictScalars e.appTop.hom).obj (ModuleCat.of Γ(T, ⊤) Γ(N, ⊤)))

end restrict

/-! ### The preimage of an affine open as a closed subscheme of a base change -/

section embedding

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (π : Y ⟶ X)
  {U : X.Opens} (hU : IsAffineOpen U)

/-- The open immersion `Spec Γ(X, U) ⟶ X` of an affine open, with source written as the spectrum
of the ring `Γ(X, U)` regarded as a type. -/
def fromSpec' : Spec (.of Γ(X, U)) ⟶ X := hU.fromSpec

instance : IsOpenImmersion (fromSpec' hU) := by
  unfold fromSpec'
  infer_instance

/-- The isomorphism `U ≅ Spec Γ(X, U)`, with target written as in `fromSpec'`. -/
def isoSpec' : U.toScheme ≅ Spec (.of Γ(X, U)) := hU.isoSpec

@[reassoc (attr := simp)]
theorem isoSpec'_hom_fromSpec' : (isoSpec' hU).hom ≫ fromSpec' hU = U.ι :=
  hU.isoSpec_hom_fromSpec

/-- The structure map `k → Γ(X, U)` of an affine open. -/
def affineBaseHom : k →+* Γ(X, U) := (Spec.preimage (fromSpec' hU ≫ pX)).hom

theorem spec_affineBaseHom :
    fromSpec' hU ≫ pX = Spec.map (CommRingCat.ofHom (affineBaseHom pX hU)) := by
  rw [affineBaseHom, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The closed embedding of `π⁻¹ U` into `Y ×_k Spec Γ(X, U)`. -/
def preimageEmbedding [IsSeparated pX] :
    (π ⁻¹ᵁ U).toScheme ⟶ pullback (π ≫ pX) (Spec.map (CommRingCat.ofHom (affineBaseHom pX hU))) :=
  (pullbackRestrictIsoRestrict π U).inv ≫
    pullback.map π U.ι π (fromSpec' hU) (𝟙 _) (isoSpec' hU).hom (𝟙 _) (by simp) (by simp) ≫
    pullback.mapDesc π (fromSpec' hU) pX ≫
    (pullback.congrHom rfl (spec_affineBaseHom pX hU)).hom

instance [IsSeparated pX] : IsClosedImmersion (preimageEmbedding pX π hU) := by
  unfold preimageEmbedding
  infer_instance

@[reassoc (attr := simp)]
theorem preimageEmbedding_fst [IsSeparated pX] :
    preimageEmbedding pX π hU ≫ pullback.fst _ _ = (π ⁻¹ᵁ U).ι := by
  simp only [preimageEmbedding, Category.assoc, pullback.congrHom_hom, pullback.mapDesc,
    pullback.map, Category.comp_id]
  rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst,
    pullbackRestrictIsoRestrict_inv_fst]

theorem preimageEmbedding_snd [IsSeparated pX] :
    preimageEmbedding pX π hU ≫ pullback.snd _ _ =
      (π ∣_ U) ≫ (isoSpec' hU).hom := by
  simp only [preimageEmbedding, morphismRestrict, Category.assoc, pullback.congrHom_hom,
    pullback.mapDesc, pullback.map, Category.comp_id]
  rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

/-- **Relative ampleness on preimages of affine opens.** -/
theorem isAmple_preimage [IsSeparated pX] (A : Y.Modules) (hA : IsAmple (π ≫ pX) A) :
    IsAmple (preimageEmbedding pX π hU ≫ pullback.snd _ _)
      ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj A) := by
  have H := IsPullback.of_hasPullback (π ≫ pX)
    (Spec.map (CommRingCat.ofHom (affineBaseHom pX hU)))
  have h1 := Vanishing.AmpleScalarBaseChange.isAmple_of_isPullback (pullback.fst _ _) (π ≫ pX)
    (pullback.snd _ _) (affineBaseHom pX hU) H A hA
  have h2 := SchemeAmpleClosedRestriction.ample_pullback h1 (preimageEmbedding pX π hU)
  exact AmpleTensorLines.ample_of_iso h2
    ((Scheme.Modules.pullbackComp (preimageEmbedding pX π hU) (pullback.fst _ _)).app A ≪≫
      (Scheme.Modules.pullbackCongr (preimageEmbedding_fst pX π hU)).app A)

end embedding

/-! ### Relative Serre vanishing -/

section serre

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsSeparated pX]
  [IsLocallyNoetherian X] (π : Y ⟶ X) (A : Y.Modules) (hA : IsAmple (π ≫ pX) A)

include hA in
/-- **Relative Serre vanishing.** For an affine open `U` of `X` and a coherent `M` on `Y`, the
sheaf `A^m ⊗ M` has no higher cohomology on `π⁻¹ U` for `m ≫ 0`. -/
theorem exists_preimage_cohomology_bound {U : X.Opens} (hU : IsAffineOpen U) (M : Y.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ, Subsingleton (CategoryTheory.Sheaf.H
      ((CanonicalGeometry.bundleTensorPower A m ⊗ M).restrict (π ⁻¹ᵁ U).ι).sheaf (q + 1)) := by
  let ι := (π ⁻¹ᵁ U).ι
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : (M.restrict ι).IsFiniteType := isFiniteType_restrict ι M
  obtain ⟨N, hN⟩ := SchemeAmpleCoherentSerreVanishing.exists_sheafCohomology_bound
    (R := Γ(X, U)) (preimageEmbedding pX π hU ≫ pullback.snd _ _)
    ((Scheme.Modules.pullback ι).obj A) (isAmple_preimage pX π hU A hA) (M.restrict ι)
  refine ⟨N, fun m hm q => ?_⟩
  let E : CanonicalGeometry.bundleTensorPower ((Scheme.Modules.pullback ι).obj A) m ⊗
      M.restrict ι ≅ (CanonicalGeometry.bundleTensorPower A m ⊗ M).restrict ι :=
    (((BundleTensorPowerPullback.pullbackIso ι A m).symm ≪≫
        ((restrictFunctorIsoPullback ι).app _).symm) ⊗ᵢ Iso.refl _) ≪≫
      (SGPT.Support.ModularCurves.restrictMonoidalTensorIso ι _ _).symm
  exact subsingleton_H_of_iso E (q + 1) (hN m hm q)

end serre

/-! ### Coherence of direct images -/

section coherence

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) [IsSeparated pX]
  [IsLocallyNoetherian X] (π : Y ⟶ X) (A : Y.Modules) (hA : IsAmple (π ≫ pX) A)

include hA in
/-- Over an affine open `U`, the direct image of a coherent sheaf restricted to `U` has finite
global sections. -/
theorem pushforward_restrict_globalSections_finite [Y.IsSeparated] {U : X.Opens}
    (hU : IsAffineOpen U) (F : Y.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite Γ(U.toScheme, ⊤)
      Γ((Scheme.Modules.pushforward (π ∣_ U)).obj (F.restrict (π ⁻¹ᵁ U).ι), ⊤) := by
  let ι := (π ⁻¹ᵁ U).ι
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : (F.restrict ι).IsFiniteType := isFiniteType_restrict ι F
  have hpf := (isAmple_preimage pX π hU A hA).isProjectiveFactorization
  have h1 := hpf.baseSections_module_finite (F.restrict ι)
  rw [preimageEmbedding_snd] at h1
  have h2 : Module.Finite Γ(Spec (.of Γ(X, U)), ⊤)
      (baseSections (isoSpec' hU).hom
        ((Scheme.Modules.pushforward (π ∣_ U)).obj (F.restrict ι))) :=
    Module.Finite.equiv (baseSectionsPushforwardIso (π ∣_ U) (isoSpec' hU).hom
      (F.restrict ι)).toLinearEquiv
  exact globalSections_finite_of_baseSections_finite (isoSpec' hU).hom _ h2

include hA in
/-- **Direct images of coherent sheaves are coherent**: for `π : Y ⟶ X` with `Y` separated and
`A` ample over `k`, and `X` separated and locally Noetherian, `π_* F` is of finite type for every
finite-type quasi-coherent `F`. -/
theorem isFiniteType_pushforward [Y.IsSeparated] [QuasiCompact π] (F : Y.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] : ((Scheme.Modules.pushforward π).obj F).IsFiniteType := by
  let P := (Scheme.Modules.pushforward π).obj F
  have hloc : ∀ U : X.affineOpens, ∃ G : (P.restrict U.1.ι).GeneratingSections, G.IsFiniteType := by
    intro U
    let ι := (π ⁻¹ᵁ U.1).ι
    let N := (Scheme.Modules.pushforward (π ∣_ U.1)).obj (F.restrict ι)
    let : IsAffine U.1.toScheme := U.2
    let : (π ⁻¹ᵁ U.1).toScheme.IsSeparated := ⟨by
      rw [← terminal.comp_from ι]
      infer_instance⟩
    let : N.IsQuasicoherent := isQuasicoherent_pushforward_of_quasiCompact (π ∣_ U.1) _
    let : Module.Finite Γ(U.1.toScheme, ⊤) Γ(N, ⊤) :=
      pushforward_restrict_globalSections_finite pX π A hA U.2 F
    obtain ⟨G, hG⟩ := exists_generatingSections_of_globalSections_module_finite_of_isAffine N
    let e : P.restrict U.1.ι ≅ N :=
      restrictPushforwardIsoOfIsPullbackApp π (π ∣_ U.1) ι U.1.ι
        (isPullback_morphismRestrict π U.1) F
    refine ⟨(SheafOfModules.GeneratingSections.equivOfIso e).symm G, ?_⟩
    exact ⟨by
      change Finite G.I
      exact hG.finite⟩
  choose G hG using hloc
  let q : P.LocalGeneratorsData :=
    { I := X.affineOpens
      X := fun U ↦ (U : X.Opens)
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
      generators := fun U ↦ generatingSectionsOverOfRestrict P U.1 (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let : (G U).IsFiniteType := hG U
    exact generatingSectionsOverOfRestrict_isFiniteType P U.1 (G U)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  exact { exists_localGeneratorsData := ⟨q.shrink, hqShrink⟩ }

end coherence

end SGPT.NAPotential.BJProj
