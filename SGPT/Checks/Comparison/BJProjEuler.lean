import SGPT.Foundations.Envelope.AlgGeom.SchemeCoherentEulerAffine
import SGPT.Foundations.Envelope.AlgGeom.CompactSeparatedPushforwardQuasicoherent

/-!
# Euler characteristics along morphisms with acyclic inverse images (lane BJ-PROJ, R3 step 2)

Let `g : Y ⟶ X` be a morphism of separated quasi-compact schemes over a field `k` and `M` a
quasi-coherent sheaf on `Y`. If `M` has no higher cohomology on the inverse images of the finite
intersections of a finite affine open cover of `X`, then

  `χ(Y, M) = χ(X, g_* M)`   (`eulerCharacteristic_pushforward_of_acyclic`).

This is the degenerate case of the Leray spectral sequence, proved with Čech complexes only:
the cover `g⁻¹ U` of `Y` and an affine cover `W` of `Y` have affine mutual intersections and
acyclic finite intersections, so the two-cover comparison of SGPT.Foundations.Envelope/aintlib identifies
their Čech cohomology (`fieldCech_finrank_eq_of_acyclic_covers`), and the Čech complex of `g⁻¹ U`
with coefficients in `M` is the Čech complex of `U` with coefficients in `g_* M`.

We also record that `g_*` preserves quasi-coherence for quasi-compact `g` with separated source
(`isQuasicoherent_pushforward_of_quasiCompact`), by reduction to SGPT.Foundations.Envelope's affine-target
case.

Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:euler-pushforward`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules TopCat TopCat.Sheaf

universe u

namespace SGPT.NAPotential.BJProj

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SchemeCoherentEulerIndex
  SGPT.Foundations.Envelope.SchemeCoherentEulerExact SGPT.Foundations.Envelope.SchemeCoherentEulerCharacteristic
  SGPT.Foundations.Envelope.SchemeCoherentEulerAffine

/-! ### Affine intersections -/

section affine

variable {X Y : Scheme.{u}}

/-- A morphism from an affine scheme to a separated scheme is affine. -/
theorem isAffineHom_of_isAffine_of_isSeparated [IsAffine Y] [X.IsSeparated] (h : Y ⟶ X) :
    IsAffineHom h := by
  have h1 : IsAffineHom (h ≫ terminal.from X) := by
    rw [terminal.comp_from]
    infer_instance
  exact MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) h
    (terminal.from X) inferInstance h1

/-- The inverse image of an affine open of a separated scheme meets an affine open in an affine
open. -/
theorem isAffineOpen_inf_preimage [X.IsSeparated] (g : Y ⟶ X) {W : Y.Opens}
    (hW : IsAffineOpen W) {U : X.Opens} (hU : IsAffineOpen U) : IsAffineOpen (W ⊓ g ⁻¹ᵁ U) := by
  let : IsAffine W.toScheme := hW
  let : IsAffineHom (W.ι ≫ g) := isAffineHom_of_isAffine_of_isSeparated (W.ι ≫ g)
  have h1 : IsAffineOpen ((W.ι ≫ g) ⁻¹ᵁ U) := hU.preimage (W.ι ≫ g)
  have h2 : W.ι ''ᵁ ((W.ι ≫ g) ⁻¹ᵁ U) = W ⊓ g ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
  rw [← h2]
  exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mpr h1

/-- The trace on an open `W` of an open `V` is affine as soon as `W ⊓ V` is. -/
theorem isAffineOpen_ι_preimage (W V : Y.Opens) (h : IsAffineOpen (W ⊓ V)) :
    IsAffineOpen (W.ι ⁻¹ᵁ V) := by
  apply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion W.ι).mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact h

end affine

/-! ### Quasi-coherence of direct images -/

section quasicoherent

/-- **Direct images are quasi-coherent**: for a quasi-compact morphism `g : Y ⟶ X` with separated
source and a quasi-coherent `M` on `Y`, the sheaf `g_* M` is quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_quasiCompact {X Y : Scheme.{u}} (g : Y ⟶ X)
    [QuasiCompact g] [Y.IsSeparated] (M : Y.Modules) [M.IsQuasicoherent] :
    ((pushforward g).obj M).IsQuasicoherent := by
  have hlocal (U : X.affineOpens) :
      (((pushforward g).obj M).over (U : X.Opens)).IsQuasicoherent := by
    let V := g ⁻¹ᵁ U.1
    let gU := g ∣_ U.1
    let MU := (restrictFunctor V.ι).obj M
    let : IsAffine U.1.toScheme := U.2
    let : V.toScheme.IsSeparated := ⟨by
      rw [← terminal.comp_from V.ι]
      infer_instance⟩
    let : CompactSpace V.toScheme := QuasiCompact.compactSpace_of_compactSpace gU
    have : MU.IsQuasicoherent := inferInstance
    have hPush : ((pushforward gU).obj MU).IsQuasicoherent :=
      CompactSeparatedPushforwardQuasicoherent.isQuasicoherent_pushforward gU MU
    have hRestrict :
        ((restrictFunctor U.1.ι).obj ((pushforward g).obj M)).IsQuasicoherent :=
      (isQuasicoherent U.1).prop_of_iso
        (restrictPushforwardIsoOfIsPullbackApp g gU V.ι U.1.ι
          (isPullback_morphismRestrict g U.1) M).symm
        hPush
    let :
        ((restrictFunctor U.1.ι).obj ((pushforward g).obj M)).IsQuasicoherent :=
      hRestrict
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen ((pushforward g).obj M) U.1
  have hcover : (Opens.grothendieckTopology X).CoversTop
      (fun U : X.affineOpens ↦ (U : X.Opens)) := by
    rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ ((pushforward g).obj M) _
      (fun U : X.affineOpens ↦ (U : X.Opens)) hcover hlocal

end quasicoherent

/-! ### Čech cohomology of two covers with acyclic intersections -/

section twoCovers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **Two-cover comparison for acyclic covers.** Let `U` and `V` be finite open covers of a
separated scheme such that every finite intersection of members of one cover meets every member
of the other in an affine open, and a quasi-coherent `M` has no higher cohomology on the finite
intersections of either cover. Then the Čech cohomology groups of `M` for the two covers have the
same dimension in every positive degree. -/
theorem fieldCech_succ_finrank_eq_of_acyclic_covers [C.IsSeparated] (f : C ⟶ Spec (.of k))
    (M : C.Modules) [M.IsQuasicoherent] {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → C.Opens) (hU : IsOpenCover U) (V : κ → C.Opens) (hV : IsOpenCover V)
    (hUV : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : κ),
      IsAffineOpen ((∏ᶜ fun l : Fin (p + 1) => U (i l)) ⊓ V j))
    (hVU : ∀ (p : ℕ) (i : Fin (p + 1) → κ) (j : ι),
      IsAffineOpen ((∏ᶜ fun l : Fin (p + 1) => V (i l)) ⊓ U j))
    (hUH : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (∏ᶜ fun l : Fin (p + 1) => U (i l)).ι).sheaf (q + 1)))
    (hVH : ∀ (p : ℕ) (i : Fin (p + 1) → κ) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (∏ᶜ fun l : Fin (p + 1) => V (i l)).ι).sheaf (q + 1)))
    (n : ℕ) :
    Module.finrank k (fieldCech f M U (n + 1)) = Module.finrank k (fieldCech f M V (n + 1)) := by
  have hrow : ∀ q p : ℕ, ((cechComplexFunctor V).obj
      (moduleCechTerm (baseModuleTopSheaf f M) U q).obj).ExactAt (p + 1) := by
    intro q p
    apply moduleCechTerm_cech_exactAt_succ_of_factors
    intro i
    apply moduleCechFixedFactorNative_exactAt_succ_of_app_exact
    exact moduleCechShortComplexApp_exact_of_restrict_subsingleton_H_succ f M V hV
      (∏ᶜ fun l : Fin (q + 1) => U (i l))
      (fun j => isAffineOpen_ι_preimage _ _ (hUV q i j)) p (hUH q i p)
  have hcol : ∀ (p q : ℕ) (i : Fin (p + 1) → κ),
      (moduleCechShortComplexApp (baseModuleTopSheaf f M) U q
        (∏ᶜ fun l : Fin (p + 1) => V (i l))).Exact := by
    intro p q i
    exact moduleCechShortComplexApp_exact_of_restrict_subsingleton_H_succ f M U hU
      (∏ᶜ fun l : Fin (p + 1) => V (i l))
      (fun j => isAffineOpen_ι_preimage _ _ (hVU p i j)) q (hVH p i q)
  let e : (baseCechComplex f M U).homology (n + 1) ≅ (baseCechComplex f M V).homology (n + 1) :=
    (moduleCechTwoCoverHomologySuccIso (baseModuleTopSheaf f M) U V hU hV n
      (fun q p _ hp => by
        cases p with
        | zero => omega
        | succ p => simpa only [Nat.succ_eq_add_one] using hrow q p)
      (fun q p _ hp => by
        cases p with
        | zero => omega
        | succ p => simpa only [Nat.succ_eq_add_one] using hrow q p)
      (fun p q _ hq i => by
        cases q with
        | zero => omega
        | succ q => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hcol p q i)
      (fun p q _ hq i => by
        cases q with
        | zero => omega
        | succ q => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hcol p q i)).symm
  exact ((ModuleCat.restrictScalars (baseScalar (k := k))).mapIso e).toLinearEquiv.finrank_eq

/-- Under the hypotheses of `fieldCech_succ_finrank_eq_of_acyclic_covers`, the Čech cohomology
groups have the same dimension in every degree. -/
theorem fieldCech_finrank_eq_of_acyclic_covers [C.IsSeparated] (f : C ⟶ Spec (.of k))
    (M : C.Modules) [M.IsQuasicoherent] {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → C.Opens) (hU : IsOpenCover U) (V : κ → C.Opens) (hV : IsOpenCover V)
    (hUV : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (j : κ),
      IsAffineOpen ((∏ᶜ fun l : Fin (p + 1) => U (i l)) ⊓ V j))
    (hVU : ∀ (p : ℕ) (i : Fin (p + 1) → κ) (j : ι),
      IsAffineOpen ((∏ᶜ fun l : Fin (p + 1) => V (i l)) ⊓ U j))
    (hUH : ∀ (p : ℕ) (i : Fin (p + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (∏ᶜ fun l : Fin (p + 1) => U (i l)).ι).sheaf (q + 1)))
    (hVH : ∀ (p : ℕ) (i : Fin (p + 1) → κ) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (∏ᶜ fun l : Fin (p + 1) => V (i l)).ι).sheaf (q + 1)))
    (n : ℕ) :
    Module.finrank k (fieldCech f M U n) = Module.finrank k (fieldCech f M V n) := by
  cases n with
  | zero => exact ((fieldSectionsCechZeroIso f M U hU).symm ≪≫
      fieldSectionsCechZeroIso f M V hV).toLinearEquiv.finrank_eq
  | succ n => exact fieldCech_succ_finrank_eq_of_acyclic_covers f M U hU V hV hUV hVU hUH hVH n

end twoCovers

/-! ### The Euler characteristic of an acyclic direct image -/

section euler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The Euler characteristic can be computed on the inverse image of a finite affine cover of a
separated target, provided the sheaf is acyclic on the inverse images of its finite
intersections. -/
theorem eulerCharacteristic_eq_on_preimage_cover [CompactSpace Y] [Y.IsSeparated] [X.IsSeparated]
    (g : Y ⟶ X) (p : Y ⟶ Spec (.of k)) (M : Y.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (hacyc : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1))) :
    eulerCharacteristic p M = coverEuler p M (fun i => g ⁻¹ᵁ U i) (Nat.card ι + 1) := by
  let W := finiteAffineOpens Y
  have hW := finiteAffineOpens_cover Y
  have hWa := finiteAffineOpens_isAffine Y
  let V : ι → Y.Opens := fun i => g ⁻¹ᵁ U i
  have hV : IsOpenCover V := g.iSup_preimage_eq_top hU
  have hVint (a : ℕ) (i : Fin (a + 1) → ι) :
      (∏ᶜ fun l : Fin (a + 1) => V (i l)) = g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l)) :=
    (g.preimage_cechIntersection U a i).symm
  have hfin (n : ℕ) : Module.finrank k (fieldCech p M W n) =
      Module.finrank k (fieldCech p M V n) := by
    refine fieldCech_finrank_eq_of_acyclic_covers p M W hW V hV ?_ ?_ ?_ ?_ n
    · intro a i j
      exact isAffineOpen_inf_preimage g (IsAffineOpen.cechIntersection W hWa a i) (hUa j)
    · intro a i j
      rw [hVint a i, inf_comm]
      exact isAffineOpen_inf_preimage g (hWa j) (IsAffineOpen.cechIntersection U hUa a i)
    · intro a i q
      exact cechIntersection_subsingleton_H M W hWa a i q
    · intro a i q
      rw [hVint a i]
      exact hacyc a i q
  let P := max (Nat.card (finiteAffineCover Y).I₀ + 1) (Nat.card ι + 1)
  rw [eulerCharacteristic,
    coverEuler_eq_of_card_le p M (finiteAffineOpens Y) (by omega)
      (show Nat.card (finiteAffineCover Y).I₀ + 1 ≤ P from le_max_left _ _),
    coverEuler_eq_of_card_le p M V (by omega)
      (show Nat.card ι + 1 ≤ P from le_max_right _ _)]
  apply Finset.sum_congr rfl
  intro n _
  rw [hfin n]

/-- **Euler characteristics of acyclic direct images.** Let `g : Y ⟶ X` be a morphism of
separated quasi-compact `k`-schemes, `M` quasi-coherent on `Y`, and `U` a finite affine open cover
of `X` such that `M` has no higher cohomology on the inverse image of any finite intersection of
members of `U`. Then `χ(Y, M) = χ(X, g_* M)`. -/
theorem eulerCharacteristic_pushforward_of_acyclic [CompactSpace X] [CompactSpace Y]
    [X.IsSeparated] [Y.IsSeparated] (g : Y ⟶ X) [QuasiCompact g] (f : X ⟶ Spec (.of k))
    (M : Y.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (hacyc : ∀ (a : ℕ) (i : Fin (a + 1) → ι) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      (M.restrict (g ⁻¹ᵁ (∏ᶜ fun l : Fin (a + 1) => U (i l))).ι).sheaf (q + 1))) :
    eulerCharacteristic (g ≫ f) M = eulerCharacteristic f ((pushforward g).obj M) := by
  let : ((pushforward g).obj M).IsQuasicoherent := isQuasicoherent_pushforward_of_quasiCompact g M
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [eulerCharacteristic_eq_on_preimage_cover g (g ≫ f) M U hU hUa hacyc,
    eulerCharacteristic_eq_on_cover f ((pushforward g).obj M) U hU hUa]
  unfold coverEuler
  apply Finset.sum_congr rfl
  intro n _
  rw [(fieldCechPushforwardIso g f M U n).toLinearEquiv.finrank_eq]

end euler

end SGPT.NAPotential.BJProj
