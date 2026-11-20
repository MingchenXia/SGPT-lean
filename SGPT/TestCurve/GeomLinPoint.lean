import SGPT.TestCurve.GeomLinDef
import SGPT.TestCurve.GeomLinLaurent

/-!
# The action of a point `c ∈ ℂ^*` on the sections of a linearized line bundle

Let `σ : 𝔾_m × 𝓧 ⟶ 𝓧` be a `𝔾_m`-action and `Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` a
linearization (`GeomLinearization`). For `c ∈ ℂ^*` let `ι_c : 𝓧 ⟶ 𝔾_m × 𝓧`, `x ↦ (c, x)`
(`pointIncl`) and `σ_c = σ ∘ ι_c : 𝓧 ⟶ 𝓧` (`actAt`). Restricting `Φ` along `ι_c` gives an
isomorphism `Φ_c : σ_c^* 𝓛 ≅ 𝓛`, hence a map on sections

`ρ_c : H⁰(𝓧, 𝓛^m) ⟶ H⁰(𝓧, 𝓛^m)`, `ρ_c(s) = Φ_c^m(σ_c^* s)` (`actSection`).

In the frames: if `s = s_i e_i^m`, then `ρ_c(s) = σ_c^♯(s_i) φ_{ij}(c)^m e_j^m` on
`σ_c⁻¹(U_i) ∩ U_j`; these local sections glue by the compatibility of the `φ_{ij}` with the
transition functions (`exists_cechPullSection`, for a general Čech morphism `g^* M ⟶ M'`).

On `𝓧 ∖ 𝓧₀` the linearization is the canonical one (`phi_frame`), so in the frames `ε_k^m`
the coefficients of `ρ_c(s)` are `σ_c^♯` of those of `s` (`epsCoeff_actSection`), where
`σ_c^♯ t = c t` (`actAt_tRes`) and `σ_c^♯ q^♯ = q^♯` (`actAt_pullFun`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite MonoidalCategory CartesianMonoidalCategory
open SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

/-! ### Restriction helpers -/

theorem appLE_res {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {U : Y.Opens} {V V' : Y'.Opens}
    (e : V ≤ g ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)) :
    Y'.presheaf.map (homOfLE h).op (g.appLE U V e x) = g.appLE U V' (h.trans e) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_of_res {Y Y' : Scheme.{0}} (g : Y' ⟶ Y) {U U' : Y.Opens} {V : Y'.Opens}
    (h : U' ≤ U) (e : V ≤ g ⁻¹ᵁ U') (x : Γ(Y, U)) :
    g.appLE U' V e (Y.presheaf.map (homOfLE h).op x) =
      g.appLE U V (e.trans (g.preimage_mono h)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem res_self {Y : Scheme.{0}} {U : Y.Opens} (x : Γ(Y, U)) :
    Y.presheaf.map (homOfLE (le_refl U)).op x = x := by
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem appLE_id_eq {Y : Scheme.{0}} {g : Y ⟶ Y} (hg : g = 𝟙 Y) {U V : Y.Opens}
    (e : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    g.appLE U V e x = Y.presheaf.map (homOfLE (show V ≤ U from by subst hg; exact e)).op x := by
  subst hg
  rfl

/-! ### Čech morphisms `g^* M ⟶ M'` and the pull-back of sections -/

section CechPull

variable {Y Y' : Scheme.{0}} {M : Y.Modules} {M' : Y'.Modules} (b : LineBundleAtlas M)
  (b' : LineBundleAtlas M') (g : Y' ⟶ Y)

/-- The open `g⁻¹(U_i) ∩ U'_j`. -/
abbrev pullOpen (i : b.I) (j : b'.I) : Y'.Opens := g ⁻¹ᵁ b.opens i ⊓ b'.opens j

/-- The open `g⁻¹(U_i ∩ U_{i'}) ∩ (U'_j ∩ U'_{j'})`. -/
abbrev pullOverlap (i i' : b.I) (j j' : b'.I) : Y'.Opens :=
  g ⁻¹ᵁ (b.opens i ⊓ b.opens i') ⊓ (b'.opens j ⊓ b'.opens j')

theorem pullOverlap_le_left (i i' : b.I) (j j' : b'.I) :
    pullOverlap b b' g i i' j j' ≤ pullOpen b b' g i j :=
  inf_le_inf (g.preimage_mono inf_le_left) inf_le_left

theorem pullOverlap_le_right (i i' : b.I) (j j' : b'.I) :
    pullOverlap b b' g i i' j j' ≤ pullOpen b b' g i' j' :=
  inf_le_inf (g.preimage_mono inf_le_right) inf_le_right

/-- **Čech form of a morphism `g^* M ⟶ M'`**: functions `ψ_{ij}` on `g⁻¹(U_i) ∩ U'_j`
(`g^* e_i ↦ ψ_{ij} e'_j`) with `g^♯(τ_{ii'}) ψ_{i'j'} = ψ_{ij} τ'_{jj'}`. -/
def IsCechHom (ψ : ∀ i j, Γ(Y', pullOpen b b' g i j)) : Prop :=
  ∀ (i i' : b.I) (j j' : b'.I),
    g.appLE (b.opens i ⊓ b.opens i') (pullOverlap b b' g i i' j j') inf_le_left
        (atlasTransition b i i') *
      Y'.presheaf.map (homOfLE (pullOverlap_le_right b b' g i i' j j')).op (ψ i' j') =
    Y'.presheaf.map (homOfLE (pullOverlap_le_left b b' g i i' j j')).op (ψ i j) *
      Y'.presheaf.map (homOfLE (inf_le_right : pullOverlap b b' g i i' j j' ≤ _)).op
        (atlasTransition b' j j')

/-- **Pull-back of sections along a Čech morphism `Ψ : g^* M ⟶ M'`**: every
`s ∈ H⁰(Y, M^m)` gives `Ψ^m(g^* s) ∈ H⁰(Y', M'^m)`, whose coefficient in `e'_j{}^m` on
`g⁻¹(U_i) ∩ U'_j` is `g^♯(s_i) ψ_{ij}^m`. -/
theorem exists_cechPullSection (ψ : ∀ i j, Γ(Y', pullOpen b b' g i j))
    (hψ : IsCechHom b b' g ψ) (m : ℕ) (s : bundlePowerGlobalSections M m) :
    ∃ s' : bundlePowerGlobalSections M' m, ∀ i j,
      Y'.presheaf.map (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)).op
          (atlasPowerGlobalCoefficients b' m j s') =
        g.appLE (b.opens i) (pullOpen b b' g i j) inf_le_left
            (atlasPowerGlobalCoefficients b m i s) * ψ i j ^ m := by
  classical
  let κ : ∀ p : b.I × b'.I, Γ(Y', pullOpen b b' g p.1 p.2) := fun p =>
    g.appLE (b.opens p.1) (pullOpen b b' g p.1 p.2) inf_le_left
      (atlasPowerGlobalCoefficients b m p.1 s) * ψ p.1 p.2 ^ m
  let loc : ∀ p : b.I × b'.I, bundleSections (bundleTensorPower M' m) (pullOpen b b' g p.1 p.2) :=
    fun p => (((b'.frame p.2).tensorPower m).coefficients (homOfLE inf_le_right)).symm (κ p)
  have hloc : ∀ (p : b.I × b'.I) {W : Y'.Opens} (k : W ⟶ pullOpen b b' g p.1 p.2),
      ((b'.frame p.2).tensorPower m).coefficients (k ≫ homOfLE inf_le_right)
          ((bundleTensorPower M' m).val.map k.op (loc p)) = Y'.presheaf.map k.op (κ p) := by
    intro p W k
    rw [((b'.frame p.2).tensorPower m).coefficients_restrict]
    simp only [loc, LinearEquiv.apply_symm_apply]
    rfl
  have hcompat : TopCat.Presheaf.IsCompatible (bundleTensorPower M' m).val.presheaf
      (fun p : b.I × b'.I => pullOpen b b' g p.1 p.2) loc := by
    rintro ⟨i, j⟩ ⟨i', j'⟩
    let P := pullOpen b b' g i j ⊓ pullOpen b b' g i' j'
    have hPO : P ≤ pullOverlap b b' g i i' j j' := by
      rintro x ⟨⟨hxi, hxj⟩, ⟨hxi', hxj'⟩⟩
      exact ⟨⟨hxi, hxi'⟩, ⟨hxj, hxj'⟩⟩
    have hPj : P ≤ b'.opens j := inf_le_left.trans inf_le_right
    have hPj' : P ≤ b'.opens j' := inf_le_right.trans inf_le_right
    apply (((b'.frame j').tensorPower m).coefficients (homOfLE hPj')).injective
    change ((b'.frame j').tensorPower m).coefficients (homOfLE hPj')
        ((bundleTensorPower M' m).val.map (homOfLE (inf_le_left : P ≤ _)).op (loc (i, j))) =
      ((b'.frame j').tensorPower m).coefficients (homOfLE hPj')
        ((bundleTensorPower M' m).val.map (homOfLE (inf_le_right : P ≤ _)).op (loc (i', j')))
    rw [LocalBundleFrame.tensorPower_coefficients_transition (b'.frame j) (b'.frame j')
      (homOfLE hPj) (homOfLE hPj')]
    have h1 := hloc (i, j) (homOfLE (inf_le_left : P ≤ _))
    have h2 := hloc (i', j') (homOfLE (inf_le_right : P ≤ _))
    rw [show (homOfLE (inf_le_left : P ≤ _) ≫ homOfLE inf_le_right : P ⟶ b'.opens j) =
      homOfLE hPj from rfl] at h1
    rw [show (homOfLE (inf_le_right : P ≤ _) ≫ homOfLE inf_le_right : P ⟶ b'.opens j') =
      homOfLE hPj' from rfl] at h2
    rw [h1, h2]
    simp only [κ, map_mul, map_pow]
    -- transition of the coefficients of `s`
    have hs := LocalBundleFrame.global_coefficients_transition (b.frame i) (b.frame i')
      (homOfLE (inf_le_left : b.opens i ⊓ b.opens i' ≤ _))
      (homOfLE (inf_le_right : b.opens i ⊓ b.opens i' ≤ _)) m s
    change Y.presheaf.map _ (atlasPowerGlobalCoefficients b m i' s) =
      (atlasTransition b i i') ^ m * Y.presheaf.map _ (atlasPowerGlobalCoefficients b m i s) at hs
    have hs' := congrArg (g.appLE (b.opens i ⊓ b.opens i') P (hPO.trans inf_le_left)) hs
    rw [map_mul, map_pow, appLE_of_res, appLE_of_res] at hs'
    rw [appLE_res, appLE_res, hs']
    -- the Čech condition, restricted to `P`
    have hc := congrArg (Y'.presheaf.map (homOfLE hPO).op) (hψ i i' j j')
    rw [map_mul, map_mul, appLE_res, presheaf_map_map, presheaf_map_map, presheaf_map_map] at hc
    have htr : (localBundleFrameTransition (b'.frame j) (b'.frame j') (homOfLE hPj)
        (homOfLE hPj')).val = Y'.presheaf.map (homOfLE (hPO.trans inf_le_right)).op
          (atlasTransition b' j j') :=
      localBundleFrameTransition_restrict (b'.frame j) (b'.frame j') _ _ (homOfLE _)
    rw [htr]
    calc (Y'.presheaf.map (homOfLE (hPO.trans inf_le_right)).op (atlasTransition b' j j')) ^ m *
          (g.appLE (b.opens i) P _ (atlasPowerGlobalCoefficients b m i s) *
            Y'.presheaf.map (homOfLE inf_le_left).op (ψ i j) ^ m)
        = g.appLE (b.opens i) P _ (atlasPowerGlobalCoefficients b m i s) *
            (Y'.presheaf.map (homOfLE (hPO.trans (pullOverlap_le_left b b' g i i' j j'))).op
                (ψ i j) *
              Y'.presheaf.map (homOfLE (hPO.trans inf_le_right)).op
                (atlasTransition b' j j')) ^ m := by
          rw [mul_pow]
          ring
      _ = g.appLE (b.opens i) P _ (atlasPowerGlobalCoefficients b m i s) *
            (g.appLE (b.opens i ⊓ b.opens i') P _ (atlasTransition b i i') *
              Y'.presheaf.map (homOfLE (hPO.trans (pullOverlap_le_right b b' g i i' j j'))).op
                (ψ i' j')) ^ m := by rw [hc]
      _ = _ := by
          rw [mul_pow]
          ring
  have hcover : (⊤ : Y'.Opens) ≤ iSup fun p : b.I × b'.I => pullOpen b b' g p.1 p.2 := by
    intro x _
    obtain ⟨j, hj⟩ := b'.covers x
    obtain ⟨i, hi⟩ := b.covers (g x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  let Sh : TopCat.Sheaf AddCommGrpCat Y' :=
    ⟨(bundleTensorPower M' m).val.presheaf, (bundleTensorPower M' m).isSheaf⟩
  obtain ⟨s', hs', -⟩ := TopCat.Sheaf.existsUnique_gluing' Sh
    (fun p : b.I × b'.I => pullOpen b b' g p.1 p.2) ⊤ (fun _ => homOfLE le_top) hcover loc
    hcompat
  refine ⟨s', fun i j => ?_⟩
  have e1 := LocalBundleFrame.global_coefficients_restrict (b'.frame j) m
    (homOfLE (inf_le_right : pullOpen b b' g i j ≤ b'.opens j)) s'
  have e2 : (bundleTensorPower M' m).val.map
      (homOfLE (le_top : pullOpen b b' g i j ≤ ⊤)).op s' = loc (i, j) := hs' (i, j)
  rw [e2] at e1
  simp only [loc, LinearEquiv.apply_symm_apply] at e1
  exact e1.symm

end CechPull

/-! ### Points of `𝔾_m` -/

/-- The point `c ∈ ℂ^*` of the group scheme `𝔾_m = Spec ℂ[T, T⁻¹]` (`T ↦ c`). -/
def gmPoint (c : ℂˣ) : Spec (.of ℂ) ⟶ GmGroup.left :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℂ) c))

theorem gmPoint_comp (c : ℂˣ) : gmPoint c ≫ GmGroup.hom = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (LaurentPolynomial ℂ))) = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  simp

theorem gmPoint_appTop_coordGm (c : ℂˣ) :
    (gmPoint c).appTop coordGm = (Scheme.ΓSpecIso (.of ℂ)).inv (c : ℂ) := by
  have h := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1 : LaurentPolynomial ℂ))
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℂ) c)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, LaurentPolynomial.eval₂_T, zpow_one] at h
  exact h.symm

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

/-- The inclusion `ι_c : 𝓧 ⟶ 𝔾_m × 𝓧`, `x ↦ (c, x)`. -/
def pointIncl (T : TestConfiguration f a) (c : ℂˣ) : T.space ⟶ gmProd T :=
  pullback.lift (f := GmGroup.hom) (g := T.overBase.hom) (T.structureMap ≫ gmPoint c) (𝟙 T.space)
    (by rw [Category.assoc, gmPoint_comp, Category.comp_id, Category.id_comp]; rfl)

theorem pointIncl_proj (T : TestConfiguration f a) (c : ℂˣ) :
    pointIncl T c ≫ gmProj T = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem pointIncl_fst (T : TestConfiguration f a) (c : ℂˣ) :
    pointIncl T c ≫ (fst GmGroup T.overBase).left = T.structureMap ≫ gmPoint c :=
  pullback.lift_fst _ _ _

theorem pointIncl_mem_proj_preimage (T : TestConfiguration f a) (c : ℂˣ) {x : T.space}
    (hx : x ∈ offCentral T.toLine) : pointIncl T c x ∈ gmProj T ⁻¹ᵁ offCentral T.toLine := by
  change (pointIncl T c ≫ gmProj T) x ∈ offCentral T.toLine
  rw [pointIncl_proj]
  exact hx

theorem le_pointIncl_preimage (T : TestConfiguration f a) (c : ℂˣ) :
    offCentral T.toLine ≤ pointIncl T c ⁻¹ᵁ (gmProj T ⁻¹ᵁ offCentral T.toLine) :=
  fun _ hx => pointIncl_mem_proj_preimage T c hx

theorem appLE_appLE {Y Z Z' : Scheme.{0}} (g : Z ⟶ Y) (k : Z' ⟶ Z) {U : Y.Opens} {V : Z.Opens}
    {W : Z'.Opens} (e1 : V ≤ g ⁻¹ᵁ U) (e2 : W ≤ k ⁻¹ᵁ V) (x : Γ(Y, U)) :
    k.appLE V W e2 (g.appLE U V e1 x) = (k ≫ g).appLE U W (e2.trans (k.preimage_mono e1)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem resLE_eq_of_eq {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (U : Y.Opens)
    (V : Z.Opens) (e : V ≤ g ⁻¹ᵁ U) : g.resLE U V e = g'.resLE U V (hg ▸ e) := by
  subst hg
  rfl

/-! ### The action of a point -/

namespace GmAction

variable {T : TestConfiguration f a} (A : GmAction T)

/-- `σ_c : 𝓧 ⟶ 𝓧`, `x ↦ c · x`. -/
def actAt (c : ℂˣ) : T.space ⟶ T.space := pointIncl T c ≫ A.smulMap

/-- `σ_c^* t = c · t`. -/
theorem actAt_appTop_tFun (c : ℂˣ) :
    (A.actAt c).appTop (tFun T.toLine) =
      schemeGlobalConstants T.structureMap (c : ℂ) * tFun T.toLine := by
  have h : A.smulMap.appTop (tFun T.toLine) =
      (fst GmGroup T.overBase).left.appTop coordGm * (gmProj T).appTop (tFun T.toLine) :=
    A.smul_tFun
  rw [actAt, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h, map_mul,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, pointIncl_fst, pointIncl_proj, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, gmPoint_appTop_coordGm]
  rfl

/-- `σ_c` preserves `𝓧 ∖ 𝓧₀`. -/
theorem le_actAt_preimage (c : ℂˣ) : offCentral T.toLine ≤ A.actAt c ⁻¹ᵁ offCentral T.toLine :=
  fun _ hx => A.le_preimage_offCentral (pointIncl_mem_proj_preimage T c hx)

/-- `q ∘ σ_c = q` on `𝓧 ∖ 𝓧₀`. -/
theorem actAt_coord (c : ℂˣ) :
    (A.actAt c).resLE (offCentral T.toLine) (offCentral T.toLine) (A.le_actAt_preimage c) ≫
      T.coord = T.coord := by
  have h := congrArg (fun φ => (pointIncl T c).resLE _ _ (le_pointIncl_preimage T c) ≫ φ)
    A.coord_smul
  rw [Scheme.Hom.resLE_comp_resLE_assoc, Scheme.Hom.resLE_comp_resLE_assoc,
    resLE_eq_of_eq (pointIncl_proj T c), Scheme.Hom.resLE_id, Scheme.homOfLE_rfl,
    Category.id_comp] at h
  exact h

/-- `σ_c` preserves `q⁻¹(V)`. -/
theorem le_actAt_overOpen (c : ℂˣ) (V : X.Opens) :
    overOpen T.coord V ≤ A.actAt c ⁻¹ᵁ overOpen T.coord V := by
  rintro _ ⟨y, hy, rfl⟩
  let ρ := (A.actAt c).resLE (offCentral T.toLine) (offCentral T.toLine) (A.le_actAt_preimage c)
  have h1 : A.actAt c ((offCentral T.toLine).ι y) = (offCentral T.toLine).ι (ρ y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
  change A.actAt c ((offCentral T.toLine).ι y) ∈ (offCentral T.toLine).ι ''ᵁ (T.coord ⁻¹ᵁ V)
  rw [h1]
  refine ⟨ρ y, ?_, rfl⟩
  change (ρ ≫ T.coord) y ∈ V
  rw [A.actAt_coord c]
  exact hy

/-- `σ_c^♯ ∘ q^♯ = q^♯` on `q⁻¹(V)`. -/
theorem actAt_pullFun (c : ℂˣ) (V : X.Opens) (x : Γ(X, V)) :
    (A.actAt c).appLE (overOpen T.coord V) (overOpen T.coord V) (A.le_actAt_overOpen c V)
      (pullFun T.coord V x) = pullFun T.coord V x := by
  let ρ := (A.actAt c).resLE (offCentral T.toLine) (offCentral T.toLine) (A.le_actAt_preimage c)
  have hρ : ρ ≫ T.coord = T.coord := A.actAt_coord c
  have e' : T.coord ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ (T.coord ⁻¹ᵁ V) := by
    intro y hy
    change (ρ ≫ T.coord) y ∈ V
    rw [hρ]
    exact hy
  have key := congrArg (fun φ : Γ((offCentral T.toLine).toScheme, T.coord ⁻¹ᵁ V) ⟶
      Γ((offCentral T.toLine).toScheme, T.coord ⁻¹ᵁ V) => φ.hom (T.coord.app V x))
    (Scheme.Hom.resLE_appLE (A.actAt c) (A.le_actAt_preimage c) (T.coord ⁻¹ᵁ V)
      (T.coord ⁻¹ᵁ V) e')
  simp only at key
  have hp : pullFun T.coord V x = T.coord.app V x := by
    rw [TCEnc.pullFun, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  rw [hp]
  refine key.symm.trans ?_
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom hρ _ _ _ le_rfl]

/-- `σ_c^♯ t = c t` on `q⁻¹(V)`. -/
theorem actAt_tResOn (c : ℂˣ) (V : X.Opens) :
    (A.actAt c).appLE (overOpen T.coord V) (overOpen T.coord V) (A.le_actAt_overOpen c V)
      (tResOn T V) =
    T.space.presheaf.map (homOfLE le_top).op (schemeGlobalConstants T.structureMap (c : ℂ)) *
      tResOn T V := by
  rw [tResOn, appLE_of_res]
  change T.space.presheaf.map _ ((A.actAt c).appTop (tFun T.toLine)) = _
  rw [A.actAt_appTop_tFun, map_mul]

end GmAction

/-! ### The action of a point on sections -/

namespace GeomLinearization

variable {T : TestConfiguration f a} (Λ : GeomLinearization T)

theorem pullOpen_le_pointIncl (c : ℂˣ) (i j : T.extAtlas.I) :
    pullOpen T.extAtlas T.extAtlas (Λ.action.actAt c) i j ≤
      pointIncl T c ⁻¹ᵁ cechOpen T.extAtlas Λ.action.smulMap (gmProj T) i j := by
  rintro x ⟨hx1, hx2⟩
  refine ⟨hx1, ?_⟩
  change (pointIncl T c ≫ gmProj T) x ∈ T.extAtlas.opens j
  rw [pointIncl_proj]
  exact hx2

/-- The matrix coefficients `φ_{ij}(c) = ι_c^♯ φ_{ij}` of `Φ_c : σ_c^* 𝓛 ≅ 𝓛`. -/
def phiAt (c : ℂˣ) (i j : T.extAtlas.I) :
    Γ(T.space, pullOpen T.extAtlas T.extAtlas (Λ.action.actAt c) i j) :=
  (pointIncl T c).appLE _ _ (Λ.pullOpen_le_pointIncl c i j) ((Λ.phi i j : Γ(gmProd T, _)))

theorem phiAt_frame (c : ℂˣ) (k : a.I) : Λ.phiAt c (.inr k) (.inr k) = 1 := by
  rw [phiAt, Λ.phi_frame k, Units.val_one, map_one]

/-- `Φ_c : σ_c^* 𝓛 ⟶ 𝓛` is a Čech morphism. -/
theorem isCechHom_phiAt (c : ℂˣ) :
    IsCechHom T.extAtlas T.extAtlas (Λ.action.actAt c) (Λ.phiAt c) := by
  intro i i' j j'
  have hle : pullOverlap T.extAtlas T.extAtlas (Λ.action.actAt c) i i' j j' ≤
      pointIncl T c ⁻¹ᵁ cechOverlap T.extAtlas Λ.action.smulMap (gmProj T) i i' j j' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    change (pointIncl T c ≫ gmProj T) x ∈ T.extAtlas.opens j ⊓ T.extAtlas.opens j'
    rw [pointIncl_proj]
    exact hx2
  have h := congrArg ((pointIncl T c).appLE _ _ hle) (Λ.isCechIso i i' j j')
  rw [map_mul, map_mul, appLE_appLE, appLE_appLE, appLE_of_res, appLE_of_res,
    appLE_id_eq (pointIncl_proj T c)] at h
  rw [phiAt, phiAt, appLE_res, appLE_res]
  exact h

/-- **The action of `c ∈ ℂ^*` on sections**: `ρ_c(s) = Φ_c^m(σ_c^* s) ∈ H⁰(𝓧, 𝓛^m)`. -/
def actSection (c : ℂˣ) (m : ℕ) (s : SectionSpace T.structureMap T.line m) :
    SectionSpace T.structureMap T.line m :=
  Classical.choose (exists_cechPullSection T.extAtlas T.extAtlas (Λ.action.actAt c) (Λ.phiAt c)
    (Λ.isCechHom_phiAt c) m s)

/-- **On `𝓧 ∖ 𝓧₀` the action is `σ_c^*`**: the coefficients of `ρ_c(s)` in the frames `ε_k^m`
are `σ_c^♯` of those of `s`. -/
theorem epsCoeff_actSection (c : ℂˣ) (m : ℕ) (s : SectionSpace T.structureMap T.line m)
    (k : a.I) :
    T.epsCoeff m k (Λ.actSection c m s) =
      (Λ.action.actAt c).appLE (overOpen T.coord (a.opens k)) (overOpen T.coord (a.opens k))
        (Λ.action.le_actAt_overOpen c _) (T.epsCoeff m k s) := by
  have hs := Classical.choose_spec (exists_cechPullSection T.extAtlas T.extAtlas
    (Λ.action.actAt c) (Λ.phiAt c) (Λ.isCechHom_phiAt c) m s) (.inr k) (.inr k)
  rw [Λ.phiAt_frame c k, one_pow, mul_one] at hs
  have hle : overOpen T.coord (a.opens k) ≤
      pullOpen T.extAtlas T.extAtlas (Λ.action.actAt c) (.inr k) (.inr k) :=
    le_inf (Λ.action.le_actAt_overOpen c _) le_rfl
  have h := congrArg (T.space.presheaf.map (homOfLE hle).op) hs
  rw [presheaf_map_map] at h
  erw [res_self] at h
  rw [appLE_res] at h
  exact h

end GeomLinearization

end SGPT.TestCurve.GeomLin
