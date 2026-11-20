import SGPT.TestCurve.TCEncDef

/-!
# The filtration induced by a test configuration

Source: `rmk:PhongSturm`, `rmk:NApotential:L862` (*"the filtration induced by a test
configuration"*); [BHJ17, §2.5], [RWN14, §8]: for a test configuration `(𝓧, 𝓛)` of `(X, L)`,

`𝓕^λ H⁰(X, L^m) = {s : t^{-λ} s̄ extends to a section of 𝓛^m on 𝓧}`, `λ ∈ ℤ`,

where `s̄ = q^* s` is the `𝔾_m`-invariant extension of `s` to `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`.

## Main definitions

* `TestConfiguration.extAtlas`: the atlas of `𝓛` made of the given atlas and the frames
  `ε_j = q^* e_j` over `q⁻¹(V_j)`.
* `TestConfiguration.piece λ m`: the subspace `𝓕^λ H⁰(X, L^m)`: the sections `s` such that some
  `σ ∈ H⁰(𝓧, 𝓛^m)` has coefficient `t^{-λ} q^♯(s_j)` in the frame `ε_j^m` for every `j` (so that
  `σ|_{𝓧 ∖ 𝓧₀} = t^{-λ} s̄`).

## Main results

* `piece_anti`: `𝓕^λ ⊇ 𝓕^{λ'}` for `λ ≤ λ'` (multiplication by `t`);
* `mul_mem_piece`: `𝓕^λ_m · 𝓕^{λ'}_{m'} ⊆ 𝓕^{λ+λ'}_{m+m'}`;
* `piece_zero_zero`: `𝓕⁰ H⁰(X, 𝒪_X) = H⁰(X, 𝒪_X)` for `X` integral and proper over `ℂ`
  (via `schemeGlobalConstants_surjective`: `H⁰(X, 𝒪_X) = ℂ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite

/-! ### Global functions on a proper integral scheme are constant -/

/-- On an integral scheme universally closed over `ℂ`, every global regular function is
constant: `H⁰(X, 𝒪_X) = ℂ` (Mathlib's integrality of `Γ(X, 𝒪_X)` over `ℂ`, and `ℂ` algebraically
closed). -/
theorem schemeGlobalConstants_surjective {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    [UniversallyClosed f] : Function.Surjective (schemeGlobalConstants f) := by
  have hint : (schemeGlobalConstants f).IsIntegral := by
    have h := isIntegral_appTop_of_universallyClosed f
    have e : schemeGlobalConstants f =
        f.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom := rfl
    rw [e]
    exact RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective) h
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ hint).2

/-! ### Pull-back of functions along the identification -/

section Pull

variable {Y X : Scheme.{0}} {π : Y ⟶ AffineLine} (q : (offCentral π).toScheme ⟶ X)

/-- `q^♯` is compatible with restrictions (morphism form). -/
theorem pullFun_restrict_hom {V V' : X.Opens} (h : V' ≤ V) :
    X.presheaf.map (homOfLE h).op ≫ pullFun q V' =
      pullFun q V ≫ Y.presheaf.map (homOfLE (overOpen_mono q h)).op := by
  simp only [pullFun]
  rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, Scheme.Hom.appIso_inv_naturality,
    ← Category.assoc]
  rfl

/-- `q^♯` is compatible with restrictions. -/
theorem pullFun_restrict {V V' : X.Opens} (h : V' ≤ V) (x : Γ(X, V)) :
    pullFun q V' (X.presheaf.map (homOfLE h).op x) =
      Y.presheaf.map (homOfLE (overOpen_mono q h)).op (pullFun q V x) := by
  rw [← CommRingCat.comp_apply, pullFun_restrict_hom, CommRingCat.comp_apply]

/-- `q^♯` of the restriction of a global function `g^♯ y`, when `q ≫ g = ι ≫ g'`
(morphism form). -/
theorem pullFun_appTop_hom {S : Scheme.{0}} {g : X ⟶ S} {g' : Y ⟶ S}
    (hg : q ≫ g = (offCentral π).ι ≫ g') (V : X.Opens) :
    g.appTop ≫ X.presheaf.map (homOfLE le_top).op ≫ pullFun q V =
      g'.appTop ≫ Y.presheaf.map (homOfLE le_top).op := by
  simp only [pullFun]
  rw [← Category.assoc (X.presheaf.map _), Scheme.Hom.naturality, ← Category.assoc,
    ← Category.assoc]
  have h1 : g.appTop ≫ q.app ⊤ = g'.appTop ≫ (offCentral π).ι.app ⊤ := by
    have := congrArg (fun φ => Scheme.Hom.appTop φ) hg
    simpa [Scheme.Hom.comp_appTop] using this
  rw [h1]
  simp only [Category.assoc]
  rw [Scheme.Hom.appIso_inv_naturality]
  have h2 := Scheme.Hom.app_appIso_inv (offCentral π).ι ⊤
  erw [reassoc_of% h2, ← Functor.map_comp]
  rfl

/-- `q^♯` of the restriction of a global function `g^♯ y`, when `q ≫ g = ι ≫ g'`. -/
theorem pullFun_appTop {S : Scheme.{0}} {g : X ⟶ S} {g' : Y ⟶ S}
    (hg : q ≫ g = (offCentral π).ι ≫ g') (V : X.Opens) (y : Γ(S, ⊤)) :
    pullFun q V (X.presheaf.map (homOfLE le_top).op (g.appTop y)) =
      Y.presheaf.map (homOfLE le_top).op (g'.appTop y) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    pullFun_appTop_hom q hg V]

end Pull

/-! ### The filtration -/

namespace TestConfiguration

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-- The atlas of `𝓛` made of the given charts and of the frames `ε_j = q^* e_j` over
`q⁻¹(V_j)`. -/
def extAtlas : LineBundleAtlas T.line where
  I := T.atlas.I ⊕ a.I
  opens := Sum.elim T.atlas.opens fun j => overOpen T.coord (a.opens j)
  covers x := by
    obtain ⟨i, hi⟩ := T.atlas.covers x
    exact ⟨Sum.inl i, hi⟩
  frame
    | .inl i => T.atlas.frame i
    | .inr j => T.frame j

/-- The coefficient of `σ ∈ H⁰(𝓧, 𝓛^m)` in the frame `ε_j^m` over `q⁻¹(V_j)`. -/
def epsCoeff (m : ℕ) (j : a.I) (σ : SectionSpace T.structureMap T.line m) :
    Γ(T.space, overOpen T.coord (a.opens j)) :=
  atlasPowerGlobalCoefficients T.extAtlas m (Sum.inr j) σ

/-- The restriction of `t` to `q⁻¹(V_j) ⊆ 𝓧 ∖ 𝓧₀`. -/
def tRes (j : a.I) : Γ(T.space, overOpen T.coord (a.opens j)) :=
  T.space.presheaf.map (homOfLE le_top).op (tFun T.toLine)

theorem tRes_isUnit (j : a.I) : IsUnit (T.tRes j) := by
  have h := T.space.toRingedSpace.isUnit_res_basicOpen (tFun T.toLine)
  have e : T.tRes j = (T.space.presheaf.map
      (homOfLE (overOpen_le_offCentral T.coord (a.opens j))).op)
      ((T.space.presheaf.map (homOfLE (T.space.basicOpen_le (tFun T.toLine))).op)
        (tFun T.toLine)) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e]
  exact h.map _

/-- `t` is invertible on `q⁻¹(V_j)`. -/
def tUnit (j : a.I) : (Γ(T.space, overOpen T.coord (a.opens j)))ˣ := (T.tRes_isUnit j).unit

@[simp] theorem tUnit_val (j : a.I) : (T.tUnit j).val = T.tRes j :=
  rfl

/-- The condition "`σ|_{𝓧 ∖ 𝓧₀} = t^{-λ} s̄`", in coefficients: the coefficient of `σ` in
`ε_j^m` is `t^{-λ} q^♯(s_j)`. -/
def Extends (lam : ℤ) (m : ℕ) (s : SectionSpace f L m)
    (σ : SectionSpace T.structureMap T.line m) : Prop :=
  ∀ j : a.I, T.epsCoeff m j σ =
    (T.tUnit j ^ (-lam)).val *
      pullFun T.coord (a.opens j) (atlasPowerGlobalCoefficients a m j s)

theorem coord_over' : T.coord ≫ f = (offCentral T.toLine).ι ≫ T.structureMap :=
  T.coord_over

/-- **The filtration induced by the test configuration** ([BHJ17, §2.5], [RWN14, §8]):
`𝓕^λ H⁰(X, L^m) = {s : t^{-λ} s̄ extends to a section of 𝓛^m on 𝓧}`. -/
def piece (lam : ℤ) (m : ℕ) : Submodule ℂ (SectionSpace f L m) where
  carrier := {s | ∃ σ, T.Extends lam m s σ}
  zero_mem' := ⟨0, fun j => by
    simp only [epsCoeff]
    rw [atlasPowerGlobalCoefficients_zero, atlasPowerGlobalCoefficients_zero, map_zero, mul_zero]⟩
  add_mem' := by
    rintro s s' ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    refine ⟨σ + σ', fun j => ?_⟩
    have e1 := hσ j
    have e2 := hσ' j
    simp only [epsCoeff] at e1 e2 ⊢
    erw [atlasPowerGlobalCoefficients_add, atlasPowerGlobalCoefficients_add]
    rw [e1, e2, map_add, mul_add]
  smul_mem' := by
    rintro c s ⟨σ, hσ⟩
    refine ⟨c • σ, fun j => ?_⟩
    have e1 := hσ j
    simp only [epsCoeff] at e1 ⊢
    rw [SectionSpace.atlasPowerGlobalCoefficients_smul_const,
      SectionSpace.atlasPowerGlobalCoefficients_smul_const, e1, map_mul]
    have hc := pullFun_appTop T.coord T.coord_over' (a.opens j)
      ((Scheme.ΓSpecIso (.of ℂ)).inv c)
    erw [hc]
    simp only [schemeGlobalConstants]
    rw [mul_left_comm]
    rfl

theorem mem_piece {lam : ℤ} {m : ℕ} {s : SectionSpace f L m} :
    s ∈ T.piece lam m ↔ ∃ σ, T.Extends lam m s σ := Iff.rfl

/-- Multiplication by `tⁿ`: if `σ` extends `t^{-λ'} s̄`, then `tⁿ σ` extends `t^{-(λ'-n)} s̄`. -/
theorem extends_tpow {lam : ℤ} {m : ℕ} {s : SectionSpace f L m}
    {σ : SectionSpace T.structureMap T.line m} (h : T.Extends lam m s σ) (n : ℕ) :
    T.Extends (lam - n) m s
      (show SectionSpace T.structureMap T.line m from
        (tFun T.toLine ^ n) • (show bundlePowerGlobalSections T.line m from σ)) := by
  intro j
  have e1 := h j
  simp only [epsCoeff] at e1 ⊢
  rw [atlasPowerGlobalCoefficients_smul, e1, ← mul_assoc]
  congr 1
  have ht : T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine ^ n) =
      (T.tUnit j ^ (n : ℤ)).val := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, tUnit_val, map_pow]
    rfl
  erw [ht]
  rw [← Units.val_mul, ← zpow_add]
  congr 2
  ring

/-- **`𝓕` is decreasing**: `𝓕^{λ'} ⊆ 𝓕^λ` for `λ ≤ λ'`. -/
theorem piece_anti {lam lam' : ℤ} (hle : lam ≤ lam') (m : ℕ) :
    T.piece lam' m ≤ T.piece lam m := by
  rintro s ⟨σ, hσ⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, lam' - n = lam := ⟨(lam' - lam).toNat, by omega⟩
  exact ⟨_, hn ▸ T.extends_tpow hσ n⟩

/-- **`𝓕` is multiplicative**: `𝓕^λ_m · 𝓕^{λ'}_{m'} ⊆ 𝓕^{λ+λ'}_{m+m'}`. -/
theorem mul_mem_piece {lam lam' : ℤ} {m m' : ℕ} {s : SectionSpace f L m}
    {s' : SectionSpace f L m'} (hs : s ∈ T.piece lam m) (hs' : s' ∈ T.piece lam' m') :
    SectionSpace.mul f a m m' s s' ∈ T.piece (lam + lam') (m + m') := by
  obtain ⟨σ, hσ⟩ := hs
  obtain ⟨σ', hσ'⟩ := hs'
  refine ⟨SectionSpace.mul T.structureMap T.extAtlas m m' σ σ', fun j => ?_⟩
  have e1 := hσ j
  have e2 := hσ' j
  simp only [epsCoeff] at e1 e2 ⊢
  rw [SectionSpace.coefficients_mul, SectionSpace.coefficients_mul, e1, e2, map_mul,
    neg_add, zpow_add, Units.val_mul]
  ring

/-- **Normalization**: `𝓕⁰ H⁰(X, 𝒪_X) = H⁰(X, 𝒪_X)` when `X` is integral and universally closed
over `ℂ` (every global function is a constant, which extends to `𝓧`). -/
theorem piece_zero_zero [IsIntegral X] [UniversallyClosed f] : T.piece 0 0 = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨c, hc⟩ := schemeGlobalConstants_surjective f (show Γ(X, ⊤) from s)
  refine ⟨show SectionSpace T.structureMap T.line 0 from schemeGlobalConstants T.structureMap c,
    fun j => ?_⟩
  simp only [epsCoeff, neg_zero, zpow_zero, Units.val_one, one_mul]
  rw [atlasPowerGlobalCoefficients_degree_zero, atlasPowerGlobalCoefficients_degree_zero]
  rw [show (show Γ(X, ⊤) from s) = schemeGlobalConstants f c from hc.symm]
  exact (pullFun_appTop T.coord T.coord_over' (a.opens j)
    ((Scheme.ΓSpecIso (.of ℂ)).inv c)).symm

end TestConfiguration

end SGPT.TestCurve.TCEnc
