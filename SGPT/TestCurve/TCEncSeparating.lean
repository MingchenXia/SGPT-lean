import SGPT.TestCurve.TCEncFiltration
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Filtration

/-!
# The filtration of a test configuration is separating

Source: `rmk:PhongSturm`, `rmk:NApotential:L862` ([BHJ17, §2.5]: the filtration induced by a test
configuration is a `ℤ`-filtration). For an integral test configuration `(𝓧, 𝓛)` of `(X, L)` with
`X ≠ ∅` and `H⁰(X, L^m)` finite dimensional we prove `𝓕^μ H⁰(X, L^m) = 0` for `μ ≫ 0`.

## Proof

* `eq_zero_of_atlasCoeff_eq_zero`: on an integral scheme a section of a line bundle vanishing on
  a nonempty open is zero; in particular `σ ∈ H⁰(𝓧, 𝓛^m)` is determined by `σ|_{𝓧 ∖ 𝓧₀}`.
* `exists_not_mem_offCentral`: the central fibre is nonempty (`π` is proper, hence closed, and
  its image contains `𝔾_m`, which is dense in `𝔸¹`).
* If `s ∈ 𝓕^λ` for all `λ`, with `σ_λ` extending `t^{-λ} s̄`, then `σ_0 = t^k σ_k`; at a point `x`
  of the central fibre the germ of `σ_0` lies in `⋂_k (t_x)^k 𝒪_{𝓧,x} = 0` (Krull's intersection
  theorem in the noetherian local ring `𝒪_{𝓧,x}`), so `σ_0 = 0`, hence `q^♯ s = 0` and `s = 0`
  (`q` is scheme-theoretically dominant, being a base change of `𝔾_m → Spec ℂ`).
* A decreasing chain of subspaces of a finite-dimensional space stabilizes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite

/-! ### Sections of line bundles on integral schemes -/

section General

variable {Z : Scheme.{0}} {M : Z.Modules}

/-- On an integral scheme, a section of `M^m` whose coefficient vanishes on one nonempty chart of
an atlas is zero. -/
theorem eq_zero_of_atlasCoeff_eq_zero [IsIntegral Z] (b : LineBundleAtlas M) (m : ℕ)
    (σ : bundlePowerGlobalSections M m) (i₀ : b.I) (hne : (b.opens i₀ : Set Z).Nonempty)
    (h : atlasPowerGlobalCoefficients b m i₀ σ = 0) : σ = 0 := by
  apply atlasPowerGlobalCoefficients_ext b m
  intro i
  rw [atlasPowerGlobalCoefficients_zero]
  by_cases hV : (b.opens i : Set Z).Nonempty
  · obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (b.opens i).isOpen (b.opens i₀).isOpen hV hne
    have : Nonempty (b.opens i ⊓ b.opens i₀ : Z.Opens) := ⟨⟨x, hx⟩⟩
    apply map_injective_of_isIntegral (X := Z)
      (homOfLE (inf_le_left : b.opens i ⊓ b.opens i₀ ≤ b.opens i))
    rw [map_zero]
    have htr := LocalBundleFrame.global_coefficients_transition (b.frame i₀) (b.frame i)
      (homOfLE (inf_le_right : b.opens i ⊓ b.opens i₀ ≤ b.opens i₀))
      (homOfLE (inf_le_left : b.opens i ⊓ b.opens i₀ ≤ b.opens i)) m σ
    change Z.sheaf.obj.map _ (atlasPowerGlobalCoefficients b m i σ) =
      _ * Z.sheaf.obj.map _ (atlasPowerGlobalCoefficients b m i₀ σ) at htr
    rw [h, map_zero, mul_zero] at htr
    exact htr
  · apply TopCat.Presheaf.IsSheaf.section_ext Z.sheaf.property
    intro x hx
    exact absurd ⟨x, hx⟩ hV

end General

/-! ### The affine line -/

theorem coordT_eq : coordT = (Scheme.ΓSpecIso (.of (Polynomial ℂ))).inv Polynomial.X := rfl

theorem mem_gmOpen (x : AffineLine) :
    x ∈ gmOpen ↔ Polynomial.X ∉ (show PrimeSpectrum (Polynomial ℂ) from x).asIdeal := by
  change x ∈ AffineLine.basicOpen coordT ↔ _
  rw [coordT_eq, basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The generic point `(0)` of `𝔸¹` lies in `𝔾_m`. -/
def gmPoint : gmOpen.toScheme :=
  ⟨show AffineLine from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Polynomial ℂ)), by
    rw [mem_gmOpen]
    exact fun h => Polynomial.X_ne_zero ((Submodule.mem_bot (Polynomial ℂ)).mp h)⟩

/-- The origin `(t) ∈ 𝔸¹`, which is not in `𝔾_m`. -/
def originPoint : AffineLine :=
  show AffineLine from (⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩ :
      PrimeSpectrum (Polynomial ℂ))

theorem originPoint_not_mem : originPoint ∉ gmOpen := by
  rw [mem_gmOpen, not_not]
  exact Ideal.subset_span rfl

instance : IsAffine gmOpen.toScheme :=
  (isAffineOpen_top AffineLine).basicOpen coordT

/-- `𝔾_m ⟶ Spec ℂ`. -/
abbrev gmToBase : gmOpen.toScheme ⟶ Spec (.of ℂ) := gmOpen.ι ≫ affineLineToBase

instance : Surjective gmToBase :=
  ⟨fun _ => ⟨gmPoint, Subsingleton.elim _ _⟩⟩

instance : QuasiCompact gmToBase :=
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact).mpr inferInstance

instance : IsSchemeTheoreticallyDominant gmToBase :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-! ### Consequences of the identification `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m` -/

namespace TestConfiguration

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

theorem coord_eq : T.coord = pullback.lift (f := f) (g := gmToBase) T.coord (toGm T.toLine)
    (by rw [T.coord_over, ← Category.assoc, ← toGm_comp_ι, Category.assoc]) ≫
      pullback.fst f gmToBase :=
  (pullback.lift_fst _ _ _).symm

theorem toGm_eq : toGm T.toLine = pullback.lift (f := f) (g := gmToBase) T.coord (toGm T.toLine)
    (by rw [T.coord_over, ← Category.assoc, ← toGm_comp_ι, Category.assoc]) ≫
      pullback.snd f gmToBase :=
  (pullback.lift_snd _ _ _).symm

instance coord_surjective : Surjective T.coord := by
  have := T.coord_isIso
  rw [T.coord_eq]
  have : Surjective (pullback.fst f gmToBase) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (Surjective gmToBase))
  infer_instance

instance coord_quasiCompact : QuasiCompact T.coord := by
  have := T.coord_isIso
  rw [T.coord_eq]
  infer_instance

instance coord_isSchemeTheoreticallyDominant : IsSchemeTheoreticallyDominant T.coord := by
  have := T.coord_isIso
  rw [T.coord_eq]
  infer_instance

/-- `q^♯` is injective: `q` is scheme-theoretically dominant (a base change of
`𝔾_m → Spec ℂ`). -/
theorem pullFun_injective (V : X.Opens) : Function.Injective (pullFun T.coord V) := by
  intro x y h
  apply T.coord.app_injective V
  exact ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).commRingCatIsoToRingEquiv.symm.injective h

theorem toGm_surjective [Nonempty X] : Function.Surjective (toGm T.toLine).base := by
  have := T.coord_isIso
  have hf : Surjective f := ⟨fun _ => ⟨Classical.arbitrary X, Subsingleton.elim _ _⟩⟩
  have : Surjective (pullback.snd f gmToBase) := MorphismProperty.pullback_snd _ _ hf
  have h : Surjective (toGm T.toLine) := by
    rw [T.toGm_eq]
    infer_instance
  exact h.surj

/-- **The central fibre is nonempty**: `π` is proper, hence closed, and its image contains the
dense open `𝔾_m ⊆ 𝔸¹`. -/
theorem exists_not_mem_offCentral [Nonempty X] : ∃ x : T.space, x ∉ offCentral T.toLine := by
  have hclosed : IsClosed (Set.range T.toLine.base) := T.toLine.isClosedMap.isClosed_range
  have hsub : (gmOpen : Set AffineLine) ⊆ Set.range T.toLine.base := by
    intro y hy
    obtain ⟨u, hu⟩ := T.toGm_surjective ⟨y, hy⟩
    refine ⟨(offCentral T.toLine).ι.base u, ?_⟩
    have := congrArg (fun φ => φ.base u) (toGm_comp_ι T.toLine)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [← this, hu]
    rfl
  have hdense : Dense (gmOpen : Set AffineLine) :=
    gmOpen.isOpen.dense ⟨_, gmPoint.2⟩
  have huniv : Set.range T.toLine.base = Set.univ := by
    rw [← hclosed.closure_eq]
    exact Set.eq_univ_of_univ_subset (hdense.closure_eq ▸ closure_mono hsub)
  obtain ⟨x, hx⟩ : originPoint ∈ Set.range T.toLine.base := huniv ▸ Set.mem_univ _
  refine ⟨x, fun hxU => originPoint_not_mem ?_⟩
  rw [offCentral_eq] at hxU
  rw [← hx]
  exact hxU

/-- Some frame chart `q⁻¹(V_j)` is nonempty (`q` is surjective). -/
theorem exists_nonempty_overOpen [Nonempty X] :
    ∃ j : a.I, (overOpen T.coord (a.opens j) : Set T.space).Nonempty := by
  obtain ⟨j, hj⟩ := a.covers (Classical.arbitrary X)
  obtain ⟨u, hu⟩ := T.coord_surjective.surj (Classical.arbitrary X)
  refine ⟨j, (offCentral T.toLine).ι.base u, Set.mem_image_of_mem _ ?_⟩
  change T.coord.base u ∈ a.opens j
  rw [hu]
  exact hj

theorem epsCoeff_sub {m : ℕ} (j : a.I) (σ σ' : SectionSpace T.structureMap T.line m) :
    T.epsCoeff m j (σ - σ') = T.epsCoeff m j σ - T.epsCoeff m j σ' := by
  rw [eq_sub_iff_add_eq]
  simp only [epsCoeff]
  rw [← atlasPowerGlobalCoefficients_add]
  congr 1
  exact sub_add_cancel σ σ'

/-- **Sections are determined by their restriction to `𝓧 ∖ 𝓧₀`** (`𝓧` integral). -/
theorem eq_of_epsCoeff_eq [IsIntegral T.space] [Nonempty X] {m : ℕ}
    {σ σ' : SectionSpace T.structureMap T.line m}
    (h : ∀ j, T.epsCoeff m j σ = T.epsCoeff m j σ') : σ = σ' := by
  obtain ⟨j, hj⟩ := T.exists_nonempty_overOpen
  have h0 := eq_zero_of_atlasCoeff_eq_zero T.extAtlas m
    (show bundlePowerGlobalSections T.line m from σ - σ') (Sum.inr j) hj
    (by
      have := T.epsCoeff_sub j σ σ'
      rw [h j, sub_self] at this
      exact this)
  exact sub_eq_zero.mp h0

/-- **Separation**: on an integral test configuration, a section lying in every `𝓕^λ` is zero.
If `σ_λ` extends `t^{-λ} s̄`, then `σ_0 = t^k σ_k` for all `k`; at a point `x` of the central fibre
the germ of `σ_0` lies in `⋂_k (t_x)^k = 0` (Krull), so `σ_0 = 0` and `q^♯ s = 0`. -/
theorem eq_zero_of_forall_mem_piece [IsIntegral T.space] [Nonempty X] {m : ℕ}
    {s : SectionSpace f L m} (hs : ∀ lam : ℤ, s ∈ T.piece lam m) : s = 0 := by
  have : IsLocallyNoetherian T.space := LocallyOfFiniteType.isLocallyNoetherian T.toLine
  choose σ hσ using fun k : ℕ => hs k
  -- `σ 0 = t^k σ k`
  have hk : ∀ k : ℕ, σ 0 = (show SectionSpace T.structureMap T.line m from
      (tFun T.toLine ^ k) • (show bundlePowerGlobalSections T.line m from σ k)) := by
    intro k
    apply T.eq_of_epsCoeff_eq
    intro j
    have h1 := hσ 0 j
    have h2 := T.extends_tpow (hσ k) k j
    rw [h1, h2]
    congr 3
    push_cast
    ring
  -- a point of the central fibre
  obtain ⟨x, hx⟩ := T.exists_not_mem_offCentral
  obtain ⟨i, hi⟩ := T.atlas.covers x
  set g := T.space.presheaf.germ (T.atlas.opens i) x hi with hg
  set τx := g (T.space.presheaf.map (homOfLE le_top).op (tFun T.toLine)) with hτx
  have hτ : ¬ IsUnit τx := by
    rw [Scheme.mem_basicOpen_top] at hx
    intro hu
    apply hx
    rw [hτx, hg, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_res] at hu
    exact hu
  set I : Ideal (T.space.presheaf.stalk x) := Ideal.span {τx} with hI
  have hItop : I ≠ ⊤ := by
    rw [hI, Ne, Ideal.span_singleton_eq_top]
    exact hτ
  set c := atlasPowerGlobalCoefficients T.atlas m i (σ 0) with hc
  have hmem : g c ∈ ⨅ k : ℕ, I ^ k := by
    rw [Submodule.mem_iInf]
    intro k
    have e : c = T.space.sheaf.obj.map (homOfLE le_top).op (tFun T.toLine ^ k) *
        atlasPowerGlobalCoefficients T.atlas m i (σ k) := by
      rw [hc, hk k]
      exact atlasPowerGlobalCoefficients_smul T.atlas m i _ _
    rw [e, map_mul, map_pow, map_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ k)
    exact Ideal.subset_span rfl
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing I hItop, Submodule.mem_bot] at hmem
  have hc0 : c = 0 := germ_injective_of_isIntegral T.space x hi (by rw [hmem, map_zero])
  have hσ0 : σ 0 = 0 := eq_zero_of_atlasCoeff_eq_zero T.atlas m _ i ⟨x, hi⟩ hc0
  -- hence `q^♯ s_j = 0` and `s = 0`
  apply atlasPowerGlobalCoefficients_ext a m
  intro j
  rw [atlasPowerGlobalCoefficients_zero]
  apply T.pullFun_injective (a.opens j)
  have h1 := hσ 0 j
  rw [hσ0] at h1
  simp only [epsCoeff, Nat.cast_zero, neg_zero, zpow_zero, Units.val_one, one_mul] at h1
  rw [map_zero, ← h1]
  exact atlasPowerGlobalCoefficients_zero _ _ _

/-- **`𝓕` is separating**: for an integral test configuration of `(X, L)` with `X ≠ ∅` and
`H⁰(X, L^m)` finite dimensional, `𝓕^μ H⁰(X, L^m) = 0` for some `μ`. -/
theorem exists_piece_eq_bot [IsIntegral T.space] [Nonempty X] (m : ℕ)
    [FiniteDimensional ℂ (SectionSpace f L m)] : ∃ μ : ℤ, T.piece μ m = ⊥ := by
  let F : ℕ →o (Submodule ℂ (SectionSpace f L m))ᵒᵈ :=
    ⟨fun k => OrderDual.toDual (T.piece k m), fun k k' h => T.piece_anti (by exact_mod_cast h) m⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes F
  refine ⟨n, eq_bot_iff.mpr fun s hs => (Submodule.mem_bot ℂ).mpr ?_⟩
  apply T.eq_zero_of_forall_mem_piece
  intro lam
  rcases le_or_gt lam n with h | h
  · exact T.piece_anti h m hs
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, lam = k := ⟨lam.toNat, by omega⟩
    have := hn k (by exact_mod_cast h.le)
    have e : T.piece n m = T.piece k m := congrArg OrderDual.ofDual this
    exact e ▸ hs

end TestConfiguration

end SGPT.TestCurve.TCEnc
