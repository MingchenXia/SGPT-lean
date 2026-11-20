import SGPT.TestCurve.TCLinPoints
import SGPT.TestCurve.TCLinChartRing
import SGPT.TestCurve.TCEncSeparating
import SGPT.TestCurve.FGRelDivision

/-!
# Laurent expansions of functions on `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`

Let `(𝓧, 𝓛)` be a test configuration of `(X, L)` (the encoding), with
`q : 𝓧 ∖ 𝓧₀ ⟶ X` and `(q, π) : 𝓧 ∖ 𝓧₀ ≅ X ×_ℂ 𝔾_m`. For an open `V ⊆ X` the regular functions
on `q⁻¹(V) ≅ V × 𝔾_m` are the Laurent polynomials in `t` with coefficients in `Γ(X, V)`
(the Künneth formula `Γ(V × 𝔾_m) = Γ(V) ⊗_ℂ ℂ[t, t⁻¹]`):

* `laurentSum V b = Σ_n tⁿ q^♯(b_n)` for `b : ℤ →₀ Γ(X, V)`;
* `laurentSum_injective`: the expansion is unique (evaluation at the points of `𝔾_m`, lane TC-LIN);
* `laurentSum_surjective_of_isAffineOpen`: every function on `q⁻¹(V)` is a Laurent sum, for `V`
  affine (`Γ(V ×_ℂ 𝔾_m)` is the pushout `Γ(V) ⊗_ℂ Γ(𝔾_m)`, Mathlib's
  `isIso_pushoutSection_of_isAffineOpen`, and `Γ(𝔾_m) = ℂ[t]_t`);
* `laurentSum_surjective`: the same for every open `V` of an integral `X` (gluing the
  coefficients over an affine cover; integrality bounds the support).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Opposite SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  (T : TestConfiguration f a)

/-! ### The coordinate `t` on `q⁻¹(V)` -/

/-- The restriction of `t ∘ π` to `q⁻¹(V)`. -/
def tResOn (V : X.Opens) : Γ(T.space, overOpen T.coord V) :=
  T.space.presheaf.map (homOfLE le_top).op (tFun T.toLine)

theorem tResOn_isUnit (V : X.Opens) : IsUnit (tResOn T V) := by
  have h := T.space.toRingedSpace.isUnit_res_basicOpen (tFun T.toLine)
  have e : tResOn T V = (T.space.presheaf.map
      (homOfLE (overOpen_le_offCentral T.coord V)).op)
      ((T.space.presheaf.map (homOfLE (T.space.basicOpen_le (tFun T.toLine))).op)
        (tFun T.toLine)) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [e]
  exact h.map _

/-- `t` as a unit on `q⁻¹(V)`. -/
def tUnitOn (V : X.Opens) : (Γ(T.space, overOpen T.coord V))ˣ := (tResOn_isUnit T V).unit

@[simp] theorem tUnitOn_val (V : X.Opens) : (tUnitOn T V).val = tResOn T V := rfl

theorem tUnitOn_chart (j : a.I) : tUnitOn T (a.opens j) = T.tUnit j := Units.ext rfl

/-- `t` restricts to `t`. -/
theorem tUnitOn_restrict {V V' : X.Opens} (h : V' ≤ V) :
    Units.map (T.space.presheaf.map (homOfLE (overOpen_mono T.coord h)).op).hom.toMonoidHom
      (tUnitOn T V) = tUnitOn T V' := by
  ext
  change T.space.presheaf.map _ (tResOn T V) = tResOn T V'
  exact presheaf_map_map _ _ _

theorem tUnitOn_zpow_restrict {V V' : X.Opens} (h : V' ≤ V) (n : ℤ) :
    T.space.presheaf.map (homOfLE (overOpen_mono T.coord h)).op ((tUnitOn T V ^ n).val) =
      (tUnitOn T V' ^ n).val := by
  rw [← tUnitOn_restrict T h, ← map_zpow]
  rfl

/-! ### Laurent sums -/

/-- **The Laurent sum** `Σ_n tⁿ q^♯(b_n)` on `q⁻¹(V)`, for `b : ℤ →₀ Γ(X, V)`. -/
def laurentSum (V : X.Opens) : (ℤ →₀ Γ(X, V)) →+ Γ(T.space, overOpen T.coord V) :=
  Finsupp.liftAddHom fun n =>
    (AddMonoidHom.mulLeft ((tUnitOn T V ^ n).val)).comp
      (pullFun T.coord V).hom.toAddMonoidHom

theorem laurentSum_apply (V : X.Opens) (b : ℤ →₀ Γ(X, V)) :
    laurentSum T V b = b.sum fun n r => (tUnitOn T V ^ n).val * pullFun T.coord V r :=
  rfl

@[simp] theorem laurentSum_single (V : X.Opens) (n : ℤ) (r : Γ(X, V)) :
    laurentSum T V (Finsupp.single n r) = (tUnitOn T V ^ n).val * pullFun T.coord V r := by
  rw [laurentSum, Finsupp.liftAddHom_apply_single]
  rfl

/-- A Laurent sum over a finite set containing the support. -/
theorem laurentSum_eq_sum (V : X.Opens) (b : ℤ →₀ Γ(X, V)) {S : Finset ℤ}
    (hS : b.support ⊆ S) :
    laurentSum T V b = ∑ n ∈ S, (tUnitOn T V ^ n).val * pullFun T.coord V (b n) := by
  rw [laurentSum_apply, Finsupp.sum_of_support_subset b hS]
  intro n _
  rw [map_zero, mul_zero]

/-- Laurent sums restrict to Laurent sums. -/
theorem laurentSum_restrict {V V' : X.Opens} (h : V' ≤ V) (b : ℤ →₀ Γ(X, V)) :
    T.space.presheaf.map (homOfLE (overOpen_mono T.coord h)).op (laurentSum T V b) =
      laurentSum T V' (b.mapRange (X.presheaf.map (homOfLE h).op) (map_zero _)) := by
  classical
  rw [laurentSum_eq_sum T V b subset_rfl,
    laurentSum_eq_sum T V' _ (Finsupp.support_mapRange), map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, tUnitOn_zpow_restrict T h, Finsupp.mapRange_apply, pullFun_restrict]

/-- Multiplication by `q^♯ r`. -/
theorem pullFun_mul_laurentSum (V : X.Opens) (r : Γ(X, V)) (b : ℤ →₀ Γ(X, V)) :
    pullFun T.coord V r * laurentSum T V b =
      laurentSum T V (b.mapRange (r * ·) (mul_zero r)) := by
  classical
  rw [laurentSum_eq_sum T V b subset_rfl,
    laurentSum_eq_sum T V _ (Finsupp.support_mapRange), Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finsupp.mapRange_apply, map_mul]
  ring

/-! ### Uniqueness -/

/-- **Uniqueness of the Laurent expansion** on `q⁻¹(V)`, for every open `V ⊆ X`: evaluation at
`t = c` for all `c ∈ ℂ^*` and independence of the characters `c ↦ cⁿ`. -/
theorem laurentSum_injective (V : X.Opens) : Function.Injective (laurentSum T V) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro b hb
  let κ : ℂ →+* Γ(X, V) :=
    (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op).hom.comp (schemeGlobalConstants f)
  have key := eq_zero_of_forall_sum_zpow_mul κ b.support b fun c => by
    let ev : Γ(T.space, overOpen T.coord V) →+* Γ(X, V) := ((evalAt T) c V).hom
    have hu : Units.map ev.toMonoidHom (tUnitOn T V) = Units.map κ.toMonoidHom c := by
      ext
      change ev (tResOn T V) = κ c
      exact (evalAt_tFun T) c V
    have h1 := congrArg ev hb
    rw [laurentSum_eq_sum T V b subset_rfl, map_sum, map_zero] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul]
    have e1 : ev (pullFun T.coord V (b n)) = b n := (evalAt_pullFun T) c _ _
    have e2 : ev ((tUnitOn T V ^ n).val) = κ ((c ^ n : ℂˣ) : ℂ) := by
      have := congrArg Units.val (congrArg (· ^ n) hu)
      simp only [← map_zpow] at this
      exact this
    rw [e1, e2]
  ext n
  by_cases hn : n ∈ b.support
  · exact key n hn
  · exact Finsupp.notMem_support_iff.mp hn

/-! ### Existence on affine opens -/

/-- The ring homomorphism `Γ(X, V)[T, T⁻¹] ⟶ Γ(𝓧, q⁻¹(V))`, `r Tⁿ ↦ tⁿ q^♯(r)`. -/
def laurentEval (V : X.Opens) : LaurentPolynomial Γ(X, V) →+* Γ(T.space, overOpen T.coord V) :=
  LaurentPolynomial.eval₂ (pullFun T.coord V).hom (tUnitOn T V)

theorem laurentEval_mem_range (V : X.Opens) (p : LaurentPolynomial Γ(X, V)) :
    laurentEval T V p ∈ Set.range (laurentSum T V) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨b, hb⟩ := hp
    obtain ⟨b', hb'⟩ := hq
    exact ⟨b + b', by rw [map_add, map_add, hb, hb']⟩
  | C_mul_T n r =>
    refine ⟨Finsupp.single n r, ?_⟩
    rw [laurentSum_single, laurentEval, LaurentPolynomial.eval₂_C_mul_T, mul_comm]

/-- The constants of `𝓧` restricted to `q⁻¹(V)` are pulled back from `X`. -/
theorem structureMap_appLE_mem_range (V : X.Opens) (c : Γ(Spec (.of ℂ), ⊤))
    (e : overOpen T.coord V ≤ T.structureMap ⁻¹ᵁ ⊤) :
    T.structureMap.appLE ⊤ (overOpen T.coord V) e c ∈ (laurentEval T V).range := by
  refine ⟨LaurentPolynomial.C (X.presheaf.map (homOfLE le_top).op (f.appTop c)), ?_⟩
  rw [laurentEval, LaurentPolynomial.eval₂_C]
  change pullFun T.coord V (X.presheaf.map (homOfLE le_top).op (f.appTop c)) = _
  rw [pullFun_appTop T.coord T.coord_over' V c]
  rfl

/-- `π^♯` of a regular function on `𝔾_m ⊆ 𝔸¹`, restricted to `q⁻¹(V)`, is a Laurent
polynomial in `t` with constant coefficients. -/
theorem toLine_appLE_gm_mem_range (V : X.Opens) {O : AffineLine.Opens} (hO : O = gmOpen)
    (e : overOpen T.coord V ≤ T.toLine ⁻¹ᵁ O) (y : Γ(AffineLine, O)) :
    T.toLine.appLE O (overOpen T.coord V) e y ∈ (laurentEval T V).range := by
  subst hO
  have eT : overOpen T.coord V ≤ T.toLine ⁻¹ᵁ ⊤ := le_preimage_top _ _
  -- functions on `𝔸¹`
  have hA : ∀ x : Γ(AffineLine, ⊤),
      T.toLine.appLE ⊤ (overOpen T.coord V) eT x ∈ (laurentEval T V).range := by
    intro x
    have hx := mem_closure_affineLine x
    have hmap : (T.toLine.appLE ⊤ (overOpen T.coord V) eT).hom x ∈
        (Subring.closure (Set.range affineLineToBase.appTop.hom ∪ {coordT})).map
          (T.toLine.appLE ⊤ (overOpen T.coord V) eT).hom :=
      Subring.mem_map.mpr ⟨x, hx, rfl⟩
    rw [RingHom.map_closure] at hmap
    refine Subring.closure_le.mpr ?_ hmap
    rintro _ ⟨_, ⟨c, rfl⟩ | hc, rfl⟩
    · change (affineLineToBase.app ⊤ ≫
        T.toLine.appLE (affineLineToBase ⁻¹ᵁ ⊤) (overOpen T.coord V) eT) c ∈ _
      rw [← Scheme.Hom.comp_appLE]
      exact structureMap_appLE_mem_range T V c _
    · rw [Set.mem_singleton_iff] at hc
      subst hc
      refine ⟨LaurentPolynomial.T 1, ?_⟩
      rw [laurentEval, LaurentPolynomial.eval₂_T, zpow_one, tUnitOn_val]
      rfl
  -- localization `Γ(𝔾_m) = ℂ[t]_t`
  have hloc := (isAffineOpen_top AffineLine).isLocalization_basicOpen coordT
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Submonoid.powers coordT) y
  obtain ⟨n, hn⟩ := s.2
  have halg : ∀ z : Γ(AffineLine, ⊤), T.toLine.appLE gmOpen (overOpen T.coord V) e
      (algebraMap Γ(AffineLine, ⊤) Γ(AffineLine, gmOpen) z) =
        T.toLine.appLE ⊤ (overOpen T.coord V) eT z := by
    intro z
    change (AffineLine.presheaf.map _ ≫ T.toLine.appLE gmOpen (overOpen T.coord V) e) z = _
    rw [Scheme.Hom.map_appLE]
  have h1 := congrArg (T.toLine.appLE gmOpen (overOpen T.coord V) e) hxs
  rw [map_mul, halg, halg, ← hn, map_pow] at h1
  have ht : T.toLine.appLE ⊤ (overOpen T.coord V) eT coordT = tResOn T V := rfl
  rw [ht] at h1
  have hy : T.toLine.appLE gmOpen (overOpen T.coord V) e y =
      T.toLine.appLE ⊤ (overOpen T.coord V) eT x * ((tUnitOn T V ^ (-(n : ℤ))).val) := by
    rw [← h1, zpow_neg, zpow_natCast, mul_assoc, ← tUnitOn_val, ← Units.val_pow_eq_pow_val,
      Units.mul_inv, mul_one]
  rw [hy]
  refine mul_mem (hA x) ⟨LaurentPolynomial.T (-(n : ℤ)), ?_⟩
  rw [laurentEval, LaurentPolynomial.eval₂_T]

/-- **Künneth on affine charts**: for `V ⊆ X` affine, every regular function on
`q⁻¹(V) ≅ V × 𝔾_m` is a Laurent polynomial `Σ tⁿ q^♯(b_n)`. -/
theorem laurentSum_surjective_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (laurentSum T V) := by
  intro g
  suffices h : g ∈ (laurentEval T V).range by
    obtain ⟨p, rfl⟩ := h
    exact laurentEval_mem_range T V p
  let Ψ := coordLift T
  have H : IsPullback (pullback.fst f gmToBase) (pullback.snd f gmToBase) f gmToBase :=
    IsPullback.of_hasPullback _ _
  let UY : (pullback f gmToBase).Opens :=
    pullback.fst f gmToBase ⁻¹ᵁ V ⊓ pullback.snd f gmToBase ⁻¹ᵁ ⊤
  have hUST : (⊤ : gmOpen.toScheme.Opens) ≤ gmToBase ⁻¹ᵁ ⊤ := le_preimage_top _ _
  have hUSX : V ≤ f ⁻¹ᵁ ⊤ := le_preimage_top _ _
  have hUS : IsAffineOpen (⊤ : (Spec (.of ℂ)).Opens) := isAffineOpen_top _
  have hUT : IsAffineOpen (⊤ : gmOpen.toScheme.Opens) := by
    have : IsAffine gmOpen.toScheme := (isAffineOpen_top AffineLine).basicOpen coordT
    exact isAffineOpen_top _
  have hpush := (isIso_pushoutSection_iff H hUST hUSX (UY := UY) rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hUST hUSX rfl hUS hUT hV)
  have hfst : Ψ ≫ pullback.fst f gmToBase = T.coord := pullback.lift_fst _ _ _
  have hsnd : Ψ ≫ pullback.snd f gmToBase = toGm T.toLine := pullback.lift_snd _ _ _
  have hpre : T.coord ⁻¹ᵁ V ≤ Ψ ⁻¹ᵁ UY := by
    intro x hx
    refine ⟨?_, trivial⟩
    change (Ψ ≫ pullback.fst f gmToBase) x ∈ V
    rw [hfst]
    exact hx
  have hinv : inv Ψ ≫ T.coord = pullback.fst f gmToBase := by
    rw [IsIso.inv_comp_eq, hfst]
  have hpre' : UY ≤ inv Ψ ⁻¹ᵁ (T.coord ⁻¹ᵁ V) := by
    intro y hy
    change (inv Ψ ≫ T.coord) y ∈ V
    rw [hinv]
    exact hy.1
  let θ : Γ(pullback f gmToBase, UY) ⟶ Γ(T.space, overOpen T.coord V) :=
    Ψ.appLE UY (T.coord ⁻¹ᵁ V) hpre ≫ ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).inv
  have hθ : Function.Surjective θ := by
    intro z
    refine ⟨(inv Ψ).appLE (T.coord ⁻¹ᵁ V) UY hpre'
      (((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).hom z), ?_⟩
    change ((inv Ψ).appLE (T.coord ⁻¹ᵁ V) UY hpre' ≫ Ψ.appLE UY (T.coord ⁻¹ᵁ V) hpre ≫
      ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).inv)
        (((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).hom z) = z
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_of_eq_id (IsIso.hom_inv_id Ψ), Category.id_comp, ← CommRingCat.comp_apply,
      Iso.hom_inv_id]
    rfl
  obtain ⟨b, rfl⟩ := hθ g
  have hb := mem_closure_of_isPushout hpush b
  have hmap : θ.hom b ∈ (Subring.closure _).map θ.hom := Subring.mem_map.mpr ⟨b, hb, rfl⟩
  rw [RingHom.map_closure] at hmap
  refine Subring.closure_le.mpr ?_ hmap
  rintro _ ⟨_, ⟨x, rfl⟩ | ⟨y, rfl⟩, rfl⟩
  · refine ⟨LaurentPolynomial.C x, ?_⟩
    rw [laurentEval, LaurentPolynomial.eval₂_C]
    change pullFun T.coord V x = ((pullback.fst f gmToBase).appLE V UY _ ≫
      Ψ.appLE UY (T.coord ⁻¹ᵁ V) hpre ≫
        ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).inv) x
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hfst _ _ _ le_rfl,
      ← Scheme.Hom.app_eq_appLE]
    rfl
  · change ((pullback.snd f gmToBase).appLE ⊤ UY _ ≫ Ψ.appLE UY (T.coord ⁻¹ᵁ V) hpre ≫
      ((offCentral T.toLine).ι.appIso (T.coord ⁻¹ᵁ V)).inv) y ∈ _
    rw [← Category.assoc, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom hsnd _ _ _ (le_preimage_top _ _), Scheme.Opens.ι_appIso, Iso.refl_inv]
    erw [Category.comp_id]
    rw [toGm, Scheme.Hom.resLE_appLE]
    exact toLine_appLE_gm_mem_range T V (Scheme.Opens.ι_image_top _) _ y

/-! ### Existence on every open of an integral `X` -/

/-- **Künneth on `q⁻¹(V)`** for every open `V` of an integral `X`: every regular function on
`q⁻¹(V) ≅ V × 𝔾_m` is a Laurent polynomial `Σ tⁿ q^♯(b_n)`, `b_n ∈ Γ(X, V)`. The coefficients
of the expansions over an affine cover of `V` agree on overlaps (uniqueness) and glue; on an
integral `X` a coefficient vanishing on a nonempty open vanishes, so the support is finite. -/
theorem laurentSum_surjective [IsIntegral X] (V : X.Opens) :
    Function.Surjective (laurentSum T V) := by
  classical
  intro g
  have hloc : ∀ x : V, ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ W ≤ V := by
    intro x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 V.isOpen
    exact ⟨W, hW, hxW, hWV⟩
  choose W hW hxW hWV using hloc
  have hexp : ∀ x : V, ∃ b : ℤ →₀ Γ(X, W x), laurentSum T (W x) b =
      T.space.presheaf.map (homOfLE (overOpen_mono T.coord (hWV x))).op g :=
    fun x => laurentSum_surjective_of_isAffineOpen T (hW x) _
  choose b hb using hexp
  -- compatibility of the local coefficients
  have hcompat : ∀ x y : V,
      (b x).mapRange (X.presheaf.map (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op)
          (map_zero _) =
        (b y).mapRange (X.presheaf.map (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op)
          (map_zero _) := by
    intro x y
    apply laurentSum_injective T (W x ⊓ W y)
    rw [← laurentSum_restrict, ← laurentSum_restrict, hb, hb, presheaf_map_map,
      presheaf_map_map]
  have hcover : V ≤ iSup W := by
    intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxW ⟨p, hp⟩⟩
  -- gluing of the coefficients
  have hglue : ∀ n : ℤ, ∃ B : Γ(X, V), ∀ x : V,
      X.presheaf.map (homOfLE (hWV x)).op B = b x n := by
    intro n
    obtain ⟨B, hB, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf W V
      (fun x => homOfLE (hWV x)) hcover (fun x => b x n) (fun x y => by
        have := congrArg (fun c : ℤ →₀ _ => c n) (hcompat x y)
        simp only [Finsupp.mapRange_apply] at this
        exact this)
    exact ⟨B, hB⟩
  choose B hB using hglue
  -- the support is finite
  let S : Finset ℤ := if h : Nonempty V then (b h.some).support else ∅
  have hS : ∀ n, B n ≠ 0 → n ∈ S := by
    intro n hn
    by_cases hV : Nonempty V
    · simp only [S, dif_pos hV]
      by_contra hns
      apply hn
      have h0 : b hV.some n = 0 := Finsupp.notMem_support_iff.mp hns
      have hne : Nonempty (W hV.some) := ⟨⟨_, hxW hV.some⟩⟩
      apply map_injective_of_isIntegral (X := X) (homOfLE (hWV hV.some))
      rw [hB, h0, map_zero]
    · exfalso
      apply hn
      apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun _ : Empty => V) V
        (fun _ => 𝟙 _) (fun p hp => absurd ⟨⟨p, hp⟩⟩ hV)
      intro e
      exact e.elim
  let B' : ℤ →₀ Γ(X, V) := Finsupp.onFinset S B hS
  refine ⟨B', ?_⟩
  -- the glued expansion is `g`, checked on the cover `q⁻¹(W_x)`
  have hcover' : overOpen T.coord V ≤ iSup fun x : V => overOpen T.coord (W x) := by
    rintro _ ⟨p, hp, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, hp⟩, ⟨p, hxW ⟨_, hp⟩, rfl⟩⟩
  apply TopCat.Sheaf.eq_of_locally_eq' T.space.sheaf (fun x : V => overOpen T.coord (W x))
    (overOpen T.coord V) (fun x => homOfLE (overOpen_mono T.coord (hWV x))) hcover'
  intro x
  change T.space.presheaf.map _ (laurentSum T V B') = T.space.presheaf.map _ g
  rw [laurentSum_restrict T (hWV x), ← hb x]
  congr 1
  ext n
  rw [Finsupp.mapRange_apply, Finsupp.onFinset_apply, hB]

/-! ### Laurent expansions of sections of `𝓛^m` -/

/-- The coefficients of a section in the frames `ε_j^m` obey the pulled-back transition law. -/
theorem epsCoeff_transition (m : ℕ) (σ : SectionSpace T.structureMap T.line m) (j k : a.I) :
    T.space.presheaf.map (homOfLE (overOpen_mono T.coord
        (inf_le_right : a.opens j ⊓ a.opens k ≤ a.opens k))).op (T.epsCoeff m k σ) =
      pullFun T.coord (a.opens j ⊓ a.opens k)
          (transitionFun (a.frame j) (a.frame k) (homOfLE inf_le_left) (homOfLE inf_le_right)) ^ m *
        T.space.presheaf.map (homOfLE (overOpen_mono T.coord
          (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j))).op (T.epsCoeff m j σ) := by
  rw [← T.frame_transition j k]
  exact LocalBundleFrame.global_coefficients_transition (T.frame j) (T.frame k) _ _ m σ

/-- **Laurent expansion of the sections of `𝓛^m`** (Künneth on `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`): for `X`
integral, the restriction of every `σ ∈ H⁰(𝓧, 𝓛^m)` to `𝓧 ∖ 𝓧₀` is a finite sum
`Σ_λ t^{-λ} q^* s_λ` with `s_λ ∈ H⁰(X, L^m)`: in the frames `ε_j^m`,
`σ_j = Σ_λ t^{-λ} q^♯((s_λ)_j)`. -/
theorem exists_section_expansion [IsIntegral X] (m : ℕ)
    (σ : SectionSpace T.structureMap T.line m) :
    ∃ (S : Finset ℤ) (s : ℤ → SectionSpace f L m), ∀ j : a.I,
      T.epsCoeff m j σ = ∑ lam ∈ S, (T.tUnit j ^ (-lam)).val *
        pullFun T.coord (a.opens j) (atlasPowerGlobalCoefficients a m j (s lam)) := by
  classical
  choose b hb using fun j : a.I => laurentSum_surjective T (a.opens j) (T.epsCoeff m j σ)
  -- the coefficients obey the transition law of `L^m`
  have htr : ∀ (n : ℤ) (j k : a.I),
      X.presheaf.map (homOfLE (inf_le_right : a.opens j ⊓ a.opens k ≤ a.opens k)).op (b k n) =
        (transitionFun (a.frame j) (a.frame k) (homOfLE inf_le_left) (homOfLE inf_le_right)) ^ m *
          X.presheaf.map (homOfLE (inf_le_left : a.opens j ⊓ a.opens k ≤ a.opens j)).op
            (b j n) := by
    intro n j k
    have h := epsCoeff_transition T m σ j k
    rw [← hb j, ← hb k, laurentSum_restrict T inf_le_right, laurentSum_restrict T inf_le_left,
      ← map_pow, pullFun_mul_laurentSum] at h
    have h' := congrArg (fun c : ℤ →₀ _ => c n) (laurentSum_injective T _ h)
    simpa only [Finsupp.mapRange_apply] using h'
  -- glue the coefficients to sections of `L^m`
  choose s hs using fun n : ℤ =>
    FGRel.exists_section_of_coefficients a m (fun j => b j n) (fun j k => htr n j k)
  -- the support is finite
  have hX : Nonempty X := inferInstance
  obtain ⟨j0, hj0⟩ := a.covers (Classical.arbitrary X)
  have hzero : ∀ n, n ∉ (b j0).support → ∀ j, b j n = 0 := by
    intro n hn j
    have h0 : s n = 0 := eq_zero_of_atlasCoeff_eq_zero a m (s n) j0 ⟨_, hj0⟩
      (by rw [hs n j0]; exact Finsupp.notMem_support_iff.mp hn)
    rw [← hs n j, h0, atlasPowerGlobalCoefficients_zero]
  refine ⟨(b j0).support.map (Equiv.neg ℤ).toEmbedding, fun lam => s (-lam), fun j => ?_⟩
  rw [Finset.sum_map, ← hb j, laurentSum_eq_sum T _ (b j) (S := (b j0).support)]
  · refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Equiv.toEmbedding_apply, Equiv.neg_apply, neg_neg]
    rw [tUnitOn_chart, hs]
  · intro n hn
    by_contra hn0
    exact Finsupp.mem_support_iff.mp hn (hzero n hn0 j)

end SGPT.TestCurve.GeomLin
