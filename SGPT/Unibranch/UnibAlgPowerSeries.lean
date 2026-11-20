import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Formal power series rings: powers of the maximal ideal, flatness, normality

Let `σ` be a finite type and `T = R⟦σ⟧` the ring of formal power series.

* `mem_span_X_pow_iff`: a power series lies in `(X)ⁿ` iff its coefficients of total degree
  `< n` vanish (via Mathlib's identification of `R⟦σ⟧` with the adic completion of
  `R[σ]`);
* `sub_coe_truncTotal_mem`: every power series is congruent to its truncation modulo `(X)ⁿ`;
* `flat_mvPolynomial`: `R⟦σ⟧` is flat over `R[σ]` for Noetherian `R`;
* `maximalIdeal_eq_span_X`: over a field, the maximal ideal is `(X)`;
* `isIntegrallyClosed`: over a field, `K⟦σ⟧` is integrally closed. The proof is the classical
  graded argument (Zariski–Samuel): the associated graded ring is the polynomial ring, which is
  integrally closed; initial forms of an almost-integral fraction `a / b` give a homogeneous
  correction `H` with `a - b H` of higher order; Krull's intersection theorem in `T / (b)`
  concludes.

These are inputs of lane UNIB-ALG (step U3 of `claude-serre-gaga.tex`, the excellence step of
`prop:unibranch_gaga`). Blueprint: `claude-unib-alg.tex`.
-/

set_option autoImplicit false

open MvPowerSeries

namespace SGPT.Unibranch.UnibAlg

noncomputable section

variable {σ : Type*} [Finite σ]

/-- The ideal `(X)` of a power series ring. -/
abbrev spanX (σ R : Type*) [CommRing R] : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range X)

/-! ### Powers of `(X)` -/

theorem mem_span_X_pow_iff {R : Type*} [CommRing R] (n : ℕ) (f : MvPowerSeries σ R) :
    f ∈ spanX σ R ^ n ↔ ∀ x : σ →₀ ℕ, x.degree < n → coeff x f = 0 := by
  classical
  have hmap : Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (spanX σ R) =
      (MvPolynomial.idealOfVars σ R).map (algebraMap _ _) := by
    simp_rw [spanX, Ideal.map_span, ← Set.range_comp]
    congr 2; ext1
    simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]
  have hmem : f ∈ spanX σ R ^ n ↔ (toAdicCompletionAlgEquiv σ R).toRingEquiv f ∈
      Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (spanX σ R ^ n) := by
    constructor
    · intro h
      exact Ideal.mem_map_of_mem _ h
    · intro h
      rw [Ideal.mem_map_iff_of_surjective _ (toAdicCompletionAlgEquiv σ R).toRingEquiv.surjective]
        at h
      obtain ⟨g, hg, hge⟩ := h
      rw [← (toAdicCompletionAlgEquiv σ R).toRingEquiv.injective hge]
      exact hg
  rw [hmem, Ideal.map_pow, hmap, ← Ideal.map_pow]
  have hker : ∀ y : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R),
      y ∈ (MvPolynomial.idealOfVars σ R ^ n).map (algebraMap _ _) ↔
        AdicCompletion.eval (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) n y = 0 := by
    intro y
    rw [← LinearMap.mem_ker,
      ← AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R),
      Ideal.smul_top_eq_map]
    rfl
  rw [hker, AdicCompletion.eval_apply]
  change (toAdicCompletion σ R f).val n = 0 ↔ _
  rw [toAdicCompletion_apply_eq_mk_truncTotal, Ideal.Quotient.eq_zero_iff_mem]
  have hsm : (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (MvPolynomial σ R)) = (MvPolynomial.idealOfVars σ R ^ n : Ideal (MvPolynomial σ R)) := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [hsm, MvPolynomial.mem_pow_idealOfVars_iff']
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  rw [coeff_truncTotal _ hx]

/-- A power series is congruent to its truncation modulo `(X)ⁿ`. -/
theorem sub_coe_truncTotal_mem {R : Type*} [CommRing R] (n : ℕ) (f : MvPowerSeries σ R) :
    f - (truncTotal n f : MvPowerSeries σ R) ∈ spanX σ R ^ n := by
  rw [mem_span_X_pow_iff]
  intro x hx
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx, sub_self]

/-- The kernel of the constant coefficient is `(X)`. -/
theorem mem_spanX_iff {R : Type*} [CommRing R] (f : MvPowerSeries σ R) :
    f ∈ spanX σ R ↔ constantCoeff f = 0 := by
  have h := mem_span_X_pow_iff 1 f
  rw [pow_one] at h
  rw [h]
  constructor
  · intro H
    have := H 0 (by simp)
    simpa using this
  · intro H x hx
    have hx0 : x = 0 := by
      rw [Nat.lt_one_iff] at hx
      exact (Finsupp.degree_eq_zero_iff x).mp hx
    subst hx0
    simpa using H

/-- Polynomials are dense: `T = R[σ] + (X)ⁿ`. -/
theorem exists_coe_add_mem {R : Type*} [CommRing R] (n : ℕ) (f : MvPowerSeries σ R) :
    ∃ p : MvPolynomial σ R, ∃ g ∈ spanX σ R ^ n, f = p + g :=
  ⟨truncTotal n f, _, sub_coe_truncTotal_mem n f, by ring⟩

/-! ### Flatness over the polynomial ring -/

instance flat_mvPolynomial {R : Type*} [CommRing R] [IsNoetherianRing R] :
    Module.Flat (MvPolynomial σ R) (MvPowerSeries σ R) := by
  have := Fintype.ofFinite σ
  have : Module.Flat (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :=
    AdicCompletion.flat_of_isNoetherian _
  exact Module.Flat.of_linearEquiv (toAdicCompletionAlgEquiv σ R).toLinearEquiv

/-! ### Over a field -/

variable {K : Type*} [Field K]

instance isDomain : IsDomain (MvPowerSeries σ K) := NoZeroDivisors.to_isDomain _

theorem maximalIdeal_eq_spanX : IsLocalRing.maximalIdeal (MvPowerSeries σ K) = spanX σ K := by
  ext f
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not, mem_spanX_iff]

/-! ### Normality -/

/-- The homogeneous component of a power series, as a polynomial. -/
def homPoly (p : ℕ) (f : MvPowerSeries σ K) : MvPolynomial σ K :=
  truncTotal (p + 1) (homogeneousComponent p f)

theorem coe_homPoly (p : ℕ) (f : MvPowerSeries σ K) :
    (homPoly p f : MvPowerSeries σ K) = homogeneousComponent p f := by
  ext x
  rw [MvPolynomial.coeff_coe, homPoly, coeff_truncTotal_eq_ite, coeff_homogeneousComponent]
  by_cases h : x.degree = p
  · simp [h]
  · simp [h]

/-- In a UFD (here: an integrally closed Noetherian domain), if `g ^ j ∣ c * f ^ j` for every
`j` with `c ≠ 0`, then `g ∣ f`. -/
theorem dvd_of_forall_pow_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {f g c : A} (hg : g ≠ 0) (hc : c ≠ 0)
    (h : ∀ j : ℕ, g ^ j ∣ c * f ^ j) : g ∣ f := by
  set F := FractionRing A
  set x : F := algebraMap A F f / algebraMap A F g
  have hg' : algebraMap A F g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hg
  have hc' : algebraMap A F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A F)).mpr hc
  -- every power of `x` lies in the cyclic module `A • c⁻¹`
  set M : Submodule A F := Submodule.span A {(algebraMap A F c)⁻¹}
  have hpow : ∀ j : ℕ, x ^ j ∈ M := by
    intro j
    obtain ⟨e, he⟩ := h j
    rw [Submodule.mem_span_singleton]
    refine ⟨e, ?_⟩
    rw [Algebra.smul_def]
    have : algebraMap A F c * (algebraMap A F f) ^ j =
        (algebraMap A F g) ^ j * algebraMap A F e := by
      rw [← map_pow, ← map_mul, he, map_mul, map_pow]
    rw [mul_inv_eq_iff_eq_mul₀ hc', div_pow, div_mul_eq_mul_div,
      eq_div_iff (pow_ne_zero _ hg')]
    linear_combination -this
  have hle : Subalgebra.toSubmodule (Algebra.adjoin A {x}) ≤ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    rintro _ ⟨p, rfl⟩
    change Polynomial.aeval x p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpow j)
  have hMfg : M.FG := ⟨{(algebraMap A F c)⁻¹}, by simp [M]⟩
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin A {x})).FG := by
    have := isNoetherian_of_fg_of_noetherian M hMfg
    have h1 := IsNoetherian.noetherian
      ((Subalgebra.toSubmodule (Algebra.adjoin A {x})).comap M.subtype)
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral A x :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin A {x}) hfg x (Algebra.self_mem_adjoin_singleton A x)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := F)).mp hint
  refine ⟨y, IsFractionRing.injective A F ?_⟩
  rw [map_mul, hy, mul_div_cancel₀ _ hg']

/-- The order of a power series, as a natural number. -/
def ordN (f : MvPowerSeries σ K) : ℕ := f.order.toNat

omit [Finite σ] in
theorem ordN_spec {f : MvPowerSeries σ K} (hf : f ≠ 0) : (ordN f : ℕ∞) = f.order :=
  ENat.natCast_toNat (by rwa [ne_eq, order_eq_top_iff])

omit [Finite σ] in
theorem homogeneousComponent_ordN_ne_zero {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    homogeneousComponent (ordN f) f ≠ 0 :=
  homogeneousComponent_of_order (ordN_spec hf)

omit [Finite σ] in
theorem ordN_mul {f g : MvPowerSeries σ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordN (f * g) = ordN f + ordN g := by
  have h := order_mul f g
  rw [← ordN_spec hf, ← ordN_spec hg, ← ordN_spec (mul_ne_zero hf hg)] at h
  exact_mod_cast h

omit [Finite σ] in
theorem homogeneousComponent_ordN_mul {f g : MvPowerSeries σ K} (hf : f ≠ 0) (hg : g ≠ 0) :
    homogeneousComponent (ordN (f * g)) (f * g) =
      homogeneousComponent (ordN f) f * homogeneousComponent (ordN g) g := by
  rw [ordN_mul hf hg]
  exact homogeneousComponent_mul_of_le_order (ordN_spec hf).le (ordN_spec hg).le

omit [Finite σ] in
theorem le_order_of_coeff {f : MvPowerSeries σ K} {n : ℕ}
    (h : ∀ x : σ →₀ ℕ, x.degree < n → coeff x f = 0) : (n : ℕ∞) ≤ f.order :=
  nat_le_order h

theorem le_ordN_of_mem {f : MvPowerSeries σ K} (hf : f ≠ 0) {n : ℕ} (h : f ∈ spanX σ K ^ n) :
    n ≤ ordN f := by
  have := le_order_of_coeff ((mem_span_X_pow_iff n f).mp h)
  rw [← ordN_spec hf] at this
  exact_mod_cast this

omit [Finite σ] in
theorem order_homogeneousComponent (p : ℕ) (f : MvPowerSeries σ K) :
    (p : ℕ∞) ≤ (homogeneousComponent p f).order := by
  refine nat_le_order fun x hx => ?_
  rw [coeff_homogeneousComponent, if_neg (by omega)]

omit [Finite σ] in
theorem homogeneousComponent_homogeneousComponent (p : ℕ) (f : MvPowerSeries σ K) :
    homogeneousComponent p (homogeneousComponent p f) = homogeneousComponent p f :=
  (isHomogeneous_iff_eq_homogeneousComponent.mp (isHomogeneous_homogeneousComponent f p)).symm

theorem homPoly_ne_zero {f : MvPowerSeries σ K} {p : ℕ} (h : homogeneousComponent p f ≠ 0) :
    homPoly p f ≠ 0 := by
  intro h0
  apply h
  rw [← coe_homPoly, h0, MvPolynomial.coe_zero]

/-- **Graded step.** If `a / b` is almost integral with denominator `d`, the initial form of
`b` divides that of `a`, and one can subtract a homogeneous multiple of `b` to raise the
order of `a`. -/
theorem exists_step {r b d : MvPowerSeries σ K} (hr : r ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : ∀ j : ℕ, b ^ j ∣ d * r ^ j) :
    ∃ H : MvPowerSeries σ K, ∀ x : σ →₀ ℕ, x.degree ≤ ordN r → coeff x (r - b * H) = 0 := by
  classical
  set α := ordN r
  set β := ordN b
  -- initial forms
  have hcomp_pow : ∀ (f : MvPowerSeries σ K), f ≠ 0 → ∀ j : ℕ,
      homogeneousComponent (ordN (f ^ j)) (f ^ j) = (homogeneousComponent (ordN f) f) ^ j := by
    intro f hf j
    induction j with
    | zero =>
      have h1 : ordN (1 : MvPowerSeries σ K) = 0 := by
        have h0 := ordN_spec (one_ne_zero (α := MvPowerSeries σ K))
        have h2 : (1 : MvPowerSeries σ K).order ≤ (0 : σ →₀ ℕ).degree :=
          order_le (by simp)
        have hdeg0 : (0 : σ →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
        rw [← h0, hdeg0] at h2
        exact_mod_cast Nat.le_zero.mp (by exact_mod_cast h2)
      rw [pow_zero, pow_zero, h1]
      ext x
      rw [coeff_homogeneousComponent, coeff_one]
      by_cases hx : x = 0
      · simp [hx, Finsupp.degree]
      · have : x.degree ≠ 0 := fun h => hx ((Finsupp.degree_eq_zero_iff x).mp h)
        simp [hx, this]
    | succ j ih =>
      rw [pow_succ, homogeneousComponent_ordN_mul (pow_ne_zero _ hf) hf, ih, pow_succ]
  have hdiv : ∀ j : ℕ, homPoly β b ^ j ∣ homPoly (ordN d) d * homPoly α r ^ j := by
    intro j
    obtain ⟨e, he⟩ := h j
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [mul_zero] at he
      exact mul_ne_zero hd (pow_ne_zero _ hr) he
    have hbj : b ^ j ≠ 0 := pow_ne_zero _ hb
    have hrj : r ^ j ≠ 0 := pow_ne_zero _ hr
    have key := congrArg (fun F => homogeneousComponent (ordN F) F) he
    rw [homogeneousComponent_ordN_mul hd hrj, homogeneousComponent_ordN_mul hbj he0,
      hcomp_pow r hr, hcomp_pow b hb] at key
    refine ⟨homPoly (ordN e) e, MvPolynomial.coe_injective σ K ?_⟩
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_pow, coe_homPoly]
    exact key
  have hPb : homPoly β b ≠ 0 := homPoly_ne_zero (homogeneousComponent_ordN_ne_zero hb)
  have hPd : homPoly (ordN d) d ≠ 0 := homPoly_ne_zero (homogeneousComponent_ordN_ne_zero hd)
  obtain ⟨Q, hQ⟩ := dvd_of_forall_pow_dvd hPb hPd hdiv
  have hQ' : homogeneousComponent α r = homogeneousComponent β b * (Q : MvPowerSeries σ K) := by
    rw [← coe_homPoly, ← coe_homPoly, hQ, MvPolynomial.coe_mul]
  have hinr := homogeneousComponent_ordN_ne_zero hr
  have hinb := homogeneousComponent_ordN_ne_zero hb
  have hQ0 : (Q : MvPowerSeries σ K) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hQ'
    exact hinr hQ'
  -- orders: `α = β + ordN Q`
  have hordr : ordN (homogeneousComponent α r) = α := by
    have h1 := order_homogeneousComponent α r
    have h2 : (homogeneousComponent α r).order ≤ α := by
      obtain ⟨x, hx⟩ : ∃ x, coeff x (homogeneousComponent α r) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hinr (MvPowerSeries.ext hcon)
      have hdeg : x.degree = α := by
        by_contra hne
        rw [coeff_homogeneousComponent, if_neg hne] at hx
        exact hx rfl
      have h3 := order_le hx
      rwa [hdeg] at h3
    have := le_antisymm h2 h1
    rw [← ordN_spec hinr] at this
    exact_mod_cast this
  have hordb : ordN (homogeneousComponent β b) = β := by
    have h1 := order_homogeneousComponent β b
    have h2 : (homogeneousComponent β b).order ≤ β := by
      obtain ⟨x, hx⟩ : ∃ x, coeff x (homogeneousComponent β b) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hinb (MvPowerSeries.ext hcon)
      have hdeg : x.degree = β := by
        by_contra hne
        rw [coeff_homogeneousComponent, if_neg hne] at hx
        exact hx rfl
      have h3 := order_le hx
      rwa [hdeg] at h3
    have := le_antisymm h2 h1
    rw [← ordN_spec hinb] at this
    exact_mod_cast this
  have hαβ : α = β + ordN (Q : MvPowerSeries σ K) := by
    have := ordN_mul hinb hQ0
    rw [← hQ', hordr, hordb] at this
    exact this
  set H := homogeneousComponent (α - β) (Q : MvPowerSeries σ K)
  have hH : homogeneousComponent α r = homogeneousComponent β b * H := by
    have h1 : homogeneousComponent α (homogeneousComponent α r) = homogeneousComponent α r :=
      homogeneousComponent_homogeneousComponent α r
    rw [hQ'] at h1
    have h2 := homogeneousComponent_mul_of_le_order (p := β) (q := α - β)
      (f := homogeneousComponent β b) (g := (Q : MvPowerSeries σ K))
      (order_homogeneousComponent β b) (by
        rw [← ordN_spec hQ0]
        exact_mod_cast (by omega : α - β ≤ ordN (Q : MvPowerSeries σ K)))
    rw [show β + (α - β) = α by omega, homogeneousComponent_homogeneousComponent] at h2
    rw [hQ', ← h1, h2]
  refine ⟨H, fun x hx => ?_⟩
  have hordbH : (α : ℕ∞) ≤ (b * H).order := by
    calc (α : ℕ∞) = (β : ℕ∞) + ((α - β : ℕ) : ℕ∞) := by
          rw [← Nat.cast_add, Nat.add_sub_cancel' (by omega)]
      _ ≤ b.order + H.order := add_le_add (ordN_spec hb).le (order_homogeneousComponent _ _)
      _ ≤ (b * H).order := le_order_mul
  rcases lt_or_eq_of_le hx with hlt | heq
  · rw [map_sub, coeff_of_lt_order (by rw [← ordN_spec hr]; exact_mod_cast hlt),
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt) hordbH), sub_zero]
  · have h1 : coeff x r = coeff x (homogeneousComponent α r) := by
      rw [coeff_homogeneousComponent, if_pos heq]
    have h2 : coeff x (b * H) = coeff x (homogeneousComponent α (b * H)) := by
      rw [coeff_homogeneousComponent, if_pos heq]
    have h3 : homogeneousComponent α (b * H) = homogeneousComponent β b * H := by
      have := homogeneousComponent_mul_of_le_order (p := β) (q := α - β) (f := b) (g := H)
        (ordN_spec hb).le (order_homogeneousComponent _ _)
      rw [show β + (α - β) = α by omega, homogeneousComponent_homogeneousComponent] at this
      exact this
    rw [map_sub, h1, h2, h3, ← hH, sub_self]

/-- **`K⟦σ⟧` is integrally closed.** -/
theorem isIntegrallyClosed : IsIntegrallyClosed (MvPowerSeries σ K) := by
  classical
  set T := MvPowerSeries σ K
  set F := FractionRing T
  rw [isIntegrallyClosed_iff F]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap T F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T F)).mpr hb0
  -- a common denominator for `T[x]`
  obtain ⟨s, hs⟩ := hx.fg_adjoin_singleton
  obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T) s
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hspan : ∀ z ∈ Submodule.span T (s : Set F), IsLocalization.IsInteger T (d • z) := by
    intro z hz'
    induction hz' using Submodule.span_induction with
    | mem y hy => exact hdint y hy
    | zero => rw [smul_zero]; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz => rw [smul_add]; exact IsLocalization.isInteger_add hy hz
    | smul t y _ hy => rw [smul_comm]; exact IsLocalization.isInteger_smul hy
  have hdall : ∀ z ∈ Algebra.adjoin T {algebraMap T F a / algebraMap T F b},
      IsLocalization.IsInteger T (d • z) := by
    intro z hz
    refine hspan z ?_
    rw [hs]
    exact hz
  -- almost integrality of the remainders
  have hdvd : ∀ q : T, ∀ j : ℕ, b ^ j ∣ d * (a - b * q) ^ j := by
    intro q j
    have hmem : (algebraMap T F a / algebraMap T F b - algebraMap T F q) ^ j ∈
        Algebra.adjoin T {algebraMap T F a / algebraMap T F b} :=
      Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton T _)
        (Subalgebra.algebraMap_mem _ q)) j
    obtain ⟨e, he⟩ := hdall _ hmem
    refine ⟨e, IsFractionRing.injective T F ?_⟩
    rw [Algebra.smul_def] at he
    rw [map_mul, map_mul, map_pow, map_pow, he, map_sub, map_mul]
    have hxq : algebraMap T F a / algebraMap T F b - algebraMap T F q =
        (algebraMap T F a - algebraMap T F b * algebraMap T F q) / algebraMap T F b := by
      rw [eq_div_iff hb', sub_mul, div_mul_cancel₀ _ hb']
      ring
    have hbj : (algebraMap T F b) ^ j ≠ 0 := pow_ne_zero _ hb'
    rw [hxq, div_pow, ← mul_div_assoc, mul_comm ((algebraMap T F b) ^ j),
      div_mul_cancel₀ _ hbj]
  -- approximation to all orders
  have happrox : ∀ k : ℕ, ∃ q : T, a - b * q ∈ spanX σ K ^ k := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨q, hq⟩ := ih
      by_cases hr : a - b * q = 0
      · exact ⟨q, by rw [hr]; exact Ideal.zero_mem _⟩
      obtain ⟨H, hH⟩ := exists_step hr hb0 hd0 (hdvd q)
      refine ⟨q + H, ?_⟩
      have hk := le_ordN_of_mem hr hq
      rw [mem_span_X_pow_iff]
      intro y hy
      have := hH y (by omega)
      rw [show a - b * (q + H) = a - b * q - b * H by ring]
      exact this
  -- Krull's intersection theorem in `T ⧸ (b)`
  set M := T ⧸ Ideal.span {b}
  have hmem : (Ideal.Quotient.mk (Ideal.span {b}) a : M) ∈
      (⨅ i : ℕ, spanX σ K ^ i • ⊤ : Submodule T M) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨q, hq⟩ := happrox i
    have : (Ideal.Quotient.mk (Ideal.span {b}) a : M) =
        (a - b * q) • (Ideal.Quotient.mk (Ideal.span {b}) 1 : M) := by
      rw [← Ideal.Quotient.mk_eq_mk (1 : T), ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
        Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq]
      rw [show a - (a - b * q) = b * q by ring]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    rw [this]
    exact Submodule.smul_mem_smul hq Submodule.mem_top
  obtain ⟨⟨t, ht⟩, hteq⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (spanX σ K) _).mp hmem
  have hunit : IsUnit (1 - t) := by
    rw [isUnit_iff_constantCoeff, map_sub, map_one, (mem_spanX_iff t).mp ht, sub_zero]
    exact isUnit_one
  have hzero : (Ideal.Quotient.mk (Ideal.span {b}) a : M) = 0 := by
    have h1 : (1 - t) • (Ideal.Quotient.mk (Ideal.span {b}) a : M) = 0 := by
      rw [sub_smul, one_smul, hteq, sub_self]
    obtain ⟨u, hu⟩ := hunit
    rw [← hu] at h1
    have := congrArg (fun m : M => (↑u⁻¹ : T) • m) h1
    simpa [smul_smul] using this
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hzero
  obtain ⟨y, rfl⟩ := hzero
  refine ⟨y, ?_⟩
  rw [map_mul, mul_div_cancel_left₀ _ hb']

end

end SGPT.Unibranch.UnibAlg
