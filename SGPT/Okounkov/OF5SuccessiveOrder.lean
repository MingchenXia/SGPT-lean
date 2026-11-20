import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Successive orders of vanishing along a chain of local equations

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*, the definition
of the valuation `ν_{Y•}` of an admissible flag (after `def:admfl`):

*Let `s⁽⁰⁾ = s ∈ ℂ(X)^×`. For `i = 1, …, n`, after localizing around `Yₙ`, choose a local
defining equation `tᵢ` of `Yᵢ` in `Yᵢ₋₁`, and set `νᵢ = ord_{Yᵢ}(s⁽ⁱ⁻¹⁾)`,
`s⁽ⁱ⁾ = (s⁽ⁱ⁻¹⁾ tᵢ^{-νᵢ})|_{Yᵢ} ∈ ℂ(Yᵢ)^×`. Then `ν_{Y•}(s) = (ν₁, …, νₙ) ∈ ℤⁿ`. It is easy to
verify that `ν_{Y•}` is indeed a rank `n` valuation.*

This file carries out this construction in commutative algebra. After localizing around `Yₙ`,
the local ring `R = 𝒪_{X,Yₙ}` carries the chain of primes `P 0 ⊆ P 1 ⊆ ⋯ ⊆ P n` of the members
`Yᵢ` (`R ⧸ P i = 𝒪_{Yᵢ,Yₙ}`), and a *local defining equation* `T i` of `Yᵢ₊₁` in `Yᵢ` is an
element with `P (i+1) = P i + (T i)` (`LocalEquationChain`; indices are shifted by one with
respect to the source: the source's `t_{i+1}` is `T i`). In the domain `R ⧸ P i` the image `τᵢ`
of `T i` is a prime element (`τ_prime`), so `ord_{Yᵢ₊₁}` is the multiplicity of `τᵢ`
(`ord`), and `s⁽ⁱ⁺¹⁾ = (s⁽ⁱ⁾ τᵢ^{-ord})|_{Yᵢ₊₁}` is the image in `R ⧸ P (i+1)` of a residual
`residual i a` with `a ≡ Tᵢ^{ord} · residual i a (mod P i)` (well defined modulo `P i`,
`decomposition_unique`).

## Main definitions and results

* `LocalEquationChain.valAt i a`: the successive orders `(0, …, 0, νᵢ₊₁, …, νₙ)` from step `i` on
  (`⊤` on `P i`); `valAt 0` is `ν_{Y•}` on `R`.
* `LocalEquationChain.valuation`: `ν_{Y•}` as an additive valuation of `R` with values in
  `ℤⁿ_lex ∪ {∞}` (`ℤⁿ` with the lexicographic order, the first coordinate being the most
  significant); `fractionValuation K`: its extension to the fraction field `K` (`ℂ(X)`).
* `fractionValuation_T`: `ν(T i)` is the `i`-th standard basis vector; hence
  `fractionValuation_surjective`: `ν_{Y•}` is surjective onto `ℤⁿ ∪ {∞}` (a rank `n` valuation).
* `valuation_apply_zero_coord`: the first coordinate of `ν(a)` is `ord_{Y₁}(a)`, the
  multiplicity of `τ₀`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF5

open Ideal

attribute [local instance] Classical.propDecidable

/-- **Local defining equations of a flag** in a ring `R` (source: the definition of `ν_{Y•}`,
*"after localizing around `Yₙ`, choose a local defining equation `tᵢ` of `Yᵢ` in `Yᵢ₋₁`"*):
prime ideals `P i` (the members of the flag) and elements `T i` (`i < n`) with
`P (i+1) = P i + (T i)` and `T i ∉ P i`. -/
structure LocalEquationChain (R : Type*) [CommRing R] (n : ℕ) where
  /-- The prime ideal of the `i`-th member. -/
  P : ℕ → Ideal R
  /-- The local equation of the `(i+1)`-st member in the `i`-th. -/
  T : ℕ → R
  isPrime : ∀ i, (P i).IsPrime
  succ_eq : ∀ i < n, P (i + 1) = P i ⊔ Ideal.span {T i}
  T_notMem : ∀ i < n, T i ∉ P i

namespace LocalEquationChain

variable {R : Type*} [CommRing R] {n : ℕ} (C : LocalEquationChain R n)

instance isPrime' (i : ℕ) : (C.P i).IsPrime := C.isPrime i

theorem le_succ {i : ℕ} (hi : i < n) : C.P i ≤ C.P (i + 1) := by
  rw [C.succ_eq i hi]
  exact le_sup_left

theorem T_mem_succ {i : ℕ} (hi : i < n) : C.T i ∈ C.P (i + 1) := by
  rw [C.succ_eq i hi]
  exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem mem_succ_iff {i : ℕ} (hi : i < n) (a : R) :
    a ∈ C.P (i + 1) ↔ ∃ c, a - c * C.T i ∈ C.P i := by
  rw [C.succ_eq i hi, Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨c, by simpa using hy⟩
  · rintro ⟨c, hc⟩
    exact ⟨a - c * C.T i, hc, c * C.T i, Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩, by ring⟩

/-- The image `τᵢ` of the local equation `T i` in `R ⧸ P i`. -/
abbrev τ (i : ℕ) : R ⧸ C.P i := Ideal.Quotient.mk (C.P i) (C.T i)

theorem τ_dvd_iff {i : ℕ} (hi : i < n) (a : R) :
    C.τ i ∣ Ideal.Quotient.mk (C.P i) a ↔ a ∈ C.P (i + 1) := by
  rw [C.mem_succ_iff hi]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective d
    refine ⟨c, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, mul_comm]
    exact sub_self _
  · rintro ⟨c, hc⟩
    refine ⟨Ideal.Quotient.mk (C.P i) c, ?_⟩
    rw [← sub_eq_zero, mul_comm, ← map_mul, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hc

theorem τ_ne_zero {i : ℕ} (hi : i < n) : C.τ i ≠ 0 := by
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact C.T_notMem i hi

/-- **`τᵢ` is a prime element of `R ⧸ P i`**: `Yᵢ₊₁` is a prime Cartier divisor of `Yᵢ` near
`Yₙ`. -/
theorem τ_prime {i : ℕ} (hi : i < n) : Prime (C.τ i) := by
  refine ⟨C.τ_ne_zero hi, fun hu => ?_, fun a b hab => ?_⟩
  · have h1 : C.τ i ∣ Ideal.Quotient.mk (C.P i) 1 := hu.dvd
    rw [C.τ_dvd_iff hi] at h1
    exact (C.isPrime (i + 1)).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, C.τ_dvd_iff hi] at hab
    rw [C.τ_dvd_iff hi, C.τ_dvd_iff hi]
    exact (C.isPrime (i + 1)).mem_or_mem hab

/-- `ord_{Yᵢ₊₁}(a)` on `Yᵢ`: the multiplicity of `τᵢ` in the image of `a` in `R ⧸ P i`. -/
def ord (i : ℕ) (a : R) : ℕ :=
  multiplicity (C.τ i) (Ideal.Quotient.mk (C.P i) a)

/-- The quotient `a / τᵢ^{ord}` in `R ⧸ P i`. -/
def residualQ (i : ℕ) (a : R) : R ⧸ C.P i :=
  Classical.choose (show ∃ c, Ideal.Quotient.mk (C.P i) a = C.τ i ^ C.ord i a * c from
    pow_multiplicity_dvd (C.τ i) (Ideal.Quotient.mk (C.P i) a))

/-- A representative in `R` of `a / Tᵢ^{ord}`: `s⁽ⁱ⁺¹⁾` is its image in `R ⧸ P (i+1)`. -/
def residual (i : ℕ) (a : R) : R :=
  Classical.choose (Ideal.Quotient.mk_surjective (C.residualQ i a))

theorem residual_spec (i : ℕ) (a : R) :
    Ideal.Quotient.mk (C.P i) a =
      C.τ i ^ C.ord i a * Ideal.Quotient.mk (C.P i) (C.residual i a) := by
  rw [residual, Classical.choose_spec (Ideal.Quotient.mk_surjective (C.residualQ i a))]
  exact Classical.choose_spec (show ∃ c, Ideal.Quotient.mk (C.P i) a = C.τ i ^ C.ord i a * c from
    pow_multiplicity_dvd (C.τ i) (Ideal.Quotient.mk (C.P i) a))

theorem ord_congr {i : ℕ} {a b : R} (h : a - b ∈ C.P i) : C.ord i a = C.ord i b := by
  unfold ord
  rw [Ideal.Quotient.eq.mpr h]

variable [IsNoetherianRing R]

theorem finiteMultiplicity {i : ℕ} (hi : i < n) {a : R} (ha : a ∉ C.P i) :
    FiniteMultiplicity (C.τ i) (Ideal.Quotient.mk (C.P i) a) :=
  FiniteMultiplicity.of_not_isUnit (C.τ_prime hi).not_isUnit
    (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])

/-- The residual does not vanish on `Yᵢ₊₁`. -/
theorem residual_notMem {i : ℕ} (hi : i < n) {a : R} (ha : a ∉ C.P i) :
    C.residual i a ∉ C.P (i + 1) := by
  intro h
  rw [← C.τ_dvd_iff hi] at h
  apply (C.finiteMultiplicity hi ha).not_pow_dvd_of_multiplicity_lt (lt_add_one (C.ord i a))
  rw [C.residual_spec i a, pow_succ]
  exact mul_dvd_mul_left _ h

omit [IsNoetherianRing R] in
/-- **Uniqueness of the decomposition** `a ≡ Tᵢᵏ c (mod P i)` with `c ∉ P (i+1)`: `k` is
`ord_{Yᵢ₊₁}(a)` and `c ≡ residual i a (mod P i)`. -/
theorem decomposition_unique {i : ℕ} (hi : i < n) {a c : R} {k : ℕ}
    (h : Ideal.Quotient.mk (C.P i) a = C.τ i ^ k * Ideal.Quotient.mk (C.P i) c)
    (hc : c ∉ C.P (i + 1)) :
    C.ord i a = k ∧ c - C.residual i a ∈ C.P i := by
  have hτ := C.τ_prime hi
  have hk : C.ord i a = k := by
    unfold ord
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [h]
      exact dvd_mul_right _ _
    · rw [h, pow_succ]
      intro hd
      exact hc ((C.τ_dvd_iff hi c).mp
        ((mul_dvd_mul_iff_left (pow_ne_zero k hτ.ne_zero)).mp hd))
  refine ⟨hk, ?_⟩
  rw [← Ideal.Quotient.eq]
  have h2 := C.residual_spec i a
  rw [hk, h] at h2
  exact mul_left_cancel₀ (pow_ne_zero k hτ.ne_zero) h2

/-! ### The successive order vector -/

/-- `w` vanishes in the coordinates below `i`. -/
def VanishBelow (i : ℕ) (w : Fin n → ℤ) : Prop :=
  ∀ j : Fin n, (j : ℕ) < i → w j = 0

/-- **The successive orders from step `i` on**: `⊤` on `P i`; otherwise
`(0, …, 0, ord_{Yᵢ₊₁}(a), …)`, the remaining coordinates being those of the residual on
`Yᵢ₊₁`. -/
def valAt (i : ℕ) (a : R) : WithTop (Lex (Fin n → ℤ)) :=
  if a ∈ C.P i then ⊤ else
    if hi : i < n then
      ((toLex (Pi.single (⟨i, hi⟩ : Fin n) (C.ord i a : ℤ)) : Lex (Fin n → ℤ)) :
          WithTop (Lex (Fin n → ℤ))) + valAt (i + 1) (C.residual i a)
    else 0
termination_by n - i

omit [IsNoetherianRing R] in
theorem valAt_of_mem {i : ℕ} {a : R} (ha : a ∈ C.P i) : C.valAt i a = ⊤ := by
  rw [valAt, if_pos ha]

omit [IsNoetherianRing R] in
theorem valAt_of_lt {i : ℕ} (hi : i < n) {a : R} (ha : a ∉ C.P i) :
    C.valAt i a = ((toLex (Pi.single (⟨i, hi⟩ : Fin n) (C.ord i a : ℤ)) : Lex (Fin n → ℤ)) :
      WithTop (Lex (Fin n → ℤ))) + C.valAt (i + 1) (C.residual i a) := by
  rw [valAt, if_neg ha, dif_pos hi]

omit [IsNoetherianRing R] in
theorem valAt_of_le {i : ℕ} (hi : n ≤ i) {a : R} (ha : a ∉ C.P i) : C.valAt i a = 0 := by
  rw [valAt, if_neg ha, dif_neg (not_lt.mpr hi)]

/-- Off `P i`, the value is a vector vanishing below `i`. -/
theorem valAt_coe (i : ℕ) {a : R} (ha : a ∉ C.P i) :
    ∃ w : Fin n → ℤ, C.valAt i a = ((toLex w : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) ∧
      VanishBelow i w := by
  by_cases hi : i < n
  · obtain ⟨w, hw, hwv⟩ := valAt_coe (i + 1) (C.residual_notMem hi ha)
    refine ⟨Pi.single (⟨i, hi⟩ : Fin n) (C.ord i a : ℤ) + w, ?_, ?_⟩
    · rw [C.valAt_of_lt hi ha, hw, ← WithTop.coe_add]
      rfl
    · intro j hj
      rw [Pi.add_apply, hwv j (by omega), Pi.single_eq_of_ne (by
        intro h
        rw [h] at hj
        exact lt_irrefl _ hj), add_zero]
  · exact ⟨0, by rw [C.valAt_of_le (not_lt.mp hi) ha]; rfl, fun _ _ => rfl⟩
termination_by n - i

theorem valAt_eq_top_iff (i : ℕ) (a : R) : C.valAt i a = ⊤ ↔ a ∈ C.P i := by
  refine ⟨fun h => ?_, C.valAt_of_mem⟩
  by_contra ha
  obtain ⟨w, hw, -⟩ := C.valAt_coe i ha
  rw [hw] at h
  exact WithTop.coe_ne_top h

/-- The value only depends on the class modulo `P i`. -/
theorem valAt_congr (i : ℕ) {a b : R} (h : a - b ∈ C.P i) : C.valAt i a = C.valAt i b := by
  by_cases ha : a ∈ C.P i
  · have hb : b ∈ C.P i := by
      have := (C.P i).sub_mem ha h
      rwa [sub_sub_cancel] at this
    rw [C.valAt_of_mem ha, C.valAt_of_mem hb]
  have hb : b ∉ C.P i := fun hb => ha (by simpa using (C.P i).add_mem h hb)
  by_cases hi : i < n
  · rw [C.valAt_of_lt hi ha, C.valAt_of_lt hi hb, C.ord_congr h]
    congr 1
    apply valAt_congr (i + 1)
    have hmk : Ideal.Quotient.mk (C.P i) b =
        C.τ i ^ C.ord i a * Ideal.Quotient.mk (C.P i) (C.residual i a) := by
      rw [← C.residual_spec i a]
      exact (Ideal.Quotient.eq.mpr h).symm
    obtain ⟨-, hres⟩ := C.decomposition_unique hi hmk (C.residual_notMem hi ha)
    exact C.le_succ hi hres
  · rw [C.valAt_of_le (not_lt.mp hi) ha, C.valAt_of_le (not_lt.mp hi) hb]
termination_by n - i

/-- The coordinates of a value off `P i`, for `i < n`: the `i`-th is `ord_{Yᵢ₊₁}`, the next ones
come from the residual. -/
theorem valAt_decomp {i : ℕ} (hi : i < n) {a : R} (ha : a ∉ C.P i) :
    ∃ w : Fin n → ℤ, C.valAt (i + 1) (C.residual i a) = ((toLex w : Lex (Fin n → ℤ)) :
        WithTop (Lex (Fin n → ℤ))) ∧ VanishBelow (i + 1) w ∧
      C.valAt i a = ((toLex (Pi.single (⟨i, hi⟩ : Fin n) (C.ord i a : ℤ) + w) :
        Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ))) := by
  obtain ⟨w, hw, hwv⟩ := C.valAt_coe (i + 1) (C.residual_notMem hi ha)
  refine ⟨w, hw, hwv, ?_⟩
  rw [C.valAt_of_lt hi ha, hw, ← WithTop.coe_add]
  rfl

theorem valAt_one (i : ℕ) (h1 : (1 : R) ∉ C.P i) : C.valAt i 1 = 0 := by
  by_cases hi : i < n
  · have h1' : (1 : R) ∉ C.P (i + 1) := (C.isPrime (i + 1)).ne_top ∘ (Ideal.eq_top_iff_one _).mpr
    obtain ⟨hk, hres⟩ := C.decomposition_unique hi (a := 1) (c := 1) (k := 0)
      (by rw [pow_zero, one_mul]) h1'
    rw [C.valAt_of_lt hi h1, hk, C.valAt_congr (i + 1) (C.le_succ hi (by
      simpa using (C.P i).neg_mem hres)), valAt_one (i + 1) h1']
    simp
  · exact C.valAt_of_le (not_lt.mp hi) h1
termination_by n - i

theorem valAt_mul (i : ℕ) (a b : R) : C.valAt i (a * b) = C.valAt i a + C.valAt i b := by
  by_cases ha : a ∈ C.P i
  · rw [C.valAt_of_mem ha, C.valAt_of_mem ((C.P i).mul_mem_right b ha), top_add]
  by_cases hb : b ∈ C.P i
  · rw [C.valAt_of_mem hb, C.valAt_of_mem ((C.P i).mul_mem_left a hb), add_top]
  have hab : a * b ∉ C.P i := fun h => ((C.isPrime i).mem_or_mem h).elim ha hb
  by_cases hi : i < n
  · have hτ := C.τ_prime hi
    have hmk : Ideal.Quotient.mk (C.P i) (a * b) =
        C.τ i ^ (C.ord i a + C.ord i b) *
          Ideal.Quotient.mk (C.P i) (C.residual i a * C.residual i b) := by
      rw [map_mul, map_mul, C.residual_spec i a, C.residual_spec i b, pow_add]
      ring
    have hc : C.residual i a * C.residual i b ∉ C.P (i + 1) := fun h =>
      ((C.isPrime (i + 1)).mem_or_mem h).elim (C.residual_notMem hi ha) (C.residual_notMem hi hb)
    obtain ⟨hk, hres⟩ := C.decomposition_unique hi hmk hc
    rw [C.valAt_of_lt hi hab, C.valAt_of_lt hi ha, C.valAt_of_lt hi hb, hk,
      C.valAt_congr (i + 1) (C.le_succ hi (by simpa using (C.P i).neg_mem hres)),
      valAt_mul (i + 1)]
    rw [show ((C.ord i a + C.ord i b : ℕ) : ℤ) = (C.ord i a : ℤ) + (C.ord i b : ℤ) by push_cast; ring,
      Pi.single_add, toLex_add, WithTop.coe_add]
    abel
  · rw [C.valAt_of_le (not_lt.mp hi) hab, C.valAt_of_le (not_lt.mp hi) ha,
      C.valAt_of_le (not_lt.mp hi) hb, add_zero]
termination_by n - i

/-- Lexicographic comparison of vectors agreeing below `i`. -/
theorem toLex_lt_of_coord {v w : Fin n → ℤ} (j : Fin n) (h0 : ∀ k < j, v k = w k)
    (hj : v j < w j) : toLex v < toLex w :=
  ⟨j, h0, hj⟩

theorem valAt_add_ge (i : ℕ) (a b : R) :
    min (C.valAt i a) (C.valAt i b) ≤ C.valAt i (a + b) := by
  by_cases ha : a ∈ C.P i
  · rw [C.valAt_of_mem ha, min_eq_right le_top, C.valAt_congr i (show a + b - b ∈ C.P i by simpa)]
  by_cases hb : b ∈ C.P i
  · rw [C.valAt_of_mem hb, min_eq_left le_top, C.valAt_congr i (show a + b - a ∈ C.P i by simpa)]
  by_cases hab : a + b ∈ C.P i
  · rw [C.valAt_of_mem hab]
    exact le_top
  by_cases hi : i < n
  swap
  · rw [C.valAt_of_le (not_lt.mp hi) ha, C.valAt_of_le (not_lt.mp hi) hb,
      C.valAt_of_le (not_lt.mp hi) hab, min_self]
  have hra := C.residual_spec i a
  have hrb := C.residual_spec i b
  -- the case `ord x < ord y`: the value of `x + y` is that of `x`
  have hlt : ∀ (x y : R), x ∉ C.P i → x + y ∉ C.P i →
      C.ord i x < C.ord i y → C.valAt i (x + y) = C.valAt i x := by
    intro x y hx hxy hlt
    have hT : C.T i ^ (C.ord i y - C.ord i x) * C.residual i y ∈ C.P (i + 1) :=
      (C.P (i + 1)).mul_mem_right _ (Ideal.pow_mem_of_mem _ (C.T_mem_succ hi) _ (by omega))
    have hmk : Ideal.Quotient.mk (C.P i) (x + y) = C.τ i ^ C.ord i x *
        Ideal.Quotient.mk (C.P i) (C.residual i x +
          C.T i ^ (C.ord i y - C.ord i x) * C.residual i y) := by
      rw [map_add, C.residual_spec i x, C.residual_spec i y, map_add, map_mul, map_pow]
      have : C.ord i y = C.ord i x + (C.ord i y - C.ord i x) := by omega
      conv_lhs => rw [this, pow_add]
      ring
    have hc : C.residual i x + C.T i ^ (C.ord i y - C.ord i x) * C.residual i y ∉
        C.P (i + 1) := by
      intro h
      apply C.residual_notMem hi hx
      simpa using (C.P (i + 1)).sub_mem h hT
    obtain ⟨hk, hres⟩ := C.decomposition_unique hi hmk hc
    rw [C.valAt_of_lt hi hxy, C.valAt_of_lt hi hx, hk]
    congr 1
    apply C.valAt_congr (i + 1)
    have h2 := (C.P (i + 1)).sub_mem hT (C.le_succ hi hres)
    convert h2 using 1
    ring
  rcases lt_trichotomy (C.ord i a) (C.ord i b) with hαβ | hαβ | hαβ
  · rw [hlt a b ha hab hαβ]
    exact min_le_left _ _
  · -- equal orders
    obtain ⟨wa, -, hwva, hva⟩ := C.valAt_decomp hi ha
    obtain ⟨wc, -, hwvc, hvc⟩ := C.valAt_decomp hi hab
    have hsum : Ideal.Quotient.mk (C.P i) (a + b) = C.τ i ^ C.ord i a *
        Ideal.Quotient.mk (C.P i) (C.residual i a + C.residual i b) := by
      rw [map_add, hra, hrb, ← hαβ, map_add, mul_add]
    have hγα : C.ord i a ≤ C.ord i (a + b) := by
      apply (C.finiteMultiplicity hi hab).le_multiplicity_of_pow_dvd
      rw [hsum]
      exact dvd_mul_right _ _
    rcases hγα.lt_or_eq with hγα | hγα
    · -- the order of `a + b` jumps: its value is larger
      refine (min_le_left _ _).trans (le_of_lt ?_)
      rw [hva, hvc]
      refine WithTop.coe_lt_coe.mpr (toLex_lt_of_coord (⟨i, hi⟩ : Fin n) (fun k hk => ?_) ?_)
      · have hk' : (k : ℕ) < i := hk
        have hne : k ≠ (⟨i, hi⟩ : Fin n) := fun h => by rw [h] at hk'; exact lt_irrefl _ hk'
        simp only [Pi.add_apply, hwva k (by omega), hwvc k (by omega), Pi.single_eq_of_ne hne]
      · simp only [Pi.add_apply, Pi.single_eq_same, hwva (⟨i, hi⟩ : Fin n) (by simp),
          hwvc (⟨i, hi⟩ : Fin n) (by simp), add_zero]
        exact_mod_cast hγα
    · -- same order: compare the residuals
      have hc : C.residual i a + C.residual i b ∉ C.P (i + 1) := by
        intro h
        apply (C.finiteMultiplicity hi hab).not_pow_dvd_of_multiplicity_lt
          (lt_add_one (C.ord i (a + b)))
        rw [← hγα, hsum, pow_succ]
        exact mul_dvd_mul_left _ ((C.τ_dvd_iff hi _).mpr h)
      obtain ⟨-, hres⟩ := C.decomposition_unique hi hsum hc
      have hcongr : C.valAt (i + 1) (C.residual i (a + b)) =
          C.valAt (i + 1) (C.residual i a + C.residual i b) :=
        C.valAt_congr (i + 1) (C.le_succ hi (by simpa using (C.P i).neg_mem hres))
      have hmin := valAt_add_ge (i + 1) (C.residual i a) (C.residual i b)
      rw [C.valAt_of_lt hi ha, C.valAt_of_lt hi hb, C.valAt_of_lt hi hab, hcongr, ← hγα,
        ← hαβ, min_add_add_left]
      exact add_le_add le_rfl hmin
  · rw [add_comm a b] at hab ⊢
    rw [hlt b a hb hab hαβ]
    exact min_le_right _ _
termination_by n - i

omit [IsNoetherianRing R] in
theorem P_mono {k : ℕ} : ∀ l, k ≤ l → l ≤ n → C.P k ≤ C.P l := by
  intro l hkl
  induction l, hkl using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ m hkm ih => intro hl; exact le_trans (ih (by omega)) (C.le_succ (by omega))

omit [IsNoetherianRing R] in
/-- The successive orders are nonnegative. -/
theorem valAt_nonneg (i : ℕ) (a : R) : 0 ≤ C.valAt i a := by
  by_cases ha : a ∈ C.P i
  · rw [C.valAt_of_mem ha]
    exact le_top
  by_cases hi : i < n
  · rw [C.valAt_of_lt hi ha]
    refine add_nonneg ?_ (valAt_nonneg (i + 1) _)
    refine WithTop.coe_nonneg.mpr ?_
    have h0 : (toLex (0 : Fin n → ℤ) : Lex (Fin n → ℤ)) = 0 := rfl
    rw [← h0]
    apply Pi.toLex_monotone
    intro j
    by_cases hj : j = ⟨i, hi⟩
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  · rw [C.valAt_of_le (not_lt.mp hi) ha]
termination_by n - i

/-- The successive orders are positive on the last member `P n` (the maximal ideal of the
point `Yₙ`). -/
theorem valAt_pos (i : ℕ) (hin : i ≤ n) {a : R} (ha : a ∈ C.P n) : 0 < C.valAt i a := by
  by_cases hai : a ∈ C.P i
  · rw [C.valAt_of_mem hai]
    exact WithTop.coe_lt_top 0
  have hi : i < n := by
    rcases hin.lt_or_eq with h | rfl
    · exact h
    · exact absurd ha hai
  obtain ⟨w, -, hwv, hv⟩ := C.valAt_decomp hi hai
  by_cases hk : C.ord i a = 0
  · -- the residual is congruent to `a`, hence also on `Yₙ`
    have hdec := C.residual_spec i a
    rw [hk, pow_zero, one_mul] at hdec
    have hres : C.residual i a ∈ C.P n := by
      have h1 : C.residual i a - a ∈ C.P i := by
        rw [← Ideal.Quotient.eq]
        exact hdec.symm
      have h2 := C.P_mono n hin le_rfl h1
      simpa using (C.P n).add_mem h2 ha
    rw [C.valAt_of_lt hi hai, hk]
    simpa using valAt_pos (i + 1) hi hres
  · rw [hv]
    refine WithTop.coe_lt_coe.mpr (toLex_lt_of_coord (⟨i, hi⟩ : Fin n) (fun j hj => ?_) ?_)
    · have hj' : (j : ℕ) < i := hj
      have hne : j ≠ (⟨i, hi⟩ : Fin n) := fun h => by rw [h] at hj'; exact lt_irrefl _ hj'
      simp [Pi.single_eq_of_ne hne, hwv j (by omega)]
    · simp only [Pi.add_apply, Pi.single_eq_same, hwv (⟨i, hi⟩ : Fin n) (by simp), add_zero]
      exact_mod_cast Nat.pos_of_ne_zero hk
termination_by n - i

/-! ### The valuation -/

/-- **`ν_{Y•}` on `R`**: the successive orders from the first member on. -/
def valuation : AddValuation R (WithTop (Lex (Fin n → ℤ))) :=
  AddValuation.of (C.valAt 0) (C.valAt_of_mem (C.P 0).zero_mem)
    (C.valAt_one 0 ((Ideal.ne_top_iff_one _).mp (C.isPrime 0).ne_top)) (C.valAt_add_ge 0)
    (C.valAt_mul 0)

theorem valuation_apply (a : R) : C.valuation a = C.valAt 0 a := rfl

theorem valuation_eq_top_iff (a : R) : C.valuation a = ⊤ ↔ a ∈ C.P 0 :=
  C.valAt_eq_top_iff 0 a

/-- The first coordinate of `ν(a)` is `ord_{Y₁}(a)`, the multiplicity of `τ₀`. -/
theorem valuation_apply_zero_coord (hn : 0 < n) {a : R} (ha : a ∉ C.P 0) :
    ∃ w : Fin n → ℤ, C.valuation a = ((toLex w : Lex (Fin n → ℤ)) : WithTop _) ∧
      w ⟨0, hn⟩ = (C.ord 0 a : ℤ) := by
  obtain ⟨w, -, hwv, hv⟩ := C.valAt_decomp hn ha
  refine ⟨_, hv, ?_⟩
  simp [hwv ⟨0, hn⟩ (by simp)]

/-- `ν(T i)` is the `i`-th standard basis vector: `T i ∉ P j` for `j ≤ i`, its orders vanish
before step `i` and are `1` at step `i`. -/
theorem valAt_T {i : ℕ} (hi : i < n) (j : ℕ) (hj : j ≤ i) :
    C.valAt j (C.T i) = ((toLex (Pi.single (⟨i, hi⟩ : Fin n) (1 : ℤ)) : Lex (Fin n → ℤ)) :
      WithTop (Lex (Fin n → ℤ))) := by
  have hPj : ∀ k ≤ i, C.P k ≤ C.P i := fun k hk => C.P_mono i hk hi.le
  have hT : C.T i ∉ C.P j := fun h => C.T_notMem i hi (hPj j hj h)
  have hj' : j < n := by omega
  rcases hj.lt_or_eq with hji | rfl
  · -- `T i ∉ P (j+1)`: order `0`, residual `T i`
    have hT1 : C.T i ∉ C.P (j + 1) := fun h => C.T_notMem i hi (hPj (j + 1) (by omega) h)
    obtain ⟨hk, hres⟩ := C.decomposition_unique hj' (a := C.T i) (c := C.T i) (k := 0)
      (by rw [pow_zero, one_mul]) hT1
    rw [C.valAt_of_lt hj' hT, hk, C.valAt_congr (j + 1) (C.le_succ hj' (by
      simpa using (C.P j).neg_mem hres)), valAt_T hi (j + 1) (by omega)]
    simp
  · -- step `i`: order `1`, residual `1`
    have h1 : (1 : R) ∉ C.P (j + 1) := (C.isPrime (j + 1)).ne_top ∘ (Ideal.eq_top_iff_one _).mpr
    obtain ⟨hk, hres⟩ := C.decomposition_unique hj' (a := C.T j) (c := 1) (k := 1)
      (by rw [pow_one, map_one, mul_one]) h1
    rw [C.valAt_of_lt hj' hT, hk, C.valAt_congr (j + 1) (C.le_succ hj' (by
      simpa using (C.P j).neg_mem hres)), C.valAt_one (j + 1) h1]
    simp
termination_by n - j

/-! ### Independence of the local equations -/

/-- **`ν_{Y•}` does not depend on the choice of the local defining equations**: two chains of
local equations of the same members give the same successive orders. (A second equation of
`Yᵢ₊₁` in `Yᵢ` is a unit multiple of the first; units have value `0`.) -/
theorem valAt_eq_of_P_eq (C' : LocalEquationChain R n) (hP : C.P = C'.P) (i : ℕ) (a : R) :
    C.valAt i a = C'.valAt i a := by
  have hPi : ∀ j, C'.P j = C.P j := fun j => (congrFun hP j).symm
  by_cases ha : a ∈ C.P i
  · rw [C.valAt_of_mem ha, C'.valAt_of_mem (by rw [hPi]; exact ha)]
  have ha' : a ∉ C'.P i := by rw [hPi]; exact ha
  by_cases hi : i < n
  swap
  · rw [C.valAt_of_le (not_lt.mp hi) ha, C'.valAt_of_le (not_lt.mp hi) ha']
  -- `T' ≡ u T` and `T ≡ u' T'` modulo `P i`
  have hT' : C'.T i ∈ C.P (i + 1) := by rw [← hPi]; exact C'.T_mem_succ hi
  have hT : C.T i ∈ C'.P (i + 1) := by rw [hPi]; exact C.T_mem_succ hi
  obtain ⟨u, hu⟩ := (C.mem_succ_iff hi _).mp hT'
  obtain ⟨u', hu'⟩ := (C'.mem_succ_iff hi _).mp hT
  rw [hPi] at hu'
  -- `u u' ≡ 1`
  have huu' : u * u' - 1 ∈ C.P i := by
    have h1 : C.T i - u' * (u * C.T i) ∈ C.P i := by
      have := (C.P i).add_mem hu' ((C.P i).mul_mem_left u' hu)
      convert this using 1
      ring
    have h2 : (1 - u * u') * C.T i ∈ C.P i := by
      convert h1 using 1
      ring
    rcases (C.isPrime i).mem_or_mem h2 with h | h
    · simpa using (C.P i).neg_mem h
    · exact absurd h (C.T_notMem i hi)
  have hu1 : u ∉ C.P (i + 1) := by
    intro h
    apply (C.isPrime (i + 1)).ne_top
    rw [Ideal.eq_top_iff_one]
    have := (C.P (i + 1)).sub_mem ((C.P (i + 1)).mul_mem_right u' h) (C.le_succ hi huu')
    simpa using this
  -- `u` has value `0` from step `i + 1` on
  have hu0 : C.valAt (i + 1) u = 0 := by
    have h1 : C.valAt (i + 1) (u * u') = 0 := by
      rw [C.valAt_congr (i + 1) (C.le_succ hi huu'), C.valAt_one (i + 1)
        (fun h => (C.isPrime (i + 1)).ne_top ((Ideal.eq_top_iff_one _).mpr h))]
    rw [C.valAt_mul] at h1
    refine le_antisymm ?_ (C.valAt_nonneg _ _)
    rw [← h1]
    exact le_add_of_nonneg_right (C.valAt_nonneg _ _)
  -- the decomposition of `a` for `C'`, read for `C`
  set k := C'.ord i a with hk
  set r := C'.residual i a with hr
  have hdec : a - C'.T i ^ k * r ∈ C.P i := by
    rw [← hPi, ← Ideal.Quotient.eq, map_mul, map_pow]
    exact C'.residual_spec i a
  have hr1 : r ∉ C.P (i + 1) := by rw [← hPi]; exact C'.residual_notMem hi ha'
  have hdec' : Ideal.Quotient.mk (C.P i) a =
      C.τ i ^ k * Ideal.Quotient.mk (C.P i) (u ^ k * r) := by
    have hTT : Ideal.Quotient.mk (C.P i) (C'.T i) =
        Ideal.Quotient.mk (C.P i) u * C.τ i := by
      rw [← map_mul]
      exact Ideal.Quotient.eq.mpr hu
    rw [Ideal.Quotient.eq.mpr hdec, map_mul, map_pow, hTT, map_mul, map_pow, mul_pow]
    ring
  have hc : u ^ k * r ∉ C.P (i + 1) := fun h =>
    ((C.isPrime (i + 1)).mem_or_mem h).elim
      (fun h' => hu1 ((C.isPrime (i + 1)).mem_of_pow_mem k h')) hr1
  obtain ⟨hord, hres⟩ := C.decomposition_unique hi hdec' hc
  rw [C.valAt_of_lt hi ha, C'.valAt_of_lt hi ha', hord,
    C.valAt_congr (i + 1) (C.le_succ hi (by simpa using (C.P i).neg_mem hres)),
    C.valAt_mul, show C.valAt (i + 1) (u ^ k) = 0 by
      induction k with
      | zero =>
        rw [pow_zero]
        exact C.valAt_one (i + 1) (fun h => (C.isPrime (i + 1)).ne_top
          ((Ideal.eq_top_iff_one _).mpr h))
      | succ k ih => rw [pow_succ, C.valAt_mul, ih, hu0, add_zero],
    zero_add, valAt_eq_of_P_eq C' hP (i + 1) r]
termination_by n - i

theorem valuation_eq_of_P_eq (C' : LocalEquationChain R n) (hP : C.P = C'.P) :
    C.valuation = C'.valuation := by
  ext a
  exact C.valAt_eq_of_P_eq C' hP 0 a

/-! ### The extension to the fraction field -/

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem nonZeroDivisors_le_primeCompl (h0 : C.P 0 = ⊥) :
    nonZeroDivisors R ≤ C.valuation.toValuation.supp.primeCompl := by
  have : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact (C.isPrime 0).ne_top (Subsingleton.elim _ _)
  intro a ha
  change C.valuation a ≠ ⊤
  rw [ne_eq, C.valuation_eq_top_iff, h0, Ideal.mem_bot]
  exact nonZeroDivisors.ne_zero ha

/-- **`ν_{Y•}` on the fraction field** (`ℂ(X)`). -/
def fractionValuation (h0 : C.P 0 = ⊥) : AddValuation K (WithTop (Lex (Fin n → ℤ))) :=
  C.valuation.toValuation.extendToLocalization
    (C.nonZeroDivisors_le_primeCompl h0) K

theorem fractionValuation_algebraMap (h0 : C.P 0 = ⊥) (a : R) :
    C.fractionValuation K h0 (algebraMap R K a) = C.valAt 0 a :=
  Valuation.extendToLocalization_apply_map_apply C.valuation.toValuation
    (C.nonZeroDivisors_le_primeCompl h0) K a

theorem fractionValuation_T (h0 : C.P 0 = ⊥) {i : ℕ} (hi : i < n) :
    C.fractionValuation K h0 (algebraMap R K (C.T i)) =
      ((toLex (Pi.single (⟨i, hi⟩ : Fin n) (1 : ℤ)) : Lex (Fin n → ℤ)) :
        WithTop (Lex (Fin n → ℤ))) := by
  rw [C.fractionValuation_algebraMap K h0, C.valAt_T hi 0 (Nat.zero_le i)]

/-- **`ν_{Y•}` is surjective onto `ℤⁿ ∪ {∞}`**: a valuation of rank `n` with value group
`ℤⁿ_lex`. -/
theorem fractionValuation_surjective (h0 : C.P 0 = ⊥) :
    Function.Surjective (C.fractionValuation K h0) := by
  classical
  set v := C.fractionValuation K h0 with hv
  -- the values of nonzero elements form a subgroup containing the basis vectors
  let G : AddSubgroup (Fin n → ℤ) :=
    { carrier := {w | ∃ q : K, q ≠ 0 ∧ v q = ((toLex w : Lex (Fin n → ℤ)) : WithTop _)}
      add_mem' := by
        rintro x y ⟨p, hp0, hp⟩ ⟨q, hq0, hq⟩
        refine ⟨p * q, mul_ne_zero hp0 hq0, ?_⟩
        rw [v.map_mul, hp, hq, ← WithTop.coe_add, ← toLex_add]
      zero_mem' := ⟨1, one_ne_zero, by rw [v.map_one]; rfl⟩
      neg_mem' := by
        rintro x ⟨p, hp0, hp⟩
        refine ⟨p⁻¹, inv_ne_zero hp0, ?_⟩
        rw [AddValuation.map_inv, hp]
        rfl }
  have hbasis : ∀ i : Fin n, Pi.single i (1 : ℤ) ∈ G := by
    intro i
    refine ⟨algebraMap R K (C.T i), ?_, C.fractionValuation_T K h0 i.2⟩
    intro h
    have h' := congrArg v h
    rw [C.fractionValuation_T K h0 i.2, v.map_zero] at h'
    exact WithTop.coe_ne_top h'
  have hall : ∀ w : Fin n → ℤ, w ∈ G := by
    intro w
    have hw : w = ∑ i, w i • Pi.single i (1 : ℤ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hw]
    exact G.sum_mem fun i _ => G.zsmul_mem (hbasis i) _
  intro x
  induction x using WithTop.recTopCoe with
  | top => exact ⟨0, v.map_zero⟩
  | coe x =>
    obtain ⟨q, -, hq⟩ := hall (ofLex x)
    exact ⟨q, hq⟩

theorem fractionValuation_eq_of_P_eq (C' : LocalEquationChain R n) (hP : C.P = C'.P)
    (h0 : C.P 0 = ⊥) :
    C.fractionValuation K h0 = C'.fractionValuation K (by rw [← hP]; exact h0) := by
  ext g
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) g
  rw [AddValuation.map_div, AddValuation.map_div, C.fractionValuation_algebraMap,
    C.fractionValuation_algebraMap, C'.fractionValuation_algebraMap,
    C'.fractionValuation_algebraMap, C.valAt_eq_of_P_eq C' hP, C.valAt_eq_of_P_eq C' hP]

end LocalEquationChain

end SGPT.Okounkov.OF5
