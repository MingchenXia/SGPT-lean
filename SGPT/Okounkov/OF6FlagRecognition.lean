import SGPT.Okounkov.OF5SuccessiveOrder
import SGPT.Okounkov.ValCurrLexEquivalence

/-!
# Recognizing flag valuations up to equivalence

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`:

*Conversely, maximal-rank valuations of `ℂ(X)` are closely related to flag valuations. More
precisely, if a valuation has value group identified with `ℤⁿ_lex` and maximal rational rank `n`,
then [CFKLRS17, Theorem 2.9] shows that it is equivalent to, but not necessarily equal to, a
valuation induced by an admissible flag on a modification of `X`.*

(equivalence: `ν' = ν G` with `G = I + N`, `N` strictly upper triangular.)

This file proves the algebraic criterion which decides, for a given flag, *which* valuations are
equivalent to its flag valuation, and with *which* matrix `G`. Let `R` be a Noetherian ring with a
chain of local defining equations `P (i+1) = P i + (T i)` (the `LocalEquationChain`; for an
admissible flag `R = 𝒪_{X,Yₙ}`, `P i` the prime of `Yᵢ`, `T i` the local equation `t_{i+1}` of
`Y_{i+1}` in `Yᵢ`) and let `ν_C` be its successive-order valuation (`ν_{Y•}`).

**Recognition theorem** (`eq_valuation`, `eq_fractionValuation`): a valuation `v` with values in
`ℤⁿ_lex ∪ {∞}` which is nonnegative on `R`, vanishes off `P n`, is `∞` on `P 0`, and takes the
standard basis values `v(T i) = eᵢ` on the local equations, *is* `ν_C`. No completion,
dimension theory or Abhyankar inequality is needed: writing `a ≡ Tᵢᵏ r (mod P i)` with
`r ∉ P (i+1)`, the correction `a - Tᵢᵏ r ∈ P i = P 0 + (T 0, …, T (i-1))` has value
`≥ e_{i-1}`, which is lexicographically larger than every value vanishing below `i`; a downward
induction on `i` then identifies `v` with the successive orders.

**Equivalence criterion** (`eq_lexMap_fractionValuation_iff`): `v = ν_C G` for a unitriangular `G`
iff `v ≥ 0` on `R`, `v = 0` off `P n` and `v(T i)` is the `i`-th row of `G`. Hence (`G` is the
matrix of the values of the local equations, `lexEquivalent_fractionValuation_iff`) a valuation is
equivalent to `ν_C` iff it is nonnegative on `R`, vanishes off `P n`, and the matrix of the values
`v(T 0), …, v(T (n-1))` is unit upper triangular. The scheme-level form for admissible flags is in
`SGPT.Okounkov.OF6AdmissibleRecognition`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open SGPT.Okounkov.OF5 SGPT.Okounkov.ValCurr

/-- The standard basis vector `eᵢ` of `ℤⁿ_lex`, as a value in `ℤⁿ_lex ∪ {∞}`. -/
abbrev basisValue {n : ℕ} (i : Fin n) : WithTop (Lex (Fin n → ℤ)) :=
  ((toLex (Pi.single i (1 : ℤ)) : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))

/-- The value `toLex x ∈ ℤⁿ_lex ∪ {∞}` of an integer vector. -/
abbrev vecValue {n : ℕ} (x : Fin n → ℤ) : WithTop (Lex (Fin n → ℤ)) :=
  ((toLex x : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))

/-- `e_i < e_j` for `j < i` in `ℤⁿ_lex`. -/
theorem basisValue_lt {n : ℕ} {i j : Fin n} (h : j < i) : basisValue i < basisValue j := by
  refine WithTop.coe_lt_coe.mpr ⟨j, fun k hk => ?_, ?_⟩
  · have hki : k ≠ i := (lt_trans hk h).ne
    have hkj : k ≠ j := hk.ne
    simp [hki, hkj]
  · simp [h.ne']

/-- A nonnegative and a further nonnegative value adding up to `0` vanish. -/
theorem eq_zero_of_add_eq_zero {n : ℕ} {x y : WithTop (Lex (Fin n → ℤ))} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (h : x + y = 0) : x = 0 :=
  le_antisymm (by
    calc x ≤ x + y := le_add_of_nonneg_right hy
      _ = 0 := h) hx

namespace LocalEquationChain

variable {R : Type*} [CommRing R] {n : ℕ} (C : OF5.LocalEquationChain R n)

/-! ### The lower bound on the members -/

/-- **Elements of `P (i+1)` have value `≥ eᵢ`** for every valuation which is nonnegative on `R`,
`∞` on `P 0` and takes the values `v(T j) = e_j`: `P (i+1) = P 0 + (T 0, …, T i)` and
`e_j ≥ eᵢ` for `j ≤ i`. -/
theorem basisValue_le_of_mem (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = basisValue ⟨i, hi⟩) :
    ∀ (i : ℕ) (hi : i < n) (a : R), a ∈ C.P (i + 1) → basisValue ⟨i, hi⟩ ≤ v a := by
  intro i
  induction i with
  | zero =>
    intro hi a ha
    rw [C.succ_eq 0 hi, Submodule.mem_sup] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    refine v.map_le_add ?_ ?_
    · rw [htop b hb]
      exact le_top
    · rw [v.map_mul, hT 0 hi]
      exact le_add_of_nonneg_left (hnonneg d)
  | succ k ih =>
    intro hi a ha
    rw [C.succ_eq (k + 1) hi, Submodule.mem_sup] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    refine v.map_le_add ?_ ?_
    · refine le_trans (basisValue_lt ?_).le (ih (by omega) b hb)
      change k < k + 1
      omega
    · rw [v.map_mul, hT (k + 1) hi]
      exact le_add_of_nonneg_left (hnonneg d)

variable [IsNoetherianRing R]

/-! ### Auxiliary identities for the successive orders -/

theorem valAt_pow (i : ℕ) (x : R) : ∀ k : ℕ, C.valAt i (x ^ k) = k • C.valAt i x
  | 0 => by
    rw [pow_zero, zero_smul]
    exact C.valAt_one i (fun h => (C.isPrime i).ne_top ((Ideal.eq_top_iff_one _).mpr h))
  | k + 1 => by rw [pow_succ, C.valAt_mul, valAt_pow i x k, succ_nsmul]

/-- Off `P (i+1)` the order at step `i` vanishes: `valAt i r = valAt (i+1) r`. -/
theorem valAt_eq_valAt_succ {i : ℕ} (hi : i < n) {r : R} (hr : r ∉ C.P (i + 1)) :
    C.valAt i r = C.valAt (i + 1) r := by
  have hri : r ∉ C.P i := fun h => hr (C.le_succ hi h)
  obtain ⟨hk, hres⟩ := C.decomposition_unique hi (a := r) (c := r) (k := 0)
    (by rw [pow_zero, one_mul]) hr
  rw [C.valAt_of_lt hi hri, hk, C.valAt_congr (i + 1) (C.le_succ hi (by
    simpa using (C.P i).neg_mem hres))]
  simp

/-- `ν_C` vanishes off the last member `P n`. -/
theorem valAt_eq_zero_of_notMem_last (i : ℕ) (hin : i ≤ n) {a : R} (ha : a ∉ C.P n) :
    C.valAt i a = 0 := by
  rcases hin.lt_or_eq with hi | rfl
  · have ha' : a ∉ C.P (i + 1) := fun h => ha (C.P_mono n (by omega) le_rfl h)
    rw [valAt_eq_valAt_succ C hi ha']
    exact valAt_eq_zero_of_notMem_last (i + 1) hi ha
  · exact C.valAt_of_le le_rfl ha
termination_by n - i

/-- A value off `P i`, `i < n`, is lexicographically smaller than every value of an element of
`P i`. -/
theorem valAt_lt_of_mem (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = basisValue ⟨i, hi⟩)
    {i : ℕ} (hi : i < n) {a b : R} (ha : a ∉ C.P i) (hb : b ∈ C.P i) :
    C.valAt i a < v b := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [htop b hb]
    exact lt_top_iff_ne_top.mpr (fun h => ha ((C.valAt_eq_top_iff 0 a).mp h))
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨w, -, hwv, hv⟩ := C.valAt_decomp hi ha
  refine lt_of_lt_of_le ?_ (basisValue_le_of_mem C v hnonneg htop hT j (by omega) b hb)
  rw [hv]
  refine WithTop.coe_lt_coe.mpr (OF5.LocalEquationChain.toLex_lt_of_coord (⟨j, by omega⟩ : Fin n)
    (fun k hk => ?_) ?_)
  · have hk' : (k : ℕ) < j := hk
    have hne : k ≠ (⟨j + 1, hi⟩ : Fin n) := fun h => by
      rw [h] at hk'
      exact absurd hk' (by simp)
    have hne' : k ≠ (⟨j, by omega⟩ : Fin n) := fun h => by
      rw [h] at hk'
      exact lt_irrefl _ hk'
    simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne', hwv k (by omega)]
  · have hne : (⟨j, by omega⟩ : Fin n) ≠ (⟨j + 1, hi⟩ : Fin n) := fun h => by
      simp at h
    simp [hwv (⟨j, by omega⟩ : Fin n) (by simp)]

/-! ### The recognition theorem -/

/-- **Main step**: under the hypotheses of the recognition theorem, `v = valAt i` off `P i`, by a
downward induction on `i`. -/
theorem eq_valAt_of_notMem (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = basisValue ⟨i, hi⟩)
    (hunit : ∀ a, a ∉ C.P n → v a = 0) (i : ℕ) (hin : i ≤ n) (a : R) (ha : a ∉ C.P i) :
    v a = C.valAt i a := by
  rcases hin.lt_or_eq with hi | rfl
  · have hr : C.residual i a ∉ C.P (i + 1) := C.residual_notMem hi ha
    have hdiff : a - C.T i ^ C.ord i a * C.residual i a ∈ C.P i := by
      rw [← Ideal.Quotient.eq, map_mul, map_pow]
      exact C.residual_spec i a
    have hIH := eq_valAt_of_notMem v hnonneg htop hT hunit (i + 1) hi (C.residual i a) hr
    have hmain : v (C.T i ^ C.ord i a * C.residual i a) = C.valAt i a := by
      rw [v.map_mul, v.map_pow, hT i hi, hIH, C.valAt_congr i hdiff, C.valAt_mul, valAt_pow C,
        C.valAt_T hi i le_rfl, valAt_eq_valAt_succ C hi hr]
    have hlt : v (C.T i ^ C.ord i a * C.residual i a) <
        v (a - C.T i ^ C.ord i a * C.residual i a) := by
      rw [hmain]
      exact valAt_lt_of_mem C v hnonneg htop hT hi ha hdiff
    have hsum := v.map_add_eq_of_lt_left hlt
    rw [add_sub_cancel] at hsum
    rw [hsum, hmain]
  · rw [C.valAt_of_le le_rfl ha]
    exact hunit a ha
termination_by n - i

/-- **Recognition theorem** (on `R`): a valuation `v : R → ℤⁿ_lex ∪ {∞}` which is nonnegative,
`∞` on `P 0`, `0` off `P n`, and takes the standard basis values `v(T i) = eᵢ` on the local
equations is the successive-order valuation `ν_C`. -/
theorem eq_valuation (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = basisValue ⟨i, hi⟩)
    (hunit : ∀ a, a ∉ C.P n → v a = 0) : v = C.valuation := by
  refine AddValuation.ext fun a => ?_
  rw [C.valuation_apply]
  by_cases ha : a ∈ C.P 0
  · rw [htop a ha, C.valAt_of_mem ha]
  · exact eq_valAt_of_notMem C v hnonneg htop hT hunit 0 (Nat.zero_le n) a ha

/-! ### On the fraction field -/

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- `ν_C ≥ 0` on `R`. -/
theorem fractionValuation_nonneg (h0 : C.P 0 = ⊥) (a : R) :
    0 ≤ C.fractionValuation K h0 (algebraMap R K a) := by
  rw [C.fractionValuation_algebraMap]
  exact C.valAt_nonneg 0 a

/-- `ν_C = 0` off `P n`. -/
theorem fractionValuation_eq_zero (h0 : C.P 0 = ⊥) {a : R} (ha : a ∉ C.P n) :
    C.fractionValuation K h0 (algebraMap R K a) = 0 := by
  rw [C.fractionValuation_algebraMap]
  exact valAt_eq_zero_of_notMem_last C 0 (Nat.zero_le n) ha

/-- **Recognition theorem** (on the fraction field `K`, e.g. `ℂ(X)`): a valuation of `K` with
values in `ℤⁿ_lex ∪ {∞}`, nonnegative on `R`, `0` off `P n`, with `v(T i) = eᵢ`, is `ν_C`. -/
theorem eq_fractionValuation (h0 : C.P 0 = ⊥) (v : AddValuation K (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a))
    (hT : ∀ (i : ℕ) (hi : i < n), v (algebraMap R K (C.T i)) = basisValue ⟨i, hi⟩)
    (hunit : ∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0) :
    v = C.fractionValuation K h0 := by
  have htop : ∀ a ∈ C.P 0, v.comap (algebraMap R K) a = ⊤ := by
    intro a ha
    rw [h0, Ideal.mem_bot] at ha
    subst ha
    change v (algebraMap R K 0) = ⊤
    rw [map_zero, v.map_zero]
  have hc := eq_valuation C (v.comap (algebraMap R K)) hnonneg htop hT hunit
  have hR : ∀ a : R, v (algebraMap R K a) = C.fractionValuation K h0 (algebraMap R K a) := by
    intro a
    rw [C.fractionValuation_algebraMap, ← C.valuation_apply, ← hc]
    rfl
  refine AddValuation.ext fun g => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) g
  rw [AddValuation.map_div, AddValuation.map_div, hR a, hR b]

/-- **Equivalence criterion**: for a unitriangular `G` (`G = I + N`), `v = ν_C G` as soon as `v`
is nonnegative on `R`, vanishes off `P n` and `v(T i)` is the `i`-th row of `G`. -/
theorem eq_lexMap_fractionValuation (h0 : C.P 0 = ⊥)
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ))))
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G)
    (hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a))
    (hT : ∀ (i : ℕ) (hi : i < n), v (algebraMap R K (C.T i)) = vecValue (G ⟨i, hi⟩))
    (hunit : ∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0) :
    v = lexMapValuation G hG (C.fractionValuation K h0) := by
  set v' := lexMapValuation G⁻¹ hG.inv v with hv'
  have hzero : lexWithTopHom G⁻¹ hG.inv 0 = 0 := map_zero _
  have h' : v' = C.fractionValuation K h0 := by
    refine eq_fractionValuation C K h0 v' (fun a => ?_) (fun i hi => ?_) (fun a ha => ?_)
    · rw [hv', lexMapValuation_apply, ← hzero]
      exact monotone_lexWithTopHom _ _ (hnonneg a)
    · rw [hv', lexMapValuation_apply, hT i hi, lexWithTopHom_coe, ofLex_toLex]
      congr 2
      have hrow : G ⟨i, hi⟩ = Matrix.vecMul (Pi.single (⟨i, hi⟩ : Fin n) (1 : ℤ)) G := by
        rw [Matrix.single_vecMul, one_smul]
        rfl
      rw [hrow, Matrix.vecMul_vecMul, hG.mul_inv, Matrix.vecMul_one]
    · rw [hv', lexMapValuation_apply, hunit a ha, hzero]
  refine AddValuation.ext fun g => ?_
  rw [lexMapValuation_apply, ← h', hv', lexMapValuation_apply, lexWithTopHom_mul,
    lexWithTopHom_congr hG.inv_mul _ IsUnitUpperTriangular.one, lexWithTopHom_one]

/-- The values of `ν_C G` on the local equations: the rows of `G`. -/
theorem lexMap_fractionValuation_T (h0 : C.P 0 = ⊥) (G : Matrix (Fin n) (Fin n) ℤ)
    (hG : IsUnitUpperTriangular G) {i : ℕ} (hi : i < n) :
    lexMapValuation G hG (C.fractionValuation K h0) (algebraMap R K (C.T i)) =
      vecValue (G ⟨i, hi⟩) := by
  rw [lexMapValuation_apply, C.fractionValuation_algebraMap, C.valAt_T hi 0 (Nat.zero_le i),
    lexWithTopHom_coe, ofLex_toLex, Matrix.single_vecMul, one_smul]
  rfl

/-- **Equivalence criterion (iff form)**: for a unitriangular `G`, `v = ν_C G` iff `v` is
nonnegative on `R`, vanishes off `P n`, and `v(T i) = G_i` (the `i`-th row of `G`). -/
theorem eq_lexMap_fractionValuation_iff (h0 : C.P 0 = ⊥)
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ))))
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : IsUnitUpperTriangular G) :
    v = lexMapValuation G hG (C.fractionValuation K h0) ↔
      (∀ a : R, 0 ≤ v (algebraMap R K a)) ∧
      (∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0) ∧
      ∀ (i : ℕ) (hi : i < n), v (algebraMap R K (C.T i)) = vecValue (G ⟨i, hi⟩) := by
  refine ⟨?_, fun ⟨h1, h2, h3⟩ => eq_lexMap_fractionValuation C K h0 v G hG h1 h3 h2⟩
  rintro rfl
  have hzero : lexWithTopHom G hG 0 = 0 := map_zero _
  refine ⟨fun a => ?_, fun a ha => ?_, fun i hi => lexMap_fractionValuation_T C K h0 G hG hi⟩
  · rw [lexMapValuation_apply, ← hzero]
    exact monotone_lexWithTopHom _ _ (fractionValuation_nonneg C K h0 a)
  · rw [lexMapValuation_apply, fractionValuation_eq_zero C K h0 ha, hzero]

/-- The matrix of the values of the local equations: row `i` is `v(T i)` (read as an integer
vector; `0` if `v(T i) = ∞`). -/
def valueMatrix (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) : Matrix (Fin n) (Fin n) ℤ :=
  fun i => ofLex ((v (algebraMap R K (C.T i))).untopD 0)

omit [IsNoetherianRing R] in
theorem vecValue_valueMatrix (v : AddValuation K (WithTop (Lex (Fin n → ℤ))))
    {i : ℕ} (hi : i < n) :
    vecValue (valueMatrix C K v ⟨i, hi⟩) = v (algebraMap R K (C.T i)) := by
  have hne : v (algebraMap R K (C.T i)) ≠ ⊤ := by
    rw [AddValuation.ne_top_iff, ne_eq,
      map_eq_zero_iff _ (IsFractionRing.injective R K)]
    intro h
    exact C.T_notMem i hi (by rw [h]; exact Ideal.zero_mem _)
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hne
  unfold valueMatrix vecValue
  rw [← hx, WithTop.untopD_coe, toLex_ofLex]

/-- **Which valuations are equivalent to `ν_C`** (`rmk:Abhyankar`, *equivalent to, but not
necessarily equal to*): `v ∼ ν_C` (`v = ν_C G` with `G = I + N`) iff `v` is nonnegative on `R`,
vanishes off `P n`, and the matrix of the values `v(T 0), …, v(T (n-1))` of the local equations
is unit upper triangular; then `v = ν_C G` with `G` that matrix (and with no other `G`). -/
theorem lexEquivalent_fractionValuation_iff (h0 : C.P 0 = ⊥)
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) :
    ValuationsLexEquivalent (C.fractionValuation K h0) v ↔
      (∀ a : R, 0 ≤ v (algebraMap R K a)) ∧
      (∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0) ∧
      IsUnitUpperTriangular (valueMatrix C K v) := by
  constructor
  · rintro ⟨G, hG, hv⟩
    obtain ⟨h1, h2, h3⟩ := (eq_lexMap_fractionValuation_iff C K h0 v G hG).mp hv
    refine ⟨h1, h2, ?_⟩
    have hGM : valueMatrix C K v = G := by
      funext i
      unfold valueMatrix
      rw [h3 i i.2, WithTop.untopD_coe, ofLex_toLex]
    rw [hGM]
    exact hG
  · rintro ⟨h1, h2, h3⟩
    refine ⟨valueMatrix C K v, h3, eq_lexMap_fractionValuation C K h0 v _ h3 h1
      (fun i hi => (vecValue_valueMatrix C K v hi).symm) h2⟩

end LocalEquationChain

end SGPT.Okounkov.OF6
