import SGPT.Okounkov.OF6AdmissibleRecognition
import SGPT.Okounkov.FlagValuationGenericCenters

/-!
# Valuations whose prefix centres form an admissible flag

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`: *if a valuation has value group
identified with `ℤⁿ_lex` and maximal rational rank `n`, then [CFKLRS17, Theorem 2.9] shows that it
is equivalent to, but not necessarily equal to, a valuation induced by an admissible flag on a
modification of `X`.*

A valuation `ν : ℂ(X)^× → ℤⁿ_lex` has coarsenings `ν_{≤k}` (its first `k` coordinates,
`SGPT.Okounkov.ValCurr.prefixValuation`); on a proper `X` each has a centre `η_k`. This file proves
that `ν` is equivalent to an admissible-flag valuation **as soon as these centres form an
admissible flag** — the flag is then forced to be `Y_k = {η_k}‾`:

* `lexEquivalent_admissibleFlagValuation_of_prefixCentres`: let `Y•` be an admissible flag on `X`
  (integral, smooth of relative dimension `n` over `ℂ`) and `ν` a surjective valuation of `ℂ(X)`
  with values in `ℤⁿ_lex`, centred at the point `Yₙ`, such that for every `k` the centre of the
  coarsening `ν_{≤k}` is the generic point of `Y_k`. Then `ν ∼ ν_{Y•}`, namely `ν = ν_{Y•} G` with
  `G = (ν(tᵢ))ᵢ` the matrix of the values of local equations.

Hence [CFKLRS17, Thm 2.9] is equivalent to the existence of a modification of `X` on which the
prefix centres of `ν` form an admissible flag (the converse being `SGPT.Okounkov.OF6`'s
`isValuationCenter_of_lexEquivalent` together with the prefix-centre invariance of lane OF2).

The proof is a recognition theorem for upper triangular matrices with positive diagonal
(`LocalEquationChain.eq_vecMul_valAt_of_notMem`): the prefix centres force `ν(tᵢ)` to vanish in the
coordinates before `i` and to be positive in coordinate `i`; then `ν = (x ↦ x G) ∘ ν_{Y•}` on
`𝒪_{X,Yₙ}`, and surjectivity of `ν` forces the diagonal of `G` to be `1`
(`LocalEquationChain.diag_eq_one_of_surjective`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open AlgebraicGeometry CategoryTheory IsLocalRing SGPT.Okounkov.OF5 SGPT.Okounkov.ValCurr

/-! ### The linear map `x ↦ x G` -/

section VecMul

variable {n : ℕ}

/-- `x ↦ x G` on `ℤⁿ_lex`. -/
def vecMulLexHom (G : Matrix (Fin n) (Fin n) ℤ) : Lex (Fin n → ℤ) →+ Lex (Fin n → ℤ) where
  toFun x := toLex (Matrix.vecMul (ofLex x) G)
  map_zero' := by
    change toLex (Matrix.vecMul 0 G) = 0
    rw [Matrix.zero_vecMul]
    rfl
  map_add' x y := by
    change toLex (Matrix.vecMul (ofLex x + ofLex y) G) = _
    rw [Matrix.add_vecMul]
    rfl

/-- `x ↦ x G` on `ℤⁿ_lex ∪ {∞}` (`∞ ↦ ∞`). -/
def vecMulWithTop (G : Matrix (Fin n) (Fin n) ℤ) :
    WithTop (Lex (Fin n → ℤ)) →+ WithTop (Lex (Fin n → ℤ)) :=
  (vecMulLexHom G).withTopMap

theorem vecMulWithTop_vecValue (G : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    vecMulWithTop G (vecValue x) = vecValue (Matrix.vecMul x G) := rfl

theorem vecMulWithTop_basisValue (G : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    vecMulWithTop G (basisValue i) = vecValue (G i) := by
  change vecValue (Matrix.vecMul (Pi.single i 1) G) = _
  rw [Matrix.single_vecMul, one_smul]
  rfl

/-- Upper triangular integer matrices with positive diagonal. -/
def IsPosUpperTriangular (G : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i, 0 < G i i) ∧ G.IsUpperTriangular

/-- `x ↦ x G` preserves vanishing below `i` for upper triangular `G`. -/
theorem vecMul_vanish_below {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsUpperTriangular)
    {i : ℕ} {u : Fin n → ℤ} (hu : ∀ j : Fin n, (j : ℕ) < i → u j = 0) :
    ∀ j : Fin n, (j : ℕ) < i → Matrix.vecMul u G j = 0 := by
  intro j hj
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < i
  · rw [hu l hl, zero_mul]
  · have hjl : j < l := by
      change (j : ℕ) < l
      omega
    rw [hG hjl, mul_zero]

/-- The `j`-th coordinate of `y G` for `y` vanishing before `j`. -/
theorem vecMul_apply_of_vanish {G : Matrix (Fin n) (Fin n) ℤ} (hG : G.IsUpperTriangular)
    {y : Fin n → ℤ} (j : Fin n) (hy : ∀ l : Fin n, l < j → y l = 0) :
    Matrix.vecMul y G j = y j * G j j := by
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_eq_single j (fun l _ hlj => ?_) (by simp)
  rcases lt_or_gt_of_ne hlj with h | h
  · rw [hy l h, zero_mul]
  · rw [hG h, mul_zero]

/-- If `y G = eᵢ` for an upper triangular `G` with positive diagonal, then `G i i = 1`. -/
theorem diag_eq_one_of_vecMul_eq_single {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : IsPosUpperTriangular G) {y : Fin n → ℤ} {i : Fin n}
    (h : Matrix.vecMul y G = Pi.single i 1) : G i i = 1 := by
  have hzero : ∀ m : ℕ, ∀ l : Fin n, (l : ℕ) = m → l < i → y l = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro l hlm hli
      have hprev : ∀ l' : Fin n, l' < l → y l' = 0 := fun l' hl' =>
        ih l' (by rw [← hlm]; exact hl') l' rfl (lt_trans hl' hli)
      have h1 := congrFun h l
      rw [vecMul_apply_of_vanish hG.2 l hprev, Pi.single_eq_of_ne hli.ne] at h1
      exact (mul_eq_zero.mp h1).resolve_right (hG.1 l).ne'
  have hprev : ∀ l : Fin n, l < i → y l = 0 := fun l hl => hzero l l rfl hl
  have h1 := congrFun h i
  rw [vecMul_apply_of_vanish hG.2 i hprev, Pi.single_eq_same] at h1
  exact Int.eq_one_of_dvd_one (hG.1 i).le ⟨y i, by rw [mul_comm]; exact h1.symm⟩

end VecMul

namespace LocalEquationChain

variable {R : Type*} [CommRing R] {n : ℕ} (C : OF5.LocalEquationChain R n)

/-- Elements of `P (i+1)` have value larger than every vector vanishing in the coordinates
`0, …, i`, for a valuation with `v(T j) = G_j`, `G` upper triangular with positive diagonal. -/
theorem vecValue_lt_of_mem (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤) {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : IsPosUpperTriangular G)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = vecValue (G ⟨i, hi⟩)) :
    ∀ (i : ℕ), i < n → ∀ (a : R), a ∈ C.P (i + 1) →
      ∀ y : Fin n → ℤ, (∀ j : Fin n, (j : ℕ) ≤ i → y j = 0) → vecValue y < v a := by
  intro i
  induction i with
  | zero =>
    intro hi a ha y hy
    rw [C.succ_eq 0 hi, Submodule.mem_sup] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    refine lt_of_lt_of_le (lt_min ?_ ?_) (v.map_add _ _)
    · rw [htop b hb]
      exact WithTop.coe_lt_top _
    · rw [v.map_mul, hT 0 hi]
      refine lt_of_lt_of_le ?_ (le_add_of_nonneg_left (hnonneg d))
      refine WithTop.coe_lt_coe.mpr (OF5.LocalEquationChain.toLex_lt_of_coord ⟨0, hi⟩
        (fun k hk => absurd hk (by simp [Fin.lt_def])) ?_)
      rw [hy ⟨0, hi⟩ le_rfl]
      exact hG.1 ⟨0, hi⟩
  | succ k ih =>
    intro hi a ha y hy
    rw [C.succ_eq (k + 1) hi, Submodule.mem_sup] at ha
    obtain ⟨b, hb, c, hc, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    refine lt_of_lt_of_le (lt_min ?_ ?_) (v.map_add _ _)
    · exact ih (by omega) b hb y fun j hj => hy j (by omega)
    · rw [v.map_mul, hT (k + 1) hi]
      refine lt_of_lt_of_le ?_ (le_add_of_nonneg_left (hnonneg d))
      refine WithTop.coe_lt_coe.mpr (OF5.LocalEquationChain.toLex_lt_of_coord ⟨k + 1, hi⟩
        (fun j hj => ?_) ?_)
      · have hj' : (j : ℕ) < k + 1 := hj
        rw [hy j (by omega)]
        exact (hG.2 hj).symm
      · rw [hy ⟨k + 1, hi⟩ le_rfl]
        exact hG.1 ⟨k + 1, hi⟩

variable [IsNoetherianRing R]

/-- **Recognition theorem for upper triangular matrices with positive diagonal**: if `v ≥ 0` on
`R`, `v = ∞` on `P 0`, `v = 0` off `P n` and `v(T i) = G_i`, then `v = (x ↦ x G) ∘ valAt i` off
`P i`. -/
theorem eq_vecMul_valAt_of_notMem (v : AddValuation R (WithTop (Lex (Fin n → ℤ))))
    (hnonneg : ∀ a, 0 ≤ v a) (htop : ∀ a ∈ C.P 0, v a = ⊤) {G : Matrix (Fin n) (Fin n) ℤ}
    (hG : IsPosUpperTriangular G)
    (hT : ∀ (i : ℕ) (hi : i < n), v (C.T i) = vecValue (G ⟨i, hi⟩))
    (hunit : ∀ a, a ∉ C.P n → v a = 0) (i : ℕ) (hin : i ≤ n) (a : R) (ha : a ∉ C.P i) :
    v a = vecMulWithTop G (C.valAt i a) := by
  rcases hin.lt_or_eq with hi | rfl
  · have hr : C.residual i a ∉ C.P (i + 1) := C.residual_notMem hi ha
    have hdiff : a - C.T i ^ C.ord i a * C.residual i a ∈ C.P i := by
      rw [← Ideal.Quotient.eq, map_mul, map_pow]
      exact C.residual_spec i a
    have hIH := eq_vecMul_valAt_of_notMem v hnonneg htop hG hT hunit (i + 1) hi (C.residual i a) hr
    have hmain : v (C.T i ^ C.ord i a * C.residual i a) = vecMulWithTop G (C.valAt i a) := by
      rw [v.map_mul, v.map_pow, hT i hi, hIH, C.valAt_congr i hdiff, C.valAt_mul,
        valAt_pow C, C.valAt_T hi i le_rfl, valAt_eq_valAt_succ C hi hr, map_add, map_nsmul,
        vecMulWithTop_basisValue]
    have hlt : v (C.T i ^ C.ord i a * C.residual i a) <
        v (a - C.T i ^ C.ord i a * C.residual i a) := by
      rw [hmain]
      obtain ⟨u, hu, hvan⟩ := C.valAt_coe i ha
      rw [hu, show (((toLex u : Lex (Fin n → ℤ)) : WithTop (Lex (Fin n → ℤ)))) = vecValue u
        from rfl, vecMulWithTop_vecValue]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [htop _ hdiff]
        exact WithTop.coe_lt_top _
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact vecValue_lt_of_mem C v hnonneg htop hG hT j (by omega) _ hdiff _
        fun l hl => vecMul_vanish_below hG.2 hvan l (by omega)
    have hsum := v.map_add_eq_of_lt_left hlt
    rw [add_sub_cancel] at hsum
    rw [hsum, hmain]
  · rw [C.valAt_of_le le_rfl ha, map_zero]
    exact hunit a ha
termination_by n - i

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Surjectivity forces a unit diagonal**: if a surjective valuation `v` of `K` with values in
`ℤⁿ_lex` is nonnegative on `R`, `0` off `P n`, and `v(T i) = G_i` with `G` upper triangular with
positive diagonal, then the diagonal of `G` is `1`. -/
theorem diag_eq_one_of_surjective (h0 : C.P 0 = ⊥)
    (v : AddValuation K (WithTop (Lex (Fin n → ℤ)))) (hv : Function.Surjective v)
    {G : Matrix (Fin n) (Fin n) ℤ} (hG : IsPosUpperTriangular G)
    (hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a))
    (hT : ∀ (i : ℕ) (hi : i < n), v (algebraMap R K (C.T i)) = vecValue (G ⟨i, hi⟩))
    (hunit : ∀ a : R, a ∉ C.P n → v (algebraMap R K a) = 0) (i : Fin n) : G i i = 1 := by
  have : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact (C.isPrime 0).ne_top (Subsingleton.elim _ _)
  have htop : ∀ a ∈ C.P 0, v.comap (algebraMap R K) a = ⊤ := by
    intro a ha
    rw [h0, Ideal.mem_bot] at ha
    subst ha
    change v (algebraMap R K 0) = ⊤
    rw [map_zero, v.map_zero]
  -- values of nonzero elements of `R` lie in `ℤⁿ G`
  have hR : ∀ a : R, a ≠ 0 → ∃ u : Fin n → ℤ,
      v (algebraMap R K a) = vecValue (Matrix.vecMul u G) := by
    intro a ha
    have ha0 : a ∉ C.P 0 := by rw [h0, Ideal.mem_bot]; exact ha
    have h := eq_vecMul_valAt_of_notMem C (v.comap (algebraMap R K)) hnonneg htop hG hT hunit 0
      (Nat.zero_le n) a ha0
    obtain ⟨u, hu, -⟩ := C.valAt_coe 0 ha0
    refine ⟨u, ?_⟩
    change v.comap (algebraMap R K) a = _
    rw [h, hu]
    rfl
  obtain ⟨z, hz⟩ := hv (basisValue i)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, v.map_zero] at hz
    exact WithTop.top_ne_coe hz
  obtain ⟨ua, hua⟩ := hR a ha0
  obtain ⟨ub, hub⟩ := hR b hb0
  have hmul : v (algebraMap R K a) = basisValue i + v (algebraMap R K b) := by
    rw [← hz, ← v.map_mul, div_mul_cancel₀ _ hbK]
  rw [hua, hub] at hmul
  have hvec : Matrix.vecMul (ua - ub) G = Pi.single i 1 := by
    have h := WithTop.coe_injective hmul
    have h2 : Matrix.vecMul ua G = Pi.single i 1 + Matrix.vecMul ub G := congrArg ofLex h
    rw [Matrix.sub_vecMul, h2, add_sub_cancel_right]
  exact diag_eq_one_of_vecMul_eq_single hG hvec

end LocalEquationChain

/-! ### Admissible flags -/

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)} {n : ℕ}
  [SmoothOfRelativeDimension n f] {Y : Fin (n + 1) → Set X} (hY : IsAdmissibleFlag f n Y)

/-- **A valuation whose prefix centres form an admissible flag is equivalent to its flag
valuation.** Let `ν` be a surjective valuation of `ℂ(X)` with values in `ℤⁿ_lex`, centred at the
point `Yₙ` of an admissible flag `Y•`, such that the centre of every coarsening `ν_{≤k}` (first
`k` coordinates) is the generic point of `Y_k`. Then `ν ∼ ν_{Y•}`. -/
theorem lexEquivalent_admissibleFlagValuation_of_prefixCentres
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))
    (hν : Function.Surjective ν) (hcent : AlgebraicValuation.IsValuationCenter ν hY.point)
    (hpref : ∀ (k : ℕ) (hk : k ≤ n),
      AlgebraicValuation.IsValuationCenter (prefixValuation hk ν) (memberPoint hY k)) :
    ValuationsLexEquivalent (admissibleFlagValuation hY) ν := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let C := admissibleFlagChain hY
  have hC : C.P = admissibleIdeal hY := admissibleFlagChain_P hY
  have h0 : C.P 0 = ⊥ := admissibleFlagChain_P_zero hY
  let M := LocalEquationChain.valueMatrix C X.functionField ν
  have hnonneg := hcent.1
  have hunit : ∀ a : X.presheaf.stalk hY.point, a ∉ C.P n →
      ν (algebraMap _ X.functionField a) = 0 := by
    intro a ha
    refine val_eq_zero_of_isUnit ν hnonneg ?_
    by_contra hu
    apply ha
    rw [hC, admissibleIdeal_last]
    exact (mem_maximalIdeal a).mpr hu
  -- the prefix-positivity criterion on `𝒪_{X,Yₙ}`
  have hpos : ∀ (k : ℕ) (hk : k ≤ n) (a : X.presheaf.stalk hY.point),
      a ∈ C.P k ↔ 0 < prefixValuation hk ν (algebraMap _ X.functionField a) := by
    intro k hk a
    rw [hC]
    exact generizationIdeal_mem_iff_valuation_pos (hpref k hk) (memberPoint_specializes hY k) a
  have hval : ∀ (i : ℕ) (hi : i < n),
      ν (algebraMap _ X.functionField (C.T i)) = vecValue (M ⟨i, hi⟩) :=
    fun i hi => (LocalEquationChain.vecValue_valueMatrix C X.functionField ν hi).symm
  have hpre : ∀ (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < n),
      prefixValuation hk ν (algebraMap _ X.functionField (C.T i)) =
        ((toLex fun j : Fin k => M ⟨i, hi⟩ (Fin.castLE hk j) : Lex (Fin k → ℤ)) :
          WithTop (Lex (Fin k → ℤ))) := by
    intro k hk i hi
    change prefixWithTopHom hk (ν _) = _
    rw [hval i hi]
    rfl
  -- the value matrix is upper triangular with positive diagonal
  have hlow : ∀ (i : ℕ) (hi : i < n) (j : Fin n), (j : ℕ) < i → M ⟨i, hi⟩ j = 0 := by
    intro i hi j hj
    have hnot : ¬ 0 < prefixValuation (le_of_lt hi) ν (algebraMap _ X.functionField (C.T i)) := by
      rw [← hpos i hi.le]
      exact C.T_notMem i hi
    have hge : 0 ≤ prefixValuation (le_of_lt hi) ν (algebraMap _ X.functionField (C.T i)) := by
      have h0' : prefixWithTopHom (le_of_lt hi) 0 = 0 := map_zero _
      change 0 ≤ prefixWithTopHom (le_of_lt hi) (ν _)
      rw [← h0']
      exact monotone_prefixWithTopHom _ (hnonneg _)
    have heq := le_antisymm (not_lt.mp hnot) hge
    rw [hpre i hi.le i hi] at heq
    have h := congrArg (fun z : Lex (Fin i → ℤ) => ofLex z ⟨j, hj⟩) (WithTop.coe_injective heq)
    exact h.trans rfl
  have hdiag : ∀ (i : ℕ) (hi : i < n), 0 < M ⟨i, hi⟩ ⟨i, hi⟩ := by
    intro i hi
    have hmem : C.T i ∈ C.P (i + 1) := C.T_mem_succ hi
    rw [hpos (i + 1) hi, hpre (i + 1) hi i hi] at hmem
    obtain ⟨l, hbefore, hl⟩ := toLex_lt_toLex_iff.mp (WithTop.coe_lt_coe.mp hmem)
    have hli : (l : ℕ) = i := by
      by_contra hne
      have hlt : (l : ℕ) < i := by have := l.isLt; omega
      have h := hlow i hi (Fin.castLE hi l) hlt
      change (0 : ℤ) < M ⟨i, hi⟩ (Fin.castLE hi l) at hl
      rw [h] at hl
      exact lt_irrefl _ hl
    change (0 : ℤ) < M ⟨i, hi⟩ (Fin.castLE hi l) at hl
    have hcast : Fin.castLE hi l = ⟨i, hi⟩ := Fin.ext hli
    rwa [hcast] at hl
  have hG : IsPosUpperTriangular M :=
    ⟨fun i => hdiag i i.2, fun i j hji => hlow i i.2 j hji⟩
  have hone : ∀ i : Fin n, M i i = 1 := fun i =>
    LocalEquationChain.diag_eq_one_of_surjective C X.functionField h0 ν hν hG hnonneg hval
      hunit i
  exact (lexEquivalent_admissibleFlagValuation_iff hY C hC ν).mpr
    ⟨hnonneg, hone, hG.2⟩

end SGPT.Okounkov.OF6
