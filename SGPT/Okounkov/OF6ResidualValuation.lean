import SGPT.Okounkov.OF6ZariskiModel
import SGPT.Okounkov.ValuationCoarseningCenters
import Mathlib.RingTheory.Valuation.ExtendToLocalization

/-!
# The residual valuation along the divisor of `ν₁`

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar`, the induction in the proof of
the cited [CFKLRS17, Theorem 2.9]: once the first coordinate `ν₁` of `ν : ℂ(X)^× → ℤⁿ_lex` is
realized as `ord_E` for a prime divisor `E` of a normal model (lane OF6, `OF6ZariskiScheme`), the
remaining coordinates define a valuation of `ℂ(E)` of rank `n - 1`, to which the induction applies.

Setting: a domain `A` with fraction field `K`, a valuation `ν : K → ℤ^{m+1}_lex ∪ {∞}` nonnegative
on `A`, and `q = {a ∈ A : ν(a)₁ > 0}` the centre of its first coordinate on `A`
(`SGPT.Okounkov.OF6.centerIdeal` of the coarsening `ν_{≤1}`). For `A` the normal affine chart of
`exists_normalChart_prefixOne`, `A ⧸ q` is the coordinate ring of the affine chart of `E`.

* `resValuation`: the residual valuation `ν̄` on `A ⧸ q`: `ν̄(ā) = (ν(a)₂, …, ν(a)_{m+1})` for
  `a ∉ q` (whose first coordinate is `0`), `∞` on `0`; well defined (`resValuation_mk`) because
  elements of `q` have strictly larger value.
* `resFracValuation`: its extension to `ℂ(E) = Frac(A ⧸ q)`.
* `resValuation_nonneg`: `ν̄ ≥ 0` on `A ⧸ q`.
* `resFracValuation_surjective`: **the residual valuation has value group `ℤᵐ_lex`**, as soon as
  `ν` is surjective and the valuation ring of `ν₁` is `A_q` (Zariski's realization).
* `not_algebraicIndependent_quotient`: if `A` has no `m + 2` algebraically independent elements and
  `q ≠ 0`, then `A ⧸ q` has no `m + 1`: `trdeg ℂ(E) ≤ m`, so the residual valuation has maximal
  rational rank (`= m` by Abhyankar's inequality, lane OF4).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open SGPT.Okounkov.ValCurr

attribute [local instance] Classical.propDecidable

section Tail

variable {m : ℕ}

/-- The last `m` coordinates `(x₂, …, x_{m+1})` of `x ∈ ℤ^{m+1}`. -/
def tailHom : Lex (Fin (m + 1) → ℤ) →+ Lex (Fin m → ℤ) where
  toFun x := toLex fun j => ofLex x j.succ
  map_zero' := rfl
  map_add' _ _ := rfl

theorem tailHom_apply (x : Lex (Fin (m + 1) → ℤ)) (j : Fin m) :
    ofLex (tailHom x) j = ofLex x j.succ := rfl

/-- On vectors with first coordinate `0`, the lexicographic order is that of the tails. -/
theorem tailHom_le_tailHom {x y : Lex (Fin (m + 1) → ℤ)} (hx : ofLex x 0 = 0)
    (hy : ofLex y 0 = 0) (h : x ≤ y) : tailHom x ≤ tailHom y := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hbefore, hj⟩ := toLex_lt_toLex_iff.mp hlt
  refine not_lt_of_ge h ?_
  change toLex (ofLex y) < toLex (ofLex x)
  refine toLex_lt_toLex_iff.mpr ⟨j.succ, fun l hl => ?_, hj⟩
  induction l using Fin.cases with
  | zero => rw [hx, hy]
  | succ l =>
    exact hbefore l (Fin.succ_lt_succ_iff.mp hl)

end Tail

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]
  {m : ℕ} (ν : AddValuation K (WithTop (Lex (Fin (m + 1) → ℤ))))

/-- The first coordinate `ν₁ = ν_{≤1}` of `ν`. -/
abbrev firstVal : AddValuation K (WithTop (Lex (Fin 1 → ℤ))) :=
  prefixValuation (Nat.succ_le_succ (Nat.zero_le m)) ν

theorem firstVal_nonneg (hA : ∀ a : A, 0 ≤ ν (algebraMap A K a)) (a : A) :
    0 ≤ firstVal ν (algebraMap A K a) := by
  have h0 : prefixWithTopHom (Nat.succ_le_succ (Nat.zero_le m)) 0 = 0 := map_zero _
  change 0 ≤ prefixWithTopHom _ (ν _)
  rw [← h0]
  exact monotone_prefixWithTopHom _ (hA a)

variable (hA : ∀ a : A, 0 ≤ ν (algebraMap A K a))

/-- The centre `q = {a ∈ A : ν(a)₁ > 0}` of the first coordinate on `A`. -/
abbrev firstCenter : Ideal A := centerIdeal (firstVal ν) (firstVal_nonneg ν hA)

instance firstCenter_isPrime : (firstCenter ν hA).IsPrime := centerIdeal_isPrime _ _

theorem firstVal_coe (x : Lex (Fin (m + 1) → ℤ)) {z : K} (hz : ν z = x) :
    firstVal ν z = ((toLex fun _ : Fin 1 => ofLex x 0 : Lex (Fin 1 → ℤ)) :
      WithTop (Lex (Fin 1 → ℤ))) := by
  change prefixWithTopHom _ (ν z) = _
  rw [hz]
  change ((prefixHom _ x : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) = _
  congr 1
  apply ofLex.injective
  funext i
  fin_cases i
  rfl

/-- Off `q`, `ν` is finite with first coordinate `0`. -/
theorem exists_coe_of_notMem {a : A} (ha : a ∉ firstCenter ν hA) :
    ∃ x : Lex (Fin (m + 1) → ℤ), ν (algebraMap A K a) = x ∧ ofLex x 0 = 0 := by
  have hne : ν (algebraMap A K a) ≠ ⊤ := by
    intro h
    apply ha
    change 0 < firstVal ν (algebraMap A K a)
    change 0 < prefixWithTopHom _ (ν _)
    rw [h]
    exact WithTop.coe_lt_top _
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨x, hx.symm, ?_⟩
  have hnot : ¬ 0 < firstVal ν (algebraMap A K a) := ha
  have hge := firstVal_nonneg ν hA a
  have heq := le_antisymm (not_lt.mp hnot) hge
  rw [firstVal_coe ν x hx.symm] at heq
  have h := congrArg (fun z : Lex (Fin 1 → ℤ) => ofLex z 0) (WithTop.coe_injective heq)
  exact h.trans rfl

/-- Elements of `q` have strictly larger value than elements off `q`. -/
theorem val_lt_of_notMem_of_mem {a b : A} (ha : a ∉ firstCenter ν hA)
    (hb : b ∈ firstCenter ν hA) : ν (algebraMap A K a) < ν (algebraMap A K b) := by
  obtain ⟨x, hx, hx0⟩ := exists_coe_of_notMem ν hA ha
  rw [hx]
  induction h : ν (algebraMap A K b) using WithTop.recTopCoe with
  | top => exact WithTop.coe_lt_top _
  | coe y =>
    have hpos : 0 < firstVal ν (algebraMap A K b) := hb
    rw [firstVal_coe ν y h] at hpos
    have hy0 : 0 < ofLex y 0 := by
      obtain ⟨i, -, hi⟩ := toLex_lt_toLex_iff.mp (WithTop.coe_lt_coe.mp hpos)
      exact hi
    refine WithTop.coe_lt_coe.mpr (toLex_lt_toLex_iff.mpr ⟨0, fun l hl => absurd hl (by simp), ?_⟩)
    change ofLex x 0 < ofLex y 0
    rw [hx0]
    exact hy0

theorem val_eq_of_sub_mem {a b : A} (ha : a ∉ firstCenter ν hA)
    (hab : a - b ∈ firstCenter ν hA) : ν (algebraMap A K b) = ν (algebraMap A K a) := by
  have hlt : ν (algebraMap A K a) < ν (algebraMap A K (-(a - b))) :=
    val_lt_of_notMem_of_mem ν hA ha ((firstCenter ν hA).neg_mem hab)
  have h := ν.map_add_eq_of_lt_left hlt
  rw [← map_add, show a + -(a - b) = b by ring] at h
  exact h

theorem notMem_of_sub_mem {a b : A} (ha : a ∉ firstCenter ν hA)
    (hab : a - b ∈ firstCenter ν hA) : b ∉ firstCenter ν hA := fun hb =>
  ha (by simpa using (firstCenter ν hA).add_mem hab hb)

/-- The residual value on `A`: the tail of `ν(a)` off `q`, `∞` on `q`. -/
def resValA (a : A) : WithTop (Lex (Fin m → ℤ)) :=
  if a ∈ firstCenter ν hA then ⊤ else (tailHom ((ν (algebraMap A K a)).untopD 0) : _)

theorem resValA_of_mem {a : A} (ha : a ∈ firstCenter ν hA) : resValA ν hA a = ⊤ := by
  rw [resValA, if_pos ha]

theorem resValA_of_notMem {a : A} (ha : a ∉ firstCenter ν hA) {x : Lex (Fin (m + 1) → ℤ)}
    (hx : ν (algebraMap A K a) = x) : resValA ν hA a = (tailHom x : _) := by
  rw [resValA, if_neg ha, hx, WithTop.untopD_coe]

theorem resValA_congr {a b : A} (hab : a - b ∈ firstCenter ν hA) :
    resValA ν hA a = resValA ν hA b := by
  by_cases ha : a ∈ firstCenter ν hA
  · have hb : b ∈ firstCenter ν hA := by simpa using (firstCenter ν hA).sub_mem ha hab
    rw [resValA_of_mem ν hA ha, resValA_of_mem ν hA hb]
  · have hb := notMem_of_sub_mem ν hA ha hab
    rw [resValA, resValA, if_neg ha, if_neg hb, val_eq_of_sub_mem ν hA ha hab]

/-- The residual value on `A ⧸ q`. -/
def resValFun (x : A ⧸ firstCenter ν hA) : WithTop (Lex (Fin m → ℤ)) :=
  resValA ν hA (Ideal.Quotient.mk_surjective x).choose

theorem resValFun_mk (a : A) : resValFun ν hA (Ideal.Quotient.mk _ a) = resValA ν hA a := by
  apply resValA_congr
  rw [← Ideal.Quotient.eq]
  exact (Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (firstCenter ν hA) a)).choose_spec

/-- **The residual valuation `ν̄` on `A ⧸ q`** (values in `ℤᵐ_lex ∪ {∞}`). -/
def resValuation : AddValuation (A ⧸ firstCenter ν hA) (WithTop (Lex (Fin m → ℤ))) :=
  AddValuation.of (resValFun ν hA)
    (by
      rw [← map_zero (Ideal.Quotient.mk (firstCenter ν hA)), resValFun_mk]
      exact resValA_of_mem ν hA (firstCenter ν hA).zero_mem)
    (by
      rw [← map_one (Ideal.Quotient.mk (firstCenter ν hA)), resValFun_mk,
        resValA_of_notMem ν hA ((Ideal.ne_top_iff_one _).mp (firstCenter_isPrime ν hA).ne_top)
          (x := 0) (by rw [map_one, ν.map_one]; rfl), map_zero]
      rfl)
    (by
      intro x y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_add, resValFun_mk, resValFun_mk, resValFun_mk]
      by_cases ha : a ∈ firstCenter ν hA
      · rw [resValA_congr ν hA (show a + b - b ∈ firstCenter ν hA by simpa using ha)]
        exact min_le_right _ _
      by_cases hb : b ∈ firstCenter ν hA
      · rw [resValA_congr ν hA (show a + b - a ∈ firstCenter ν hA by simpa using hb)]
        exact min_le_left _ _
      by_cases hab : a + b ∈ firstCenter ν hA
      · rw [resValA_of_mem ν hA hab]
        exact le_top
      obtain ⟨x, hx, hx0⟩ := exists_coe_of_notMem ν hA ha
      obtain ⟨y, hy, hy0⟩ := exists_coe_of_notMem ν hA hb
      obtain ⟨z, hz, hz0⟩ := exists_coe_of_notMem ν hA hab
      rw [resValA_of_notMem ν hA ha hx, resValA_of_notMem ν hA hb hy,
        resValA_of_notMem ν hA hab hz]
      have hmin := ν.map_add (algebraMap A K a) (algebraMap A K b)
      rw [← map_add, hx, hy, hz] at hmin
      rcases le_total x y with hxy | hxy
      · rw [min_eq_left (WithTop.coe_le_coe.mpr hxy)] at hmin
        exact (min_le_left _ _).trans
          (WithTop.coe_le_coe.mpr (tailHom_le_tailHom hx0 hz0 (WithTop.coe_le_coe.mp hmin)))
      · rw [min_eq_right (WithTop.coe_le_coe.mpr hxy)] at hmin
        exact (min_le_right _ _).trans
          (WithTop.coe_le_coe.mpr (tailHom_le_tailHom hy0 hz0 (WithTop.coe_le_coe.mp hmin))))
    (by
      intro x y
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul, resValFun_mk, resValFun_mk, resValFun_mk]
      by_cases ha : a ∈ firstCenter ν hA
      · rw [resValA_of_mem ν hA ha, resValA_of_mem ν hA ((firstCenter ν hA).mul_mem_right b ha),
          top_add]
      by_cases hb : b ∈ firstCenter ν hA
      · rw [resValA_of_mem ν hA hb, resValA_of_mem ν hA ((firstCenter ν hA).mul_mem_left a hb),
          add_top]
      have hab : a * b ∉ firstCenter ν hA := fun h =>
        ((firstCenter_isPrime ν hA).mem_or_mem h).elim ha hb
      obtain ⟨x, hx, -⟩ := exists_coe_of_notMem ν hA ha
      obtain ⟨y, hy, -⟩ := exists_coe_of_notMem ν hA hb
      have hxy : ν (algebraMap A K (a * b)) = ((x + y : Lex (Fin (m + 1) → ℤ)) : _) := by
        rw [map_mul, ν.map_mul, hx, hy, WithTop.coe_add]
      rw [resValA_of_notMem ν hA ha hx, resValA_of_notMem ν hA hb hy,
        resValA_of_notMem ν hA hab hxy, map_add, WithTop.coe_add])

theorem resValuation_mk (a : A) :
    resValuation ν hA (Ideal.Quotient.mk _ a) = resValA ν hA a := resValFun_mk ν hA a

/-- `ν(a) = (0, ν̄(ā))` off `q`. -/
theorem resValuation_mk_of_notMem {a : A} (ha : a ∉ firstCenter ν hA) :
    ∃ x : Lex (Fin (m + 1) → ℤ), ν (algebraMap A K a) = x ∧ ofLex x 0 = 0 ∧
      resValuation ν hA (Ideal.Quotient.mk _ a) = (tailHom x : _) := by
  obtain ⟨x, hx, hx0⟩ := exists_coe_of_notMem ν hA ha
  exact ⟨x, hx, hx0, by rw [resValuation_mk, resValA_of_notMem ν hA ha hx]⟩

/-- `ν̄ ≥ 0` on `A ⧸ q`. -/
theorem resValuation_nonneg (x : A ⧸ firstCenter ν hA) : 0 ≤ resValuation ν hA x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resValuation_mk]
  by_cases ha : a ∈ firstCenter ν hA
  · rw [resValA_of_mem ν hA ha]
    exact le_top
  obtain ⟨x, hx, hx0⟩ := exists_coe_of_notMem ν hA ha
  rw [resValA_of_notMem ν hA ha hx, WithTop.coe_nonneg, ← map_zero (tailHom (m := m))]
  refine tailHom_le_tailHom rfl hx0 ?_
  have h := hA a
  rw [hx] at h
  exact WithTop.coe_le_coe.mp h

theorem resValuation_eq_top_iff (x : A ⧸ firstCenter ν hA) :
    resValuation ν hA x = ⊤ ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [resValuation_mk, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨fun h => ?_, resValA_of_mem ν hA⟩
  by_contra ha
  obtain ⟨x, hx, -⟩ := exists_coe_of_notMem ν hA ha
  rw [resValA_of_notMem ν hA ha hx] at h
  exact WithTop.coe_ne_top h

/-! ### The extension to `ℂ(E) = Frac(A ⧸ q)` -/

theorem nonZeroDivisors_le_resValuation_supp :
    nonZeroDivisors (A ⧸ firstCenter ν hA) ≤
      (resValuation ν hA).toValuation.supp.primeCompl := by
  intro x hx
  change resValuation ν hA x ≠ ⊤
  rw [ne_eq, resValuation_eq_top_iff]
  exact nonZeroDivisors.ne_zero hx

/-- **The residual valuation of `ν` along `E`, on `ℂ(E) = Frac(A ⧸ q)`.** -/
def resFracValuation :
    AddValuation (FractionRing (A ⧸ firstCenter ν hA)) (WithTop (Lex (Fin m → ℤ))) :=
  (resValuation ν hA).toValuation.extendToLocalization
    (nonZeroDivisors_le_resValuation_supp ν hA) (FractionRing (A ⧸ firstCenter ν hA))

theorem resFracValuation_algebraMap (x : A ⧸ firstCenter ν hA) :
    resFracValuation ν hA (algebraMap _ (FractionRing (A ⧸ firstCenter ν hA)) x) =
      resValuation ν hA x :=
  Valuation.extendToLocalization_apply_map_apply (resValuation ν hA).toValuation
    (nonZeroDivisors_le_resValuation_supp ν hA) _ x

/-- **The residual valuation has value group `ℤᵐ_lex`.** If `ν` is surjective and the valuation
ring of `ν₁` is `A_q` (`ν₁(z) ≥ 0 ⟹ z s ∈ A` for some `s ∉ q`; Zariski's realization,
`exists_normalChart_prefixOne`), then `ν̄ : ℂ(E)^× → ℤᵐ_lex` is surjective. -/
theorem resFracValuation_surjective (hν : Function.Surjective ν)
    (hring : ∀ z : K, 0 ≤ firstVal ν z →
      ∃ a s : A, s ∉ firstCenter ν hA ∧ z * algebraMap A K s = algebraMap A K a) :
    Function.Surjective (resFracValuation ν hA) := by
  intro t
  induction t using WithTop.recTopCoe with
  | top => exact ⟨0, (resFracValuation ν hA).map_zero⟩
  | coe t =>
    let x : Lex (Fin (m + 1) → ℤ) := toLex (Fin.cons 0 (ofLex t))
    have hx0 : ofLex x 0 = 0 := rfl
    have htx : tailHom x = t := by
      apply ofLex.injective
      funext j
      rfl
    obtain ⟨z, hz⟩ := hν x
    have hz1 : 0 ≤ firstVal ν z := by
      rw [firstVal_coe ν x hz, hx0]
      rfl
    obtain ⟨a, s, hs, hzs⟩ := hring z hz1
    obtain ⟨y, hy, hy0, hsy⟩ := resValuation_mk_of_notMem ν hA hs
    have haval : ν (algebraMap A K a) = ((x + y : Lex (Fin (m + 1) → ℤ)) : _) := by
      rw [← hzs, ν.map_mul, hz, hy, WithTop.coe_add]
    have ha : a ∉ firstCenter ν hA := by
      intro ha
      have hpos : 0 < firstVal ν (algebraMap A K a) := ha
      rw [firstVal_coe ν _ haval] at hpos
      obtain ⟨i, -, hi⟩ := toLex_lt_toLex_iff.mp (WithTop.coe_lt_coe.mp hpos)
      change (0 : ℤ) < ofLex x 0 + ofLex y 0 at hi
      rw [hx0, hy0] at hi
      exact lt_irrefl _ hi
    have hsa := resValuation_mk ν hA a
    rw [resValA_of_notMem ν hA ha haval, map_add] at hsa
    have hs0 : Ideal.Quotient.mk (firstCenter ν hA) s ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    have hsK : algebraMap _ (FractionRing (A ⧸ firstCenter ν hA))
        (Ideal.Quotient.mk (firstCenter ν hA) s) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs0
    refine ⟨algebraMap _ _ (Ideal.Quotient.mk (firstCenter ν hA) a) /
      algebraMap _ _ (Ideal.Quotient.mk (firstCenter ν hA) s), ?_⟩
    set w := resFracValuation ν hA (algebraMap _ _ (Ideal.Quotient.mk (firstCenter ν hA) a) /
      algebraMap _ _ (Ideal.Quotient.mk (firstCenter ν hA) s)) with hw
    have hmul : w + resFracValuation ν hA (algebraMap _ (FractionRing (A ⧸ firstCenter ν hA))
        (Ideal.Quotient.mk (firstCenter ν hA) s)) = resFracValuation ν hA
          (algebraMap _ (FractionRing (A ⧸ firstCenter ν hA))
            (Ideal.Quotient.mk (firstCenter ν hA) a)) := by
      rw [hw, ← AddValuation.map_mul, div_mul_cancel₀ _ hsK]
    rw [resFracValuation_algebraMap, resFracValuation_algebraMap, hsa, hsy, htx] at hmul
    have hwne : w ≠ ⊤ := by
      intro h
      rw [h, top_add] at hmul
      exact WithTop.top_ne_coe hmul
    obtain ⟨w', hw'⟩ := WithTop.ne_top_iff_exists.mp hwne
    rw [← hw'] at hmul ⊢
    rw [← WithTop.coe_add] at hmul
    exact congrArg _ (add_right_cancel (WithTop.coe_injective hmul))

/-- **`trdeg ℂ(E) ≤ m`**: if the domain `B` has no `m + 2` algebraically independent elements and
`q ≠ 0` is prime, then `B ⧸ q` has no `m + 1`. -/
theorem not_algebraicIndependent_quotient {k : Type*} [Field k] {B : Type*} [CommRing B]
    [IsDomain B] [Algebra k B] {m : ℕ}
    (htr : ∀ z : Fin (m + 2) → B, ¬ AlgebraicIndependent k z) (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∀ z : Fin (m + 1) → B ⧸ q, ¬ AlgebraicIndependent k z := by
  intro z hz
  choose z' hz' using fun i => Ideal.Quotient.mk_surjective (z i)
  have hz'' : AlgebraicIndependent k (Ideal.Quotient.mk q ∘ z') := by
    have h : (Ideal.Quotient.mk q ∘ z') = z := funext hz'
    rwa [h]
  have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  obtain ⟨x, hx⟩ := exists_algebraicIndependent_option_of_lt (bot_lt_iff_ne_bot.mpr hq) z' hz''
  have hx' := AlgebraicIndependent.of_comp (Ideal.Quotient.mkₐ k ⊥) hx
  exact htr _ (hx'.comp (finSuccEquiv (m + 1)) (finSuccEquiv (m + 1)).injective)

end SGPT.Okounkov.OF6
