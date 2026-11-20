import SGPT.Foundations.Schemes.ResiduePolynomialCoefficientShifts
import SGPT.Foundations.Schemes.ResiduePolynomialFullAsymptotic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.LiminfLimsup

/-!
# Quasi-polynomial section counts: growth degree, limits and error terms

Numerical core of the asymptotic Riemann–Roch theorem for ample line bundles
(`SGPT.LineBundle.RiemannRochAmple`).

A sequence `h : ℕ → ℝ` is *eventually quasi-polynomial of period `q`* if on every residue class
`k = q m + r` it agrees, for `m ≥ b`, with a polynomial `Q r` in `m`. This is the shape of
`h⁰(X, L^k)` for an ample line bundle `L` whose `q`-th power is very ample (Serre's theorem on
the twists of a coherent sheaf on projective space, applied to the pushforwards of `L^r`,
`0 ≤ r < q`). If moreover `h` is shift-monotone in two consecutive degrees (multiplication by
nonzero sections of `L^a` and `L^{a+1}` on an integral scheme), then all residue polynomials
have the same coefficient in every degree bounding all of them, and the full sequence has the
expected asymptotics.

## Main results

* `tendsto_div_pow_of_common_coeff`: if all residue polynomials have degree `≤ n` and the same
  coefficient `β` at `n`, then `h k / k^n → β / q^n`.
* `coeff_eq_of_shifts`: consecutive shift monotonicity forces a common coefficient.
* `exists_tendsto_div_pow_supDegree`, `exists_growthDegree`: for a nonnegative, eventually
  positive, eventually quasi-polynomial and consecutively shift-monotone sequence,
  `h k / k^e → c > 0`, where `e = supDegree Q` is the maximal degree of the residue polynomials.
* `natDegree_le_of_not_tendsto_atTop`: if `h k / k^n` does not tend to `+∞`, all residue
  polynomials have degree `≤ n`.
* `tendsto_div_pow_of_lt`, `tendsto_div_pow_atTop_of_gt`: the corresponding limits in the other
  normalising degrees (`0` above `e`, `+∞` below `e`).
* `tendsto_ennreal_ratio_of_tendsto`, `tendsto_ennreal_ratio_of_tendsto_atTop`: the translation
  to the `ℝ≥0∞`-valued normalised counts `n! h k / k^n` used by `SGPT.LineBundle.volume`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle.QuasiPolynomial

open Filter Polynomial Asymptotics
open scoped Topology ENNReal Nat

/-- If on each residue class `k = q m + r` (`m ≥ b`) the sequence `h` is given by a polynomial
`Q r` of degree `≤ n`, all with the same coefficient `β` at `n`, then `h k / k^n → β / q^n`. -/
theorem tendsto_div_pow_of_common_coeff (h : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (n b : ℕ)
    (Q : Fin q → ℝ[X]) (β : ℝ) (hdeg : ∀ r, (Q r).natDegree ≤ n)
    (hcoeff : ∀ r, (Q r).coeff n = β)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ)) :
    Tendsto (fun k : ℕ => h k / (k : ℝ) ^ n) atTop (𝓝 (β / (q : ℝ) ^ n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hev := SGPT.Foundations.Schemes.residuePolynomial_eventually_eq_of_common_constant h q hq b Q β
      hdeg hcoeff hQ
    have hβ : β / (q : ℝ) ^ 0 = β := by simp
    rw [hβ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    simp [hk]
  · have hO := SGPT.Foundations.Schemes.residuePolynomial_full_isBigO_of_common_coeff h q hq n hn b Q β
      hdeg hcoeff hQ
    set α : ℝ := β / (q : ℝ) ^ n with hα
    have hmul := hO.mul (isBigO_refl (fun k : ℕ => ((k : ℝ) ^ n)⁻¹) atTop)
    have hlim : Tendsto (fun k : ℕ => (k : ℝ) ^ (n - 1) * ((k : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      have heq : (fun k : ℕ => 1 / (k : ℝ)) =ᶠ[atTop]
          (fun k : ℕ => (k : ℝ) ^ (n - 1) * ((k : ℝ) ^ n)⁻¹) := by
        filter_upwards [eventually_ge_atTop 1] with k hk
        have hk0 : (k : ℝ) ≠ 0 := by
          have : (1 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ, mul_inv]
        field_simp
      exact (tendsto_one_div_atTop_nhds_zero_nat).congr' heq
    have h1 := hmul.trans_tendsto hlim
    have heq : (fun k : ℕ => (h k - α * (k : ℝ) ^ n) * ((k : ℝ) ^ n)⁻¹ + α) =ᶠ[atTop]
        (fun k : ℕ => h k / (k : ℝ) ^ n) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (k : ℝ) ^ n ≠ 0 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        exact pow_ne_zero _ (by linarith)
      field_simp
      ring
    have h2 := h1.add_const α
    rw [zero_add] at h2
    exact h2.congr' heq

/-- Consecutive shift monotonicity forces a common top coefficient (restatement of the
workspace lemma `SGPT.Foundations.Schemes.residuePolynomial_coeff_eq_of_consecutive_shifts`). -/
theorem coeff_eq_of_shifts (h : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (n b : ℕ)
    (Q : Fin q → ℝ[X]) (hdeg : ∀ r, (Q r).natDegree ≤ n)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (hshift : ∃ a : ℕ, (∀ k, h k ≤ h (k + a)) ∧ ∀ k, h k ≤ h (k + (a + 1))) :
    ∀ r s, (Q r).coeff n = (Q s).coeff n := by
  obtain ⟨a, ha, hb⟩ := hshift
  exact SGPT.Foundations.Schemes.residuePolynomial_coeff_eq_of_consecutive_shifts h q hq n b a Q hdeg hQ
    ha hb

/-- Above the growth degree the normalised counts tend to `0`. -/
theorem tendsto_div_pow_of_lt (h : ℕ → ℝ) {e n : ℕ} {c : ℝ} (hen : e < n)
    (hc : Tendsto (fun k : ℕ => h k / (k : ℝ) ^ e) atTop (𝓝 c)) :
    Tendsto (fun k : ℕ => h k / (k : ℝ) ^ n) atTop (𝓝 0) := by
  have hz : Tendsto (fun k : ℕ => ((k : ℝ) ^ (n - e))⁻¹) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ (n - e)) atTop atTop :=
      (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
    exact hpow.inv_tendsto_atTop
  have hprod := hc.mul hz
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hn : n = e + (n - e) := by omega
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, ← mul_inv]
  conv_rhs => rw [hn, pow_add]

/-- Below the growth degree the normalised counts tend to `+∞`. -/
theorem tendsto_div_pow_atTop_of_gt (h : ℕ → ℝ) {e n : ℕ} {c : ℝ} (hc0 : 0 < c) (hne : n < e)
    (hc : Tendsto (fun k : ℕ => h k / (k : ℝ) ^ e) atTop (𝓝 c)) :
    Tendsto (fun k : ℕ => h k / (k : ℝ) ^ n) atTop atTop := by
  have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ (e - n)) atTop atTop :=
    (tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop
  have hprod := hc.pos_mul_atTop hc0 hpow
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hpe : (k : ℝ) ^ e = (k : ℝ) ^ n * (k : ℝ) ^ (e - n) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpe]
  field_simp

/-- The maximal degree of a finite family of residue polynomials. -/
def supDegree {q : ℕ} (Q : Fin q → ℝ[X]) : ℕ := Finset.univ.sup fun r => (Q r).natDegree

theorem natDegree_le_supDegree {q : ℕ} (Q : Fin q → ℝ[X]) (r : Fin q) :
    (Q r).natDegree ≤ supDegree Q :=
  Finset.le_sup (f := fun r => (Q r).natDegree) (Finset.mem_univ r)

/-- **Growth degree of a quasi-polynomial count.** For a nonnegative, eventually positive
sequence which is eventually quasi-polynomial of period `q` and shift-monotone in two
consecutive degrees, `h k / k^D → c` for some `c > 0`, where `D` is the maximal degree of the
residue polynomials. -/
theorem exists_tendsto_div_pow_supDegree (h : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (b : ℕ)
    (Q : Fin q → ℝ[X])
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (hnonneg : ∀ k, 0 ≤ h k) (hpos : ∀ᶠ k in atTop, 0 < h k)
    (hshift : ∃ a : ℕ, (∀ k, h k ≤ h (k + a)) ∧ ∀ k, h k ≤ h (k + (a + 1))) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun k : ℕ => h k / (k : ℝ) ^ supDegree Q) atTop (𝓝 c) := by
  classical
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  set e : ℕ := supDegree Q with he_def
  have hdeg_e : ∀ r, (Q r).natDegree ≤ e := natDegree_le_supDegree Q
  obtain ⟨r₁, -, hr₁⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin q))
    Finset.univ_nonempty fun r => (Q r).natDegree
  have hcommon := coeff_eq_of_shifts h hq e b Q hdeg_e hQ hshift
  set β : ℝ := (Q r₁).coeff e with hβ
  -- the polynomial attaining the maximal degree is nonzero
  have hQ₁ : Q r₁ ≠ 0 := by
    intro hz
    obtain ⟨K, hK⟩ := eventually_atTop.mp hpos
    have hk := hK (q * (max b K) + r₁.val) (by nlinarith [le_max_right b K, hq])
    rw [hQ r₁ (max b K) (le_max_left _ _), hz, eval_zero] at hk
    exact lt_irrefl _ hk
  have hβ0 : β ≠ 0 := by
    rw [hβ, show e = (Q r₁).natDegree from hr₁, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hQ₁
  have hβnn : 0 ≤ β := by
    have hle := SGPT.Foundations.Schemes.polynomial_coeff_le_of_eventually_eval_le 0 (Q r₁) e
      (by simp) (hdeg_e r₁) (by
        filter_upwards [eventually_ge_atTop b] with m hm
        rw [eval_zero, ← hQ r₁ m hm]
        exact hnonneg _)
    simpa using hle
  have hβpos : 0 < β := lt_of_le_of_ne hβnn (Ne.symm hβ0)
  refine ⟨β / (q : ℝ) ^ e, div_pos hβpos (pow_pos (by exact_mod_cast hq) _), ?_⟩
  exact tendsto_div_pow_of_common_coeff h hq e b Q β hdeg_e (fun r => hcommon r r₁) hQ

/-- **Growth degree of a quasi-polynomial count.** Under the hypotheses of
`exists_tendsto_div_pow_supDegree`, if the residue polynomials have degree `≤ N`, then
`h k / k^e → c` for some `e ≤ N` and some `c > 0`. -/
theorem exists_growthDegree (h : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (N b : ℕ)
    (Q : Fin q → ℝ[X]) (hdeg : ∀ r, (Q r).natDegree ≤ N)
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (hnonneg : ∀ k, 0 ≤ h k) (hpos : ∀ᶠ k in atTop, 0 < h k)
    (hshift : ∃ a : ℕ, (∀ k, h k ≤ h (k + a)) ∧ ∀ k, h k ≤ h (k + (a + 1))) :
    ∃ e ≤ N, ∃ c : ℝ, 0 < c ∧ Tendsto (fun k : ℕ => h k / (k : ℝ) ^ e) atTop (𝓝 c) :=
  ⟨supDegree Q, Finset.sup_le fun r _ => hdeg r,
    exists_tendsto_div_pow_supDegree h hq b Q hQ hnonneg hpos hshift⟩

/-- If `h k / k^n` does not tend to `+∞`, all residue polynomials have degree `≤ n`. -/
theorem natDegree_le_of_not_tendsto_atTop (h : ℕ → ℝ) {q : ℕ} (hq : 0 < q) (b : ℕ)
    (Q : Fin q → ℝ[X])
    (hQ : ∀ (r : Fin q) m, b ≤ m → h (q * m + r.val) = (Q r).eval (m : ℝ))
    (hnonneg : ∀ k, 0 ≤ h k) (hpos : ∀ᶠ k in atTop, 0 < h k)
    (hshift : ∃ a : ℕ, (∀ k, h k ≤ h (k + a)) ∧ ∀ k, h k ≤ h (k + (a + 1))) {n : ℕ}
    (hn : ¬ Tendsto (fun k : ℕ => h k / (k : ℝ) ^ n) atTop atTop) :
    ∀ r, (Q r).natDegree ≤ n := by
  intro r
  by_contra hr
  push Not at hr
  obtain ⟨c, hc0, hc⟩ := exists_tendsto_div_pow_supDegree h hq b Q hQ hnonneg hpos hshift
  exact hn (tendsto_div_pow_atTop_of_gt h hc0
    (lt_of_lt_of_le hr (natDegree_le_supDegree Q r)) hc)

/-- For `k ≥ 1`, the `ℝ≥0∞`-valued normalised count `n! H k / k^n` is the image of the real one. -/
theorem ennreal_ratio_eq_ofReal (H : ℕ → ℕ) (n k : ℕ) (hk : 1 ≤ k) :
    ((n ! : ℝ≥0∞) * (H k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n =
      ENNReal.ofReal ((n ! : ℝ) * ((H k : ℝ) / (k : ℝ) ^ n)) := by
  have hk0 : (0 : ℝ) < (k : ℝ) ^ n := pow_pos (by exact_mod_cast hk) n
  rw [← mul_div_assoc, ENNReal.ofReal_div_of_pos hk0]
  congr 1
  · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

/-- A real limit of `H k / k^n` gives the limit `n! c` of the `ℝ≥0∞`-valued normalised counts. -/
theorem tendsto_ennreal_ratio_of_tendsto (H : ℕ → ℕ) (n : ℕ) {c : ℝ}
    (hc : Tendsto (fun k : ℕ => (H k : ℝ) / (k : ℝ) ^ n) atTop (𝓝 c)) :
    Tendsto (fun k : ℕ => ((n ! : ℝ≥0∞) * (H k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n) atTop
      (𝓝 (ENNReal.ofReal ((n ! : ℝ) * c))) := by
  have h := ENNReal.tendsto_ofReal (hc.const_mul (n ! : ℝ))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (ennreal_ratio_eq_ofReal H n k hk).symm

/-- A divergent `H k / k^n` gives the limit `∞` of the `ℝ≥0∞`-valued normalised counts. -/
theorem tendsto_ennreal_ratio_of_tendsto_atTop (H : ℕ → ℕ) (n : ℕ)
    (hc : Tendsto (fun k : ℕ => (H k : ℝ) / (k : ℝ) ^ n) atTop atTop) :
    Tendsto (fun k : ℕ => ((n ! : ℝ≥0∞) * (H k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n) atTop (𝓝 ∞) := by
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := ENNReal.tendsto_ofReal_atTop.comp (hc.const_mul_atTop hfac)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (ennreal_ratio_eq_ofReal H n k hk).symm

end SGPT.LineBundle.QuasiPolynomial
