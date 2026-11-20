import SGPT.Unibranch.FNSHull
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
import SGPT.Foundations.Analysis.PlurisubharmonicLimits

/-!
# The Hartogs step for monomial polyhedra

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), end of the proof of Theorem 5.3.1 (`[FN80]`), for `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`).

`[FN80]` ends with a pseudoconvex Hartogs domain `V'' = {|w| < exp(-λ(z))}` over `D ⊇ X` and
concludes that `λ` is plurisubharmonic with `λ|_X = φ`. We obtain the Stein neighbourhood as an
increasing union of **monomial polyhedra** `P = {|aᵢ(z)| |w|^{kᵢ} < 1}` (`FNSSiu`), and for these
the Hartogs radius is explicit: over `z` with `|aᵢ(z)| < 1` for the `kᵢ = 0` monomials, the fibre of
`P` is the disc `|w| < exp(-λ_P(z))` with

`λ_P(z) = max_{kᵢ ≥ 1} (1/kᵢ) log |aᵢ(z)|` (`polyLambda`),

a finite maximum of plurisubharmonic functions (`discPshOn_polyLambda`). So no theory of
pseudoconvex Hartogs domains is needed:

* `polyLambda_lt_iff`, `mem_monoPoly_of_polyLambda_lt` (`|w| ≤ e^{-t}`, `λ_P(z) < t` ⇒ `(w, z) ∈ P`),
  `polyLambda_lt_of_mem_monoPoly` (`(w, z) ∈ P`, `w ≠ 0` ⇒ `λ_P(z) < -log |w|`);
* `polyLambda_anti`: `P ⊆ P'` ⇒ `λ_{P'} ≤ λ_P` over the base of `P`;
* `discPshOn_iInf_polyLambda`: for an increasing sequence of monomial polyhedra the decreasing
  limit `λ = inf_j λ_{P_j}` is plurisubharmonic over the base of `P₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNS

open E2Nov16FNPolynomialPolyhedron E2Nov16FNPolynomialGraphBox FNR

variable {n : ℕ}

/-! ### The functions `(1/k) log |a|` -/

/-- `(1/k) log |a(z)|`, written as `(2k)⁻¹ log |a(z)|²` (TN's `generatorLog`). -/
def monoLog (a : Poly n) (k : ℕ) (z : ComplexModel n) : EReal :=
  (((2 * k : ℝ))⁻¹ : ℝ) * generatorLog (fun _ : Fin 1 => polyEval a) z

theorem generatorLog_one (a : Poly n) (z : ComplexModel n) :
    generatorLog (fun _ : Fin 1 => polyEval a) z =
      ENNReal.log (ENNReal.ofReal (‖polyEval a z‖ ^ 2)) := by
  simp only [generatorLog, SGPT.Foundations.Analysis.logNormSq]
  rw [generatorVector_norm_sq, generatorNormSq]
  simp

theorem monoLog_lt_iff (a : Poly n) {k : ℕ} (hk : k ≠ 0) (z : ComplexModel n) (t : ℝ) :
    monoLog a k z < t ↔ ‖polyEval a z‖ < Real.exp (k * t) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hc : (0 : ℝ) < (2 * k : ℝ)⁻¹ := by positivity
  rw [monoLog, generatorLog_one]
  by_cases ha : polyEval a z = 0
  · rw [ha, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero,
      ENNReal.log_zero]
    rw [EReal.coe_mul_bot_of_pos hc]
    exact ⟨fun _ => Real.exp_pos _, fun _ => EReal.bot_lt_coe t⟩
  · have hpos : 0 < ‖polyEval a z‖ ^ 2 := by positivity
    rw [ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul, EReal.coe_lt_coe_iff]
    rw [inv_mul_lt_iff₀ (by positivity), Real.log_lt_iff_lt_exp hpos]
    have h2 : Real.exp (2 * k * t) = Real.exp (k * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [h2]
    exact sq_lt_sq₀ (norm_nonneg _) (Real.exp_pos _).le

/-- `(1/k) log |a|` is plurisubharmonic on `ℂⁿ`. -/
theorem discPshOn_monoLog (a : Poly n) {k : ℕ} (hk : k ≠ 0) (U : Set (ComplexModel n)) :
    DiscPshOn (monoLog a k) U := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hc : (0 : ℝ) < (2 * k : ℝ)⁻¹ := by positivity
  refine (SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn (U := univ) fun x _ => ?_).mono
    (subset_univ U)
  exact SGPT.Foundations.Analysis.Pending.plurisubharmonicAt_scaled_generatorLog
    ⟨univ, isOpen_univ, mem_univ x, fun _ => (differentiable_polyEval a).differentiableOn⟩ hc

/-! ### The Hartogs radius of a monomial polyhedron -/

/-- `λ_S(z) = max_{(a, k) ∈ S, k ≥ 1} (1/k) log |a(z)|`. -/
def polyLambda (S : Finset (Poly n × ℕ)) (z : ComplexModel n) : EReal :=
  S.sup fun m => if m.2 = 0 then ⊥ else monoLog m.1 m.2 z

/-- The base condition of a monomial polyhedron: `|a(z)| < 1` for the monomials with `k = 0`. -/
def zcond (S : Finset (Poly n × ℕ)) (z : ComplexModel n) : Prop :=
  ∀ m ∈ S, m.2 = 0 → ‖polyEval m.1 z‖ < 1

theorem polyLambda_lt_iff (S : Finset (Poly n × ℕ)) (z : ComplexModel n) (t : ℝ) :
    polyLambda S z < t ↔ ∀ m ∈ S, m.2 ≠ 0 → ‖polyEval m.1 z‖ < Real.exp (m.2 * t) := by
  rw [polyLambda, Finset.sup_lt_iff (EReal.bot_lt_coe t)]
  refine forall₂_congr fun m _ => ?_
  by_cases hm : m.2 = 0
  · simp [hm, EReal.bot_lt_coe]
  · simp only [hm, if_false, ne_eq, not_false_eq_true, forall_const]
    exact monoLog_lt_iff m.1 hm z t

theorem mem_monoPoly_mkPt_iff (S : Finset (Poly n × ℕ)) (z : ComplexModel n) (w : ℂ) :
    mkPt z w ∈ monoPoly S ↔ ∀ m ∈ S, ‖polyEval m.1 z‖ * ‖w‖ ^ m.2 < 1 := by
  simp only [monoPoly, mem_setOf_eq, polyEval_mono, zpart_mkPt, mkPt_zero, norm_mul, norm_pow]

theorem zcond_iff_mem_monoPoly (S : Finset (Poly n × ℕ)) (z : ComplexModel n) :
    zcond S z ↔ mkPt z 0 ∈ monoPoly S := by
  rw [mem_monoPoly_mkPt_iff]
  refine forall₂_congr fun m _ => ?_
  by_cases hm : m.2 = 0
  · simp [hm]
  · simp [hm, norm_zero, zero_pow hm]

theorem isOpen_setOf_zcond (S : Finset (Poly n × ℕ)) : IsOpen {z : ComplexModel n | zcond S z} := by
  have h : {z : ComplexModel n | zcond S z} = (fun z => mkPt z 0) ⁻¹' monoPoly S := by
    ext z; exact zcond_iff_mem_monoPoly S z
  rw [h]
  exact (isOpen_monoPoly S).preimage (continuous_mkPt.comp (continuous_id.prodMk continuous_const))

/-- `λ_P(z) < t` and `|w| ≤ e^{-t}` put `(w, z)` in `P` (over the base of `P`). -/
theorem mem_monoPoly_of_polyLambda_lt {S : Finset (Poly n × ℕ)} {z : ComplexModel n}
    (hz : zcond S z) {t : ℝ} (ht : polyLambda S z < t) {w : ℂ} (hw : ‖w‖ ≤ Real.exp (-t)) :
    mkPt z w ∈ monoPoly S := by
  rw [mem_monoPoly_mkPt_iff]
  intro m hm
  by_cases hk : m.2 = 0
  · simpa [hk] using hz m hm hk
  · have h1 := (polyLambda_lt_iff S z t).mp ht m hm hk
    have h2 : ‖w‖ ^ m.2 ≤ Real.exp (-(m.2 * t)) := by
      calc ‖w‖ ^ m.2 ≤ Real.exp (-t) ^ m.2 := pow_le_pow_left₀ (norm_nonneg _) hw _
        _ = Real.exp (-(m.2 * t)) := by rw [← Real.exp_nat_mul]; ring_nf
    calc ‖polyEval m.1 z‖ * ‖w‖ ^ m.2 ≤ ‖polyEval m.1 z‖ * Real.exp (-(m.2 * t)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ < Real.exp (m.2 * t) * Real.exp (-(m.2 * t)) :=
          mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _ = 1 := by rw [← Real.exp_add]; simp

/-- `(w, z) ∈ P` with `w ≠ 0` gives `λ_P(z) < -log |w|`. -/
theorem polyLambda_lt_of_mem_monoPoly {S : Finset (Poly n × ℕ)} {z : ComplexModel n} {w : ℂ}
    (hzw : mkPt z w ∈ monoPoly S) (hw : w ≠ 0) :
    polyLambda S z < ((-Real.log ‖w‖ : ℝ) : EReal) := by
  rw [polyLambda_lt_iff]
  intro m hm hk
  have h := (mem_monoPoly_mkPt_iff S z w).mp hzw m hm
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hpow : 0 < ‖w‖ ^ m.2 := pow_pos hwpos _
  have he : Real.exp (m.2 * -Real.log ‖w‖) = (‖w‖ ^ m.2)⁻¹ := by
    rw [mul_neg, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hwpos]
  rw [he]
  calc ‖polyEval m.1 z‖ = ‖polyEval m.1 z‖ * ‖w‖ ^ m.2 / ‖w‖ ^ m.2 := by field_simp
    _ < 1 / ‖w‖ ^ m.2 := div_lt_div_of_pos_right h hpow
    _ = (‖w‖ ^ m.2)⁻¹ := one_div _

theorem zcond_of_mem_monoPoly {S : Finset (Poly n × ℕ)} {z : ComplexModel n} {w : ℂ}
    (hzw : mkPt z w ∈ monoPoly S) : zcond S z := by
  intro m hm hk
  have h := (mem_monoPoly_mkPt_iff S z w).mp hzw m hm
  simpa [hk] using h

/-- Larger monomial polyhedra have smaller Hartogs functions over the base of the smaller one. -/
theorem polyLambda_anti {S S' : Finset (Poly n × ℕ)} (hSS' : monoPoly S ⊆ monoPoly S')
    {z : ComplexModel n} (hz : zcond S z) : polyLambda S' z ≤ polyLambda S z := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hn : ‖(Real.exp (-t) : ℂ)‖ = Real.exp (-t) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hmem := hSS' (mem_monoPoly_of_polyLambda_lt hz ht1 hn.le)
  have h := polyLambda_lt_of_mem_monoPoly hmem
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [hn, Real.log_exp, neg_neg] at h
  exact absurd (h.trans ht2) (lt_irrefl _)

/-- `λ_S` is plurisubharmonic on `ℂⁿ`. -/
theorem discPshOn_polyLambda (S : Finset (Poly n × ℕ)) (U : Set (ComplexModel n)) :
    DiscPshOn (polyLambda S) U := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h : polyLambda (∅ : Finset (Poly n × ℕ)) = fun _ => ⊥ := by
      funext z; simp [polyLambda]
    rw [h]
    exact discPshOn_const ⊥ bot_ne_top U
  | insert m S hm ih =>
    have h : polyLambda (insert m S) =
        fun z => Max.max ((if m.2 = 0 then ⊥ else monoLog m.1 m.2 z)) (polyLambda S z) := by
      funext z; simp only [polyLambda, Finset.sup_insert]
    rw [h]
    refine DiscPshOn.max ?_ ih
    by_cases hk : m.2 = 0
    · simp only [hk, if_true]
      exact discPshOn_const ⊥ bot_ne_top U
    · simp only [hk, if_false]
      exact discPshOn_monoLog m.1 hk U

/-- **Hartogs step.** For an increasing sequence of monomial polyhedra `P_j`, the decreasing
limit `λ = inf_j λ_{P_j}` is plurisubharmonic over the base of `P₀`. -/
theorem discPshOn_iInf_polyLambda {S : ℕ → Finset (Poly n × ℕ)}
    (hS : ∀ j, monoPoly (S j) ⊆ monoPoly (S (j + 1))) :
    DiscPshOn (fun z => ⨅ j, polyLambda (S j) z) {z | zcond (S 0) z} := by
  refine DiscPshOn.iInf_of_antitone (fun j => discPshOn_polyLambda (S j) _) ?_
  intro z hz
  have hmono : ∀ j, monoPoly (S 0) ⊆ monoPoly (S j) := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact ih.trans (hS j)
  have hzj : ∀ j, zcond (S j) z := fun j =>
    zcond_of_mem_monoPoly (hmono j ((zcond_iff_mem_monoPoly (S 0) z).mp hz))
  exact antitone_nat_of_succ_le fun j => polyLambda_anti (hS j) (hzj j)

end SGPT.Unibranch.FNS
