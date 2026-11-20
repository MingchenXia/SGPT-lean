import SGPT.PSH.BookThinNormalization
import SGPT.PSH.BoundaryGluing
import SGPT.PSH.DecreasingNets
import SGPT.Foundations.Analysis.LogPole
import SGPT.Foundations.Analysis.PshAddition
import SGPT.Foundations.Analysis.Pending.PshConvexCone
import SGPT.Foundations.Analysis.FirstPass.PshDiscLocalGlobal

/-!
# The Bedford–Taylor base theorem for thin sets (`prop:BTthin`)

Source: `prop:BTthin` of the chapter *Plurisubharmonic functions*. Let `Ω ⊆ ℂⁿ` be open,
`E ⊆ Ω` and `x ∈ closure E` such that `E` is thin at `x` (`def:pshfunctions:L691`, formalized as
`SGPT.PSH.sourceThinAt`). Then there is `φ ∈ PSH(ℂⁿ)` such that

1. `φ` is locally bounded on `ℂⁿ \ {x}`;
2. `φ(x) > -∞`;
3. `φ(y) → -∞` as `y → x` along `E \ {x}`.

We follow the book's proof. By `rmk:cstthindef` there is a psh function `ψ` near `x` with
`ψ = -1` on `E \ {x}` and `ψ(x) = 0`. For radii `δⱼ ↓` chosen by upper semicontinuity
(`ψ < 2^{-(j+3)}` on `B(x, δⱼ)`) one glues (`cor:glbdry`)

`φⱼ = kⱼ log |z - x|² ∨ (ψ - 2^{-(j+1)})` on `B(x, δⱼ)`, `φⱼ = kⱼ log |z - x|²` outside,

with `kⱼ = 2^{-(j+1)} / (4 |log δⱼ|)`, and sums: on a small ball the partial sums decrease
(`prop:pshfunction_closedseq`), outside `B(x, δ₀)` the series is `K log |z - x|²` with
`K = Σ kⱼ`.

Main declarations:

* `SGPT.PSH.BookDeepThin.exists_pole_function_of_normalized` — the construction from a
  normalized local witness;
* `SGPT.PSH.BookDeepThin.bedfordTaylor_thin` — `prop:BTthin`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.BookDeepThin

open Set Filter Metric TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

variable {n : ℕ}

/-! ### Logarithmic poles -/

/-- The logarithmic pole `log |z - a|²` centred at `a`, with value `-∞` at `a`. -/
def logPole (a z : ComplexModel n) : EReal := logNormSq (z - a)

theorem discPshOn_logPole (a : ComplexModel n) (U : Set (ComplexModel n)) :
    DiscPshOn (logPole a) U := by
  have h := (discPshOn_logNormSq (univ : Set (ComplexModel n))).comp_affine
    (ContinuousLinearMap.id ℂ (ComplexModel n)) (-a)
  have heq : (fun y : ComplexModel n => logNormSq (-a + (ContinuousLinearMap.id ℂ _) y)) =
      logPole a := by
    funext y
    simp [logPole, sub_eq_neg_add]
  rw [heq, preimage_univ] at h
  exact h.mono (subset_univ U)

theorem logPole_of_ne {a z : ComplexModel n} (hz : z ≠ a) :
    logPole a z = ((Real.log (‖z - a‖ ^ 2) : ℝ) : EReal) :=
  logNormSq_of_ne_zero (sub_ne_zero.mpr hz)

@[simp] theorem logPole_self (a : ComplexModel n) : logPole a a = ⊥ := by
  simp [logPole]

theorem logPole_ne_top (a z : ComplexModel n) : logPole a z ≠ ⊤ := logNormSq_ne_top _

/-- A positive multiple of the pole is nonpositive on the closed unit ball. -/
theorem mul_logPole_nonpos {a z : ComplexModel n} (hz : ‖z - a‖ ≤ 1) {k : ℝ} (hk : 0 < k) :
    (k : EReal) * logPole a z ≤ 0 := by
  by_cases hza : z = a
  · subst hza
    rw [logPole_self, EReal.coe_mul_bot_of_pos hk]
    exact bot_le
  · rw [logPole_of_ne hza, ← EReal.coe_mul]
    apply EReal.coe_nonpos.mpr
    apply mul_nonpos_of_nonneg_of_nonpos hk.le
    exact Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)

theorem pshOn_mul_logPole (a : ComplexModel n) {k : ℝ} (hk : 0 < k)
    (hpt : ∃ z : ComplexModel n, z ≠ a) :
    PSHOn (fun z => (k : EReal) * logPole a z) univ := by
  refine ⟨(discPshOn_logPole a univ).const_mul hk, ?_⟩
  obtain ⟨z, hz⟩ := hpt
  refine ⟨z, mem_univ z, ?_⟩
  rw [logPole_of_ne hz, ← EReal.coe_mul]
  exact EReal.coe_ne_bot _

/-! ### Finite sums -/

theorem discPshOn_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ComplexModel n → EReal}
    {U : Set (ComplexModel n)} (hf : ∀ j ∈ s, DiscPshOn (f j) U) :
    DiscPshOn (fun z => ∑ j ∈ s, f j z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using discPshOn_const (0 : EReal) EReal.zero_ne_top U
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ j ∈ s, f j : ℝ) : EReal) = ∑ j ∈ s, ((f j : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]


/-! ### Dyadic weights and radii -/

/-- The dyadic weights `tⱼ = 2^{-(j+1)}`, with `Σ tⱼ = 1`. -/
def tw (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

theorem tw_pos (j : ℕ) : 0 < tw j := by unfold tw; positivity

theorem summable_tw : Summable tw := by
  have h := summable_geometric_two.mul_left (1 / 2 : ℝ)
  refine h.congr fun j => ?_
  simp only [tw, pow_succ]
  ring

theorem sum_range_tw_le_one (N : ℕ) : ∑ j ∈ Finset.range N, tw j ≤ 1 := by
  have h := sum_geometric_two_le N
  have heq : ∑ j ∈ Finset.range N, tw j = (1 / 2) * ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tw, pow_succ]
    ring
  rw [heq]
  linarith

/-- Radii `δⱼ` with `δ₀ ≤ min(ε₀, r/2, e⁻¹)` and `δ_{j+1} ≤ min(ε_{j+1}, δⱼ/2)`. -/
def radii (ε : ℕ → ℝ) (r : ℝ) : ℕ → ℝ
  | 0 => min (ε 0) (min (r / 2) (Real.exp (-1)))
  | j + 1 => min (ε (j + 1)) (radii ε r j / 2)

section Radii

variable {ε : ℕ → ℝ} {r : ℝ} (hε : ∀ j, 0 < ε j) (hr : 0 < r)
include hε hr

theorem radii_pos (j : ℕ) : 0 < radii ε r j := by
  induction j with
  | zero => exact lt_min (hε 0) (lt_min (by linarith) (Real.exp_pos _))
  | succ j ih => exact lt_min (hε (j + 1)) (by linarith)

omit hε hr in
theorem radii_le_eps (j : ℕ) : radii ε r j ≤ ε j := by
  cases j with
  | zero => exact min_le_left _ _
  | succ j => exact min_le_left _ _

theorem radii_succ_le (j : ℕ) : radii ε r (j + 1) ≤ radii ε r j := by
  have h := radii_pos hε hr j
  show min (ε (j + 1)) (radii ε r j / 2) ≤ radii ε r j
  exact (min_le_right _ _).trans (by linarith)

theorem radii_antitone : Antitone (radii ε r) :=
  antitone_nat_of_succ_le (radii_succ_le hε hr)

theorem radii_le_zero (j : ℕ) : radii ε r j ≤ radii ε r 0 :=
  radii_antitone hε hr (Nat.zero_le j)

omit hε in
theorem radii_zero_lt : radii ε r 0 < r := by
  have : radii ε r 0 ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  linarith

theorem radii_lt (j : ℕ) : radii ε r j < r :=
  (radii_le_zero hε hr j).trans_lt (radii_zero_lt hr)

theorem radii_le_exp (j : ℕ) : radii ε r j ≤ Real.exp (-1) :=
  (radii_le_zero hε hr j).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem one_le_neg_log_radii (j : ℕ) : 1 ≤ -Real.log (radii ε r j) := by
  have h := Real.log_le_log (radii_pos hε hr j) (radii_le_exp hε hr j)
  rw [Real.log_exp] at h
  linarith

end Radii

/-! ### The construction from a normalized witness -/

/-- **Core of `prop:BTthin`.** Let `ψ` be psh on a ball `B(x₀, r)`, `r ≤ 1`, with `ψ(x₀) = 0`
and `ψ = -1` on `S ∩ B(x₀, r)`. Then there is `φ ∈ PSH(ℂⁿ)`, locally bounded off `x₀`, with
`φ(x₀) > -∞`, and `φ ≤ -J` on `S` near `x₀` for every `J`. -/
theorem exists_pole_function_of_normalized {x₀ : ComplexModel n} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) {ψ : ComplexModel n → EReal} (hψ : PSHOn ψ (ball x₀ r)) (hψ0 : ψ x₀ = 0)
    {S : Set (ComplexModel n)} (hS : ∀ y ∈ S, y ∈ ball x₀ r → ψ y = -1)
    (hpt : ∃ z : ComplexModel n, z ≠ x₀) :
    ∃ φ : ComplexModel n → EReal, PSHOn φ univ ∧
      (∀ z, z ≠ x₀ → ∃ V ∈ 𝓝 z, ∃ C : ℝ, ∀ y ∈ V, ((-C : ℝ) : EReal) ≤ φ y ∧ φ y ≤ C) ∧
      φ x₀ ≠ ⊥ ∧
      ∀ J : ℕ, ∃ ε > 0, ∀ y ∈ S, ‖y - x₀‖ < ε → φ y ≤ ((-(J : ℝ) : ℝ) : EReal) := by
  classical
  -- Step 1: radii from upper semicontinuity of `ψ` at `x₀`.
  have hnhds : 𝓝[ball x₀ r] x₀ = 𝓝 x₀ := nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds
    (mem_ball_self hr))
  have hev : ∀ j : ℕ, ∀ᶠ z in 𝓝 x₀, ψ z < ((tw j / 4 : ℝ) : EReal) := by
    intro j
    have h := hψ.disc.upperSemicontinuousOn x₀ (mem_ball_self hr) ((tw j / 4 : ℝ) : EReal)
      (by show ψ x₀ < _; rw [hψ0]; exact EReal.coe_pos.mpr (by linarith [tw_pos j]))
    rwa [hnhds] at h
  choose ε hε hεP using fun j => Metric.eventually_nhds_iff_ball.mp (hev j)
  set δ : ℕ → ℝ := radii ε r with hδdef
  have hδpos : ∀ j, 0 < δ j := radii_pos hε hr
  have hδr : ∀ j, δ j < r := radii_lt hε hr
  have hδ0 : ∀ j, δ j ≤ δ 0 := radii_le_zero hε hr
  have hψδ : ∀ j, ∀ z ∈ ball x₀ (δ j), ψ z < ((tw j / 4 : ℝ) : EReal) :=
    fun j z hz => hεP j z (ball_subset_ball (radii_le_eps j) hz)
  have hlog : ∀ j, 1 ≤ -Real.log (δ j) := one_le_neg_log_radii hε hr
  -- Step 2: the coefficients `kⱼ = tⱼ / (4 |log δⱼ|)`.
  set k : ℕ → ℝ := fun j => tw j / (4 * -Real.log (δ j)) with hkdef
  have hk : ∀ j, 0 < k j := fun j => div_pos (tw_pos j) (by linarith [hlog j])
  have hk_le : ∀ j, k j ≤ tw j := by
    intro j
    rw [hkdef, div_le_iff₀ (by linarith [hlog j])]
    nlinarith [tw_pos j, hlog j]
  have hk_summable : Summable k :=
    Summable.of_nonneg_of_le (fun j => (hk j).le) hk_le summable_tw
  set K : ℝ := ∑' j, k j with hKdef
  have hK : 0 < K := hk_summable.tsum_pos (fun j => (hk j).le) 0 (hk 0)
  have hpartial : ∀ N, ∑ j ∈ Finset.range N, k j ≤ K := fun N =>
    hk_summable.sum_le_tsum _ (fun j _ => (hk j).le)
  -- Step 3: the glued functions `φⱼ`.
  set φj : ℕ → ComplexModel n → EReal := fun j => gluedMax (ball x₀ (δ j))
    (fun z => ψ z + ((-tw j : ℝ) : EReal)) (fun z => (k j : EReal) * logPole x₀ z) with hφjdef
  have hφj_psh : ∀ j, PSHOn (φj j) univ := by
    intro j
    apply pshOn_gluedMax_of_boundary_limsup isOpen_univ isOpen_ball
      (pshOn_mul_logPole x₀ (hk j) hpt)
    · refine ⟨(hψ.disc.mono (ball_subset_ball (hδr j).le)).add
        (discPshOn_const _ (EReal.coe_ne_top _) _), ⟨x₀, mem_ball_self (hδpos j), ?_⟩⟩
      rw [hψ0, zero_add]
      exact EReal.coe_ne_bot _
    · intro z hz
      have hzs : z ∈ sphere x₀ (δ j) := by
        have := hz.2
        rwa [frontier_ball x₀ (hδpos j).ne'] at this
      have hnorm : ‖z - x₀‖ = δ j := by rwa [mem_sphere_iff_norm] at hzs
      have hzne : z ≠ x₀ := by
        intro h
        rw [h, sub_self, norm_zero] at hnorm
        exact (hδpos j).ne' hnorm.symm
      have hlogδ : Real.log (δ j) ≠ 0 := by linarith [hlog j]
      have hrhs : (k j : EReal) * logPole x₀ z = ((-(tw j / 2) : ℝ) : EReal) := by
        rw [logPole_of_ne hzne, ← EReal.coe_mul, hnorm, Real.log_pow]
        congr 1
        have htw : tw j ≠ 0 := (tw_pos j).ne'
        rw [hkdef]
        field_simp
        push_cast
        ring
      rw [hrhs]
      calc limsup (fun z => ψ z + ((-tw j : ℝ) : EReal)) (𝓝[ball x₀ (δ j)] z)
          ≤ ((tw j / 4 - tw j : ℝ) : EReal) := by
            apply limsup_le_of_le
            · isBoundedDefault
            · refine eventually_nhdsWithin_of_forall fun y hy => ?_
              have h1 := (hψδ j y hy).le
              calc ψ y + ((-tw j : ℝ) : EReal) ≤ ((tw j / 4 : ℝ) : EReal) + ((-tw j : ℝ) : EReal) :=
                    add_le_add h1 le_rfl
                _ = ((tw j / 4 - tw j : ℝ) : EReal) := by
                    rw [← EReal.coe_add, ← sub_eq_add_neg]
        _ ≤ ((-(tw j / 2) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith [tw_pos j])
  have hφj_ge : ∀ j z, (k j : EReal) * logPole x₀ z ≤ φj j z := by
    intro j z
    simp only [hφjdef, gluedMax]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hφj_nonpos : ∀ j, ∀ z ∈ ball x₀ r, φj j z ≤ 0 := by
    intro j z hz
    have hz1 : ‖z - x₀‖ ≤ 1 := by
      rw [mem_ball, dist_eq_norm] at hz
      linarith
    by_cases hzj : z ∈ ball x₀ (δ j)
    · simp only [hφjdef, gluedMax, hzj, if_true]
      refine max_le ?_ (mul_logPole_nonpos hz1 (hk j))
      calc ψ z + ((-tw j : ℝ) : EReal) ≤ ((tw j / 4 : ℝ) : EReal) + ((-tw j : ℝ) : EReal) :=
            add_le_add (hψδ j z hzj).le le_rfl
        _ = ((tw j / 4 - tw j : ℝ) : EReal) := by rw [← EReal.coe_add, ← sub_eq_add_neg]
        _ ≤ 0 := EReal.coe_nonpos.mpr (by linarith [tw_pos j])
    · simp only [hφjdef, gluedMax, hzj, if_false]
      exact mul_logPole_nonpos hz1 (hk j)
  have hφj_center : ∀ j, φj j x₀ = ((-tw j : ℝ) : EReal) := by
    intro j
    simp only [hφjdef, gluedMax, mem_ball_self (hδpos j), if_true, hψ0, zero_add, logPole_self,
      EReal.coe_mul_bot_of_pos (hk j)]
    exact max_bot_right _
  have hφj_outer : ∀ j z, δ 0 < ‖z - x₀‖ → φj j z = (k j : EReal) * logPole x₀ z := by
    intro j z hz
    have hzj : z ∉ ball x₀ (δ j) := by
      rw [mem_ball, dist_eq_norm, not_lt]
      exact (hδ0 j).trans hz.le
    simp only [hφjdef, gluedMax, hzj, if_false]
  set γ : ℕ → ℝ := fun j => Real.exp (2 * Real.log (δ j) / tw j) with hγdef
  have hγ : ∀ j, 0 < γ j := fun j => Real.exp_pos _
  have hφj_pole : ∀ j, ∀ y ∈ S, ‖y - x₀‖ < γ j → φj j y ≤ -1 := by
    intro j y hyS hyγ
    have hkL : (k j : EReal) * logPole x₀ y ≤ -1 := by
      by_cases hyx : y = x₀
      · rw [hyx, logPole_self, EReal.coe_mul_bot_of_pos (hk j)]
        exact bot_le
      · rw [logPole_of_ne hyx, ← EReal.coe_mul]
        have hpos : 0 < ‖y - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
        have hl : Real.log ‖y - x₀‖ < 2 * Real.log (δ j) / tw j := by
          have := Real.log_lt_log hpos hyγ
          rwa [hγdef, Real.log_exp] at this
        have hlogδ : 0 < -Real.log (δ j) := by linarith [hlog j]
        have hkey : k j * Real.log (‖y - x₀‖ ^ 2) < -1 := by
          have hl2 : Real.log (‖y - x₀‖ ^ 2) = 2 * Real.log ‖y - x₀‖ := by
            rw [Real.log_pow]; push_cast; ring
          rw [hl2]
          have h2 : k j * (2 * Real.log ‖y - x₀‖) < k j * (2 * (2 * Real.log (δ j) / tw j)) :=
            mul_lt_mul_of_pos_left (by linarith) (hk j)
          have htw : tw j ≠ 0 := (tw_pos j).ne'
          have hlogδne : Real.log (δ j) ≠ 0 := by linarith
          have h3 : k j * (2 * (2 * Real.log (δ j) / tw j)) = -1 := by
            rw [hkdef]
            field_simp
            ring
          linarith
        rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp]
        exact EReal.coe_le_coe_iff.mpr hkey.le
    by_cases hyj : y ∈ ball x₀ (δ j)
    · simp only [hφjdef, gluedMax, hyj, if_true]
      refine max_le ?_ hkL
      rw [hS y hyS (ball_subset_ball (hδr j).le hyj)]
      calc (-1 : EReal) + ((-tw j : ℝ) : EReal) = ((-1 - tw j : ℝ) : EReal) := by
            rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp, ← EReal.coe_add, ← sub_eq_add_neg]
        _ ≤ -1 := by
            rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp]
            exact EReal.coe_le_coe_iff.mpr (by linarith [tw_pos j])
    · simp only [hφjdef, gluedMax, hyj, if_false]
      exact hkL
  -- Step 4: the partial sums, decreasing on `B(x₀, r)`.
  set Ssum : ℕ → ComplexModel n → EReal := fun N z => ∑ j ∈ Finset.range N, φj j z
    with hSsumdef
  have hS_center : ∀ N, Ssum N x₀ = ((-(∑ j ∈ Finset.range N, tw j) : ℝ) : EReal) := by
    intro N
    simp only [hSsumdef, hφj_center]
    rw [← coe_finset_sum, Finset.sum_neg_distrib]
  have hS_center_ge : ∀ N, ((-1 : ℝ) : EReal) ≤ Ssum N x₀ := by
    intro N
    rw [hS_center]
    exact EReal.coe_le_coe_iff.mpr (by linarith [sum_range_tw_le_one N])
  have hS_disc : ∀ N, DiscPshOn (Ssum N) univ := fun N =>
    discPshOn_finset_sum _ fun j _ => (hφj_psh j).disc
  have hS_anti : ∀ z ∈ ball x₀ r, Antitone fun N => Ssum N z := by
    intro z hz
    refine antitone_nat_of_succ_le fun N => ?_
    simp only [hSsumdef, Finset.sum_range_succ]
    exact add_le_of_nonpos_right (hφj_nonpos N z hz)
  have hinf_psh : PSHOn (fun z => ⨅ N, Ssum N z) (ball x₀ r) := by
    refine SGPT.PSH.pshOn_iInf_of_antitone (fun N => ⟨(hS_disc N).mono (subset_univ _),
      ⟨x₀, mem_ball_self hr, ?_⟩⟩) hS_anti ⟨x₀, mem_ball_self hr, ?_⟩
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hS_center_ge N)
    · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-1)) (le_iInf hS_center_ge)
  -- Step 5: off `B(x₀, δ₀)` the series is `K log |z - x₀|²`.
  have hS_outer : ∀ z, δ 0 < ‖z - x₀‖ → ‖z - x₀‖ ≤ 1 →
      ⨅ N, Ssum N z = (K : EReal) * logPole x₀ z := by
    intro z hz hz1
    have hzne : z ≠ x₀ := by
      intro h
      rw [h, sub_self, norm_zero] at hz
      linarith [hδpos 0]
    set ℓ : ℝ := Real.log (‖z - x₀‖ ^ 2) with hℓ
    have hℓ0 : ℓ ≤ 0 := Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hz1)
    have hval : ∀ N, Ssum N z = (((∑ j ∈ Finset.range N, k j) * ℓ : ℝ) : EReal) := by
      intro N
      simp only [hSsumdef, hφj_outer _ z hz, logPole_of_ne hzne, ← EReal.coe_mul]
      rw [← coe_finset_sum, Finset.sum_mul]
    simp only [hval]
    rw [logPole_of_ne hzne, ← EReal.coe_mul]
    have hanti : Antitone fun N => ((((∑ j ∈ Finset.range N, k j) * ℓ : ℝ)) : EReal) := by
      refine antitone_nat_of_succ_le fun N => EReal.coe_le_coe_iff.mpr ?_
      rw [Finset.sum_range_succ, add_mul]
      nlinarith [hk N]
    have htend : Tendsto (fun N => ((((∑ j ∈ Finset.range N, k j) * ℓ : ℝ)) : EReal)) atTop
        (𝓝 ((K * ℓ : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr (hk_summable.hasSum.tendsto_sum_nat.mul_const ℓ)
    exact tendsto_nhds_unique (tendsto_atTop_iInf hanti) htend
  -- Step 6: the function `φ`.
  set φ : ComplexModel n → EReal := fun z =>
    if z ∈ ball x₀ r then ⨅ N, Ssum N z else (K : EReal) * logPole x₀ z with hφdef
  have hKL : ∀ z, PlurisubharmonicAt (fun w => (K : EReal) * logPole x₀ w) z := fun z =>
    ((discPshOn_logPole x₀ univ).const_mul hK).plurisubharmonicOn isOpen_univ z (mem_univ z)
  have hφ_psh_on : PlurisubharmonicOn φ univ := by
    intro z _
    by_cases hz : z ∈ ball x₀ r
    · refine ((hinf_psh.disc.plurisubharmonicOn isOpen_ball) z hz).congr ?_
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      simp only [hφdef, hw, if_true]
    · have hzr : r ≤ ‖z - x₀‖ := by
        rw [mem_ball, dist_eq_norm, not_lt] at hz
        exact hz
      have hO : IsOpen {w : ComplexModel n | δ 0 < ‖w - x₀‖} :=
        isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
      have hzO : z ∈ {w : ComplexModel n | δ 0 < ‖w - x₀‖} :=
        (radii_zero_lt hr).trans_le hzr
      refine (hKL z).congr ?_
      filter_upwards [hO.mem_nhds hzO] with w hw
      by_cases hwr : w ∈ ball x₀ r
      · simp only [hφdef, hwr, if_true]
        have hw1 : ‖w - x₀‖ ≤ 1 := by
          rw [mem_ball, dist_eq_norm] at hwr
          linarith
        exact (hS_outer w hw hw1).symm
      · simp only [hφdef, hwr, if_false]
  have hφx₀ : φ x₀ ≠ ⊥ := by
    simp only [hφdef, mem_ball_self hr, if_true]
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-1)) (le_iInf hS_center_ge)
  have hφ_psh : PSHOn φ univ := ⟨hφ_psh_on.discPshOn, ⟨x₀, mem_univ _, hφx₀⟩⟩
  -- Step 7: the lower bound `φ ≥ K log |z - x₀|²`.
  have hφ_ge : ∀ y, (K : EReal) * logPole x₀ y ≤ φ y := by
    intro y
    by_cases hy : y ∈ ball x₀ r
    · simp only [hφdef, hy, if_true]
      refine le_iInf fun N => ?_
      by_cases hyx : y = x₀
      · rw [hyx, logPole_self, EReal.coe_mul_bot_of_pos hK]
        exact bot_le
      · have hy1 : ‖y - x₀‖ ≤ 1 := by
          rw [mem_ball, dist_eq_norm] at hy
          linarith
        set ℓ : ℝ := Real.log (‖y - x₀‖ ^ 2) with hℓ
        have hℓ0 : ℓ ≤ 0 := Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hy1)
        rw [logPole_of_ne hyx, ← EReal.coe_mul]
        calc ((K * ℓ : ℝ) : EReal) ≤ (((∑ j ∈ Finset.range N, k j) * ℓ : ℝ) : EReal) :=
              EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonpos_right (hpartial N) hℓ0)
          _ = ∑ j ∈ Finset.range N, ((k j : EReal) * logPole x₀ y) := by
              rw [Finset.sum_mul, coe_finset_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [logPole_of_ne hyx, ← EReal.coe_mul]
          _ ≤ Ssum N y := Finset.sum_le_sum fun j _ => hφj_ge j y
    · simp only [hφdef, hy, if_false, le_refl]
  refine ⟨φ, hφ_psh, ?_, hφx₀, ?_⟩
  · -- Property 1: local boundedness off `x₀`.
    intro z hz
    obtain ⟨q, hq, -⟩ := EReal.exists_rat_btwn_of_lt
      (lt_top_iff_ne_top.mpr (hφ_psh.disc.ne_top z (mem_univ z)))
    have hup : ∀ᶠ y in 𝓝 z, φ y < ((q : ℝ) : EReal) := by
      have h := hφ_psh.disc.upperSemicontinuousOn z (mem_univ z) ((q : ℝ) : EReal) (by
        exact_mod_cast hq)
      rwa [nhdsWithin_univ] at h
    set ρ : ℝ := ‖z - x₀‖ / 2 with hρ
    have hρpos : 0 < ρ := by
      have := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
      rw [hρ]; linarith
    refine ⟨ball z ρ ∩ {y | φ y < ((q : ℝ) : EReal)},
      inter_mem (ball_mem_nhds z hρpos) hup, max (q : ℝ) (-(K * Real.log (ρ ^ 2))), ?_⟩
    rintro y ⟨hyb, hyq⟩
    have hyρ : ρ ≤ ‖y - x₀‖ := by
      rw [mem_ball, dist_eq_norm] at hyb
      have h1 : ‖z - x₀‖ ≤ ‖z - y‖ + ‖y - x₀‖ := by
        calc ‖z - x₀‖ = ‖(z - y) + (y - x₀)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖y - x₀‖ := norm_add_le _ _
      have h2 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev _ _
      rw [hρ] at hyb ⊢
      linarith
    have hyne : y ≠ x₀ := by
      intro h
      rw [h, sub_self, norm_zero] at hyρ
      linarith
    constructor
    · have hlow := hφ_ge y
      rw [logPole_of_ne hyne, ← EReal.coe_mul] at hlow
      refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hlow
      have hlog : Real.log (ρ ^ 2) ≤ Real.log (‖y - x₀‖ ^ 2) :=
        Real.log_le_log (by positivity) (pow_le_pow_left₀ hρpos.le hyρ 2)
      have := mul_le_mul_of_nonneg_left hlog hK.le
      have hmax : -(K * Real.log (ρ ^ 2)) ≤ max (q : ℝ) (-(K * Real.log (ρ ^ 2))) :=
        le_max_right _ _
      linarith
    · exact hyq.le.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  · -- Property 3: `φ ≤ -J` on `S` near `x₀`.
    intro J
    have hεJ : ∃ ε₀ > 0, ε₀ ≤ r ∧ ∀ j < J, ε₀ ≤ γ j := by
      induction J with
      | zero => exact ⟨r, hr, le_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      | succ J ih =>
        obtain ⟨ε₀, hε₀, hε₀r, hε₀γ⟩ := ih
        refine ⟨min ε₀ (γ J), lt_min hε₀ (hγ J), (min_le_left _ _).trans hε₀r, ?_⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact (min_le_left _ _).trans (hε₀γ j hj)
        · exact min_le_right _ _
    obtain ⟨ε₀, hε₀, hε₀r, hε₀γ⟩ := hεJ
    refine ⟨ε₀, hε₀, fun y hyS hy => ?_⟩
    have hyr : y ∈ ball x₀ r := by
      rw [mem_ball, dist_eq_norm]
      linarith
    simp only [hφdef, hyr, if_true]
    calc ⨅ N, Ssum N y ≤ Ssum J y := iInf_le _ J
      _ ≤ ∑ j ∈ Finset.range J, ((-1 : ℝ) : EReal) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [show ((-1 : ℝ) : EReal) = -1 by simp]
          exact hφj_pole j y hyS (hy.trans_le (hε₀γ j (Finset.mem_range.mp hj)))
      _ = ((-(J : ℝ) : ℝ) : EReal) := by
          rw [← coe_finset_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg,
            mul_one]

/-! ### `prop:BTthin` -/

/-- **`prop:BTthin`** (Bedford–Taylor). Let `Ω ⊆ ℂⁿ` be open, `E ⊆ Ω` and `x ∈ closure E`, and
assume that `E` is thin at `x`. Then there is `φ ∈ PSH(ℂⁿ)` which is locally bounded outside `x`,
satisfies `φ(x) > -∞`, and tends to `-∞` along `E \ {x}` at `x`. -/
theorem bedfordTaylor_thin (Ω : Opens (ComplexModel n)) (E : Set Ω) (x : Ω)
    (hxE : x ∈ closure E) (hthin : sourceThinAt Ω E x) :
    ∃ φ : ComplexModel n → EReal, PSHOn φ univ ∧
      (∀ z : ComplexModel n, z ≠ x.val →
        ∃ V ∈ 𝓝 z, ∃ C : ℝ, ∀ y ∈ V, ((-C : ℝ) : EReal) ≤ φ y ∧ φ y ≤ C) ∧
      φ x.val ≠ ⊥ ∧
      Tendsto (fun y : Ω => φ y.val) (𝓝[E \ {x}] x) (𝓝 ⊥) := by
  rcases hthin with hx | ⟨-, U, u, hU, hUΩ, hxU, hu, hgap⟩
  · exact absurd hxE hx
  obtain ⟨U', ψ₀, hU', -, hxU', hψ₀, hzero, hgap'⟩ :=
    exists_thin_witness_zero_on_set Ω E x hU hUΩ hxU hu hgap
  by_cases hne : (𝓝[E \ {x}] x).NeBot
  swap
  · -- `x` is not an accumulation point of `E \ {x}`: the constant `0` works.
    rw [not_neBot] at hne
    refine ⟨fun _ => ((0 : ℝ) : EReal), pshOn_real_const 0 univ_nonempty, ?_,
      EReal.coe_ne_bot 0, ?_⟩
    · intro z _
      exact ⟨univ, univ_mem, 0, fun _ _ => by simp⟩
    · rw [hne]
      exact tendsto_bot
  -- The normalized witness `ψ = ψ₀ / ψ₀(x) - 1`.
  have hU'mem : Subtype.val ⁻¹' U' ∈ 𝓝 x :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hU'.mem_nhds hxU')
  have hset : (Subtype.val ⁻¹' U' ∩ E) \ {x} = (E \ {x}) ∩ Subtype.val ⁻¹' U' := by
    ext y
    constructor
    · rintro ⟨⟨hyU, hyE⟩, hyx⟩
      exact ⟨⟨hyE, hyx⟩, hyU⟩
    · rintro ⟨⟨hyE, hyx⟩, hyU⟩
      exact ⟨⟨hyU, hyE⟩, hyx⟩
  have hF : 𝓝[(Subtype.val ⁻¹' U' ∩ E) \ {x}] x = 𝓝[E \ {x}] x := by
    rw [hset, ← nhdsWithin_restrict' _ hU'mem]
  have hlimsup : limsup (fun y : Ω => ψ₀ y.val) (𝓝[(Subtype.val ⁻¹' U' ∩ E) \ {x}] x) = 0 := by
    have : (𝓝[(Subtype.val ⁻¹' U' ∩ E) \ {x}] x).NeBot := by rw [hF]; exact hne
    rw [limsup_congr (eventually_nhdsWithin_of_forall fun y hy => hzero y hy)]
    exact limsup_const 0
  rw [hlimsup] at hgap'
  have hxV : x.val ∈ U' := hxU'
  have hψtop : ψ₀ x.val ≠ ⊤ := hψ₀.ne_top hxV
  set a : ℝ := (ψ₀ x.val).toReal with hadef
  have ha_eq : ψ₀ x.val = (a : EReal) := (EReal.coe_toReal hψtop (ne_bot_of_gt hgap')).symm
  have ha : 0 < a := by
    have := hgap'
    rw [ha_eq] at this
    exact EReal.coe_pos.mp this
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hU' x.val hxV
  set r : ℝ := min r₀ 1 with hrdef
  have hr : 0 < r := lt_min hr₀ one_pos
  have hballU' : ball x.val r ⊆ U' := (ball_subset_ball (min_le_left _ _)).trans hball
  have hψ₀b : PSHOn ψ₀ (ball x.val r) :=
    (VariableComplexAtlas.identityAtlas_isPSHOn_iff isOpen_ball (isConnected_ball hr)).mp
      (hψ₀.mono_open hU' isOpen_ball hballU')
  set ψ : ComplexModel n → EReal := fun z => ((1 / a : ℝ) : EReal) * ψ₀ z + ((-1 : ℝ) : EReal)
    with hψdef
  have hψ0 : ψ x.val = 0 := by
    simp only [hψdef, ha_eq, ← EReal.coe_mul, ← EReal.coe_add]
    rw [show 1 / a * a + -1 = (0 : ℝ) by field_simp; ring]
    rfl
  have hψ : PSHOn ψ (ball x.val r) := by
    refine ⟨(hψ₀b.disc.const_mul (by positivity : (0 : ℝ) < 1 / a)).add
      (discPshOn_const _ (EReal.coe_ne_top _) _), ⟨x.val, mem_ball_self hr, ?_⟩⟩
    show ψ x.val ≠ ⊥
    rw [hψ0]
    exact EReal.zero_ne_bot
  set S : Set (ComplexModel n) := Subtype.val '' ((Subtype.val ⁻¹' U' ∩ E) \ {x}) with hSdef
  have hS : ∀ y ∈ S, y ∈ ball x.val r → ψ y = -1 := by
    rintro _ ⟨y, hy, rfl⟩ _
    simp only [hψdef, hzero y hy, mul_zero, zero_add]
    simp
  have hpt : ∃ z : ComplexModel n, z ≠ x.val := by
    obtain ⟨y, hyE, hyx⟩ := hne.nonempty_of_mem self_mem_nhdsWithin
    exact ⟨y.val, fun h => hyx (Subtype.ext h)⟩
  obtain ⟨φ, hφ, hbdd, hφx, hpole⟩ :=
    exists_pole_function_of_normalized hr (min_le_right _ _) hψ hψ0 hS hpt
  refine ⟨φ, hφ, hbdd, hφx, ?_⟩
  rw [EReal.tendsto_nhds_bot_iff_real]
  intro c
  obtain ⟨J, hJ⟩ := exists_nat_gt (-c)
  obtain ⟨ε₀, hε₀, hε₀P⟩ := hpole J
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x hε₀),
    nhdsWithin_le_nhds hU'mem] with y hyE hyb hyU
  have hyS : y.val ∈ S := ⟨y, ⟨⟨hyU, hyE.1⟩, hyE.2⟩, rfl⟩
  have hyd : ‖y.val - x.val‖ < ε₀ := by
    rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hyb
    exact hyb
  refine (hε₀P y.val hyS hyd).trans_lt (EReal.coe_lt_coe_iff.mpr ?_)
  linarith

end SGPT.PSH.BookDeepThin
