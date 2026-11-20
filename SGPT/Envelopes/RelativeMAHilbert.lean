import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Near-minimal convex combinations of tails in a real inner product space

This is the Hilbert-space step of the proof that integrals against a
non-pluripolar measure are lower semicontinuous along `L¹`-convergent
sequences of bounded quasi-plurisubharmonic functions (Xia, *Foundations of
pluripotential theory*, `lem:bounded-psh-nonpluripolar-measure-continuity`).

For a bounded sequence `x` in a real inner product space let `C l` be the convex
hull of the tail `{x k : k ≥ l}` and `d l` the infimum of the norms on `C l`.
Elements `y l ∈ C l` with `‖y l‖ < d l + 1/(l+1)` form a Cauchy sequence, by the
parallelogram law (the midpoint of `y l` and `y l'` lies in `C l`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The convex hull of the tail of a sequence starting at index `l`. -/
def tailHull (x : ℕ → E) (l : ℕ) : Set E :=
  convexHull ℝ (range fun k => x (k + l))

theorem tailHull_antitone (x : ℕ → E) : Antitone (tailHull x) := by
  intro l l' hll'
  apply convexHull_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨k + (l' - l), by simp only; congr 1; omega⟩

theorem self_mem_tailHull (x : ℕ → E) (l : ℕ) : x l ∈ tailHull x l :=
  subset_convexHull ℝ _ ⟨0, by simp⟩

/-- The infimum of the norms on the tail hull. -/
def tailHullNorm (x : ℕ → E) (l : ℕ) : ℝ :=
  sInf (norm '' tailHull x l)

theorem tailHullNorm_bddBelow (x : ℕ → E) (l : ℕ) : BddBelow (norm '' tailHull x l) :=
  ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg y⟩

theorem tailHullNorm_nonempty (x : ℕ → E) (l : ℕ) : (norm '' tailHull x l).Nonempty :=
  ⟨_, x l, self_mem_tailHull x l, rfl⟩

theorem tailHullNorm_le {x : ℕ → E} {l : ℕ} {y : E} (hy : y ∈ tailHull x l) :
    tailHullNorm x l ≤ ‖y‖ :=
  csInf_le (tailHullNorm_bddBelow x l) ⟨y, hy, rfl⟩

theorem tailHullNorm_monotone (x : ℕ → E) : Monotone (tailHullNorm x) := by
  intro l l' hll'
  apply csInf_le_csInf (tailHullNorm_bddBelow x l) (tailHullNorm_nonempty x l')
  exact image_mono (tailHull_antitone x hll')

theorem tailHullNorm_le_bound {x : ℕ → E} {R : ℝ} (hx : ∀ k, ‖x k‖ ≤ R) (l : ℕ) :
    tailHullNorm x l ≤ R :=
  (tailHullNorm_le (self_mem_tailHull x l)).trans (hx l)

/-- **Near-minimal tail combinations form a Cauchy sequence.** For a bounded
sequence in a real inner product space there are elements of the convex hulls
of the tails that form a Cauchy sequence. -/
theorem exists_cauchySeq_mem_tailHull (x : ℕ → E) {R : ℝ} (hx : ∀ k, ‖x k‖ ≤ R) :
    ∃ y : ℕ → E, (∀ l, y l ∈ tailHull x l) ∧ CauchySeq y := by
  set d := tailHullNorm x with hd
  set δ : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1) with hδ
  have hδpos : ∀ l, 0 < δ l := fun l => by simp only [hδ]; positivity
  have hchoose : ∀ l, ∃ y ∈ tailHull x l, ‖y‖ < d l + δ l := by
    intro l
    obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (tailHullNorm_nonempty x l)
      (show tailHullNorm x l < d l + δ l by linarith [hδpos l])
    exact ⟨y, hy, hlt⟩
  choose y hyC hyn using hchoose
  refine ⟨y, hyC, ?_⟩
  have hdmono : Monotone d := tailHullNorm_monotone x
  have hdbdd : BddAbove (range d) := ⟨R, by rintro _ ⟨l, rfl⟩; exact tailHullNorm_le_bound hx l⟩
  set D := ⨆ l, d l with hD
  have hdD : ∀ l, d l ≤ D := fun l => le_ciSup hdbdd l
  have hdlim : Tendsto d atTop (𝓝 D) := tendsto_atTop_ciSup hdmono hdbdd
  have hd0 : ∀ l, 0 ≤ d l := fun l =>
    le_csInf (tailHullNorm_nonempty x l) (by rintro _ ⟨z, -, rfl⟩; exact norm_nonneg z)
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the key bound on the squared distances
  let f : ℕ → ℝ := fun l => 2 * (d l + δ l) ^ 2 + 2 * (D + δ l) ^ 2 - 4 * d l ^ 2
  have hflim : Tendsto f atTop (𝓝 0) := by
    have h := ((((hdlim.add hδlim).pow 2).const_mul 2).add
      (((tendsto_const_nhds (x := D)).add hδlim).pow 2 |>.const_mul 2)).sub
      ((hdlim.pow 2).const_mul 4)
    convert h using 2
    ring
  have hkey : ∀ l l', l ≤ l' → ‖y l' - y l‖ ^ 2 ≤ f l := by
    intro l l' hll'
    have hy' : y l' ∈ tailHull x l := tailHull_antitone x hll' (hyC l')
    have hmid : (1 / 2 : ℝ) • y l + (1 / 2 : ℝ) • y l' ∈ tailHull x l :=
      (convex_convexHull ℝ _) (hyC l) hy' (by norm_num) (by norm_num) (by norm_num)
    have hmidn : d l ≤ ‖(1 / 2 : ℝ) • y l + (1 / 2 : ℝ) • y l'‖ := tailHullNorm_le hmid
    have hmid2 : ‖(1 / 2 : ℝ) • y l + (1 / 2 : ℝ) • y l'‖ = (1 / 2) * ‖y l + y l'‖ := by
      rw [← smul_add, norm_smul]
      norm_num
    have hpar := parallelogram_law_with_norm ℝ (y l) (y l')
    have hyl : ‖y l‖ ≤ d l + δ l := (hyn l).le
    have hyl' : ‖y l'‖ ≤ D + δ l := by
      have h1 := hyn l'
      have h2 : δ l' ≤ δ l := by
        simp only [hδ]
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right hll' 1
      linarith [hdD l']
    have hn1 : 0 ≤ ‖y l‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖y l'‖ := norm_nonneg _
    have hsum : 2 * d l ≤ ‖y l + y l'‖ := by
      rw [hmid2] at hmidn
      linarith
    have hsq : (2 * d l) ^ 2 ≤ ‖y l + y l'‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith [hd0 l]) hsum 2
    have hsq1 : ‖y l‖ ^ 2 ≤ (d l + δ l) ^ 2 := pow_le_pow_left₀ hn1 hyl 2
    have hsq2 : ‖y l'‖ ^ 2 ≤ (D + δ l) ^ 2 := pow_le_pow_left₀ hn2 hyl' 2
    have hdiff : ‖y l' - y l‖ = ‖y l - y l'‖ := norm_sub_rev _ _
    simp only [f]
    rw [hdiff]
    nlinarith [hpar]
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hε2 : 0 < ε ^ 2 := by positivity
  obtain ⟨N, hN⟩ := (hflim.eventually (gt_mem_nhds hε2)).exists_forall_of_atTop
  refine ⟨N, fun l' hl' => ?_⟩
  rw [dist_eq_norm]
  have h := (hkey N l' hl').trans_lt (hN N le_rfl)
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h

end SGPT.Envelopes.RelativeMA
