import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.RooftopUscObstacleApproximation
import Mathlib.Topology.Semicontinuity.Basic

/-! Actual source-chart smooth insertion and monotone approximation.
Complete mathematical proofs precede this file in global-weight-approximation.tex.
No desired sequence or smoothing certificate is an incoming premise. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.GlobalWeightSmoothApproximation

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending ChartPartition
open scoped Topology ContDiff

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual source smoothness gives actual original-space continuity. -/
theorem continuous_of_chartSmooth {g : M → ℝ} (hg : ChartSmooth (n := n) g) :
    Continuous g := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have he := e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hx)
  have hge := (hg e).continuousOn.continuousAt
    (e.val.open_target.mem_nhds (e.val.map_source hx))
  have hc := hge.comp he
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  exact congrArg g (e.val.left_inv hy).symm

variable [CompactSpace M]

/-- A genuine smooth function is produced strictly between a continuous
lower function and an LSC real upper function on the original compact space. -/
theorem exists_chartSmooth_strict_between {a b : M → ℝ}
    (ha : Continuous a) (hb : LowerSemicontinuous b) (hab : ∀ x, a x < b x) :
    ∃ g : M → ℝ, ChartSmooth (n := n) g ∧ ∀ x, a x < g x ∧ g x < b x := by
  classical
  let c : M → ℝ := fun x => (a x + b x) / 2
  let S : M → Opens M := fun x =>
    ⟨{y | a y < c x} ∩ {y | c x < b y},
      (isOpen_Iio.preimage ha).inter (hb.isOpen_preimage (c x))⟩
  have hcover (x : M) : ∃ i, x ∈ S i := by
    refine ⟨x, ?_⟩
    change a x < (a x + b x) / 2 ∧ (a x + b x) / 2 < b x
    constructor <;> linarith [hab x]
  obtain ⟨m, χ, idx, hχ, hχpos, hχsupp, _hχcompact, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  let g : M → ℝ := fun x => ∑ i : Fin m, χ i x * c (idx i)
  have hg : ChartSmooth (n := n) g := by
    intro e
    apply ContDiffOn.sum
    intro i _hi
    exact (hχ i e).mul contDiffOn_const
  refine ⟨g, hg, ?_⟩
  intro x
  have hactive (i : Fin m) (hi : χ i x ≠ 0) : a x < c (idx i) ∧ c (idx i) < b x :=
    hχsupp i (subset_tsupport _ hi)
  have hpositive : ∃ i : Fin m, 0 < χ i x := by
    by_contra hnone
    push Not at hnone
    have hz (i : Fin m) : χ i x = 0 := le_antisymm (hnone i) (hχpos i x)
    have hh := hsum x
    simp only [hz, Finset.sum_const_zero] at hh
    norm_num at hh
  obtain ⟨i₀, hi₀⟩ := hpositive
  have hlo (i : Fin m) : χ i x * a x ≤ χ i x * c (idx i) := by
    by_cases hi : χ i x = 0
    · simp only [hi, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hactive i hi).1.le (hχpos i x)
  have hup (i : Fin m) : χ i x * c (idx i) ≤ χ i x * b x := by
    by_cases hi : χ i x = 0
    · simp only [hi, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hactive i hi).2.le (hχpos i x)
  have hl : (∑ i : Fin m, χ i x * a x) < ∑ i : Fin m, χ i x * c (idx i) :=
    Finset.sum_lt_sum (fun i _hi => hlo i)
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hactive i₀ hi₀.ne').1 hi₀⟩
  have hu : (∑ i : Fin m, χ i x * c (idx i)) < ∑ i : Fin m, χ i x * b x :=
    Finset.sum_lt_sum (fun i _hi => hup i)
      ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hactive i₀ hi₀.ne').2 hi₀⟩
  constructor
  · simpa only [← Finset.sum_mul, hsum x, one_mul] using hl
  · simpa only [← Finset.sum_mul, hsum x, one_mul] using hu




include n in
/-- The actual native continuous-majorant theorem, by negation, produces
continuous monotone real minorants, with genuine pointwise real convergence. -/
theorem exists_continuous_monotone_minorants [Nonempty M] {b : M → ℝ}
    (hb : LowerSemicontinuous b) :
    ∃ c : ℕ → M → ℝ, (∀ j, Continuous (c j)) ∧ Monotone c ∧
      (∀ j x, c j x ≤ b x) ∧ ∀ x, Tendsto (fun j => c j x) atTop (𝓝 (b x)) := by
  have hneg : UpperSemicontinuous (fun x => -b x) :=
    continuous_neg.comp_lowerSemicontinuous_antitone hb (fun _ _ h => neg_le_neg h)
  have hnegE : UpperSemicontinuous (fun x => ((-b x : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp_upperSemicontinuous hneg
      (fun _ _ h => EReal.coe_le_coe_iff.mpr h)
  obtain ⟨_C, r, hr, hmaj, _hbound, hanti, hinf⟩ :=
    RooftopUscObstacleApproximation.exists_continuous_antitone_majorants n hnegE
      (fun x => EReal.coe_ne_top (-b x))
  let c : ℕ → M → ℝ := fun j x => -r j x
  have hc (j) : Continuous (c j) := (hr j).neg
  have hm : Monotone c := fun j k hjk x => neg_le_neg (hanti x hjk)
  have hle (j) (x) : c j x ≤ b x := by
    have h := EReal.coe_le_coe_iff.mp (hmaj j x)
    change -r j x ≤ b x
    linarith
  refine ⟨c, hc, hm, hle, ?_⟩
  intro x
  apply tendsto_order.2
  constructor
  · intro z hz
    have ht : (⨅ j, (r j x : EReal)) < ((-z : ℝ) : EReal) := by
      rw [hinf x]
      exact EReal.coe_lt_coe_iff.mpr (neg_lt_neg hz)
    obtain ⟨j, hj⟩ := iInf_lt_iff.mp ht
    have hjr := EReal.coe_lt_coe_iff.mp hj
    have hzj : z < c j x := by dsimp only [c]; linarith
    exact eventually_atTop.2 ⟨j, fun k hjk => hzj.trans_le (hm hjk x)⟩
  · intro z hz
    exact Eventually.of_forall fun j => (hle j x).trans_lt hz

/-- A bounded real LSC obstacle internally yields a uniformly bounded
monotone sequence of ACTUAL source-chart smooth functions, selected without
any potential reference or theta-perturbation parameter. -/
theorem exists_chartSmooth_monotone_approximation [Nonempty M] {b : M → ℝ}
    (hb : LowerSemicontinuous b) (L U : ℝ)
    (hL : ∀ x, L ≤ b x) (hU : ∀ x, b x ≤ U) :
    ∃ g : ℕ → M → ℝ, (∀ j, ChartSmooth (n := n) (g j)) ∧ Monotone g ∧
      (∀ j x, L - 1 < g j x ∧ g j x < b x) ∧
      (∀ j x, |g j x| ≤ max |L - 1| |U|) ∧
      ∀ x, Tendsto (fun j => g j x) atTop (𝓝 (b x)) := by
  classical
  obtain ⟨c, hc, hcm, hcle, hclim⟩ := exists_continuous_monotone_minorants (n := n) hb
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hεpos (j) : 0 < ε j := by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let P : ℕ → (M → ℝ) → Prop := fun j g => ChartSmooth (n := n) g ∧
    ∀ x, L - 1 < g x ∧ g x < b x ∧ c j x - ε j < g x
  have hbase : ∃ g : M → ℝ, P 0 g := by
    let a : M → ℝ := fun x => max (L - 1) (c 0 x - ε 0)
    have ha : Continuous a := continuous_const.max ((hc 0).sub continuous_const)
    have hab (x) : a x < b x := by
      exact max_lt_iff.mpr ⟨by linarith [hL x], by linarith [hcle 0 x, hεpos 0]⟩
    obtain ⟨g, hg, hag⟩ := exists_chartSmooth_strict_between (n := n) ha hb hab
    refine ⟨g, hg, fun x => ?_⟩
    exact ⟨(le_max_left _ _).trans_lt (hag x).1,
      (hag x).2, (le_max_right _ _).trans_lt (hag x).1⟩
  have hstep (j : ℕ) (g : M → ℝ) (hg : P j g) :
      ∃ k : M → ℝ, P (j + 1) k ∧ ∀ x, g x < k x := by
    let a : M → ℝ := fun x => max (g x) (c (j + 1) x - ε (j + 1))
    have ha : Continuous a :=
      (continuous_of_chartSmooth hg.1).max ((hc (j + 1)).sub continuous_const)
    have hab (x) : a x < b x :=
      max_lt_iff.mpr ⟨(hg.2 x).2.1, by linarith [hcle (j + 1) x, hεpos (j + 1)]⟩
    obtain ⟨k, hk, hak⟩ := exists_chartSmooth_strict_between (n := n) ha hb hab
    have hgk (x) : g x < k x := (le_max_left _ _).trans_lt (hak x).1
    refine ⟨k, ⟨hk, fun x => ?_⟩, hgk⟩
    exact ⟨(hg.2 x).1.trans (hgk x), (hak x).2,
      (le_max_right _ _).trans_lt (hak x).1⟩
  obtain ⟨g₀, hg₀⟩ := hbase
  let step : (j : ℕ) → {g : M → ℝ // P j g} → {g : M → ℝ // P (j + 1) g} :=
    fun j g => ⟨(hstep j g.val g.property).choose, (hstep j g.val g.property).choose_spec.1⟩
  let G : (j : ℕ) → {g : M → ℝ // P j g} :=
    fun j => Nat.rec ⟨g₀, hg₀⟩ (fun k g => step k g) j
  let g : ℕ → M → ℝ := fun j => (G j).val
  have hg (j) : P j (g j) := (G j).property
  have hsucc (j) (x) : g j x < g (j + 1) x := by
    change (G j).val x < (step j (G j)).val x
    exact (hstep j (G j).val (G j).property).choose_spec.2 x
  have hm : Monotone g := monotone_nat_of_le_succ fun j x => (hsucc j x).le
  refine ⟨g, fun j => (hg j).1, hm, fun j x => ⟨(hg j).2 x |>.1, (hg j).2 x |>.2.1⟩, ?_, ?_⟩
  · intro j x
    apply abs_le.mpr
    constructor
    · have hneg : -|L - 1| ≤ L - 1 := neg_abs_le _
      exact (neg_le_neg (le_max_left |L - 1| |U|)).trans (hneg.trans ((hg j).2 x).1.le)
    · exact ((hg j).2 x).2.1.le.trans ((hU x).trans ((le_abs_self U).trans (le_max_right _ _)))
  · intro x
    have hlow : Tendsto (fun j => c j x - ε j) atTop (𝓝 (b x)) := by
      simpa only [sub_zero] using (hclim x).sub hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun j => ((hg j).2 x).2.2.le) (fun j => ((hg j).2 x).2.1.le)




/-- The upper-semicontinuous companion is internally produced by negating
actual smooth minorants; its whole sequence has one explicit real bound. -/
theorem exists_chartSmooth_antitone_approximation [Nonempty M] {b : M → ℝ}
    (hb : UpperSemicontinuous b) (L U : ℝ)
    (hL : ∀ x, L ≤ b x) (hU : ∀ x, b x ≤ U) :
    ∃ g : ℕ → M → ℝ, (∀ j, ChartSmooth (n := n) (g j)) ∧ Antitone g ∧
      (∀ j x, b x < g j x ∧ g j x < U + 1) ∧
      (∀ j x, |g j x| ≤ max |L| |U + 1|) ∧
      ∀ x, Tendsto (fun j => g j x) atTop (𝓝 (b x)) := by
  have hneg : LowerSemicontinuous (fun x => -b x) :=
    continuous_neg.comp_upperSemicontinuous_antitone hb (fun _ _ h => neg_le_neg h)
  obtain ⟨q, hq, hqm, hqbounds, _hqabs, hqlim⟩ :=
    exists_chartSmooth_monotone_approximation (n := n) hneg (-U) (-L)
      (fun x => neg_le_neg (hU x)) (fun x => neg_le_neg (hL x))
  let g : ℕ → M → ℝ := fun j x => -q j x
  have hg (j) : ChartSmooth (n := n) (g j) := fun e => (hq j e).neg
  have hgm : Antitone g := fun j k hjk x => neg_le_neg (hqm hjk x)
  have hbnd (j) (x) : b x < g j x ∧ g j x < U + 1 := by
    have h := hqbounds j x
    change b x < -q j x ∧ -q j x < U + 1
    constructor <;> linarith
  refine ⟨g, hg, hgm, hbnd, ?_, ?_⟩
  · intro j x
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left |L| |U + 1|)).trans
        ((neg_abs_le L).trans ((hL x).trans (hbnd j x).1.le))
    · exact (hbnd j x).2.le.trans ((le_abs_self (U + 1)).trans (le_max_right _ _))
  · intro x
    simpa only [neg_neg] using (hqlim x).neg


end SGPT.Bergman.GlobalWeightSmoothApproximation
