import SGPT.Envelopes.RelativeMAHilbert
import SGPT.Foundations.Analysis.Pending.ThetaPshL1Limsup
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import SGPT.Foundations.Analysis.Pending.EndpointMixedMassConvexCombination
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Lower semicontinuity of integrals against non-pluripolar measures

Let `ν` be a finite measure on a connected compact complex manifold that charges
no pluripolar set, and let `F : ℝ → ℝ` be continuous, nondecreasing and convex.
If uniformly bounded `θ`-psh functions `q_j` converge in `L¹` to a bounded
`θ`-psh function `p` and `∫ F(q_j) dν → L`, then `∫ F(p) dν ≤ L`.

This is the analytic core of the variational solution of Monge–Ampère equations
with non-pluripolar right-hand sides (Xia, *Foundations of pluripotential
theory*, `lem:bounded-psh-nonpluripolar-measure-continuity` and
`cor:exponential-psh-measure-continuity`). The proof follows the book:
convex combinations `g_l` of the tails `{q_k : k ≥ l}` that are almost of minimal
`L²(ν)` norm form a Cauchy sequence in `L²(ν)` (`RelativeMAHilbert`), so a
subsequence converges `ν`-almost everywhere to some `Z`. The `g_l` are again
`θ`-psh and converge to `p` in `L¹`, so `p ≤ limsup g_l = Z` quasi-everywhere,
hence `ν`-almost everywhere (TN `ThetaPshL1Limsup`). Convexity of `F` bounds
`∫ F(g_l) dν` by the tail suprema of `∫ F(q_k) dν`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

theorem canonicalERealAbsDiff_coe (a b : ℝ) :
    canonicalERealAbsDiff (a : EReal) (b : EReal) = ENNReal.ofReal |a - b| := by
  simp only [canonicalERealAbsDiff, poleModifiedERealAbsDiff, EReal.coe_ne_bot, false_and,
    if_false]
  rw [← EReal.coe_sub, EReal.abs_def]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Real convex combinations of real-valued `θ`-psh functions are `θ`-psh. -/
theorem isThetaPshPotential_coe_convex {θ : SmoothRealForm n M 2} {g₁ g₂ : M → ℝ}
    (h₁ : IsThetaPshPotential θ (fun x => (g₁ x : EReal)))
    (h₂ : IsThetaPshPotential θ (fun x => (g₂ x : EReal))) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    IsThetaPshPotential θ (fun x => ((a * g₁ x + b * g₂ x : ℝ) : EReal)) := by
  have h := EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed h₁ h₂ ha
    (by linarith)
  convert h using 1
  funext x
  simp only [ThetaPshConvexCombination.convexComb, ← EReal.coe_mul, ← EReal.coe_add]
  congr 2
  rw [show b = 1 - a by linarith]

variable [MeasurableSpace M] [BorelSpace M]

theorem measurable_of_isThetaPshPotential_coe {θ : SmoothRealForm n M 2} {g : M → ℝ}
    (hg : IsThetaPshPotential θ (fun x => (g x : EReal))) : Measurable g := by
  have h := measurable_ereal_toReal.comp hg.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have e : (EReal.toReal ∘ fun x => (g x : EReal)) = g := by
    funext x
    simp only [Function.comp_apply, EReal.toReal_coe]
  rwa [e] at h

/-- The convex property defining the admissible convex combinations at stage `l`. -/
def AdmissibleComb (ν : Measure M) (vol : Measure M) (θ : SmoothRealForm n M 2) (F : ℝ → ℝ)
    (p : M → ℝ) (B : ℝ) (T : ℝ≥0∞) (s : ℝ) (g : M → ℝ) : Prop :=
  IsThetaPshPotential θ (fun x => (g x : EReal)) ∧ (∀ x, |g x| ≤ B) ∧
    globalL1EDistance vol (fun x => (g x : EReal)) (fun x => (p x : EReal)) ≤ T ∧
    ∫ x, F (g x) ∂ν ≤ s

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [BorelSpace M] in
theorem integrable_comp_of_bound {ν : Measure M} [IsFiniteMeasure ν] {F : ℝ → ℝ}
    (hFc : Continuous F) (hFm : Monotone F) {g : M → ℝ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ᵐ x ∂ν, |g x| ≤ B) : Integrable (fun x => F (g x)) ν := by
  refine Integrable.of_bound (hFc.measurable.comp hg).aestronglyMeasurable
    (max |F B| |F (-B)|) ?_
  filter_upwards [hgB] with x hx
  have h1 := hFm (abs_le.mp hx).2
  have h2 := hFm (abs_le.mp hx).1
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (F (-B))
    have := le_max_right |F B| |F (-B)|
    linarith
  · have := le_abs_self (F B)
    have := le_max_left |F B| |F (-B)|
    linarith

theorem admissibleComb_convex {ν : Measure M} [IsFiniteMeasure ν] {vol : Measure M}
    {θ : SmoothRealForm n M 2} {F : ℝ → ℝ} (hFc : Continuous F) (hFm : Monotone F)
    (hFconv : ConvexOn ℝ univ F) {p : M → ℝ} (hp : Measurable p) {B : ℝ} {T : ℝ≥0∞} {s : ℝ} :
    Convex ℝ {g | AdmissibleComb ν vol θ F p B T s g} := by
  intro g₁ hg₁ g₂ hg₂ a b ha hb hab
  obtain ⟨h₁, hB₁, hT₁, hs₁⟩ := hg₁
  obtain ⟨h₂, hB₂, hT₂, hs₂⟩ := hg₂
  have hm₁ := measurable_of_isThetaPshPotential_coe h₁
  have hm₂ := measurable_of_isThetaPshPotential_coe h₂
  have happ : ∀ x, (a • g₁ + b • g₂) x = a * g₁ x + b * g₂ x := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [happ] using isThetaPshPotential_coe_convex h₁ h₂ ha hb hab
  · intro x
    rw [happ]
    calc |a * g₁ x + b * g₂ x| ≤ |a * g₁ x| + |b * g₂ x| := abs_add_le _ _
      _ = a * |g₁ x| + b * |g₂ x| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * B + b * B := by gcongr; exacts [hB₁ x, hB₂ x]
      _ = B := by rw [← add_mul, hab, one_mul]
  · unfold globalL1EDistance at hT₁ hT₂ ⊢
    simp only [canonicalERealAbsDiff_coe, happ] at hT₁ hT₂ ⊢
    have hpt : ∀ x, ENNReal.ofReal |a * g₁ x + b * g₂ x - p x| ≤
        ENNReal.ofReal a * ENNReal.ofReal |g₁ x - p x| +
          ENNReal.ofReal b * ENNReal.ofReal |g₂ x - p x| := by
      intro x
      rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have e : a * g₁ x + b * g₂ x - p x = a * (g₁ x - p x) + b * (g₂ x - p x) := by
        linear_combination (p x) * hab
      rw [e]
      calc |a * (g₁ x - p x) + b * (g₂ x - p x)| ≤ |a * (g₁ x - p x)| + |b * (g₂ x - p x)| :=
            abs_add_le _ _
        _ = a * |g₁ x - p x| + b * |g₂ x - p x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hf₁ : Measurable fun x => ENNReal.ofReal |g₁ x - p x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hm₁.sub hp))
    have hf₂ : Measurable fun x => ENNReal.ofReal |g₂ x - p x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hm₂.sub hp))
    have hmeas₁ : Measurable fun x => ENNReal.ofReal a * ENNReal.ofReal |g₁ x - p x| :=
      measurable_const.mul hf₁
    calc ∫⁻ x, ENNReal.ofReal |a * g₁ x + b * g₂ x - p x| ∂vol
        ≤ ∫⁻ x, (ENNReal.ofReal a * ENNReal.ofReal |g₁ x - p x| +
            ENNReal.ofReal b * ENNReal.ofReal |g₂ x - p x|) ∂vol := lintegral_mono hpt
      _ = ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal |g₁ x - p x| ∂vol +
            ENNReal.ofReal b * ∫⁻ x, ENNReal.ofReal |g₂ x - p x| ∂vol := by
          rw [lintegral_add_left hmeas₁, lintegral_const_mul _ hf₁, lintegral_const_mul _ hf₂]
      _ ≤ ENNReal.ofReal a * T + ENNReal.ofReal b * T := by gcongr
      _ = T := by
          rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
  · have hI₁ := integrable_comp_of_bound (ν := ν) hFc hFm hm₁ (ae_of_all _ hB₁)
    have hI₂ := integrable_comp_of_bound (ν := ν) hFc hFm hm₂ (ae_of_all _ hB₂)
    have hmab : Measurable (a • g₁ + b • g₂) := (hm₁.const_smul a).add (hm₂.const_smul b)
    have hBab : ∀ x, |(a • g₁ + b • g₂) x| ≤ B := by
      intro x
      rw [happ]
      calc |a * g₁ x + b * g₂ x| ≤ |a * g₁ x| + |b * g₂ x| := abs_add_le _ _
        _ = a * |g₁ x| + b * |g₂ x| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * B + b * B := by gcongr; exacts [hB₁ x, hB₂ x]
        _ = B := by rw [← add_mul, hab, one_mul]
    have hIab := integrable_comp_of_bound (ν := ν) hFc hFm hmab (ae_of_all _ hBab)
    calc ∫ x, F ((a • g₁ + b • g₂) x) ∂ν
        ≤ ∫ x, (a * F (g₁ x) + b * F (g₂ x)) ∂ν := by
          apply integral_mono hIab ((hI₁.const_mul a).add (hI₂.const_mul b))
          intro x
          have := hFconv.2 (mem_univ (g₁ x)) (mem_univ (g₂ x)) ha hb hab
          simp only [smul_eq_mul] at this
          simpa only [happ, Pi.add_apply] using this
      _ = a * ∫ x, F (g₁ x) ∂ν + b * ∫ x, F (g₂ x) ∂ν := by
          rw [integral_add (hI₁.const_mul a) (hI₂.const_mul b), integral_const_mul,
            integral_const_mul]
      _ ≤ a * s + b * s := by gcongr
      _ = s := by rw [← add_mul, hab, one_mul]

variable [CompactSpace M] [ConnectedSpace M]

/-- **Lower semicontinuity against a non-pluripolar measure** (convex weights).
Uniformly bounded `θ`-psh functions `q_j → p` in `L¹`, `F` continuous, nondecreasing
and convex, `∫ F(q_j) dν → L`: then `∫ F(p) dν ≤ L`. -/
theorem integral_comp_le_of_tendsto (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {ν : Measure M} [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν)
    {F : ℝ → ℝ} (hFc : Continuous F) (hFm : Monotone F) (hFconv : ConvexOn ℝ univ F)
    {q : ℕ → M → ℝ} {p : M → ℝ} {B : ℝ}
    (hq : ∀ j, IsThetaPshPotential θ.val (fun x => (q j x : EReal)))
    (hp : IsThetaPshPotential θ.val (fun x => (p x : EReal)))
    (hqB : ∀ j x, |q j x| ≤ B) (hpB : ∀ x, |p x| ≤ B)
    (hlim : ManifoldL1LocallyTendsto (n := n) (fun j x => (q j x : EReal)) atTop
      (fun x => (p x : EReal)))
    {L : ℝ} (hL : Tendsto (fun j => ∫ x, F (q j x) ∂ν) atTop (𝓝 L)) :
    ∫ x, F (p x) ∂ν ≤ L := by
  classical
  let vol : Measure M := IntegrationCurrent.kahlerVolume omega
  have hvol : IsSmoothPositiveVolume (n := n) vol :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  have hqm : ∀ j, Measurable (q j) := fun j => measurable_of_isThetaPshPotential_coe (hq j)
  have hpm : Measurable p := measurable_of_isThetaPshPotential_coe hp
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hqB 0 (Classical.arbitrary M))
  -- global L¹ distances
  let dist : ℕ → ℝ≥0∞ := fun j =>
    globalL1EDistance vol (fun x => (q j x : EReal)) (fun x => (p x : EReal))
  have hdist : Tendsto dist atTop (𝓝 0) :=
    (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hvol
      (fun j => (hq j).1.quasiPlurisubharmonic) hp.1.quasiPlurisubharmonic).mp hlim
  let T : ℕ → ℝ≥0∞ := fun l => ⨆ k, dist (k + l)
  have hT : Tendsto T atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero] at hdist ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := (hdist ε hε).exists_forall_of_atTop
    filter_upwards [eventually_ge_atTop N] with l hl
    exact iSup_le fun k => hN (k + l) (by omega)
  -- tail suprema of the weighted integrals
  let I : ℕ → ℝ := fun j => ∫ x, F (q j x) ∂ν
  have hIbdd : BddAbove (range I) := hL.bddAbove_range
  let s : ℕ → ℝ := fun l => ⨆ k, I (k + l)
  have hsbdd : ∀ l, BddAbove (range fun k => I (k + l)) := fun l => by
    obtain ⟨C, hC⟩ := hIbdd
    exact ⟨C, by rintro _ ⟨k, rfl⟩; exact hC ⟨k + l, rfl⟩⟩
  have hs : Tendsto s atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop] at hL ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hL (ε / 2) (by positivity)
    refine ⟨N, fun l hl => ?_⟩
    have hup : s l ≤ L + ε / 2 := ciSup_le fun k => by
      have := hN (k + l) (by omega)
      rw [Real.dist_eq, abs_lt] at this
      linarith
    have hlow : I l ≤ s l := by
      simpa only [zero_add] using le_ciSup (hsbdd l) 0
    have := hN l hl
    rw [Real.dist_eq, abs_lt] at this
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  -- the L² setting
  have hmem : ∀ j, MemLp (q j) 2 ν := fun j =>
    MemLp.of_bound (hqm j).aestronglyMeasurable B (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hqB j x)
  let X : ℕ → Lp ℝ 2 ν := fun j => (hmem j).toLp (q j)
  have hXn : ∀ j, ‖X j‖ ≤ measureUnivNNReal ν ^ (2 : ℝ≥0∞).toReal⁻¹ * B := fun j =>
    Lp.norm_le_of_ae_bound hB0 (by
      filter_upwards [MemLp.coeFn_toLp (hmem j)] with x hx
      rw [hx, Real.norm_eq_abs]
      exact hqB j x)
  obtain ⟨y, hyC, hyc⟩ := exists_cauchySeq_mem_tailHull X hXn
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hyc
  -- each element of the tail hull has an admissible representative
  let S : ℕ → Set (Lp ℝ 2 ν) := fun l =>
    {Y | ∃ g : M → ℝ, (Y : M → ℝ) =ᵐ[ν] g ∧ AdmissibleComb ν vol θ.val F p B (T l) (s l) g}
  have hSconv : ∀ l, Convex ℝ (S l) := by
    intro l Y₁ hY₁ Y₂ hY₂ a b ha hb hab
    obtain ⟨g₁, hg₁e, hg₁⟩ := hY₁
    obtain ⟨g₂, hg₂e, hg₂⟩ := hY₂
    refine ⟨a • g₁ + b • g₂, ?_, admissibleComb_convex hFc hFm hFconv hpm hg₁ hg₂ ha hb hab⟩
    filter_upwards [Lp.coeFn_add (a • Y₁) (b • Y₂), Lp.coeFn_smul a Y₁, Lp.coeFn_smul b Y₂,
      hg₁e, hg₂e] with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5]
    rfl
  have hXS : ∀ l k, X (k + l) ∈ S l := by
    intro l k
    refine ⟨q (k + l), MemLp.coeFn_toLp (hmem (k + l)), hq (k + l), hqB (k + l), ?_, ?_⟩
    · exact le_iSup (fun k => dist (k + l)) k
    · exact le_ciSup (hsbdd l) k
  have hHull : ∀ l, tailHull X l ⊆ S l := fun l =>
    convexHull_min (by rintro _ ⟨k, rfl⟩; exact hXS l k) (hSconv l)
  have hyS : ∀ l, y l ∈ S l := fun l => hHull l (hyC l)
  choose g hge hgA using hyS
  -- almost everywhere convergence along a subsequence
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hZ).exists_seq_tendsto_ae
  have hgae : ∀ᵐ x ∂ν, Tendsto (fun i => g (ns i) x) atTop (𝓝 (Z x)) := by
    have hall : ∀ᵐ x ∂ν, ∀ i, (y (ns i) : M → ℝ) x = g (ns i) x := ae_all_iff.mpr
      fun i => hge (ns i)
    filter_upwards [hae, hall] with x hx hx'
    simpa only [hx'] using hx
  -- the subsequence of combinations converges to `p` in L¹
  have hgpsh : ∀ i, IsThetaPshPotential θ.val (fun x => (g (ns i) x : EReal)) :=
    fun i => (hgA (ns i)).1
  have hgL1 : ManifoldL1LocallyTendsto (n := n) (fun i x => (g (ns i) x : EReal)) atTop
      (fun x => (p x : EReal)) := by
    refine (manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic hvol
      (fun i => (hgpsh i).1.quasiPlurisubharmonic) hp.1.quasiPlurisubharmonic).mpr ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hT.comp hns.tendsto_atTop) (fun _ => zero_le) (fun i => (hgA (ns i)).2.2.1)
  have hqe := ThetaPshL1Limsup.le_limsup_quasiEverywhere_of_manifoldL1LocallyTendsto omega θ
    hgpsh hp hgL1 (C := B) (fun i x => EReal.coe_le_coe_iff.mpr (abs_le.mp ((hgA (ns i)).2.1 x)).2)
  have hpZ : ∀ᵐ x ∂ν, p x ≤ Z x := by
    filter_upwards [hν.ae_of_quasiEverywhere hqe, hgae] with x hx hxZ
    have hlim' : Tendsto (fun i => ((g (ns i) x : ℝ) : EReal)) atTop (𝓝 ((Z x : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hxZ
    rw [hlim'.limsup_eq] at hx
    exact EReal.coe_le_coe_iff.mp hx
  have hZB : ∀ᵐ x ∂ν, |Z x| ≤ B := by
    filter_upwards [hgae] with x hx
    exact le_of_tendsto ((continuous_abs.tendsto _).comp hx)
      (Eventually.of_forall fun i => (hgA (ns i)).2.1 x)
  have hZm : AEStronglyMeasurable (fun x => F (Z x)) ν :=
    hFc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable Z)
  -- dominated convergence for the weighted integrals
  have hFZ : Tendsto (fun i => ∫ x, F (g (ns i) x) ∂ν) atTop (𝓝 (∫ x, F (Z x) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => max |F B| |F (-B)|) ?_ ?_ ?_ ?_
    · intro i
      exact (hFc.measurable.comp (measurable_of_isThetaPshPotential_coe (hgpsh i))).aestronglyMeasurable
    · exact integrable_const _
    · intro i
      refine Eventually.of_forall fun x => ?_
      have hx := abs_le.mp ((hgA (ns i)).2.1 x)
      have h1 := hFm hx.2
      have h2 := hFm hx.1
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := neg_abs_le (F (-B))
        have := le_max_right |F B| |F (-B)|
        linarith
      · have := le_abs_self (F B)
        have := le_max_left |F B| |F (-B)|
        linarith
    · filter_upwards [hgae] with x hx
      exact (hFc.tendsto _).comp hx
  have hFZL : ∫ x, F (Z x) ∂ν ≤ L :=
    le_of_tendsto_of_tendsto' hFZ (hs.comp hns.tendsto_atTop) fun i => (hgA (ns i)).2.2.2
  have hIp := integrable_comp_of_bound (ν := ν) hFc hFm hpm (ae_of_all _ hpB)
  have hIZ : Integrable (fun x => F (Z x)) ν := by
    refine Integrable.of_bound hZm (max |F B| |F (-B)|) ?_
    filter_upwards [hZB] with x hx
    have hx' := abs_le.mp hx
    have h1 := hFm hx'.2
    have h2 := hFm hx'.1
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := neg_abs_le (F (-B))
      have := le_max_right |F B| |F (-B)|
      linarith
    · have := le_abs_self (F B)
      have := le_max_left |F B| |F (-B)|
      linarith
  calc ∫ x, F (p x) ∂ν ≤ ∫ x, F (Z x) ∂ν :=
        integral_mono_ae hIp hIZ (by filter_upwards [hpZ] with x hx; exact hFm hx)
    _ ≤ L := hFZL

end SGPT.Envelopes.RelativeMA
