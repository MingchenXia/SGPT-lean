import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.TietzeExtension

set_option autoImplicit false

/-!
# Weighted weak convergence under capacity control

The measure-theoretic producer in Lu, arXiv:2005.04264v1, Theorem 2.5.
The capacity is an arbitrary extended-real set function. Uniform small-set
control, convergence in capacity, and weak convergence are separate natural
hypotheses; no weighted convergence conclusion is assumed. Actual nonpluripolar
families must separately supply these inputs.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Uniform absolute continuity of a family and its limit with respect to a
capacity, expressed solely as control of measurable sets. -/
def UniformCapacityControl (cap : Set X → ℝ≥0∞)
    (mu : ℕ → Measure X) (nu : Measure X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ eta : ℝ≥0∞, 0 < eta ∧
    ∀ A : Set X, MeasurableSet A → cap A < eta →
      (∀ j, mu j A ≤ ENNReal.ofReal r) ∧ nu A ≤ ENNReal.ofReal r

/-- A continuous capacity modulus supplies uniform small-set control. -/
theorem uniformCapacityControl_of_modulus
    {cap : Set X → ℝ≥0∞} {mu : ℕ → Measure X} {nu : Measure X}
    {F : ℝ≥0∞ → ℝ≥0∞} (hF : Tendsto F (𝓝 0) (𝓝 0))
    (hmu : ∀ j A, MeasurableSet A → mu j A ≤ F (cap A))
    (hnu : ∀ A, MeasurableSet A → nu A ≤ F (cap A)) :
    UniformCapacityControl cap mu nu := by
  intro r hr
  have he : ∀ᶠ t in 𝓝 (0 : ℝ≥0∞), F t < ENNReal.ofReal r :=
    hF.eventually_lt_const (ENNReal.ofReal_pos.mpr hr)
  obtain ⟨eta, heta, hsmall⟩ := ENNReal.nhds_zero_basis.mem_iff.mp he
  refine ⟨eta, heta, fun A hA hcap => ⟨fun j => ?_, ?_⟩⟩
  · exact (hmu j A hA).trans (hsmall hcap).le
  · exact (hnu A hA).trans (hsmall hcap).le

/-- Bounded measurable real functions are genuinely integrable against a
finite measure. -/
theorem integrable_of_bounded {mu : Measure X} [IsFiniteMeasure mu]
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable f mu :=
  (integrable_const B).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)

/-- The signed integral error is controlled by the mass of the actual gap set. -/
theorem abs_integral_sub_le_gap {mu : Measure X} [IsFiniteMeasure mu]
    {f g chi : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hchi : Measurable chi) {B K delta : ℝ} (_hB : 0 ≤ B) (hK : 0 ≤ K)
    (hdelta : 0 ≤ delta) (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B)
    (hchiK : ∀ x, |chi x| ≤ K) :
    |(∫ x, chi x * f x ∂mu) - ∫ x, chi x * g x ∂mu| ≤
      K * delta * mu.real univ + (2 * K * B) *
        mu.real {x | delta < |f x - g x|} := by
  classical
  let A : Set X := {x | delta < |f x - g x|}
  have hA : MeasurableSet A := by
    simpa only [A, Pi.sub_apply, Real.norm_eq_abs] using
      (measurableSet_lt measurable_const (hf.sub hg).norm)
  have hfi : Integrable (fun x => chi x * f x) mu :=
    integrable_of_bounded (hchi.mul hf) fun x => by
      rw [abs_mul]
      exact mul_le_mul (hchiK x) (hfB x) (abs_nonneg _) hK
  have hgi : Integrable (fun x => chi x * g x) mu :=
    integrable_of_bounded (hchi.mul hg) fun x => by
      rw [abs_mul]
      exact mul_le_mul (hchiK x) (hgB x) (abs_nonneg _) hK
  have hcost : Integrable (fun x => K * delta +
      A.indicator (fun _ => 2 * K * B) x) mu :=
    (integrable_const _).add ((integrable_const _).indicator hA)
  have hbound : ∀ x, |chi x * f x - chi x * g x| ≤
      K * delta + A.indicator (fun _ => 2 * K * B) x := by
    intro x
    rw [← mul_sub, abs_mul]
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      have hfg : |f x - g x| ≤ 2 * B :=
        (abs_sub _ _).trans (by linarith [hfB x, hgB x])
      have h := mul_le_mul (hchiK x) hfg (abs_nonneg _) hK
      nlinarith [mul_nonneg hK hdelta]
    · rw [indicator_of_notMem hx, add_zero]
      have hfg : |f x - g x| ≤ delta := not_lt.mp hx
      exact mul_le_mul (hchiK x) hfg (abs_nonneg _) hK
  rw [← integral_sub hfi hgi]
  have h := norm_integral_le_of_norm_le
    (f := fun x => chi x * f x - chi x * g x) hcost (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hbound x)
  calc
    |∫ x, chi x * f x - chi x * g x ∂mu|
        ≤ ∫ x, K * delta + A.indicator (fun _ => 2 * K * B) x ∂mu := h
    _ = K * delta * mu.real univ + (2 * K * B) *
        mu.real {x | delta < |f x - g x|} := by
      rw [integral_add (integrable_const (K * delta))
        ((integrable_const (2 * K * B)).indicator hA),
        integral_const, integral_indicator hA, setIntegral_const]
      simp only [smul_eq_mul, A]
      ring

/-- Agreement outside a small measurable set controls the signed integral. -/
theorem abs_integral_sub_le_of_eqOn_compl {mu : Measure X} [IsFiniteMeasure mu]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B)
    {G : Set X} (heq : EqOn f g Gᶜ) :
    |(∫ x, f x ∂mu) - ∫ x, g x ∂mu| ≤ 2 * B * mu.real G := by
  have h := abs_integral_sub_le_gap (mu := mu) hf hg (measurable_const (a := (1 : ℝ)))
    hB zero_le_one (le_refl 0) hfB hgB (fun _ => by norm_num)
  simp only [one_mul, mul_one, mul_zero, zero_mul, zero_add] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine measureReal_mono ?_ (measure_ne_top mu G)
  intro x hx
  by_contra hxG
  have hx0 : f x = g x := heq hxG
  change 0 < |f x - g x| at hx
  simp only [hx0, sub_self, abs_zero, lt_self_iff_false] at hx

variable [TopologicalSpace X]

/-- Continuity outside open exceptional sets of arbitrarily small capacity. -/
def QuasiContinuousFor (cap : Set X → ℝ≥0∞) (u : X → ℝ) : Prop :=
  ∀ eta : ℝ≥0∞, 0 < eta → ∃ G : Set X, IsOpen G ∧ cap G < eta ∧
    ContinuousOn u Gᶜ

variable [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The bounded Tietze extension preserves the original bound and the actual
values outside the exceptional open set. -/
theorem exists_continuous_eqOn_compl [NormalSpace X]
    {u : X → ℝ} {B : ℝ} (hB : 0 ≤ B) (huB : ∀ x, |u x| ≤ B)
    {G : Set X} (hG : IsOpen G) (hu : ContinuousOn u Gᶜ) :
    ∃ v : C(X, ℝ), (∀ x, |v x| ≤ B) ∧ EqOn u v Gᶜ := by
  let f : C(↥(Gᶜ), ℝ) := ⟨fun x => u x, hu.domRestrict⟩
  have hf : ∀ x, f x ∈ Icc (-B) B := fun x => abs_le.mp (huB x)
  obtain ⟨v, hvB, hv⟩ := f.exists_restrict_eq_forall_mem_of_closed
    hf ⟨0, by constructor <;> linarith⟩ hG.isClosed_compl
  refine ⟨v, fun x => abs_le.mpr (hvB x), fun x hx => ?_⟩
  exact (congrArg (fun w : C(↥(Gᶜ), ℝ) => w ⟨x, hx⟩) hv).symm

/-- A fixed bounded quasicontinuous weight is admissible in weak convergence
when the measures have uniform capacity control. -/
theorem tendsto_integral_of_quasiContinuousFor [NormalSpace X]
    {cap : Set X → ℝ≥0∞} {mu : ℕ → Measure X} {nu : Measure X}
    [∀ j, IsFiniteMeasure (mu j)] [IsFiniteMeasure nu]
    (hcontrol : UniformCapacityControl cap mu nu)
    (hweak : ∀ v : C(X, ℝ), Tendsto (fun j => ∫ x, v x ∂mu j) atTop
      (𝓝 (∫ x, v x ∂nu)))
    {u : X → ℝ} (hu : Measurable u) (hquasi : QuasiContinuousFor cap u)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ x, |u x| ≤ B) :
    Tendsto (fun j => ∫ x, u x ∂mu j) atTop (𝓝 (∫ x, u x ∂nu)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  let r : ℝ := eps / (8 * (B + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨eta, heta, hsmall⟩ := hcontrol r hr
  obtain ⟨G, hG, hGcap, huG⟩ := hquasi eta heta
  obtain ⟨v, hvB, heq⟩ := exists_continuous_eqOn_compl hB huB hG huG
  obtain ⟨hmG, hnG⟩ := hsmall G hG.measurableSet hGcap
  have hmGr : ∀ j, (mu j).real G ≤ r := fun j => by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmG j)).trans_eq
      (ENNReal.toReal_ofReal hr.le)
  have hnGr : nu.real G ≤ r :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnG).trans_eq
      (ENNReal.toReal_ofReal hr.le)
  have hrmul : r * (8 * (B + 1)) = eps := by
    dsimp [r]
    exact div_mul_cancel₀ _ (by positivity)
  have herr : 2 * B * r < eps / 4 := by nlinarith
  have hmerr : ∀ j, |(∫ x, u x ∂mu j) - ∫ x, v x ∂mu j| < eps / 4 := by
    intro j
    apply lt_of_le_of_lt (abs_integral_sub_le_of_eqOn_compl hu v.continuous.measurable
      hB huB hvB heq)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hmGr j) (by positivity)) herr
  have hnerr : |(∫ x, u x ∂nu) - ∫ x, v x ∂nu| < eps / 4 :=
    lt_of_le_of_lt (abs_integral_sub_le_of_eqOn_compl hu v.continuous.measurable
      hB huB hvB heq)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnGr (by positivity)) herr)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hweak v) (eps / 2) (by positivity)
  refine ⟨N, fun j hj => ?_⟩
  have hvlim := hN j hj
  rw [Real.dist_eq] at hvlim ⊢
  have htri := abs_add_three
    ((∫ x, u x ∂mu j) - ∫ x, v x ∂mu j)
    ((∫ x, v x ∂mu j) - ∫ x, v x ∂nu)
    ((∫ x, v x ∂nu) - ∫ x, u x ∂nu)
  have hid : ((∫ x, u x ∂mu j) - ∫ x, v x ∂mu j) +
      ((∫ x, v x ∂mu j) - ∫ x, v x ∂nu) +
      ((∫ x, v x ∂nu) - ∫ x, u x ∂nu) =
      (∫ x, u x ∂mu j) - ∫ x, u x ∂nu := by ring
  rw [hid, abs_sub_comm (∫ x, v x ∂nu) (∫ x, u x ∂nu)] at htri
  linarith [hmerr j]

omit [TopologicalSpace X] [BorelSpace X] in
/-- Convergence in capacity permits replacing the varying bounded weight by
its limit inside the varying measure, even with a bounded measurable test. -/
theorem tendsto_integral_sub_of_tendsto_capacity
    {cap : Set X → ℝ≥0∞} {mu : ℕ → Measure X} {nu : Measure X}
    [∀ j, IsFiniteMeasure (mu j)]
    (hcontrol : UniformCapacityControl cap mu nu)
    {u : ℕ → X → ℝ} {v chi : X → ℝ}
    (hu : ∀ j, Measurable (u j)) (hv : Measurable v) (hchi : Measurable chi)
    {B K Mass : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hMass : 0 ≤ Mass)
    (huB : ∀ j x, |u j x| ≤ B) (hvB : ∀ x, |v x| ≤ B)
    (hchiK : ∀ x, |chi x| ≤ K)
    (hmass : ∀ᶠ j in atTop, (mu j).real univ ≤ Mass)
    (hcap : ∀ delta : ℝ, 0 < delta → Tendsto
      (fun j => cap {x | delta < |u j x - v x|}) atTop (𝓝 0)) :
    Tendsto (fun j => (∫ x, chi x * u j x ∂mu j) -
      ∫ x, chi x * v x ∂mu j) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  let delta : ℝ := eps / (4 * (K + 1) * (Mass + 1))
  let r : ℝ := eps / (8 * (K + 1) * (B + 1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hdmul : delta * (4 * (K + 1) * (Mass + 1)) = eps := by
    dsimp [delta]; exact div_mul_cancel₀ _ (by positivity)
  have hrmul : r * (8 * (K + 1) * (B + 1)) = eps := by
    dsimp [r]; exact div_mul_cancel₀ _ (by positivity)
  have hleft : K * delta * Mass < eps / 4 := by
    have hKM : K * Mass < (K + 1) * (Mass + 1) := by nlinarith
    have h := mul_lt_mul_of_pos_right hKM hd
    nlinarith
  have hright : 2 * K * B * r < eps / 4 := by
    have hKB : K * B < (K + 1) * (B + 1) := by nlinarith
    have h := mul_lt_mul_of_pos_right hKB hr
    nlinarith
  obtain ⟨eta, heta, hsmall⟩ := hcontrol r hr
  filter_upwards [hmass, (hcap delta hd).eventually_lt_const heta] with j hj hcapj
  have hA : MeasurableSet {x | delta < |u j x - v x|} := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      measurableSet_lt measurable_const ((hu j).sub hv).norm
  have hsmallj := (hsmall _ hA hcapj).1 j
  have hmA : (mu j).real {x | delta < |u j x - v x|} ≤ r :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmallj).trans_eq
      (ENNReal.toReal_ofReal hr.le)
  have hestimate := abs_integral_sub_le_gap (mu := mu j) (hu j) hv hchi
    hB hK hd.le (huB j) hvB hchiK
  have hmassTerm : K * delta * (mu j).real univ ≤ K * delta * Mass :=
    mul_le_mul_of_nonneg_left hj (by positivity)
  have hgapTerm : 2 * K * B * (mu j).real {x | delta < |u j x - v x|} ≤
      2 * K * B * r := mul_le_mul_of_nonneg_left hmA (by positivity)
  simp only [Real.dist_eq, sub_zero]
  linarith

/-- Lu's capacity-controlled weighted weak convergence, stated against each
continuous test. The weak measure convergence and capacity inputs are the
source hypotheses, not a weighted-limit certificate. -/
theorem tendsto_integral_mul_of_capacity [CompactSpace X] [T2Space X]
    {cap : Set X → ℝ≥0∞} {mu : ℕ → Measure X} {nu : Measure X}
    [∀ j, IsFiniteMeasure (mu j)] [IsFiniteMeasure nu]
    (hcontrol : UniformCapacityControl cap mu nu)
    (hweak : ∀ w : C(X, ℝ), Tendsto (fun j => ∫ x, w x ∂mu j) atTop
      (𝓝 (∫ x, w x ∂nu)))
    {u : ℕ → X → ℝ} {v : X → ℝ}
    (hu : ∀ j, Measurable (u j)) (hv : Measurable v)
    (hquasi : QuasiContinuousFor cap v)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ j x, |u j x| ≤ B) (hvB : ∀ x, |v x| ≤ B)
    (hcap : ∀ delta : ℝ, 0 < delta → Tendsto
      (fun j => cap {x | delta < |u j x - v x|}) atTop (𝓝 0))
    (chi : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * u j x ∂mu j) atTop
      (𝓝 (∫ x, chi x * v x ∂nu)) := by
  obtain ⟨K0, hK0⟩ := isCompact_univ.exists_bound_of_continuousOn chi.continuous.continuousOn
  let K : ℝ := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hchiK : ∀ x, |chi x| ≤ K := by
    intro x
    have h : |chi x| ≤ K0 := by
      simpa only [Real.norm_eq_abs] using hK0 x (mem_univ x)
    exact h.trans (le_max_left _ _)
  have hmasslim : Tendsto (fun j => (mu j).real univ) atTop (𝓝 (nu.real univ)) := by
    simpa using hweak (ContinuousMap.const X (1 : ℝ))
  have hmass : ∀ᶠ j in atTop, (mu j).real univ ≤ nu.real univ + 1 :=
    (hmasslim.eventually_lt_const (by linarith)).mono fun _ h => h.le
  have hreplace := tendsto_integral_sub_of_tendsto_capacity hcontrol hu hv
    chi.continuous.measurable hB hK (by positivity : 0 ≤ nu.real univ + 1)
    huB hvB hchiK hmass hcap
  have hquasiProd : QuasiContinuousFor cap (fun x => chi x * v x) := by
    intro eta heta
    obtain ⟨G, hG, hGcap, hvG⟩ := hquasi eta heta
    exact ⟨G, hG, hGcap, chi.continuous.continuousOn.mul hvG⟩
  have hprodB : ∀ x, |chi x * v x| ≤ K * B := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hchiK x) (hvB x) (abs_nonneg _) hK
  have hfixed := tendsto_integral_of_quasiContinuousFor hcontrol hweak
    (chi.continuous.measurable.mul hv) hquasiProd (mul_nonneg hK hB) hprodB
  have hsum := hreplace.add hfixed
  simpa only [Pi.mul_apply, sub_add_cancel, zero_add] using hsum

/-- The same result using mathlib's native weak topology of finite measures. -/
theorem tendsto_integral_mul_of_weakTendsto [CompactSpace X] [T2Space X]
    {cap : Set X → ℝ≥0∞} {mu : ℕ → FiniteMeasure X} {nu : FiniteMeasure X}
    (hcontrol : UniformCapacityControl cap (fun j => (mu j : Measure X)) nu)
    (hweak : Tendsto mu atTop (𝓝 nu))
    {u : ℕ → X → ℝ} {v : X → ℝ}
    (hu : ∀ j, Measurable (u j)) (hv : Measurable v)
    (hquasi : QuasiContinuousFor cap v)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ j x, |u j x| ≤ B) (hvB : ∀ x, |v x| ≤ B)
    (hcap : ∀ delta : ℝ, 0 < delta → Tendsto
      (fun j => cap {x | delta < |u j x - v x|}) atTop (𝓝 0))
    (chi : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * u j x ∂(mu j : Measure X)) atTop
      (𝓝 (∫ x, chi x * v x ∂(nu : Measure X))) :=
  tendsto_integral_mul_of_capacity hcontrol
    (fun w => (FiniteMeasure.continuous_integral_continuousMap w).tendsto nu |>.comp hweak)
    hu hv hquasi hB huB hvB hcap chi

/-- A continuous capacity modulus and native weak convergence give Lu's
weighted integral limit directly. -/
theorem tendsto_integral_mul_of_modulus [CompactSpace X] [T2Space X]
    {cap : Set X → ℝ≥0∞} {mu : ℕ → FiniteMeasure X} {nu : FiniteMeasure X}
    {F : ℝ≥0∞ → ℝ≥0∞} (hF : Tendsto F (𝓝 0) (𝓝 0))
    (hmu : ∀ j A, MeasurableSet A → (mu j : Measure X) A ≤ F (cap A))
    (hnu : ∀ A, MeasurableSet A → (nu : Measure X) A ≤ F (cap A))
    (hweak : Tendsto mu atTop (𝓝 nu))
    {u : ℕ → X → ℝ} {v : X → ℝ}
    (hu : ∀ j, Measurable (u j)) (hv : Measurable v)
    (hquasi : QuasiContinuousFor cap v)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ j x, |u j x| ≤ B) (hvB : ∀ x, |v x| ≤ B)
    (hcap : ∀ delta : ℝ, 0 < delta → Tendsto
      (fun j => cap {x | delta < |u j x - v x|}) atTop (𝓝 0))
    (chi : C(X, ℝ)) :
    Tendsto (fun j => ∫ x, chi x * u j x ∂(mu j : Measure X)) atTop
      (𝓝 (∫ x, chi x * v x ∂(nu : Measure X))) :=
  tendsto_integral_mul_of_weakTendsto (uniformCapacityControl_of_modulus hF hmu hnu)
    hweak hu hv hquasi hB huB hvB hcap chi

end

end SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence
