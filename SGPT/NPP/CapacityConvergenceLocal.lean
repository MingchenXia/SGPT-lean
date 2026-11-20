import SGPT.NPP.CapacityConvergenceSemicon
import SGPT.Foundations.Analysis.Pending.ActualLocalFiniteBoxQuasiContinuousWeightedContinuity

/-!
# Local convergence of weighted Bedford–Taylor products under convergence in capacity

The analytic core of source `thm:loc_conv_cap` (chapter `chapter_npp.tex`; Guedj–Zeriahi,
Theorem 4.26; Xia, *Foundations of pluripotential theory*, `thm:bt-capacity-continuity`), in a
coordinate domain `D` of a compact Kähler manifold carrying a local potential of the Kähler
form: if `u_j → v` are uniformly bounded psh tuples on `D` converging in relative capacity on
compact subsets, and `χ_j → χ` are uniformly bounded Borel weights on the manifold converging
in Kähler capacity, each `χ_j` quasi-continuous, then

`∫ χ_j h dd^c u_j^1 ∧ ⋯ ∧ dd^c u_j^n → ∫ χ h dd^c v^1 ∧ ⋯ ∧ dd^c v^n`

for every continuous `h` with compact support in `D` (`local_tendsto_integral_moving`).
The limit weight `χ` need not be quasi-continuous.

Proof. For a fixed index `m`, the weight `χ_m` is quasi-continuous and the fixed-weight
theorem (`ActualLocalFiniteBoxQuasiContinuousWeightedContinuity`) gives
`∫ χ_m h dμ_j → ∫ χ_m h dν`. The Bedford–Taylor measures of the uniformly bounded tuples are
dominated by the relative capacity (`IsBTLimit.le_relCapacity_of_abs_le`), which on compact
subsets is dominated by the Kähler capacity (`exists_compact_capacity_reverse`); hence
`|∫ (a - b) h dλ| ≤ H (c λ(K) + 2A λ({|a - b| > c} ∩ K))` (`abs_integral_read_sub_le`) turns
convergence in capacity of the weights into convergence of the integrals, by a `3ε`-argument
in `j` and `m`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open ThetaCapacity CapacityWeightedConvergence BedfordTaylor MixedMongeAmpere

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- **Moving-weight error estimate**: for bounded Borel weights `a, b` and a test `h`
supported in a compact `K` of finite measure,
`|∫ a h dλ - ∫ b h dλ| ≤ H (c λ(K) + 2A λ({|a - b| > c} ∩ K))`. -/
theorem abs_integral_read_sub_le {μ : Measure (ComplexModel n)} (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ e.val.target) (hμK : μ K < ⊤)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (ht : tsupport h ⊆ K) {H : ℝ}
    (hH : ∀ z, |h z| ≤ H) {a b : M → ℝ} (ha : Measurable a) (hb : Measurable b) {A : ℝ}
    (hA : 0 ≤ A) (haA : ∀ x, |a x| ≤ A) (hbA : ∀ x, |b x| ≤ A) {c : ℝ} (hc0 : 0 ≤ c) :
    |∫ y, a (e.val.symm y) * h y ∂μ - ∫ y, b (e.val.symm y) * h y ∂μ| ≤
      H * (c * (μ K).toReal + 2 * A *
        (μ {z | z ∈ K ∧ c < |a (e.val.symm z) - b (e.val.symm z)|}).toReal) := by
  classical
  let T : Opens (ComplexModel n) := ⟨e.val.target, e.val.open_target⟩
  have hzK : ∀ z, z ∉ K → h z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hs => hz (ht hs))
  have hzT : ∀ z, z ∉ T → h z = 0 := fun z hz => hzK z (fun h' => hz (hKt h'))
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  -- measurability and integrability of the tests
  have hfm (w : M → ℝ) (hw : Measurable w) : Measurable (fun y => w (e.val.symm y) * h y) :=
    measurable_supported_read e (D := T) le_rfl hw hc hzT
  have hfi (w : M → ℝ) (hw : Measurable w) (hwA : ∀ x, |w x| ≤ A) :
      Integrable (fun y => w (e.val.symm y) * h y) μ := by
    have hsupp : Function.support (fun y => w (e.val.symm y) * h y) ⊆ K := by
      intro y hy
      by_contra hyK
      exact hy (by simp only [hzK y hyK, mul_zero])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
    refine Measure.integrableOn_of_bounded (M := A * H) hμK.ne
      (hfm w hw).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hwA _) (hH y) (abs_nonneg _) hA
  -- the gap set
  let r (w : M → ℝ) : ComplexModel n → ℝ := e.val.target.indicator (fun z => w (e.val.symm z))
  have hr (w : M → ℝ) {z : ComplexModel n} (hz : z ∈ K) : r w z = w (e.val.symm z) :=
    indicator_of_mem (hKt hz) _
  let E : Set (ComplexModel n) := {z | z ∈ K ∧ c < |a (e.val.symm z) - b (e.val.symm z)|}
  have hE : E = K ∩ {z | c < |r a z - r b z|} := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      exact ⟨hz, by simpa only [mem_ofPred_eq, hr a hz, hr b hz] using hzc⟩
    · rintro ⟨hz, hzc⟩
      exact ⟨hz, by simpa only [mem_ofPred_eq, hr a hz, hr b hz] using hzc⟩
  have hEm : MeasurableSet E := by
    rw [hE]
    exact hK.measurableSet.inter (measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((measurable_indicator_read e ha).sub
        (measurable_indicator_read e hb))))
  have hEK : E ⊆ K := fun z hz => hz.1
  have hμE : μ E < ⊤ := (measure_mono hEK).trans_lt hμK
  -- the dominating function
  let g : ComplexModel n → ℝ := fun z => H * c * K.indicator 1 z + H * (2 * A) * E.indicator 1 z
  have hK1 : Integrable (fun z => K.indicator (1 : ComplexModel n → ℝ) z) μ :=
    (integrableOn_const (C := (1 : ℝ)) hμK.ne).integrable_indicator hK.measurableSet
  have hE1 : Integrable (fun z => E.indicator (1 : ComplexModel n → ℝ) z) μ :=
    (integrableOn_const (C := (1 : ℝ)) hμE.ne).integrable_indicator hEm
  have hgi : Integrable g μ := (hK1.const_mul (H * c)).add (hE1.const_mul (H * (2 * A)))
  have hgint : ∫ z, g z ∂μ = H * (c * (μ K).toReal + 2 * A * (μ E).toReal) := by
    change ∫ z, H * c * K.indicator 1 z + H * (2 * A) * E.indicator 1 z ∂μ = _
    rw [integral_add (hK1.const_mul (H * c)) (hE1.const_mul (H * (2 * A))),
      integral_const_mul, integral_const_mul, integral_indicator_one hK.measurableSet,
      integral_indicator_one hEm, measureReal_def, measureReal_def]
    ring
  have hpt : ∀ z, ‖a (e.val.symm z) * h z - b (e.val.symm z) * h z‖ ≤ g z := by
    intro z
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    by_cases hzK' : z ∈ K
    · have habz : |a (e.val.symm z) - b (e.val.symm z)| ≤ 2 * A := by
        have h1 := haA (e.val.symm z)
        have h2 := hbA (e.val.symm z)
        calc |a (e.val.symm z) - b (e.val.symm z)| ≤ |a (e.val.symm z)| + |b (e.val.symm z)| :=
              abs_sub _ _
          _ ≤ 2 * A := by linarith
      by_cases hzE : z ∈ E
      · simp only [g, indicator_of_mem hzK', indicator_of_mem hzE, Pi.one_apply, mul_one]
        have : |a (e.val.symm z) - b (e.val.symm z)| * |h z| ≤ (2 * A) * H :=
          mul_le_mul habz (hH z) (abs_nonneg _) (by positivity)
        nlinarith [mul_nonneg hH0 hc0]
      · have hle : |a (e.val.symm z) - b (e.val.symm z)| ≤ c := le_of_not_gt fun h' => hzE ⟨hzK', h'⟩
        simp only [g, indicator_of_mem hzK', indicator_of_notMem hzE, Pi.one_apply, mul_one,
          mul_zero, add_zero]
        have : |a (e.val.symm z) - b (e.val.symm z)| * |h z| ≤ c * H :=
          mul_le_mul hle (hH z) (abs_nonneg _) hc0
        linarith
    · have hzE : z ∉ E := fun h' => hzK' h'.1
      simp only [g, indicator_of_notMem hzK', indicator_of_notMem hzE, hzK z hzK', abs_zero,
        mul_zero, add_zero, le_refl]
  rw [← integral_sub (hfi a ha haA) (hfi b hb hbA), ← hgint]
  exact (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans_eq' rfl |>.trans
    le_rfl

variable [IsComplexManifold n M] [CompactSpace M]

/-- **Local convergence of weighted Bedford–Taylor measures with moving weights**. -/
theorem local_tendsto_integral_moving (omega : KahlerBackground n M)
    (e : ComplexChart n M) {D : Opens (ComplexModel n)}
    (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {ρ : ComplexModel n → ℝ} (hρ : IsSmoothLocalPotential omega.form.val e D ρ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {u : ℕ → Fin n → ComplexModel n → ℝ} {v : Fin n → ComplexModel n → ℝ}
    (hu : ∀ j, IsLocallyBoundedMixedPshOn D (u j))
    (hv : IsLocallyBoundedMixedPshOn D v) {B : ℝ} (hB : 0 ≤ B)
    (huB : ∀ j i z, z ∈ D → -B ≤ u j i z ∧ u j i z ≤ B)
    (hvB : ∀ i z, z ∈ D → -B ≤ v i z ∧ v i z ≤ B)
    (hcap : ∀ i (V : Opens (ComplexModel n)), V ≤ D → ∀ T : Set (ComplexModel n),
      IsCompact T → T ⊆ V → ∀ a : ℝ, 0 < a →
      Tendsto (fun j => relCapacity V {z | z ∈ T ∧ a < |u j i z - v i z|}) atTop (𝓝 0))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hχA : ∀ j x, |χ j x| ≤ A) (hχ₀A : ∀ x, |χ₀ x| ≤ A)
    (hχm : ∀ j, Measurable (χ j)) (hχ₀m : Measurable χ₀)
    (hχQC : ∀ j, QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) (χ j))
    (hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | c < |χ j x - χ₀ x|}) atTop (𝓝 0))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hk : HasCompactSupport h)
    (ht : tsupport h ⊆ K) :
    Tendsto (fun j => ∫ y, χ j (e.val.symm y) * h y
        ∂canonicalMixedBedfordTaylorMeasure D (u j) (hu j)) atTop
      (𝓝 (∫ y, χ₀ (e.val.symm y) * h y ∂canonicalMixedBedfordTaylorMeasure D v hv)) := by
  classical
  let μ (j : ℕ) : Measure (ComplexModel n) := canonicalMixedBedfordTaylorMeasure D (u j) (hu j)
  let ν : Measure (ComplexModel n) := canonicalMixedBedfordTaylorMeasure D v hv
  let cap : Set M → ℝ≥0∞ := thetaCapacity omega.form (fun _ => 0)
  have hcapfin (S : Set M) : cap S ≠ ⊤ := by
    have h := SGPT.NPP.sourceThetaCapacity_lt_top omega
      (SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas omega.form) S
    rw [SGPT.NPP.sourceThetaCapacity_kahler] at h
    exact h.ne
  -- domination of the Bedford–Taylor measures by the Kähler capacity on `K`
  let Mb : ℝ≥0∞ := ENNReal.ofReal ((n * (2 * (B + 1))) ^ n)
  obtain ⟨Crev, hCrev, hrev⟩ :=
    ActualChartCapacityReverse.exists_compact_capacity_reverse omega e hDt hρ hK hKD
  let Q : ℝ≥0∞ := Mb * ENNReal.ofReal Crev
  have hQ : Q ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hdom (w : Fin n → ComplexModel n → ℝ) (hw : IsLocallyBoundedMixedPshOn D w)
      (hwB : ∀ i z, z ∈ D → -B ≤ w i z ∧ w i z ≤ B) (E : Set (ComplexModel n)) (hE : E ⊆ K) :
      canonicalMixedBedfordTaylorMeasure D w hw E ≤ Q * cap (e.val.symm '' E) := by
    have hlimit : IsBTLimit D w (canonicalMixedBedfordTaylorMeasure D w hw) :=
      IsLocalMixedBedfordTaylorMeasure.isBTLimit (canonicalMixedBedfordTaylorMeasure_spec D w hw)
    refine (hlimit.le_relCapacity_of_abs_le hw le_rfl (M := B + 1) (by linarith) (fun i z hz => ?_)
      (hE.trans hKD)).trans ?_
    · rw [abs_le]; constructor <;> linarith [(hwB i z hz).1, (hwB i z hz).2]
    · rw [mul_assoc]
      exact mul_le_mul_right (hrev E hE) _
  let R : ℝ := (Q * cap (e.val.symm '' K)).toReal
  have hRfin : Q * cap (e.val.symm '' K) ≠ ⊤ := ENNReal.mul_ne_top hQ (hcapfin _)
  -- the test bound
  obtain ⟨H, hH⟩ : ∃ H : ℝ, ∀ z, |h z| ≤ H := by
    obtain ⟨R, hR⟩ := hc.bounded_above_of_compact_support hk
    exact ⟨R, fun z => by simpa only [Real.norm_eq_abs] using hR z⟩
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  -- the estimate, uniformly over the measures
  have hest (w : Fin n → ComplexModel n → ℝ) (hw : IsLocallyBoundedMixedPshOn D w)
      (hwB : ∀ i z, z ∈ D → -B ≤ w i z ∧ w i z ≤ B) {a b : M → ℝ} (ha : Measurable a)
      (hb : Measurable b) (haA : ∀ x, |a x| ≤ A) (hbA : ∀ x, |b x| ≤ A) {c : ℝ} (hc0 : 0 ≤ c) :
      |∫ y, a (e.val.symm y) * h y ∂canonicalMixedBedfordTaylorMeasure D w hw -
          ∫ y, b (e.val.symm y) * h y ∂canonicalMixedBedfordTaylorMeasure D w hw| ≤
        H * (c * R + 2 * A * (Q * cap {x | c < |a x - b x|}).toReal) := by
    have hKle := hdom w hw hwB K le_rfl
    have hμK : canonicalMixedBedfordTaylorMeasure D w hw K < ⊤ := hKle.trans_lt hRfin.lt_top
    refine (abs_integral_read_sub_le e hK (fun z hz => hDt (hKD hz)) hμK hc ht hH ha hb hA haA
      hbA hc0).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono hRfin hKle) hc0) (mul_le_mul_of_nonneg_left ?_ (by positivity))) hH0
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hQ (hcapfin _)) ?_
    refine (hdom w hw hwB _ (fun z hz => hz.1)).trans (mul_le_mul_right (thetaCapacity_mono ?_) _)
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  -- fixed quasi-continuous weights converge
  have hfixed (m : ℕ) : Tendsto (fun j => ∫ y, χ m (e.val.symm y) * h y ∂μ j) atTop
      (𝓝 (∫ y, χ m (e.val.symm y) * h y ∂ν)) := by
    have h := ActualLocalFiniteBoxQuasiContinuousWeightedContinuity.tendsto_integral_quasiContinuous_classifier_of_relative_capacity
      omega e hDt hρ hK hKD hu hv hB huB hvB hcap (m := 0) (w := fun _ => Fin.elim0)
      (z := Fin.elim0) (fun _ i => i.elim0) (fun i => i.elim0) (fun _ i => i.elim0)
      (fun i => i.elim0) (fun i => i.elim0) (Φ := fun _ => 1) (L := 0)
      (LipschitzWith.const 1) hA (hχA m) (hχm m) (hχQC m) hc hk ht
    simpa only [mul_one] using h
  -- the gap capacities
  let G (c : ℝ) (j : ℕ) : ℝ := (Q * cap {x | c / 2 < |χ j x - χ₀ x|}).toReal
  have hG (c : ℝ) (hc0 : 0 < c) : Tendsto (G c) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (hχcap (c / 2) (by positivity)) (Or.inr hQ)
    rw [mul_zero] at h1
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa only [Function.comp_def, ENNReal.toReal_zero] using h2
  have hG0 (c : ℝ) (j : ℕ) : 0 ≤ G c j := ENNReal.toReal_nonneg
  have hsplit (c : ℝ) (hc0 : 0 < c) (j m : ℕ) :
      (Q * cap {x | c < |χ j x - χ m x|}).toReal ≤ G c j + G c m := by
    have hsub : {x | c < |χ j x - χ m x|} ⊆
        {x | c / 2 < |χ j x - χ₀ x|} ∪ {x | c / 2 < |χ m x - χ₀ x|} := by
      intro x hx
      by_contra hno
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hno
      have : |χ j x - χ m x| ≤ |χ j x - χ₀ x| + |χ m x - χ₀ x| := by
        calc |χ j x - χ m x| = |(χ j x - χ₀ x) - (χ m x - χ₀ x)| := by ring_nf
          _ ≤ |χ j x - χ₀ x| + |χ m x - χ₀ x| := abs_sub _ _
      change c < |χ j x - χ m x| at hx
      linarith
    rw [← ENNReal.toReal_add (ENNReal.mul_ne_top hQ (hcapfin _))
      (ENNReal.mul_ne_top hQ (hcapfin _)), ← mul_add]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hQ (ENNReal.add_ne_top.mpr
      ⟨hcapfin _, hcapfin _⟩)) (mul_le_mul_right ((thetaCapacity_mono hsub).trans
        (thetaCapacity_union_le _ _ _ _)) _)
  have hshrink (c : ℝ) (hc0 : 0 < c) (m : ℕ) :
      (Q * cap {x | c < |χ m x - χ₀ x|}).toReal ≤ G c m := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hQ (hcapfin _))
      (mul_le_mul_right (thetaCapacity_mono fun x hx => ?_) _)
    change c < |χ m x - χ₀ x| at hx
    change c / 2 < |χ m x - χ₀ x|
    linarith
  -- the 3ε argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  let c : ℝ := ε / (8 * (H + 1) * (R + 1))
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hc0 : 0 < c := by positivity
  have hcR : 2 * (H * (c * R)) ≤ ε / 4 := by
    have h1 : H * (c * R) ≤ (H + 1) * (c * (R + 1)) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hc0.le)
        (by positivity) (by positivity)
    have h2 : (H + 1) * (c * (R + 1)) = ε / 8 := by
      dsimp only [c]
      field_simp
    linarith
  obtain ⟨m, hm⟩ := ((hG c hc0).eventually (gt_mem_nhds (show (0 : ℝ) <
    ε / (16 * (A + 1) * (H + 1)) by positivity))).exists
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hfixed m)) (ε / 4) (by positivity)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((hG c hc0).eventually (gt_mem_nhds (show (0 : ℝ) <
    ε / (16 * (A + 1) * (H + 1)) by positivity)))
  refine ⟨max N₁ N₂, fun j hj => ?_⟩
  have hj1 := hN₁ j (le_of_max_le_left hj)
  have hj2 := hN₂ j (le_of_max_le_right hj)
  have hAH (g : ℝ) (hg0 : 0 ≤ g) (hg : g < ε / (16 * (A + 1) * (H + 1))) :
      H * (2 * A * g) ≤ ε / 8 := by
    have h1 : H * (2 * A * g) ≤ 2 * ((H + 1) * ((A + 1) * g)) := by
      nlinarith [mul_nonneg hH0 hA, mul_nonneg (mul_nonneg hH0 hA) hg0]
    have h2 : (H + 1) * ((A + 1) * g) ≤ ε / 16 := by
      have := mul_lt_mul_of_pos_left hg (show 0 < (H + 1) * (A + 1) by positivity)
      have he : (H + 1) * (A + 1) * (ε / (16 * (A + 1) * (H + 1))) = ε / 16 := by
        field_simp
      nlinarith
    linarith
  have e1 := hest (u j) (hu j) (huB j) (hχm j) (hχm m) (hχA j) (hχA m) hc0.le
  have e3 := hest v hv hvB (hχm m) hχ₀m (hχA m) hχ₀A hc0.le
  have s1 := hsplit c hc0 j m
  have s3 := hshrink c hc0 m
  have b1 := hAH (G c j) (hG0 c j) hj2
  have b2 := hAH (G c m) (hG0 c m) hm
  rw [Real.dist_eq] at hj1 ⊢
  have t1 : H * (c * R + 2 * A * (Q * cap {x | c < |χ j x - χ m x|}).toReal) ≤
      H * (c * R) + H * (2 * A * G c j) + H * (2 * A * G c m) := by
    have := mul_le_mul_of_nonneg_left s1 (show 0 ≤ 2 * A by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hH0]
  have t3 : H * (c * R + 2 * A * (Q * cap {x | c < |χ m x - χ₀ x|}).toReal) ≤
      H * (c * R) + H * (2 * A * G c m) := by
    have := mul_le_mul_of_nonneg_left s3 (show 0 ≤ 2 * A by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hH0]
  calc |∫ y, χ j (e.val.symm y) * h y ∂μ j - ∫ y, χ₀ (e.val.symm y) * h y ∂ν|
      ≤ |∫ y, χ j (e.val.symm y) * h y ∂μ j - ∫ y, χ m (e.val.symm y) * h y ∂μ j| +
        |∫ y, χ m (e.val.symm y) * h y ∂μ j - ∫ y, χ m (e.val.symm y) * h y ∂ν| +
        |∫ y, χ m (e.val.symm y) * h y ∂ν - ∫ y, χ₀ (e.val.symm y) * h y ∂ν| := by
        have := abs_sub_le (∫ y, χ j (e.val.symm y) * h y ∂μ j)
          (∫ y, χ m (e.val.symm y) * h y ∂μ j) (∫ y, χ₀ (e.val.symm y) * h y ∂ν)
        have := abs_sub_le (∫ y, χ m (e.val.symm y) * h y ∂μ j)
          (∫ y, χ m (e.val.symm y) * h y ∂ν) (∫ y, χ₀ (e.val.symm y) * h y ∂ν)
        linarith
    _ < ε := by linarith

end SGPT.NPP.CapacityConvergence
