import SGPT.Envelopes.LapClassDef
import SGPT.Envelopes.DNTRegQuasiPsh
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability

/-!
# Smoothing with one-sided Laplacian bounds

Lane LAP-CLASS (`claude-lap-class`, node `lap-class:smoothing`).  Source: FPT
`thm:kahler-metric-laplacian-rooftop`, Step 1, which smooths obstacles with bounded metric Laplacian
by convolution in charts and controls the commutator with `Δ_ω` through the `W^{2,p}` estimates of
`prop:compact-metric-laplacian-lp`.  We use instead the **resolvent** `R_s = (1 - sΔ_ω)⁻¹` of the
Kähler Laplacian, which needs no Calderón–Zygmund theory: TN solves `Δ_ω v - s⁻¹v = h` on Hölder
spaces (`KahlerLaplacianChart.exists_laplacian_sub_eq`) with elliptic regularity
(`KahlerLaplacianSolvability.exists_holderMap_of_laplacian_eq`).

* `exists_resolvent`: for `s > 0` and smooth `φ` there is a smooth `v` with `v - sΔ_ω v = φ`.
* `le_of_sub_laplacian_eq`, `abs_le_of_sub_laplacian_eq`: maximum principle,
  `inf φ ≤ R_s φ ≤ sup φ`.
* `le_of_integral_mul_nonpos`: a continuous `h` with `∫ h χ ω^N ≤ 0` for all smooth `χ ≥ 0` is
  `≤ 0`.
* `sub_le_of_resolvent` (duality): if `Δ_ω f ≤ S` in the sense of distributions and `|φ - f| ≤ δ`,
  then `R_s φ - φ ≤ sS + 2δ`, because `R_s` is symmetric (Green), positive, and preserves
  `∫ · ω^N`.
* `exists_smooth_laplacian_le` (**smoothing**): a continuous `f` with `Δ_ω f ≤ S` is a uniform
  limit of smooth `g` with `Δ_ω g ≤ S + ε`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent KahlerLaplacianSolvability
  HolderAtlas.HolderMap

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-! ### The resolvent -/

/-- **The resolvent of the Kähler Laplacian on smooth functions**: for `s > 0` and chart-smooth
`φ` there is a chart-smooth `v` with `v - sΔ_ω v = φ`. -/
theorem exists_resolvent [CompactSpace Y] (w : KahlerBackground N Y) {s : ℝ} (hs : 0 < s)
    {φ : Y → ℝ} (hφ : ChartSmooth (n := N) φ) :
    ∃ v : Y → ℝ, ChartSmooth (n := N) v ∧ ∀ y, v y - s * laplacian w.form.val v y = φ y := by
  obtain ⟨A⟩ := HolderAtlas.nonempty (n := N) (M := Y)
  have hr0 : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ≥0) < 1 := by rw [← NNReal.coe_lt_coe]; norm_num
  have hg : w.form.val.IsHermitian := w.isKahler.1
  have hψ : ChartSmooth (n := N) (fun y => -(φ y) / s) := fun e => ((hφ e).neg).div_const s
  obtain ⟨u, hu⟩ := exists_laplacian_sub_eq hg A hr0 hr1 (inv_pos.mpr hs)
    (ofChartSmooth (A := A) (k := 0) hr1.le _ hψ)
  have hu' : ∀ y, laplacian w.form.val u y = (u y - φ y) / s := by
    intro y
    have h := hu y
    rw [coe_ofChartSmooth] at h
    field_simp at h ⊢
    linarith
  -- elliptic regularity
  have hreg : ∀ k : ℕ, ∃ v : A.HolderMap (k + 2) (1 / 2) ℝ, ⇑v = ⇑u := by
    intro k
    induction k with
    | zero => exact ⟨u, rfl⟩
    | succ k ih =>
      obtain ⟨v, hv⟩ := ih
      set h : A.HolderMap (k + 1) (1 / 2) ℝ :=
        s⁻¹ • (lowerCLM (k := k + 1) hr1.le v - ofChartSmooth (A := A) (k := k + 1) hr1.le φ hφ)
        with hh
      have heq : ∀ y, laplacian w.form.val u y = h y := by
        intro y
        rw [hu' y, hh, coe_smul, coe_sub]
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, coe_ofChartSmooth]
        rw [show (lowerCLM (k := k + 1) hr1.le v) y = v y from rfl, hv]
        field_simp
      obtain ⟨v', hv'⟩ := exists_holderMap_of_laplacian_eq hg hr0 hr1 u h heq
      exact ⟨v', hv'⟩
  refine ⟨u, fun e => ?_, fun y => ?_⟩
  · apply contDiffOn_infty.mpr
    intro j
    obtain ⟨v, hv⟩ := hreg j
    have hc : ContDiffOn ℝ (j + 2) (fun z => v (e.val.symm z)) e.val.target :=
      fun z hz => (HolderGerm.holderAt_comp_symm hr1.le v e hz).contDiffAt.contDiffWithinAt
    rw [hv] at hc
    exact hc.of_le (by exact_mod_cast Nat.le_add_right j 2)
  · rw [hu' y]
    field_simp
    ring

/-! ### The maximum principle -/

/-- **Maximum principle for `1 - sΔ_ω`**: if `v - sΔ_ω v = φ` with `s ≥ 0` and `φ ≤ B`, then
`v ≤ B`. -/
theorem le_of_sub_laplacian_eq [CompactSpace Y] (w : KahlerBackground N Y) {v φ : Y → ℝ}
    (hv : ChartSmooth (n := N) v) {s : ℝ} (hs : 0 ≤ s)
    (heq : ∀ y, v y - s * laplacian w.form.val v y = φ y) {B : ℝ} (hB : ∀ y, φ y ≤ B) (y : Y) :
    v y ≤ B := by
  have : Nonempty Y := ⟨y⟩
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    (YauUniformEstimate.continuous_of_chartSmooth hv).continuousOn
  have hmax : ∀ x, v x ≤ v y₀ := fun x => hy₀ (mem_univ x)
  have hL := laplacian_nonpos_of_isMax w.isKahler.1 hv hmax
  have h := heq y₀
  have : v y₀ ≤ φ y₀ := by nlinarith
  exact (hmax y).trans (this.trans (hB y₀))

/-- Two-sided form of the maximum principle: `|v| ≤ B` if `|φ| ≤ B`. -/
theorem abs_le_of_sub_laplacian_eq [CompactSpace Y] (w : KahlerBackground N Y) {v φ : Y → ℝ}
    (hv : ChartSmooth (n := N) v) {s : ℝ} (hs : 0 ≤ s)
    (heq : ∀ y, v y - s * laplacian w.form.val v y = φ y) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (y : Y) : |v y| ≤ B := by
  have hvn : ChartSmooth (n := N) (fun x => (-1) * v x) := fun e => contDiffOn_const.mul (hv e)
  have hneg : ∀ x, (-1) * v x - s * laplacian w.form.val (fun x => (-1) * v x) x = -φ x := by
    intro x
    rw [laplacian_const_mul _ hv, ← heq x]
    ring
  have h1 := le_of_sub_laplacian_eq w hv hs heq (fun x => (abs_le.mp (hB x)).2) y
  have h2 := le_of_sub_laplacian_eq w hvn hs hneg (fun x => by linarith [(abs_le.mp (hB x)).1]) y
  rw [abs_le]
  constructor <;> linarith

/-! ### Duality -/

variable [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- A continuous function whose integral against every smooth `χ ≥ 0` is `≤ 0` is `≤ 0`. -/
theorem le_of_integral_mul_nonpos (w : KahlerBackground N Y) {h : Y → ℝ} (hh : Continuous h)
    (H : ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
      ∫ y, h y * χ y ∂(kahlerVolume w) ≤ 0) (y : Y) : h y ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set U : TopologicalSpace.Opens Y := ⟨{x | h y / 2 < h x}, isOpen_lt continuous_const hh⟩
  have hyU : y ∈ U := by show h y / 2 < h y; linarith
  obtain ⟨χ, hχs, hχ0, -, hχU, -, hχ1⟩ := ChartPartition.exists_chartSmooth_bump (n := N) y U hyU
  have hχc := YauUniformEstimate.continuous_of_chartSmooth hχs
  -- `h χ ≥ (h y / 2) χ`
  have hpt : ∀ x, h y / 2 * χ x ≤ h x * χ x := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact mul_le_mul_of_nonneg_right (hχU hx).le (hχ0 x)
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  -- `∫ χ > 0`
  obtain ⟨O, hOy, hO, hO1⟩ : ∃ O : Set Y, y ∈ O ∧ IsOpen O ∧ ∀ x ∈ O, 1 / 2 < χ x := by
    have hc : ∀ᶠ x in 𝓝 y, 1 / 2 < χ x := by
      filter_upwards [hχ1] with x hx
      rw [hx]; norm_num
    obtain ⟨O, hO1, hO, hOy⟩ := eventually_nhds_iff.mp hc
    exact ⟨O, hOy, hO, hO1⟩
  have hvol := kahlerVolume_pos_of_isOpen w hO ⟨y, hOy⟩
  have hint : 0 < ∫ x, χ x ∂(kahlerVolume w) := by
    have h1 : ∫ x in O, (1 / 2 : ℝ) ∂(kahlerVolume w) ≤ ∫ x in O, χ x ∂(kahlerVolume w) :=
      setIntegral_mono_on (integrable_const (1 / 2 : ℝ)).integrableOn
        (integral_continuous hχc _).integrableOn
        hO.measurableSet fun x hx => (hO1 x hx).le
    have h2 : ∫ x in O, χ x ∂(kahlerVolume w) ≤ ∫ x, χ x ∂(kahlerVolume w) :=
      setIntegral_le_integral (integral_continuous hχc _) (Eventually.of_forall hχ0)
    rw [setIntegral_const, smul_eq_mul] at h1
    have h3 : 0 < (kahlerVolume w).real O := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hvol.ne' (measure_ne_top _ _)
    nlinarith
  have hle : ∫ x, h y / 2 * χ x ∂(kahlerVolume w) ≤ ∫ x, h x * χ x ∂(kahlerVolume w) :=
    integral_mono (integral_continuous (continuous_const.mul hχc) _)
      (integral_continuous (hh.mul hχc) _) hpt
  have e : ∫ x, h y / 2 * χ x ∂(kahlerVolume w) = h y / 2 * ∫ x, χ x ∂(kahlerVolume w) :=
    integral_const_mul _ _
  rw [e] at hle
  have := H χ hχs hχ0
  nlinarith

/-- **Duality estimate.**  If `Δ_ω f ≤ S` in the sense of distributions (`f` continuous),
`φ` is smooth with `|φ - f| ≤ δ`, `s > 0`, and `g - sΔ_ω g = φ`, then `g - φ ≤ sS + 2δ`. -/
theorem sub_le_of_resolvent (w : KahlerBackground N Y) {f : Y → ℝ} (hf : Continuous f) {S : ℝ}
    (hS : LaplacianLE w f S) {φ g : Y → ℝ} (hφ : ChartSmooth (n := N) φ)
    (hg : ChartSmooth (n := N) g) {s δ : ℝ} (hs : 0 < s) (hφf : ∀ y, |φ y - f y| ≤ δ)
    (heq : ∀ y, g y - s * laplacian w.form.val g y = φ y) (y : Y) :
    g y - φ y ≤ s * S + 2 * δ := by
  have hcφ := YauUniformEstimate.continuous_of_chartSmooth hφ
  have hcg := YauUniformEstimate.continuous_of_chartSmooth hg
  have hL := fun {u : Y → ℝ} (hu : ChartSmooth (n := N) u) =>
    continuous_laplacian_of_chartSmooth w.isKahler.1 hu
  have key : ∀ χ : Y → ℝ, ChartSmooth (n := N) χ → (∀ y, 0 ≤ χ y) →
      ∫ x, (g x - φ x - (s * S + 2 * δ)) * χ x ∂(kahlerVolume w) ≤ 0 := by
    intro χ hχ hχ0
    obtain ⟨χ', hχ's, hχ'eq⟩ := exists_resolvent w hs hχ
    have hχ'0 : ∀ x, 0 ≤ χ' x := fun x => by
      have h := le_of_sub_laplacian_eq w (v := fun x => (-1) * χ' x)
        (fun e => contDiffOn_const.mul (hχ's e)) hs.le (φ := fun x => -χ x)
        (fun x => by rw [laplacian_const_mul _ hχ's, ← hχ'eq x]; ring)
        (B := 0) (fun x => by linarith [hχ0 x]) x
      linarith
    have hcχ := YauUniformEstimate.continuous_of_chartSmooth hχ
    have hcχ' := YauUniformEstimate.continuous_of_chartSmooth hχ's
    -- `∫ χ' = ∫ χ`
    have hLχ' := hL hχ's
    have hmass : ∫ x, χ' x ∂(kahlerVolume w) = ∫ x, χ x ∂(kahlerVolume w) := by
      have h1 : ∫ x, χ x ∂(kahlerVolume w) = ∫ x, (χ' x - s * laplacian w.form.val χ' x)
          ∂(kahlerVolume w) := integral_congr_ae (Eventually.of_forall fun x => (hχ'eq x).symm)
      have e1 : ∫ x, (χ' x - s * laplacian w.form.val χ' x) ∂(kahlerVolume w) =
          ∫ x, χ' x ∂(kahlerVolume w) - ∫ x, s * laplacian w.form.val χ' x ∂(kahlerVolume w) :=
        integral_sub (integral_continuous hcχ' _) (integral_continuous (continuous_const.mul hLχ') _)
      have e2 : ∫ x, s * laplacian w.form.val χ' x ∂(kahlerVolume w) =
          s * ∫ x, laplacian w.form.val χ' x ∂(kahlerVolume w) := integral_const_mul s _
      have e3 : ∫ x, laplacian w.form.val χ' x ∂(kahlerVolume w) = 0 :=
        integral_laplacian_eq_zero w (chartSmooth_two' hχ's)
      rw [e3, mul_zero] at e2
      linarith
    -- `∫ g χ = ∫ φ χ'`
    have hgχ : ∫ x, g x * χ x ∂(kahlerVolume w) = ∫ x, φ x * χ' x ∂(kahlerVolume w) := by
      have h1 : ∫ x, g x * χ x ∂(kahlerVolume w) = ∫ x, (g x * χ' x -
          s * (g x * laplacian w.form.val χ' x)) ∂(kahlerVolume w) :=
        integral_congr_ae (Eventually.of_forall fun x => by
          show g x * χ x = g x * χ' x - s * (g x * laplacian w.form.val χ' x)
          rw [← hχ'eq x]; ring)
      have h2 : ∫ x, φ x * χ' x ∂(kahlerVolume w) = ∫ x, (g x * χ' x -
          s * (χ' x * laplacian w.form.val g x)) ∂(kahlerVolume w) :=
        integral_congr_ae (Eventually.of_forall fun x => by
          show φ x * χ' x = g x * χ' x - s * (χ' x * laplacian w.form.val g x)
          rw [← heq x]; ring)
      have e1 : ∫ x, (g x * χ' x - s * (g x * laplacian w.form.val χ' x)) ∂(kahlerVolume w) =
          ∫ x, g x * χ' x ∂(kahlerVolume w) -
            ∫ x, s * (g x * laplacian w.form.val χ' x) ∂(kahlerVolume w) :=
        integral_sub (integral_continuous (hcg.mul hcχ') _)
          (integral_continuous (continuous_const.mul (hcg.mul hLχ')) _)
      have e2 : ∫ x, (g x * χ' x - s * (χ' x * laplacian w.form.val g x)) ∂(kahlerVolume w) =
          ∫ x, g x * χ' x ∂(kahlerVolume w) -
            ∫ x, s * (χ' x * laplacian w.form.val g x) ∂(kahlerVolume w) :=
        integral_sub (integral_continuous (hcg.mul hcχ') _)
          (integral_continuous (continuous_const.mul (hcχ'.mul (hL hg))) _)
      have e3 : ∫ x, s * (g x * laplacian w.form.val χ' x) ∂(kahlerVolume w) =
          s * ∫ x, g x * laplacian w.form.val χ' x ∂(kahlerVolume w) := integral_const_mul s _
      have e4 : ∫ x, s * (χ' x * laplacian w.form.val g x) ∂(kahlerVolume w) =
          s * ∫ x, χ' x * laplacian w.form.val g x ∂(kahlerVolume w) := integral_const_mul s _
      have e5 := integral_mul_laplacian_comm w hg hχ's
      rw [h1, h2, e1, e2, e3, e4, e5]
    -- `∫ φ χ' - ∫ φ χ = s ∫ φ Δχ'`
    have hφχ : ∫ x, φ x * χ' x ∂(kahlerVolume w) - ∫ x, φ x * χ x ∂(kahlerVolume w) =
        s * ∫ x, φ x * laplacian w.form.val χ' x ∂(kahlerVolume w) := by
      have e1 : ∫ x, (φ x * χ' x - φ x * χ x) ∂(kahlerVolume w) =
          ∫ x, φ x * χ' x ∂(kahlerVolume w) - ∫ x, φ x * χ x ∂(kahlerVolume w) :=
        integral_sub (integral_continuous (hcφ.mul hcχ') _) (integral_continuous (hcφ.mul hcχ) _)
      have e2 : ∫ x, s * (φ x * laplacian w.form.val χ' x) ∂(kahlerVolume w) =
          s * ∫ x, φ x * laplacian w.form.val χ' x ∂(kahlerVolume w) := integral_const_mul s _
      have e3 : ∫ x, (φ x * χ' x - φ x * χ x) ∂(kahlerVolume w) =
          ∫ x, s * (φ x * laplacian w.form.val χ' x) ∂(kahlerVolume w) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have := hχ'eq x
        show φ x * χ' x - φ x * χ x = s * (φ x * laplacian w.form.val χ' x)
        rw [show χ x = χ' x - s * laplacian w.form.val χ' x by linarith]
        ring
      linarith
    -- the two estimates
    have hfS : ∫ x, f x * laplacian w.form.val χ' x ∂(kahlerVolume w) ≤
        S * ∫ x, χ' x ∂(kahlerVolume w) := hS χ' hχ's hχ'0
    have herr : s * ∫ x, (φ x - f x) * laplacian w.form.val χ' x ∂(kahlerVolume w) ≤
        δ * (∫ x, χ' x ∂(kahlerVolume w) + ∫ x, χ x ∂(kahlerVolume w)) := by
      have e1 : ∫ x, s * ((φ x - f x) * laplacian w.form.val χ' x) ∂(kahlerVolume w) =
          s * ∫ x, (φ x - f x) * laplacian w.form.val χ' x ∂(kahlerVolume w) :=
        integral_const_mul s _
      have e2 : ∫ x, δ * (χ' x + χ x) ∂(kahlerVolume w) =
          δ * ∫ x, (χ' x + χ x) ∂(kahlerVolume w) := integral_const_mul δ _
      have e3 : ∫ x, (χ' x + χ x) ∂(kahlerVolume w) =
          ∫ x, χ' x ∂(kahlerVolume w) + ∫ x, χ x ∂(kahlerVolume w) :=
        integral_add (integral_continuous hcχ' _) (integral_continuous hcχ _)
      have hpt : ∀ x, s * ((φ x - f x) * laplacian w.form.val χ' x) ≤ δ * (χ' x + χ x) := by
        intro x
        have h1 : s * laplacian w.form.val χ' x = χ' x - χ x := by linarith [hχ'eq x]
        have h2 : s * ((φ x - f x) * laplacian w.form.val χ' x) = (φ x - f x) * (χ' x - χ x) := by
          rw [← h1]; ring
        rw [h2]
        have h3 := abs_le.mp (hφf x)
        have := hχ'0 x
        have := hχ0 x
        nlinarith
      have hmono : ∫ x, s * ((φ x - f x) * laplacian w.form.val χ' x) ∂(kahlerVolume w) ≤
          ∫ x, δ * (χ' x + χ x) ∂(kahlerVolume w) :=
        integral_mono (integral_continuous (continuous_const.mul
          ((hcφ.sub hf).mul hLχ')) (kahlerVolume w)) (integral_continuous (continuous_const.mul
            (hcχ'.add hcχ)) (kahlerVolume w)) hpt
      calc s * ∫ x, (φ x - f x) * laplacian w.form.val χ' x ∂(kahlerVolume w)
          = ∫ x, s * ((φ x - f x) * laplacian w.form.val χ' x) ∂(kahlerVolume w) := e1.symm
        _ ≤ ∫ x, δ * (χ' x + χ x) ∂(kahlerVolume w) := hmono
        _ = δ * ∫ x, (χ' x + χ x) ∂(kahlerVolume w) := e2
        _ = δ * (∫ x, χ' x ∂(kahlerVolume w) + ∫ x, χ x ∂(kahlerVolume w)) :=
          congrArg (δ * ·) e3
    have hsplit : ∫ x, φ x * laplacian w.form.val χ' x ∂(kahlerVolume w) =
        ∫ x, f x * laplacian w.form.val χ' x ∂(kahlerVolume w) +
          ∫ x, (φ x - f x) * laplacian w.form.val χ' x ∂(kahlerVolume w) := by
      have e1 : ∫ x, (f x * laplacian w.form.val χ' x + (φ x - f x) * laplacian w.form.val χ' x)
          ∂(kahlerVolume w) = ∫ x, f x * laplacian w.form.val χ' x ∂(kahlerVolume w) +
            ∫ x, (φ x - f x) * laplacian w.form.val χ' x ∂(kahlerVolume w) :=
        integral_add (integral_continuous (hf.mul hLχ') _)
          (integral_continuous ((hcφ.sub hf).mul hLχ') _)
      rw [← e1]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      show φ x * laplacian w.form.val χ' x =
        f x * laplacian w.form.val χ' x + (φ x - f x) * laplacian w.form.val χ' x
      ring
    have hexp : ∫ x, (g x - φ x - (s * S + 2 * δ)) * χ x ∂(kahlerVolume w) =
        ∫ x, g x * χ x ∂(kahlerVolume w) - ∫ x, φ x * χ x ∂(kahlerVolume w) -
          (s * S + 2 * δ) * ∫ x, χ x ∂(kahlerVolume w) := by
      have e1 : ∫ x, (g x * χ x - φ x * χ x) ∂(kahlerVolume w) =
          ∫ x, g x * χ x ∂(kahlerVolume w) - ∫ x, φ x * χ x ∂(kahlerVolume w) :=
        integral_sub (integral_continuous (hcg.mul hcχ) _) (integral_continuous (hcφ.mul hcχ) _)
      have e2 : ∫ x, ((g x * χ x - φ x * χ x) - (s * S + 2 * δ) * χ x) ∂(kahlerVolume w) =
          ∫ x, (g x * χ x - φ x * χ x) ∂(kahlerVolume w) -
            ∫ x, (s * S + 2 * δ) * χ x ∂(kahlerVolume w) :=
        integral_sub (integral_continuous ((hcg.mul hcχ).sub (hcφ.mul hcχ)) _)
          (integral_continuous (continuous_const.mul hcχ) _)
      have e3 : ∫ x, (s * S + 2 * δ) * χ x ∂(kahlerVolume w) =
          (s * S + 2 * δ) * ∫ x, χ x ∂(kahlerVolume w) := integral_const_mul _ _
      have e4 : ∫ x, (g x - φ x - (s * S + 2 * δ)) * χ x ∂(kahlerVolume w) =
          ∫ x, ((g x * χ x - φ x * χ x) - (s * S + 2 * δ) * χ x) ∂(kahlerVolume w) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show (g x - φ x - (s * S + 2 * δ)) * χ x = (g x * χ x - φ x * χ x) - (s * S + 2 * δ) * χ x
        ring
      rw [e4, e2, e1, e3]
    rw [hexp, hgχ]
    have hχint : 0 ≤ ∫ x, χ x ∂(kahlerVolume w) := integral_nonneg hχ0
    rw [hmass] at hfS herr
    have hs0 := hs.le
    nlinarith
  have h : g y - φ y - (s * S + 2 * δ) ≤ 0 :=
    le_of_integral_mul_nonpos w (h := fun x => g x - φ x - (s * S + 2 * δ))
      ((hcg.sub hcφ).sub continuous_const) key y
  linarith

/-! ### Smoothing -/

/-- **Smoothing with a one-sided Laplacian bound.**  A continuous `f` with `Δ_ω f ≤ S` in the
sense of distributions is, for every `η > 0`, within `4η` of a chart-smooth `g` with
`Δ_ω g ≤ S + 2η` pointwise. -/
theorem exists_smooth_laplacian_le (w : KahlerBackground N Y) {f : Y → ℝ} (hf : Continuous f)
    {S : ℝ} (hS : LaplacianLE w f S) {η : ℝ} (hη : 0 < η) :
    ∃ g : Y → ℝ, ChartSmooth (n := N) g ∧ (∀ y, |g y - f y| ≤ 4 * η) ∧
      ∀ y, laplacian w.form.val g y ≤ S + 2 * η := by
  -- a first smooth approximation and the size of its Laplacian
  obtain ⟨φ₀, hφ₀, hφ₀f⟩ := SGPT.Envelopes.DNTReg.exists_chartSmooth_abs_sub_lt (N := N) hf hη
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_laplacian_of_chartSmooth w.isKahler.1 hφ₀).continuousOn
  have hB₀' : ∀ y, |laplacian w.form.val φ₀ y| ≤ |B₀| := fun y => by
    have := hB₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  set s : ℝ := min 1 (η / (|B₀| + 1)) with hsdef
  have hs : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsB : s * |B₀| ≤ η := by
    have h1 : s ≤ η / (|B₀| + 1) := min_le_right _ _
    have h2 : s * (|B₀| + 1) ≤ η := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg B₀]
  -- the second smooth approximation, much closer
  obtain ⟨φ, hφ, hφf⟩ := SGPT.Envelopes.DNTReg.exists_chartSmooth_abs_sub_lt (N := N) hf
    (mul_pos hη hs)
  obtain ⟨g, hg, hgeq⟩ := exists_resolvent w hs hφ
  obtain ⟨g₀, hg₀, hg₀eq⟩ := exists_resolvent w hs hφ₀
  refine ⟨g, hg, fun y => ?_, fun y => ?_⟩
  · -- `|g - g₀| ≤ |φ - φ₀|`, `|g₀ - φ₀| ≤ s sup |Δφ₀|`
    have hD : ChartSmooth (n := N) (fun x => g x - g₀ x) := fun e => (hg e).sub (hg₀ e)
    have hDeq : ∀ x, (g x - g₀ x) - s * laplacian w.form.val (fun x => g x - g₀ x) x =
        φ x - φ₀ x := fun x => by
      rw [laplacian_sub _ hg hg₀, ← hgeq x, ← hg₀eq x]; ring
    have h1 := abs_le_of_sub_laplacian_eq w hD hs.le hDeq (B := η * s + η) (fun x => by
      have := hφf x; have := hφ₀f x
      calc |φ x - φ₀ x| ≤ |φ x - f x| + |φ₀ x - f x| := by
            have h := abs_sub_le (φ x) (f x) (φ₀ x)
            rwa [abs_sub_comm (f x) (φ₀ x)] at h
        _ ≤ η * s + η := by linarith) y
    have hE : ChartSmooth (n := N) (fun x => g₀ x - φ₀ x) := fun e => (hg₀ e).sub (hφ₀ e)
    have hEeq : ∀ x, (g₀ x - φ₀ x) - s * laplacian w.form.val (fun x => g₀ x - φ₀ x) x =
        s * laplacian w.form.val φ₀ x := fun x => by
      rw [laplacian_sub _ hg₀ hφ₀]
      have := hg₀eq x
      linarith
    have h2 := abs_le_of_sub_laplacian_eq w hE hs.le hEeq (B := s * |B₀|) (fun x => by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left (hB₀' x) hs.le) y
    have h3 := (hφ₀f y).le
    have hηs : η * s ≤ η := by nlinarith
    calc |g y - f y| = |(g y - g₀ y) + (g₀ y - φ₀ y) + (φ₀ y - f y)| := by ring_nf
      _ ≤ |g y - g₀ y| + |g₀ y - φ₀ y| + |φ₀ y - f y| := abs_add_three _ _ _
      _ ≤ 4 * η := by linarith
  · -- `Δg = (g - φ)/s ≤ S + 2η`
    have hsub := sub_le_of_resolvent w hf hS hφ hg hs (δ := η * s) (fun x => (hφf x).le) hgeq y
    have hΔ : laplacian w.form.val g y = (g y - φ y) / s := by
      rw [eq_div_iff hs.ne']; linarith [hgeq y]
    rw [hΔ, div_le_iff₀ hs]
    nlinarith

end SGPT.Envelopes.LapClass
