import SGPT.Foundations.Analysis.Pending.YauClosedness
import SGPT.Foundations.Analysis.Pending.MongeAmpereSupBound
import SGPT.Foundations.Analysis.Pending.YauUniformEstimate
import SGPT.Foundations.Analysis.Pending.YauNormalizingConstant

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The continuity method for Yau's theorem

Let `A` be a Kähler background on a compact connected complex manifold `Y` of dimension `N`, `F`
chart-smooth.  Assume the uniform `C^{2,r}` estimate along the path (`hT2`, TN-CLASSICAL's piece `T2`
of the statement under discussion, `YauHolderBound.exists_norm_ofChartSmooth_le` once it lands).

* `exists_smooth_of_mem_Icc` (blueprint `bou:yau-closedness`): for `0 < ε ≤ 1` and every
  `t ∈ [0, 1]` there is a chart-smooth `φ` with `A + ddᶜφ` Kähler and
  `(A + ddᶜφ)^N = e^{tF + εφ} A^N`.  The set of such `t` is open
  (`YauSmoothOpenness.exists_smooth_ma_eq_near`), closed in `[0, 1]` (the `C⁰` bound
  `MongeAmpereSupBound.abs_le_of_mongeAmpere_eq_exp` gives `|φ| ≤ sup|F| / ε`, then `hT2` and
  `YauClosedness.exists_smooth_of_tendsto`) and contains `0` (`φ = 0`); `[0, 1]` is connected.
* `exists_smooth_eq_exp_add` (blueprint `bou:yau-eps-limit`): `ε → 0` at `t = 1`.  For `ε_k = 1/(k+1)`
  normalise `ψ_k = φ_k - max φ_k`, `κ_k = ε_k max φ_k`, so that
  `(A + ddᶜψ_k)^N = e^{F + ε_kψ_k + κ_k} A^N`; `|κ_k| ≤ sup|F|` (`C⁰` bound), `|ψ_k| ≤ C` (Błocki's
  uniform estimate `YauUniformEstimate.exists_sub_le_of_mongeAmpere_le`), `hT2` bounds `ψ_k` in
  `C^{2,r}`, and a subsequence with `κ_k → κ` converges
  (`YauClosedness.exists_smooth_of_tendsto`): `(A + ddᶜφ)^N = e^{F + κ} A^N`.
* `exists_kahler_mongeAmpere_eq_exp_of_estimates` (blueprint `bou:yau`): with `κ = 0` by class
  invariance (`hT3`), Yau's theorem in the form of `YauTheorem.exists_kahler_mongeAmpere_eq_exp`;
  `exists_kahler_mongeAmpere_eq_exp_of_holderBound`: the same with `hT3` discharged by TN-CLASSICAL's
  `T3` (`YauNormalizingConstant.eq_zero_of_mongeAmpere_eq_exp_add`, 6dee22fd), under the hypotheses of
  `YauTheorem.exists_kahler_mongeAmpere_eq_exp` (`0 < N`, `∫ e^F A^N = ∫ A^N`).

TN.4 B5, N5 = P3(c)–(e) of the the proof of Yau's theorem.  The
hypothesis `hT2` (and `hT3` of the first form) is exactly the statement of the statement under discussion specialised to
the fixed `Y, A, F` (and Hölder atlas `HA`, exponent `r`); it is not a named input: the in-place
discharge of `YauTheoremInterface:80` waits until `T2` is proved.
-/

noncomputable section

open Set Filter Topology Metric Function MeasureTheory
open scoped NNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.YauContinuityMethod

open FirstPass FirstPass.MongeAmpere ManifoldTubePositivity PositiveClasses

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- A chart-smooth function on a compact manifold is bounded. -/
theorem exists_abs_le [CompactSpace Y] {F : Y → ℝ} (hF : ChartSmooth (n := N) F) :
    ∃ B : ℝ, ∀ y, |F y| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (YauUniformEstimate.continuous_of_chartSmooth hF).continuousOn
  exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y (mem_univ y)⟩

/-- The density of a Kähler form is positive in every chart. -/
theorem actualTopPowerDensity_pos (A : KahlerBackground N Y) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    0 < actualTopPowerDensity (A.form.val.coeff e z) := by
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det (A.isKahler.1 e z hz).1]
  have hd : 0 < (normalizedHermitianMatrix (A.form.val.coeff e z)).det.re :=
    (Complex.pos_iff.mp (KahlerLaplacianChart.posDef_coeff A.isKahler.1 hz).det_pos).1
  positivity

/-- `A + ddᶜ0 = A`. -/
theorem add_ddcClosedForm_zero (A : KahlerBackground N Y)
    (h0 : ChartSmooth (n := N) (fun _ : Y => (0 : ℝ))) :
    A.form + ddcClosedForm (fun _ : Y => (0 : ℝ)) h0 = A.form := by
  ext e z
  rw [ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff]
  have : smoothDDC (fun _ : ComplexModel N => (0 : ℝ)) z = 0 :=
    GlobalPotentialTransforms.smoothDDC_const 0 z
  simp only [this, add_zero]

/-- The coefficients of `A + ddᶜ(φ - c)` and `A + ddᶜφ` agree on chart targets. -/
theorem coeff_add_ddcClosedForm_sub_const (A : KahlerBackground N Y) {φ : Y → ℝ}
    (hφ : ChartSmooth (n := N) φ) (c : ℝ) (hψ : ChartSmooth (n := N) (fun y => φ y - c))
    (e : ComplexChart N Y) {z : ComplexModel N} (hz : z ∈ e.val.target) :
    (A.form + ddcClosedForm (fun y => φ y - c) hψ).val.coeff e z =
      (A.form + ddcClosedForm φ hφ).val.coeff e z := by
  rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add, ddcClosedForm_coeff,
    ddcClosedForm_coeff, PositiveClasses.smoothDDC_sub e.val.open_target (hφ e) contDiffOn_const hz,
    GlobalPotentialTransforms.smoothDDC_const, sub_zero]

/-! ### The path at fixed `ε` -/

/-- **The `ε`-path reaches `t = 1`** (blueprint `bou:yau-closedness`): for `0 < ε ≤ 1`, under the
uniform `C^{2,r}` estimate `hT2`, every `t ∈ [0, 1]` has a chart-smooth solution of
`(A + ddᶜφ)^N = e^{tF + εφ} A^N` with `A + ddᶜφ` Kähler. -/
theorem exists_smooth_of_mem_Icc [CompactSpace Y] (A : KahlerBackground N Y) (HA : HolderAtlas N Y)
    {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ} (hF : ChartSmooth (n := N) F)
    (hT2 : ∀ S K : ℝ, ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 → |κ| ≤ K →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ y, |φ y| ≤ S) →
      ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ‖ ≤ C)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z)) *
            actualTopPowerDensity (A.form.val.coeff e z) := by
  let P : ℝ → Prop := fun t => ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
    (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
    ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
        Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z)) *
          actualTopPowerDensity (A.form.val.coeff e z)
  -- openness
  have hopen : IsOpen {t : ℝ | P t} := by
    rw [Metric.isOpen_iff]
    rintro t₀ ⟨φ₀, hφ₀, hK₀, hd₀⟩
    obtain ⟨δ, hδ, h⟩ := YauSmoothOpenness.exists_smooth_ma_eq_near A hF hε0 hφ₀ hK₀ hd₀
    refine ⟨δ, hδ, fun t ht => h t ?_⟩
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  -- closedness in `[0, 1]`
  obtain ⟨B, hB⟩ := exists_abs_le hF
  obtain ⟨C, hC⟩ := hT2 (B / ε) 0
  have hseq : ∀ (t : ℕ → ℝ) (t₀ : ℝ), (∀ j, t j ∈ Icc (0 : ℝ) 1) → (∀ j, P (t j)) →
      Tendsto t atTop (𝓝 t₀) → P t₀ := by
    intro t t₀ htI hP hlim
    choose φ hφ hK hd using hP
    have hbd : ∀ j y, |φ j y| ≤ B / ε := by
      intro j y
      have hH : ∀ y, |t j * F y| ≤ B := fun y => by
        rw [abs_mul]
        have h1 : |t j| ≤ 1 := abs_le.mpr ⟨by linarith [(htI j).1], (htI j).2⟩
        calc |t j| * |F y| ≤ 1 * |F y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ ≤ B := by rw [one_mul]; exact hB y
      have h := MongeAmpereSupBound.abs_le_of_mongeAmpere_eq_exp A (H := fun y => t j * F y)
        (hφ j) hε0 (hK j) (hd j) hH y
      rw [le_div_iff₀ hε0]
      linarith
    have hd0 : ∀ j (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm (φ j) (hφ j)).val.coeff e z) =
          Real.exp (t j * F (e.val.symm z) + (fun _ : ℕ => ε) j * φ j (e.val.symm z) +
            (fun _ : ℕ => (0 : ℝ)) j) * actualTopPowerDensity (A.form.val.coeff e z) := by
      intro j e z hz
      rw [hd j e z hz, add_zero]
    have hCj : ∀ j, ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le (φ j) (hφ j)‖ ≤
        C := fun j =>
      hC (φ j) (hφ j) (t j) ε 0 (htI j) ⟨hε0.le, hε1⟩ (by simp) (hK j)
        (fun e z hz => by rw [hd j e z hz, add_zero]) (hbd j)
    obtain ⟨φ₀, hφ₀, hK₀, hd₀⟩ := YauClosedness.exists_smooth_of_tendsto A hr0 hr1 hF hlim
      (tendsto_const_nhds (x := ε)) (tendsto_const_nhds (x := (0 : ℝ))) φ hφ hK hd0 hCj
    exact ⟨φ₀, hφ₀, hK₀, fun e z hz => by rw [hd₀ e z hz, add_zero]⟩
  -- `t = 0`
  have h0 : P 0 := by
    have h0s : ChartSmooth (n := N) (fun _ : Y => (0 : ℝ)) := fun e => contDiffOn_const
    refine ⟨fun _ => 0, h0s, ?_, fun e z hz => ?_⟩
    · rw [add_ddcClosedForm_zero A h0s]
      exact A.isKahler
    · rw [add_ddcClosedForm_zero A h0s]
      simp
  -- connectedness of `[0, 1]`
  have : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  let S : Set (Icc (0 : ℝ) 1) := {x | P x.1}
  have hSo : IsOpen S := hopen.preimage continuous_subtype_val
  have hSc : IsClosed S := by
    refine IsSeqClosed.isClosed fun x x₀ hx hlim => ?_
    exact hseq (fun j => (x j).1) x₀.1 (fun j => (x j).2) hx
      ((continuous_subtype_val.tendsto _).comp hlim)
  have hS : S = univ := IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨⟨0, left_mem_Icc.2 zero_le_one⟩, h0⟩
  have hmem : (⟨t, ht⟩ : Icc (0 : ℝ) 1) ∈ S := hS ▸ mem_univ _
  exact hmem

/-! ### `ε → 0` -/

/-- **The limit `ε → 0`** (blueprint `bou:yau-eps-limit`): under the uniform `C^{2,r}` estimate
`hT2`, there are a chart-smooth `φ` and a constant `κ` with `A + ddᶜφ` Kähler and
`(A + ddᶜφ)^N = e^{F + κ} A^N`. -/
theorem exists_smooth_eq_exp_add [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y)
    (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F)
    (hT2 : ∀ S K : ℝ, ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 → |κ| ≤ K →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ y, |φ y| ≤ S) →
      ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ‖ ≤ C) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (κ : ℝ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (F (e.val.symm z) + κ) * actualTopPowerDensity (A.form.val.coeff e z) := by
  obtain ⟨B, hB⟩ := exists_abs_le hF
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hεdef
  have hε0 : ∀ k, 0 < ε k := fun k => Nat.one_div_pos_of_nat
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    rw [hεdef, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the solutions at `t = 1`
  have hsol := fun k => exists_smooth_of_mem_Icc A HA hr0 hr1 hF hT2 (hε0 k) (hε1 k)
    (right_mem_Icc.2 zero_le_one)
  choose φ hφ hK hd using hsol
  -- maximum points
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  have hmax : ∀ k, ∃ y, ∀ x, φ k x ≤ φ k y := fun k => by
    obtain ⟨y, -, hy⟩ := isCompact_univ.exists_isMaxOn ⟨y₀, mem_univ _⟩
      (YauUniformEstimate.continuous_of_chartSmooth (hφ k)).continuousOn
    exact ⟨y, fun x => hy (mem_univ x)⟩
  choose ym hym using hmax
  -- the `C⁰` bound at fixed `ε`
  have hT1 : ∀ k y, ε k * |φ k y| ≤ B := fun k =>
    MongeAmpereSupBound.abs_le_of_mongeAmpere_eq_exp A (H := fun y => 1 * F y) (hφ k) (hε0 k)
      (hK k) (hd k) (fun y => by rw [one_mul]; exact hB y)
  -- normalisation
  set ψ : ℕ → Y → ℝ := fun k y => φ k y - φ k (ym k) with hψdef
  have hψ : ∀ k, ChartSmooth (n := N) (ψ k) := fun k e => (hφ k e).sub contDiffOn_const
  set κ : ℕ → ℝ := fun k => ε k * φ k (ym k) with hκdef
  have hκB : ∀ k, |κ k| ≤ B := fun k => by
    rw [hκdef, abs_mul, abs_of_pos (hε0 k)]
    exact hT1 k (ym k)
  have hco : ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      (A.form + ddcClosedForm (ψ k) (hψ k)).val.coeff e z =
        (A.form + ddcClosedForm (φ k) (hφ k)).val.coeff e z := fun k e z hz =>
    coeff_add_ddcClosedForm_sub_const A (hφ k) (φ k (ym k)) (hψ k) e hz
  have hKψ : ∀ k, (A.form + ddcClosedForm (ψ k) (hψ k)).val.IsKahler := fun k =>
    YauSmoothOpenness.isKahler_of_posDef A (hψ k) fun e z hz => by
      rw [← YauOpenness.normalizedHermitianMatrix_add_ddc A.form (hψ k) hz, hco k e z hz]
      exact KahlerLaplacianChart.posDef_coeff (hK k).1 hz
  have hdψ : ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      actualTopPowerDensity ((A.form + ddcClosedForm (ψ k) (hψ k)).val.coeff e z) =
        Real.exp ((fun _ : ℕ => (1 : ℝ)) k * F (e.val.symm z) + ε k * ψ k (e.val.symm z) + κ k) *
          actualTopPowerDensity (A.form.val.coeff e z) := fun k e z hz => by
    rw [hco k e z hz, hd k e z hz, hψdef, hκdef]
    congr 2
    ring
  -- Błocki's uniform estimate
  obtain ⟨C₂, hC₂⟩ := YauUniformEstimate.exists_sub_le_of_mongeAmpere_le A (Real.exp (B + B))
  have hosc : ∀ k x y, φ k x - φ k y ≤ C₂ := fun k =>
    hC₂ (φ k) (hφ k) (KahlerBackground.isSemipositive ⟨_, hK k⟩) fun e z hz => by
      rw [hd k e z hz]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
        (actualTopPowerDensity_pos A hz).le
      have h1 := hB (e.val.symm z)
      have h2 := hT1 k (e.val.symm z)
      have h3 : ε k * φ k (e.val.symm z) ≤ ε k * |φ k (e.val.symm z)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hε0 k).le
      linarith [le_abs_self (F (e.val.symm z))]
  have hψb : ∀ k y, |ψ k y| ≤ C₂ := fun k y => by
    rw [hψdef, abs_le]
    constructor
    · linarith [hosc k (ym k) y]
    · linarith [hym k y, hosc k y y]
  -- the uniform `C^{2,r}` bound
  obtain ⟨C, hC⟩ := hT2 C₂ B
  have hCk : ∀ k, ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le (ψ k) (hψ k)‖ ≤
      C := fun k =>
    hC (ψ k) (hψ k) 1 (ε k) (κ k) (right_mem_Icc.2 zero_le_one) ⟨(hε0 k).le, hε1 k⟩ (hκB k)
      (hKψ k) (hdψ k) (hψb k)
  -- a convergent subsequence of `κ_k`
  obtain ⟨κ₀, -, τ, hτ, hκτ⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : ℝ))
    (r := B)) (x := κ) fun k => by
      rw [mem_closedBall, Real.dist_eq, sub_zero]
      exact hκB k
  obtain ⟨φ₀, hφ₀, hK₀, hd₀⟩ := YauClosedness.exists_smooth_of_tendsto A hr0 hr1 hF
    (t := fun _ => 1) (ε := ε ∘ τ) (κ := κ ∘ τ) tendsto_const_nhds
    (hεlim.comp hτ.tendsto_atTop) hκτ (fun j => ψ (τ j)) (fun j => hψ (τ j)) (fun j => hKψ (τ j))
    (fun j => hdψ (τ j)) (fun j => hCk (τ j))
  refine ⟨φ₀, hφ₀, κ₀, hK₀, fun e z hz => ?_⟩
  rw [hd₀ e z hz]
  simp only [one_mul, zero_mul, add_zero]

/-! ### Yau's theorem from the estimates -/

/-- **Yau's theorem from the estimates** (blueprint `bou:yau`): under the uniform `C^{2,r}` estimate
`hT2` and the class-invariance statement `hT3` (`κ = 0`), there is a chart-smooth `φ` with `A + ddᶜφ`
Kähler and `(A + ddᶜφ)^N = e^F A^N` in every chart. -/
theorem exists_kahler_mongeAmpere_eq_exp_of_estimates [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    {F : Y → ℝ} (hF : ChartSmooth (n := N) F)
    (hT2 : ∀ S K : ℝ, ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 → |κ| ≤ K →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ y, |φ y| ≤ S) →
      ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ‖ ≤ C)
    (hT3 : ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (κ : ℝ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (F (e.val.symm z) + κ) * actualTopPowerDensity (A.form.val.coeff e z)) →
      κ = 0) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (F (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z) := by
  obtain ⟨φ, hφ, κ, hK, hd⟩ := exists_smooth_eq_exp_add A HA hr0 hr1 hF hT2
  have hκ := hT3 φ hφ κ hK hd
  refine ⟨φ, hφ, hK, fun e z hz => ?_⟩
  rw [hd e z hz, hκ, add_zero]

/-- **Yau's theorem from the uniform `C^{2,r}` estimate** (blueprint `bou:yau`): under the hypotheses of
`YauTheorem.exists_kahler_mongeAmpere_eq_exp` and the uniform estimate `hT2` (TN-CLASSICAL's `T2`),
its conclusion; `κ = 0` by `YauNormalizingConstant.eq_zero_of_mongeAmpere_eq_exp_add`. -/
theorem exists_kahler_mongeAmpere_eq_exp_of_holderBound [CompactSpace Y] [ConnectedSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (hN : 0 < N) (A : KahlerBackground N Y) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F)
    (hnorm : ∫ y, Real.exp (F y) ∂(IntegrationCurrent.kahlerVolume A) =
      (IntegrationCurrent.kahlerVolume A).real univ)
    (HA : HolderAtlas N Y) {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (hT2 : ∀ S K : ℝ, ∃ C : ℝ, ∀ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ) (t ε κ : ℝ),
      t ∈ Icc (0 : ℝ) 1 → ε ∈ Icc (0 : ℝ) 1 → |κ| ≤ K →
      (A.form + ddcClosedForm φ hφ).val.IsKahler →
      (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (t * F (e.val.symm z) + ε * φ (e.val.symm z) + κ) *
            actualTopPowerDensity (A.form.val.coeff e z)) →
      (∀ y, |φ y| ≤ S) →
      ‖HolderAtlas.HolderMap.ofChartSmooth (A := HA) (k := 2) hr1.le φ hφ‖ ≤ C) :
    ∃ (φ : Y → ℝ) (hφ : ChartSmooth (n := N) φ),
      (A.form + ddcClosedForm φ hφ).val.IsKahler ∧
      ∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm φ hφ).val.coeff e z) =
          Real.exp (F (e.val.symm z)) * actualTopPowerDensity (A.form.val.coeff e z) :=
  exists_kahler_mongeAmpere_eq_exp_of_estimates A HA hr0 hr1 hF hT2 fun _ hφ _ hK hd =>
    YauNormalizingConstant.eq_zero_of_mongeAmpere_eq_exp_add hN A hφ hK hnorm hd

end SGPT.Foundations.Analysis.Pending.YauContinuityMethod
