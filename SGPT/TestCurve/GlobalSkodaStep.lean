import SGPT.TestCurve.GlobalSkodaSystem

/-!
# One step of the global Skoda division

Blueprint `claude-global-skoda.tex`, nodes `global-skoda:chart-division`, `global-skoda:step`.

Let `θ = c₁(L, h)` be Kähler, `w₁, …, w_r ∈ H⁰(X, L^d)`, `M ≥ n + 1` and `k > Md`. For a section
`σ ∈ H⁰(X, L^{d+k})` with `I(σ) = ∫_X |σ|²_{h^{d+k}} |w|^{-2(M+1)}_{h^d} dμ < ∞`:

1. in every chart ball of the cover, Skoda's local division with the smooth psh weight
   `(k - Md) φ_b` (`weightedLocalSkoda`) gives holomorphic `H_b` with `σ = ∑ⱼ wⱼ H_{b,j}` and
   `∫ |H_b|² W_b ≤ C (r, n) · A · I(σ)` (`exists_chart_division`);
2. the glued sections `vⱼ = ∑_b χ_b H_{b,j}` of `L^k` satisfy `σ = ∑ⱼ wⱼ vⱼ` pointwise
   (`sectionGauge_eq_sum_fibreGauge_glue`, in the unitary gauges of `GlobalSkodaGauge`);
3. the global `∂̄`-correction of the gluing system `skodaSystem` (Neumann series of local
   Hörmander corrections, `GluingSystem.exists_correction`) gives holomorphic sections `Sⱼ`
   of `L^k` with `∫ |vⱼ - Sⱼ|² |w|^{-2M} ≤ O(1/λ) I(σ)`, `λ = (k - Md) c`;
4. with GAGA for `L^k`, `Sⱼ = tⱼ^an`, `tⱼ ∈ H⁰(X, L^k)`, and
   `|σ - ∑ wⱼ tⱼ|² |w|^{-2(M+1)} ≤ ∑ⱼ |vⱼ - Sⱼ|² |w|^{-2M}` (Cauchy–Schwarz), so
   `I(σ - ∑ wⱼ tⱼ) ≤ O(1/λ) I(σ)` and `∫ |tⱼ|² |w|^{-2M} < ∞`.

The constant in `O(1/λ)` depends on the cover and on `r, n` only, not on `M, k, σ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.TestCurve.GlobalSkoda

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric SGPT.Okounkov
  SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaInc MeasureTheory Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.NAPotential.GAGAMult SGPT.Bergman.TensorDictionaryDraft SGPT.PSH.GlobalL2
open SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open scoped Topology ENNReal ContDiff Manifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance globalSkodaStepTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalSkodaStepCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance globalSkodaStepMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance globalSkodaStepBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- The weighted `L²` norm `∫_X |σ|²_{h^m} |w|^{-2c}_{h^d} dμ`. -/
def skodaNorm (μ : Measure (SchemeComplexPoint f)) (d : ℕ) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (c : ℝ) (m : ℕ) (σ : SectionSpace f L m) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (H.sectionNormSq a m σ x) * multiplierWeight c (familyLog H a d w x) ∂μ

theorem measurable_skodaDensity (d : ℕ) {r : ℕ} (w : Fin r → SectionSpace f L d) {c : ℝ}
    (hc : 0 ≤ c) (m : ℕ) (σ : SectionSpace f L m) :
    Measurable fun x => ENNReal.ofReal (H.sectionNormSq a m σ x) *
      multiplierWeight c (familyLog H a d w x) :=
  (ENNReal.continuous_ofReal.comp (continuous_sectionNormSq H a m σ)).measurable.mul
    ((multiplierWeight_antitone hc).measurable.comp (continuous_familyLog H a d w).measurable)

/-- **Cauchy–Schwarz with the weight**: `F Q e^{-(M+1) log F} ≤ Q e^{-M log F}`. -/
theorem ofReal_mul_multiplierWeight_succ_le {F Q : ℝ} (hF : 0 ≤ F) (hQ : 0 ≤ Q) (M : ℝ) :
    ENNReal.ofReal (F * Q) * multiplierWeight (M + 1) (ENNReal.log (ENNReal.ofReal F)) ≤
      ENNReal.ofReal Q * multiplierWeight M (ENNReal.log (ENNReal.ofReal F)) := by
  rcases hF.lt_or_eq with hF | hF
  · rw [ENNReal.log_ofReal_of_pos hF, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (mul_nonneg hF.le hQ), ← ENNReal.ofReal_mul hQ]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [show -((M + 1) * Real.log F) = -(M * Real.log F) + -Real.log F by ring, Real.exp_add,
      Real.exp_neg (Real.log F), Real.exp_log hF]
    field_simp
  · rw [← hF, zero_mul, ENNReal.ofReal_zero, zero_mul]
    exact zero_le

section Step

variable [IsSeparated f] [QuasiCompact f]

local instance globalSkodaStepManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {ωb : KahlerBackground n (SchemeComplexPoint f)} {μ : Measure (SchemeComplexPoint f)}
  {δ : ℝ} (D : CoverData ωb μ (anBundle H a) unit (H.curvature a) δ)

/-! ### Chart transfer for measurable densities -/

/-- `∫_{z_b⁻¹ B(z_b, R_b)} F dμ = ∫_{B(z_b, R_b)} F(z_b⁻¹ z) dens_b(z) dz`. -/
theorem lintegral_region_eq {F : SchemeComplexPoint f → ℝ≥0∞} (hF : Measurable F)
    (b : Fin D.m) {ρ : ℝ} (hρ : ρ ≤ D.R b) :
    ∫⁻ x in (D.chartA b).val.source ∩ (D.chartA b).val ⁻¹' ball (ctr (n := n) (D.pt b)) ρ, F x ∂μ =
      ∫⁻ z in ball (ctr (n := n) (D.pt b)) ρ,
        F ((D.chartA b).val.symm z) * ENNReal.ofReal (D.dens b z) := by
  have hsub : ball (ctr (n := n) (D.pt b)) ρ ⊆ (D.chartA b).val.target :=
    (ball_subset_ball hρ).trans (D.ball_subset_target b)
  refine setLIntegral_chart_ball (D.chartA b) (D.dens_cont b) (D.dens_map b) isOpen_ball hsub ?_
  exact hF.comp_aemeasurable (((D.chartA b).val.continuousOn_symm.mono hsub).aemeasurable
    measurableSet_ball)

/-- An integral over a chart ball is controlled by the integral over `X`. -/
theorem lintegral_ball_le {F : SchemeComplexPoint f → ℝ≥0∞} (hF : Measurable F) (b : Fin D.m) :
    ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b), F ((D.chartA b).val.symm z) ≤
      ENNReal.ofReal D.Aμ * ∫⁻ x, F x ∂μ := by
  calc ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b), F ((D.chartA b).val.symm z)
      ≤ ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b), ENNReal.ofReal D.Aμ *
          (F ((D.chartA b).val.symm z) * ENNReal.ofReal (D.dens b z)) := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal D.Aμ * ENNReal.ofReal (D.dens b z) := by
          rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (D.one_le b z hz)
        calc F ((D.chartA b).val.symm z) = 1 * F ((D.chartA b).val.symm z) := (one_mul _).symm
          _ ≤ (ENNReal.ofReal D.Aμ * ENNReal.ofReal (D.dens b z)) * F ((D.chartA b).val.symm z) :=
              mul_le_mul_of_nonneg_right h1 zero_le
          _ = _ := by ring
    _ = ENNReal.ofReal D.Aμ * ∫⁻ x in (D.chartA b).val.source ∩
          (D.chartA b).val ⁻¹' ball (ctr (n := n) (D.pt b)) (D.R b), F x ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_region_eq H a D hF b le_rfl]
    _ ≤ ENNReal.ofReal D.Aμ * ∫⁻ x, F x ∂μ :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) zero_le

/-! ### Skoda's division in the charts -/

/-- The uniform Skoda constant `(r + 1)(2 + 2n)`. -/
def skodaConst (r n : ℕ) : ℝ := (r + 1) * (2 + 2 * n)

/-- **Skoda's division in chart `b`**: for `M ≥ n + 1`, `Md ≤ k` and `I(σ) < ∞`, the coefficient
of `σ` is `∑ⱼ G_{b,j} H_{b,j}` on the middle ball, with `∫ |H_b|² W_b ≤ (r+1)(2+2n) A I(σ)`. -/
theorem exists_chart_division {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hnM : n + 1 ≤ M) (hMk : (M : ℝ) * d ≤ k) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (σ : SectionSpace f L (d + k))
    (hσ : skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ ≠ ⊤) (b : Fin D.m) :
    ∃ Hb : Fin r → ComplexModel n → ℂ,
      (∀ j, DifferentiableOn ℂ (Hb j) (ball (ctr (n := n) (D.pt b)) (D.R b / 2))) ∧
      (∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b / 2),
        chartCoef H a D b (d + k) σ z = ∑ j, chartCoef H a D b d (w j) z * Hb j z) ∧
      ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), ENNReal.ofReal (∑ j, ‖Hb j z‖ ^ 2) *
          ballWeight (skodaPsi H a D c M k d w b) (lamOf c M k d) (ctr (n := n) (D.pt b)) z ≤
        ENNReal.ofReal (skodaConst r n) *
          (ENNReal.ofReal D.Aμ * skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ) := by
  have hM : 0 < M := by omega
  have hnMR : (n : ℝ) < M := by exact_mod_cast (show n < M by omega)
  have hRpos := D.R_pos b
  obtain ⟨U, hUo, hKU, hUD, hdiv⟩ := weightedLocalSkoda (n := n)
    (D := ball (ctr (n := n) (D.pt b)) (D.R b)) isOpen_ball (convex_ball _ _) isBounded_ball
    (K := closedBall (ctr (n := n) (D.pt b)) (D.R b / 2)) (isCompact_closedBall _ _)
    (closedBall_subset_ball (by linarith)) hnMR
  set G : Fin r → ComplexModel n → ℂ := fun j => chartCoef H a D b d (w j) with hGdef
  set ψ : ComplexModel n → ℝ := fun z => ((k : ℝ) - M * d) * phiW H a D b z with hψdef
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - M * d := by linarith
  have hGd : ∀ j, DifferentiableOn ℂ (G j) (ball (ctr (n := n) (D.pt b)) (D.R b)) := fun j =>
    (differentiableOn_chartCoef H a D b d (w j)).mono (D.ball_subset_two b)
  have hψs : ContDiffOn ℝ ∞ ψ (ball (ctr (n := n) (D.pt b)) (D.R b)) :=
    contDiffOn_const.mul ((contDiffOn_phiW H a D b).mono (D.ball_subset_two b))
  have hψL : ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v, 0 ≤ leviForm ψ z v := by
    intro z hz v
    have hφ : ContDiffAt ℝ 2 (phiW H a D b) z :=
      contDiffAt_two_of_contDiffOn isOpen_ball (contDiffOn_phiW H a D b) (D.ball_subset_two b hz)
    have hψe : ψ = ((k : ℝ) - M * d) • phiW H a D b := by
      funext y; simp only [ψ, Pi.smul_apply, smul_eq_mul]
    rw [hψe, leviForm_smul hφ]
    exact mul_nonneg hk0 (le_trans (mul_nonneg hc.le (sq_nonneg _)) (hcL b z hz v))
  have hfd : DifferentiableOn ℂ (chartCoef H a D b (d + k) σ)
      (ball (ctr (n := n) (D.pt b)) (D.R b)) :=
    (differentiableOn_chartCoef H a D b (d + k) σ).mono (D.ball_subset_two b)
  -- the local integral and the global one
  set F : SchemeComplexPoint f → ℝ≥0∞ := fun x => ENNReal.ofReal (H.sectionNormSq a (d + k) σ x) *
    multiplierWeight ((M + 1 : ℕ) : ℝ) (familyLog H a d w x) with hFdef
  have hFm : Measurable F := measurable_skodaDensity H a d w (Nat.cast_nonneg _) (d + k) σ
  have hloc : ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b),
      ENNReal.ofReal (‖chartCoef H a D b (d + k) σ z‖ ^ 2) *
        multiplierWeight ((M : ℝ) + 1) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z)) =
      F ((D.chartA b).val.symm z) := by
    intro z hz
    have hzt : z ∈ (D.chartA b).val.target := D.ball_subset_target b hz
    have hxs : (D.chartA b).val.symm z ∈ (D.chartA b).val.source := (D.chartA b).val.map_target hzt
    have hcz : (D.chartA b).val ((D.chartA b).val.symm z) = z := (D.chartA b).val.right_inv hzt
    have h := sectionDensity_chart H a D hxs (by rw [hcz]; exact hz) w
      (c := ((M + 1 : ℕ) : ℝ)) (by positivity) (d + k) σ
    rw [hcz] at h
    simp only [hFdef]
    rw [h]
    congr 3
    · push_cast; ring
    · simp only [ψ]; push_cast; ring
  have hIb : (∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b),
      ENNReal.ofReal (‖chartCoef H a D b (d + k) σ z‖ ^ 2) *
        multiplierWeight ((M : ℝ) + 1) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z))) ≤
      ENNReal.ofReal D.Aμ * skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ := by
    rw [setLIntegral_congr_fun measurableSet_ball hloc]
    exact lintegral_ball_le H a D hFm b
  have hIfin : (∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b),
      ENNReal.ofReal (‖chartCoef H a D b (d + k) σ z‖ ^ 2) *
        multiplierWeight ((M : ℝ) + 1) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσ) hIb
  obtain ⟨Hb, hHd, hHeq, hHb⟩ := hdiv r G hGd ψ hψs hψL _ hfd hIfin
  have hrU : ball (ctr (n := n) (D.pt b)) (D.R b / 2) ⊆ U := ball_subset_closedBall.trans hKU
  refine ⟨Hb, fun j => (hHd j).mono hrU, fun z hz => hHeq z (hrU hz), ?_⟩
  have hC : (r + 1 : ℝ) * (2 + 2 * n / ((M : ℝ) - n)) ≤ skodaConst r n := by
    unfold skodaConst
    have h1 : (1 : ℝ) ≤ (M : ℝ) - n := by
      have : ((n + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hnM
      push_cast at this; linarith
    have h2 : 2 * (n : ℝ) / ((M : ℝ) - n) ≤ 2 * n :=
      div_le_self (by positivity) h1
    have hr : (0 : ℝ) ≤ r + 1 := by positivity
    nlinarith
  calc ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), ENNReal.ofReal (∑ j, ‖Hb j z‖ ^ 2) *
        ballWeight (skodaPsi H a D c M k d w b) (lamOf c M k d) (ctr (n := n) (D.pt b)) z
      = ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), ENNReal.ofReal (∑ j, ‖Hb j z‖ ^ 2) *
          multiplierWeight (M : ℝ) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z)) := by
        refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
        rw [ballWeight_skodaPsi H a D c hM k d w b z, mul_assoc]
    _ ≤ ∫⁻ z in U, ENNReal.ofReal (∑ j, ‖Hb j z‖ ^ 2) *
          multiplierWeight (M : ℝ) (generatorLog G z) * ENNReal.ofReal (Real.exp (-ψ z)) :=
        lintegral_mono_set hrU
    _ ≤ ENNReal.ofReal ((r + 1) * (2 + 2 * n / ((M : ℝ) - n))) *
          ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b),
            ENNReal.ofReal (‖chartCoef H a D b (d + k) σ z‖ ^ 2) *
              multiplierWeight ((M : ℝ) + 1) (generatorLog G z) *
                ENNReal.ofReal (Real.exp (-ψ z)) := hHb
    _ ≤ ENNReal.ofReal (skodaConst r n) *
          (ENNReal.ofReal D.Aμ * skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hC) hIb

/-- `∫_{z_b⁻¹ B(z_b, ρ)} F dμ ≤ A ∫_{B(z_b, ρ)} F(z_b⁻¹ z) dz`. -/
theorem lintegral_region_le {F : SchemeComplexPoint f → ℝ≥0∞} (hF : Measurable F)
    (b : Fin D.m) {ρ : ℝ} (hρ : ρ ≤ D.R b) :
    ∫⁻ x in (D.chartA b).val.source ∩ (D.chartA b).val ⁻¹' ball (ctr (n := n) (D.pt b)) ρ, F x ∂μ ≤
      ENNReal.ofReal D.Aμ * ∫⁻ z in ball (ctr (n := n) (D.pt b)) ρ, F ((D.chartA b).val.symm z) := by
  rw [lintegral_region_eq H a D hF b hρ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
    (D.dens_le b z (ball_subset_ball hρ hz))) zero_le

/-! ### The gauge identity -/

/-- In the middle region of chart `b`, `σ = ∑ⱼ wⱼ · (H_{b,j} ∘ z_b) e_b^k` in the unitary
gauges. -/
theorem sectionGauge_eq_of_chart {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d < k) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (σ : SectionSpace f L (d + k)) {b : Fin D.m}
    {Hb : Fin r → ComplexModel n → ℂ}
    (hHeq : ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b / 2),
      chartCoef H a D b (d + k) σ z = ∑ j, chartCoef H a D b d (w j) z * Hb j z)
    {x : SchemeComplexPoint f} (hx : x ∈ (skodaSystem H a D hcL hc hM hMk w).small b) :
    sectionGauge H a (d + k) x σ = ∑ j, sectionGauge H a d x (w j) *
      fibreGauge H a k x ((skodaSystem H a D hcL hc hM hMk w).localSec b (Hb j) x) := by
  have hxs : x ∈ (D.chartA b).val.source := hx.1
  have hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b / 2) := hx.2
  have hxR : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b) :=
    ball_subset_ball (by linarith [D.R_pos b]) hxz
  have hU := mem_cFrame_of_mem_region H a D hxs hxR
  have hsz : (D.chartA b).val.symm ((D.chartA b).val x) = x := (D.chartA b).val.left_inv hxs
  have hloc : ∀ j, (skodaSystem H a D hcL hc hM hMk w).localSec b (Hb j) x =
      Hb j ((D.chartA b).val x) • (twistedFrame f n E a H (cFrame H a D b) k).val.symm x 1 := by
    intro j
    simp only [GluingSystem.localSec, if_pos hx]
    rfl
  have hfr := fibreGauge_frame H a (cFrame H a D b) k hU
  have hcoef : ∀ (m : ℕ) (s : SectionSpace f L m), chartCoef H a D b m s ((D.chartA b).val x) =
      frameCoef f n E a H (cFrame H a D b) x ^ m * sectionGauge H a m x s := by
    intro m s
    simp only [chartCoef, hsz]
    exact sectionFrameCoefficient_eq_sectionGauge H a (cFrame H a D b) m s hU
  have h := hHeq _ hxz
  simp only [hcoef] at h
  have hne : frameCoef f n E a H (cFrame H a D b) x ≠ 0 := frameCoef_ne_zero f n E a H _ hU
  refine mul_left_cancel₀ (pow_ne_zero (d + k) hne) ?_
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hloc j, map_smul, smul_eq_mul, hfr, pow_add]
  field_simp

/-- **`σ = ∑ⱼ wⱼ vⱼ` for the glued quotients `vⱼ = ∑_b χ_b H_{b,j}`**, in the unitary gauges. -/
theorem sectionGauge_eq_sum_fibreGauge_glue {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d < k) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (σ : SectionSpace f L (d + k))
    {Hb : Fin D.m → Fin r → ComplexModel n → ℂ}
    (hHeq : ∀ b, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b / 2),
      chartCoef H a D b (d + k) σ z = ∑ j, chartCoef H a D b d (w j) z * Hb b j z)
    (x : SchemeComplexPoint f) :
    sectionGauge H a (d + k) x σ = ∑ j, sectionGauge H a d x (w j) *
      fibreGauge H a k x (glue (skodaSystem H a D hcL hc hM hMk w) (fun b => Hb b j) x) := by
  set G := skodaSystem H a D hcL hc hM hMk w with hGdef
  have hglue : ∀ j, fibreGauge H a k x (glue G (fun b => Hb b j) x) =
      ∑ b, ((G.χ b x : ℝ) : ℂ) * fibreGauge H a k x (G.localSec b (Hb b j) x) := by
    intro j
    simp only [glue, map_sum, map_smul, smul_eq_mul]
  simp_rw [hglue, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hb : ∀ b, ∑ j, sectionGauge H a d x (w j) * (((G.χ b x : ℝ) : ℂ) *
      fibreGauge H a k x (G.localSec b (Hb b j) x)) =
      ((G.χ b x : ℝ) : ℂ) * sectionGauge H a (d + k) x σ := by
    intro b
    by_cases hχ : G.χ b x = 0
    · simp [hχ]
    · have hxs : x ∈ G.small b := by
        have := G.tsupport_χ b (subset_tsupport _ hχ)
        exact this
      rw [sectionGauge_eq_of_chart H a D hcL hc hM hMk w σ (hHeq b) hxs, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hb]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, G.sum_χ x, Complex.ofReal_one, one_mul]

/-! ### From local holomorphic coefficients to a holomorphic section -/

/-- A section of `L^k` given on every middle region by a holomorphic coefficient is a holomorphic
section of `((L, h)^an)^{⊗ k}`. -/
theorem exists_twistedSection_of_local {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d < k) {r : ℕ}
    (w : Fin r → SectionSpace f L d)
    (S : (x : SchemeComplexPoint f) → (twistedPower (anBundle H a) unit k).Fiber x)
    (hS : ∀ b, ∃ s : ComplexModel n → ℂ,
      DifferentiableOn ℂ s (ball ((skodaSystem H a D hcL hc hM hMk w).center b)
        ((skodaSystem H a D hcL hc hM hMk w).r b)) ∧
      ∀ x ∈ (skodaSystem H a D hcL hc hM hMk w).small b,
        S x = s ((skodaSystem H a D hcL hc hM hMk w).chart b x) •
          (skodaSystem H a D hcL hc hM hMk w).frame b x) :
    ∃ σ : twistedSections (anBundle H a) unit k, ∀ x, σ x = S x := by
  set G := skodaSystem H a D hcL hc hM hMk w with hG
  refine ⟨⟨S, fun x => ?_⟩, fun x => rfl⟩
  obtain ⟨b, hb⟩ := G.cover x
  have hxs : x ∈ G.small b := G.smaller_subset_small b hb
  obtain ⟨s, hs, hSb⟩ := hS b
  have hxR : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b) :=
    ball_subset_ball (show D.R b / 2 ≤ D.R b by linarith [D.R_pos b]) hxs.2
  have hE : x ∈ (D.frameE k b).val.baseSet := D.mem_frameE_baseSet hxs.1 hxR
  rw [Trivialization.contMDiffAt_section_iff (D.frameE k b).val hE]
  have hev : (fun y => ((D.frameE k b).val ⟨y, S y⟩).2) =ᶠ[𝓝 x]
      fun y => s ((D.chartA b).val y) := by
    filter_upwards [(G.isOpen_small b).mem_nhds hxs] with y hy
    have hyR : (D.chartA b).val y ∈ ball (ctr (n := n) (D.pt b)) (D.R b) :=
      ball_subset_ball (show D.R b / 2 ≤ D.R b by linarith [D.R_pos b]) hy.2
    have hEy : y ∈ (D.frameE k b).val.baseSet := D.mem_frameE_baseSet hy.1 hyR
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) _ hEy, hSb y hy, map_smul,
      smul_eq_mul]
    change s ((D.chartA b).val y) * ((D.frameE k b).val.continuousLinearMapAt ℂ y
      ((D.frameE k b).val.symm y 1)) = _
    rw [trivialization_coef_frame _ hEy, mul_one]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  have hsC : ContDiffAt ℂ ∞ s ((D.chartA b).val x) :=
    contDiffAt_of_differentiableOn_complex hs isOpen_ball hxs.2
  exact hsC.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (D.chartA b).property) hxs.1)

/-! ### One division step -/

/-- The constant of one division step (independent of `M`, `k` and `σ`). -/
def stepConst (r : ℕ) : ℝ≥0∞ :=
  (D.m : ℝ≥0∞) * ENNReal.ofReal D.Aμ * r * ENNReal.ofReal D.Aμ * D.m * ENNReal.ofReal D.Aμ *
    (8 * D.m * ENNReal.ofReal D.Aμ * ENNReal.ofReal D.Aμ + 2) * D.m *
    ENNReal.ofReal ((D.m : ℝ) * D.M) * D.m * ENNReal.ofReal D.Aμ * ENNReal.ofReal D.Aμ *
    ENNReal.ofReal (skodaConst r n) * ENNReal.ofReal D.Aμ

theorem stepConst_ne_top (r : ℕ) : stepConst H a D r ≠ ⊤ := by
  unfold stepConst
  finiteness

/-- **One step of the global Skoda division.** For `M ≥ n + 1`, `Md < k` with `λ = (k - Md) c ≥
D.lam`, GAGA for `L^k`, and `σ ∈ H⁰(X, L^{d+k})` with `I(σ) = ∫ |σ|² |w|^{-2(M+1)} < ∞`, there
are `tⱼ ∈ H⁰(X, L^k)` with `∫ |tⱼ|² |w|^{-2M} < ∞` and
`I(σ - ∑ wⱼ tⱼ) ≤ (2/λ) · stepConst · I(σ)`. -/
theorem exists_step {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hnM : n + 1 ≤ M) (hMk : (M : ℝ) * d < k) (hlam : D.lam ≤ lamOf c M k d) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (hgaga : SchemeSectionsAlgebraic f n E a H k)
    (σ : SectionSpace f L (d + k))
    (hσ : skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ ≠ ⊤) :
    ∃ t : Fin r → SectionSpace f L k, (∀ j, skodaNorm H a μ d w (M : ℝ) k (t j) ≠ ⊤) ∧
      skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k)
          (σ - ∑ j, SectionSpace.mul f a d k (w j) (t j)) ≤
        ENNReal.ofReal (2 / lamOf c M k d) * stepConst H a D r *
          skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ := by
  have hM : 0 < M := by omega
  set G := skodaSystem H a D hcL hc hM hMk w with hGdef
  set I := skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k) σ with hIdef
  choose Hb hHd hHeq hHb using fun b => exists_chart_division H a D hcL hc hnM hMk.le w σ hσ b
  set v : Fin r → (x : SchemeComplexPoint f) → (twistedPower (anBundle H a) unit k).Fiber x :=
    fun j => glue G (fun b => Hb b j) with hvdef
  have hHd' : ∀ j b, DifferentiableOn ℂ (Hb b j) (ball (G.center b) (G.r b)) := fun j b => hHd b j
  have hvs : ∀ j, G.IsSmooth (v j) := fun j => isSmooth_glue (hHd' j)
  set A : ℝ≥0∞ := ENNReal.ofReal D.Aμ with hAdef
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ENNReal.ofReal (skodaConst r n) * (A * I) with hBdef
  have hBtop : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hAtop hσ)
  have hLn : ∀ j b, localNorm G (fun b => Hb b j) b ≤ B := by
    intro j b
    change ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), ENNReal.ofReal (‖Hb b j z‖ ^ 2) *
      ballWeight (skodaPsi H a D c M k d w b) (lamOf c M k d) (ctr (n := n) (D.pt b)) z ≤ B
    refine le_trans (lintegral_mono fun z => ?_) (hHb b)
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (Finset.single_le_sum
      (f := fun j => ‖Hb b j z‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j))) zero_le
  set EB : ℝ≥0∞ := (D.m : ℝ≥0∞) * (ENNReal.ofReal ((D.m : ℝ) * D.M) *
    ((D.m : ℝ≥0∞) * (A * (A * B)))) with hEBdef
  have hEBtop : EB ≠ ⊤ := by
    simp only [hEBdef]
    finiteness
  have hE : ∀ j, G.totalEnergy (v j) ≤ EB := by
    intro j
    refine (totalEnergy_glue_le (hHd' j)).trans ?_
    have hsum : ∑ b, G.A * (G.A * localNorm G (fun b => Hb b j) b) ≤ (D.m : ℝ≥0∞) * (A * (A * B)) :=
      calc ∑ b, G.A * (G.A * localNorm G (fun b => Hb b j) b)
          ≤ ∑ _b : Fin D.m, A * (A * B) := Finset.sum_le_sum fun b _ => by
            change A * (A * _) ≤ _
            gcongr
            exact hLn j b
        _ = (D.m : ℝ≥0∞) * (A * (A * B)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum zero_le) zero_le
  have hκ := skodaSystem_kappa_le H a D hcL hc hM hMk w hlam
  have hEfin : ∀ j, G.totalEnergy (v j) ≠ ⊤ := fun j => ne_top_of_le_ne_top hEBtop (hE j)
  choose S' hS'loc hS'bd using fun j => G.exists_correction hκ (hvs j) (hEfin j)
  choose S hS using fun j =>
    exists_twistedSection_of_local H a D hcL hc hM hMk w (S' j) (hS'loc j)
  choose t ht using fun j => hgaga (S j)
  have hSt : ∀ j x, fibreGauge H a k x (S' j x) = sectionGauge H a k x (t j) := fun j x => by
    rw [← hS j x]; exact fibreGauge_of_isAnalytificationOf H a (ht j) x
  set lam' : ℝ := lamOf c M k d with hlam'def
  set Lw : ℝ≥0∞ := ENNReal.ofReal (2 / lam') with hLwdef
  set DB : ℝ≥0∞ := (D.m : ℝ≥0∞) * (A * (8 * ((D.m : ℝ≥0∞) * (A * (A * Lw)) * EB) +
    2 * (Lw * EB))) with hDBdef
  have hDBtop : DB ≠ ⊤ := by
    simp only [hDBdef]
    finiteness
  have hDj : ∀ j, ∫⁻ x, G.D (fun x => v j x - S' j x) x ∂μ ≤ DB := by
    intro j
    refine (hS'bd j).trans ?_
    simp only [Fintype.card_fin, GluingSystem.K₀, GluingSystem.cDiff]
    change (D.m : ℝ≥0∞) * (A * (8 * ((D.m : ℝ≥0∞) * (A * (A * Lw)) * G.totalEnergy (v j)) +
      2 * (Lw * G.totalEnergy (v j)))) ≤ DB
    simp only [hDBdef]
    gcongr
    · exact hE j
    · exact hE j
  -- continuity of the chart coefficients of the errors
  have hlocS : ∀ j b, ∃ s : ComplexModel n → ℂ,
      DifferentiableOn ℂ s (ball (G.center b) (G.r b)) ∧
        ∀ z ∈ ball (G.center b) (G.r b), G.locCoef b (S' j) z = s z := by
    intro j b
    obtain ⟨s, hs, hSb⟩ := hS'loc j b
    refine ⟨s, hs, fun z hz => ?_⟩
    have hzR : z ∈ ball (G.center b) (G.R b) := ball_subset_ball (G.r_lt_R b).le hz
    have hmem : (G.chart b).symm z ∈ G.small b := (G.symm_mem_small_iff hzR).mpr hz
    simp only [GluingSystem.locCoef]
    rw [hSb _ hmem, map_smul, smul_eq_mul, G.coef_frame b _ (G.symm_mem_source hzR)
      (by rw [G.chart_symm hzR]; exact hzR), G.chart_symm hzR, mul_one]
  have hcS : ∀ j b, ContinuousOn (G.locCoef b (S' j)) (ball (G.center b) (G.r b)) := by
    intro j b
    obtain ⟨s, hs, hsb⟩ := hlocS j b
    exact hs.continuousOn.congr fun z hz => hsb z hz
  have hcv : ∀ j b, ContinuousOn (G.locCoef b (v j)) (ball (G.center b) (G.r b)) := fun j b =>
    (hvs j b).continuousOn.mono (ball_subset_ball (G.r_lt_R b).le)
  have hcont : ∀ j b, ContinuousOn (G.locCoef b (fun x => v j x - S' j x))
      (ball (G.center b) (G.r b)) := fun j b => by
    rw [G.locCoef_sub]; exact (hcv j b).sub (hcS j b)
  have hWm : ∀ b, AEMeasurable (G.W b) (volume.restrict (ball (G.center b) (G.r b))) := fun b =>
    (G.aemeasurable_W b).mono_measure
      (Measure.restrict_mono (ball_subset_ball (G.r_lt_R b).le) le_rfl)
  refine ⟨t, fun j => ?_, ?_⟩
  · -- `∫ |tⱼ|² |w|^{-2M} < ∞`
    set F'' : SchemeComplexPoint f → ℝ≥0∞ := fun x => ENNReal.ofReal (H.sectionNormSq a k (t j) x) *
      multiplierWeight (M : ℝ) (familyLog H a d w x) with hF''def
    have hF''m : Measurable F'' := measurable_skodaDensity H a d w (Nat.cast_nonneg M) k (t j)
    have heq : ∀ x, F'' x = G.D (S' j) x := by
      intro x
      simp only [hF''def, GluingSystem.D]
      rw [sectionNormSq_eq_sectionGauge H a, ← hSt j x, ← norm_eq_fibreGauge]
    have hb : ∀ b, ∫⁻ x in G.small b, F'' x ∂μ ≠ ⊤ := by
      intro b
      have hrR : D.R b / 2 ≤ D.R b := by linarith [D.R_pos b]
      refine ne_top_of_le_ne_top ?_ (lintegral_region_le H a D hF''m b hrR)
      refine ENNReal.mul_ne_top hAtop ?_
      have hch : ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b / 2), F'' ((D.chartA b).val.symm z) =
          ENNReal.ofReal (‖G.locCoef b (v j) z - G.locCoef b (fun x => v j x - S' j x) z‖ ^ 2) *
            G.W b z := by
        intro z hz
        have hDc := G.D_chart b (S' j) (ball_subset_ball hrR hz)
        rw [heq]
        refine hDc.trans ?_
        rw [G.locCoef_sub]
        congr 3
        ring_nf
      change ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), F'' ((D.chartA b).val.symm z) ≠ ⊤
      rw [setLIntegral_congr_fun measurableSet_ball hch]
      refine ne_top_of_le_ne_top ?_ (GluingSystem.lintegral_sub_sq_le_two (hWm b)
        (b := fun _ => (0 : ℂ)) (((continuousOn_const.sub (hcont j b)).aestronglyMeasurable
          measurableSet_ball)))
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) ?_,
        ENNReal.mul_ne_top (by norm_num) ?_⟩
      · simp only [sub_zero]
        refine ne_top_of_le_ne_top ?_ (chartL2_glue_le (hHd' j) b)
        refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.sum_ne_top.mpr fun b' _ => ?_)
        exact ENNReal.mul_ne_top hAtop (ENNReal.mul_ne_top hAtop
          (ne_top_of_le_ne_top hBtop (hLn j b')))
      · simp only [zero_sub, norm_neg]
        exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hAtop hDBtop)
          ((chartL2_le_lintegral b _ (hcont j b)).trans (mul_le_mul_of_nonneg_left (hDj j) zero_le))
    exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun b _ => hb b)
      (lintegral_le_sum_small (G := G) F'')
  · -- the estimate of the remainder
    set F' : SchemeComplexPoint f → ℝ≥0∞ := fun x => ENNReal.ofReal (H.sectionNormSq a (d + k)
      (σ - ∑ j, SectionSpace.mul f a d k (w j) (t j)) x) *
        multiplierWeight ((M + 1 : ℕ) : ℝ) (familyLog H a d w x) with hF'def
    have hF'm : Measurable F' := measurable_skodaDensity H a d w (Nat.cast_nonneg _) (d + k) _
    have hpt : ∀ x, F' x ≤ ∑ j, G.D (fun x => v j x - S' j x) x := by
      intro x
      have hg := sectionGauge_eq_sum_fibreGauge_glue H a D hcL hc hM hMk w σ hHeq x
      have hν : sectionGauge H a (d + k) x (σ - ∑ j, SectionSpace.mul f a d k (w j) (t j)) =
          ∑ j, sectionGauge H a d x (w j) * fibreGauge H a k x (v j x - S' j x) := by
        rw [map_sub, map_sum, hg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sectionGauge_mul, map_sub, hSt j x, mul_sub]
      have hCS : ‖∑ j, sectionGauge H a d x (w j) * fibreGauge H a k x (v j x - S' j x)‖ ^ 2 ≤
          (∑ j, ‖sectionGauge H a d x (w j)‖ ^ 2) *
            ∑ j, ‖fibreGauge H a k x (v j x - S' j x)‖ ^ 2 := by
        have h1 : ‖∑ j, sectionGauge H a d x (w j) * fibreGauge H a k x (v j x - S' j x)‖ ≤
            ∑ j, ‖sectionGauge H a d x (w j)‖ * ‖fibreGauge H a k x (v j x - S' j x)‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
        exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
          (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
      have hfam : familyNormSq H a d w x = ∑ j, ‖sectionGauge H a d x (w j)‖ ^ 2 := by
        simp only [familyNormSq, sectionNormSq_eq_sectionGauge H a]
      have hbn : ∀ j, ‖fibreGauge H a k x (v j x - S' j x)‖ = ‖v j x - S' j x‖ := fun j =>
        (norm_eq_fibreGauge H a k x _).symm
      simp only [hbn] at hCS
      rw [← hfam] at hCS
      have hQ : (0 : ℝ) ≤ ∑ j, ‖v j x - S' j x‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
      calc F' x = ENNReal.ofReal (‖sectionGauge H a (d + k) x
            (σ - ∑ j, SectionSpace.mul f a d k (w j) (t j))‖ ^ 2) *
            multiplierWeight ((M : ℝ) + 1)
              (ENNReal.log (ENNReal.ofReal (familyNormSq H a d w x))) := by
            simp only [hF'def, familyLog]
            rw [sectionNormSq_eq_sectionGauge H a]
            push_cast
            rfl
        _ ≤ ENNReal.ofReal (familyNormSq H a d w x * ∑ j, ‖v j x - S' j x‖ ^ 2) *
            multiplierWeight ((M : ℝ) + 1)
              (ENNReal.log (ENNReal.ofReal (familyNormSq H a d w x))) := by
            rw [hν]
            exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCS) zero_le
        _ ≤ ENNReal.ofReal (∑ j, ‖v j x - S' j x‖ ^ 2) *
            multiplierWeight (M : ℝ) (ENNReal.log (ENNReal.ofReal (familyNormSq H a d w x))) :=
            ofReal_mul_multiplierWeight_succ_le (familyNormSq_nonneg H a d w x) hQ M
        _ = ∑ j, G.D (fun x => v j x - S' j x) x := by
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _, Finset.sum_mul]
            rfl
    have hchart : ∀ b, ∫⁻ x in G.small b, F' x ∂μ ≤
        A * ∑ j, A * ∫⁻ x, G.D (fun x => v j x - S' j x) x ∂μ := by
      intro b
      have hrR : D.R b / 2 ≤ D.R b := by linarith [D.R_pos b]
      calc ∫⁻ x in G.small b, F' x ∂μ
          ≤ A * ∫⁻ z in ball (ctr (n := n) (D.pt b)) (D.R b / 2), F' ((D.chartA b).val.symm z) :=
            lintegral_region_le H a D hF'm b hrR
        _ ≤ A * ∫⁻ z in ball (G.center b) (G.r b), ∑ j,
              ENNReal.ofReal (‖G.locCoef b (fun x => v j x - S' j x) z‖ ^ 2) * G.W b z := by
            refine mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_ball
              fun z hz => ?_) zero_le
            refine (hpt _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
            exact G.D_chart b _ (ball_subset_ball hrR hz)
        _ = A * ∑ j, ∫⁻ z in ball (G.center b) (G.r b),
              ENNReal.ofReal (‖G.locCoef b (fun x => v j x - S' j x) z‖ ^ 2) * G.W b z := by
            congr 1
            exact lintegral_finsetSum' _ fun j _ => (ENNReal.measurable_ofReal.comp_aemeasurable
              (((hcont j b).aestronglyMeasurable measurableSet_ball).norm.aemeasurable.pow_const
                2)).mul (hWm b)
        _ ≤ A * ∑ j, A * ∫⁻ x, G.D (fun x => v j x - S' j x) x ∂μ := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) zero_le
            exact chartL2_le_lintegral b _ (hcont j b)
    calc skodaNorm H a μ d w ((M + 1 : ℕ) : ℝ) (d + k)
          (σ - ∑ j, SectionSpace.mul f a d k (w j) (t j))
        = ∫⁻ x, F' x ∂μ := rfl
      _ ≤ ∑ b, ∫⁻ x in G.small b, F' x ∂μ := lintegral_le_sum_small (G := G) F'
      _ ≤ ∑ _b : Fin D.m, A * ∑ _j : Fin r, A * DB := by
          refine Finset.sum_le_sum fun b _ => (hchart b).trans ?_
          gcongr with j
          exact hDj j
      _ = Lw * stepConst H a D r * I := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hDBdef,
            hEBdef, hBdef, stepConst, ← hAdef]
          ring_nf

end Step

end SGPT.TestCurve.GlobalSkoda
