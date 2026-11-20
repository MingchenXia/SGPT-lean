import SGPT.TestCurve.GlobalSkodaLocal
import SGPT.TestCurve.GlobalSkodaGauge
import SGPT.TestCurve.GlobalSkodaGlue

/-!
# The gluing system of `L^k` with the Skoda weight `|w|^{-2M}_{h^d}`

Blueprint `claude-global-skoda.tex`, node `global-skoda:system`.

Let `(L, h)` be a metrized algebraic line bundle on `X` with `θ = c₁(L, h)` Kähler,
`w₁, …, w_r ∈ H⁰(X, L^d)` and `M, k` with `Md < k`. On `L^k` (analytified) consider the weight
`e^{-M log |w|²_{h^d}} = |w|^{-2M}_{h^d}`. In a coordinate ball with atlas frame `e` of `L`,
`φ = -log |e|²_h` and `Gⱼ` the coefficients of `wⱼ` in `e^d`,

`|u|²_{h^k} |w|^{-2M}_{h^d} = |coef u|² e^{-M log |G|² - (k - Md) φ}`,

and since `dd^c φ = θ ≥ c ω_eucl` on the ball, `Ψ = M log |G|² + (k - Md) φ - λ |z - z₀|²` is
plurisubharmonic for `λ = (k - Md) c`. With the charts, frames, partition of unity and density
bounds of `SGPT.PSH.GlobalL2.CoverData`, this is a `GluingSystem` (`skodaSystem`) whose
curvature constant `λ` grows linearly in `k - Md`, uniformly in `M`; its contraction factor is
`≤ 1/4` as soon as `λ ≥ D.lam` (`skodaSystem_kappa_le`).

Also: the same identity for sections of `L^{d+k}` with the weight `|w|^{-2(M+1)}`
(`sectionDensity_chart`), the local Skoda division in every chart (`exists_chart_division`), and
the gauge identity `σ = ∑ wⱼ · glue(Hⱼ)` (`sectionGauge_eq_sum_fibreGauge_glue`).
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
open scoped Topology ENNReal ContDiff

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance globalSkodaSysTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance globalSkodaSysCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance globalSkodaSysMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance globalSkodaSysBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-! ### A weight identity -/

theorem coe_mul_ne_top {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
  | coe t => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

/-- `|c|² N^m · e^{-c' log(S N^d)} = |c|² e^{-c' log S} · e^{-(m - c'd)(-log N)}`. -/
theorem weight_identity {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) {c : ℝ} (hc : 0 < c) (m d : ℕ)
    (A : ℝ) (hA : 0 ≤ A) :
    ENNReal.ofReal (A * N ^ m) * multiplierWeight c (ENNReal.log (ENNReal.ofReal (S * N ^ d))) =
      ENNReal.ofReal A * multiplierWeight c (ENNReal.log (ENNReal.ofReal S)) *
        ENNReal.ofReal (Real.exp (-((m - c * d) * -Real.log N))) := by
  have hNd : 0 < N ^ d := pow_pos hN d
  have hx : ENNReal.log (ENNReal.ofReal S) ≠ ⊤ := fun h =>
    ENNReal.ofReal_ne_top (ENNReal.log_eq_top_iff.mp h)
  rw [ENNReal.ofReal_mul hS, ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hNd, Real.log_pow,
    multiplierWeight_add_coe hc hx, ENNReal.ofReal_mul hA]
  have hNm : N ^ m = Real.exp (m * Real.log N) := by
    rw [Real.exp_nat_mul, Real.exp_log hN]
  rw [hNm]
  have : ENNReal.ofReal (Real.exp (↑m * Real.log N)) *
      ENNReal.ofReal (Real.exp (-(c * (↑d * Real.log N)))) =
      ENNReal.ofReal (Real.exp (-((↑m - c * ↑d) * -Real.log N))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [← this]
  ring

section System

variable [IsSeparated f] [QuasiCompact f]

local instance globalSkodaSysManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The analytification `(L, h)^an`. -/
abbrev anBundle : HermitianHolomorphicLineBundle.{0, 0} n (SchemeComplexPoint f) :=
  schemeHermitianLineBundle f n E a H

variable {ωb : KahlerBackground n (SchemeComplexPoint f)} {μ : Measure (SchemeComplexPoint f)}
  {δ : ℝ} (D : CoverData ωb μ (anBundle H a) unit (H.curvature a) δ)

/-- The atlas frame of `L` used in chart `b`. -/
abbrev cFrame (b : Fin D.m) : LocalBundleFrame L (a.opens (prefIndex f n E a (D.pt b))) :=
  a.frame (prefIndex f n E a (D.pt b))

/-- The local weight `φ_b = -log |e_b|²_h` in chart `b`. -/
abbrev phiW (b : Fin D.m) : ComplexModel n → ℝ :=
  frameWeight (prefFrame (anBundle H a) (D.pt b)) (D.chartA b)

/-- The coefficient of an algebraic section of `L^m` in chart `b` and frame `e_b^m`. -/
def chartCoef (b : Fin D.m) (m : ℕ) (s : SectionSpace f L m) (z : ComplexModel n) : ℂ :=
  sectionFrameCoefficient f n E (cFrame H a D b) m s ((D.chartA b).val.symm z)

theorem mem_cFrame_of_mem_ball {b : Fin D.m} {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt b)) (2 * D.R b)) :
    schemeComplexPointImage f ((D.chartA b).val.symm z) ∈
      a.opens (prefIndex f n E a (D.pt b)) :=
  ((D.hball b hz).2).1

theorem mem_cFrame_of_mem_region {b : Fin D.m} {x : SchemeComplexPoint f}
    (hx : x ∈ (D.chartA b).val.source)
    (hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) :
    schemeComplexPointImage f x ∈ a.opens (prefIndex f n E a (D.pt b)) :=
  (D.mem_baseSets_of_mem hx hxz).1

/-- The chart coefficients are holomorphic on the doubled ball. -/
theorem differentiableOn_chartCoef (b : Fin D.m) (m : ℕ) (s : SectionSpace f L m) :
    DifferentiableOn ℂ (chartCoef H a D b m s) (ball (ctr (n := n) (D.pt b)) (2 * D.R b)) := by
  intro z hz
  have ht : z ∈ (D.chartA b).val.target := (D.hball b hz).1
  have hU := mem_cFrame_of_mem_ball H a D hz
  exact (FactorizedWeightForm.differentiableAt_comp_chart_symm (D.chartA b) ht
    (schemeOpenRegularFunction_holomorphicAt f n E _ _ _ hU).self_of_nhds).differentiableWithinAt

theorem phiW_eq {b : Fin D.m} {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt b)) (2 * D.R b)) :
    phiW H a D b z = -Real.log (H.frameNormSq (cFrame H a D b) ((D.chartA b).val.symm z)) := by
  have h := schemeHermitianAtlasFrame_norm_sq f n E a H (cFrame H a D b)
    (mem_cFrame_of_mem_ball H a D hz)
  simp only [phiW, SGPT.PSH.GlobalL2.frameWeight]
  rw [← h]
  rfl

theorem contDiffOn_phiW (b : Fin D.m) :
    ContDiffOn ℝ ∞ (phiW H a D b) (ball (ctr (n := n) (D.pt b)) (2 * D.R b)) :=
  D.contDiffOn_frameWeight_L (isSourceSmoothHermitianMetric_schemeHermitianLineBundle f n E a H) b

/-- **The Kähler lower bound** for the Levi forms of the local weights: since
`dd^c φ_b = θ` is Kähler, `L_{φ_b} ≥ c |v|²` on all the balls. -/
theorem exists_levi_lower_bound (hK : (H.curvature a).val.IsKahler) :
    ∃ c : ℝ, 0 < c ∧ ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b),
      ∀ v : ComplexModel n, c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v := by
  have hb : ∀ b : Fin D.m, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b),
      ∀ v : ComplexModel n, m * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v := by
    intro b
    obtain ⟨mθ, hmθ, hmle⟩ := exists_lineValue_lower_bound_of_isCompact' hK.1 (D.chartA b)
      (isCompact_closedBall (ctr (n := n) (D.pt b)) (D.R b)) (D.closedBall_subset_target b)
    refine ⟨Real.pi * mθ, mul_pos Real.pi_pos hmθ, fun z hz v => ?_⟩
    have hz2 : z ∈ ball (ctr (n := n) (D.pt b)) (2 * D.R b) := D.ball_subset_two b hz
    have h2 : ContDiffAt ℝ 2 (phiW H a D b) z :=
      contDiffAt_two_of_contDiffOn isOpen_ball (contDiffOn_phiW H a D b) hz2
    have hdiag := smoothDDC_complexDiagonal_eq_leviForm h2 v
    have hθz := isOwnFirstChernForm_schemeHermitianLineBundle f n E a H (D.chartA b)
      (prefFrame (anBundle H a) (D.pt b)) z (D.hball b hz2).1 (D.hball b hz2).2.1
    have hddc : smoothDDC (phiW H a D b) z = (H.curvature a).val.coeff (D.chartA b) z :=
      hθz.symm
    rw [hddc] at hdiag
    have hlev : leviForm (phiW H a D b) z v =
        Real.pi * (H.curvature a).val.coeff (D.chartA b) z ![v, Complex.I • v] := by
      rw [hdiag]; field_simp
    rw [hlev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hmle z (ball_subset_closedBall hz) v) Real.pi_pos.le
  choose m hm hmle using hb
  have hS0 : 0 < 1 + ∑ b, (m b)⁻¹ := by
    have := Finset.sum_nonneg (fun b (_ : b ∈ Finset.univ) => (inv_pos.mpr (hm b)).le)
    linarith
  refine ⟨(1 + ∑ b, (m b)⁻¹)⁻¹, inv_pos.mpr hS0, fun b z hz v => ?_⟩
  have hle : (1 + ∑ b, (m b)⁻¹)⁻¹ ≤ m b := by
    rw [inv_le_comm₀ hS0 (hm b)]
    have : (m b)⁻¹ ≤ ∑ b, (m b)⁻¹ := Finset.single_le_sum (f := fun b => (m b)⁻¹)
      (fun b _ => (inv_pos.mpr (hm b)).le) (Finset.mem_univ b)
    linarith
  exact (mul_le_mul_of_nonneg_right hle (sq_nonneg _)).trans (hmle b z hz v)

/-! ### The local weights -/

/-- The curvature constant `λ = (k - Md) c`. -/
def lamOf (c : ℝ) (M k d : ℕ) : ℝ := ((k : ℝ) - M * d) * c

/-- The psh part `Ψ_b = M log |G_b|² + (k - Md) φ_b - λ |z - z_b|²` of the local weight. -/
def skodaPsi (c : ℝ) (M k d : ℕ) {r : ℕ} (w : Fin r → SectionSpace f L d) (b : Fin D.m)
    (z : ComplexModel n) : EReal :=
  ((M : ℝ) : EReal) * generatorLog (fun j => chartCoef H a D b d (w j)) z +
    ((((k : ℝ) - M * d) * phiW H a D b z - lamOf c M k d * ‖z - ctr (n := n) (D.pt b)‖ ^ 2 :
      ℝ) : EReal)

theorem leviForm_skodaSmooth_nonneg {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v)
    {M k d : ℕ} (hMk : (M : ℝ) * d ≤ k) (b : Fin D.m) {z : ComplexModel n}
    (hz : z ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) (v : ComplexModel n) :
    0 ≤ leviForm (fun z => ((k : ℝ) - M * d) * phiW H a D b z -
      lamOf c M k d * ‖z - ctr (n := n) (D.pt b)‖ ^ 2) z v := by
  have hz2 := D.ball_subset_two b hz
  have hφ : ContDiffAt ℝ 2 (phiW H a D b) z :=
    contDiffAt_two_of_contDiffOn isOpen_ball (contDiffOn_phiW H a D b) hz2
  set N : ComplexModel n → ℝ := fun z => lamOf c M k d * ‖z - ctr (n := n) (D.pt b)‖ ^ 2
  have hN2 : ContDiffAt ℝ 2 N z :=
    ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have hLeviN : leviForm N z v = lamOf c M k d * ‖v‖ ^ 2 := by
    have e : N = fun y => ((lamOf c M k d) • fun u : ComplexModel n => ‖u‖ ^ 2)
        (y - ctr (n := n) (D.pt b)) := by
      funext y; simp [N, smul_eq_mul]
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul
      (contDiff_norm_sq ℝ).contDiffAt, leviForm_norm_sq]
  have hsplit : (fun z => ((k : ℝ) - M * d) * phiW H a D b z -
      lamOf c M k d * ‖z - ctr (n := n) (D.pt b)‖ ^ 2) =
      (((k : ℝ) - M * d) • phiW H a D b) + -N := by
    funext y; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, N]; ring
  have hkφ : ContDiffAt ℝ 2 (((k : ℝ) - M * d) • phiW H a D b) z := by
    have := hφ.const_smul ((k : ℝ) - M * d); exact this
  have hNn : ContDiffAt ℝ 2 (-N) z := hN2.neg
  rw [hsplit, leviForm_add hkφ hNn, leviForm_neg, leviForm_smul hφ, hLeviN]
  have h1 := hcL b z hz v
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - M * d := by linarith
  have := mul_le_mul_of_nonneg_left h1 hk0
  simp only [lamOf]
  nlinarith

/-- `Ψ_b` is plurisubharmonic on the ball. -/
theorem skodaPsi_psh {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d ≤ k) {r : ℕ} (w : Fin r → SectionSpace f L d)
    (b : Fin D.m) :
    PlurisubharmonicOn (skodaPsi H a D c M k d w b) (ball (ctr (n := n) (D.pt b)) (D.R b)) := by
  have h1 : PlurisubharmonicOn (fun z => ((M : ℝ) : EReal) *
      generatorLog (fun j => chartCoef H a D b d (w j)) z) (ball (ctr (n := n) (D.pt b)) (D.R b)) :=
    fun z hz => plurisubharmonicAt_scaled_generatorLog
      ⟨ball (ctr (n := n) (D.pt b)) (2 * D.R b), isOpen_ball, D.ball_subset_two b hz,
        fun j => differentiableOn_chartCoef H a D b d (w j)⟩ (by exact_mod_cast hM)
  have hsm : ContDiffOn ℝ ∞ (fun z => ((k : ℝ) - M * d) * phiW H a D b z -
      lamOf c M k d * ‖z - ctr (n := n) (D.pt b)‖ ^ 2) (ball (ctr (n := n) (D.pt b)) (D.R b)) :=
    (contDiffOn_const.mul ((contDiffOn_phiW H a D b).mono (D.ball_subset_two b))).sub
      ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp
        (contDiff_id.sub contDiff_const))).contDiffOn)
  have h2 := plurisubharmonicOn_of_contDiffOn_levi_nonneg isOpen_ball hsm
    fun z hz v => leviForm_skodaSmooth_nonneg H a D hcL hMk b hz v
  exact h1.add h2

/-- `W_b = e^{-Ψ_b - λ|z - z_b|²} = e^{-M log |G_b|²} e^{-(k - Md) φ_b}`. -/
theorem ballWeight_skodaPsi (c : ℝ) {M : ℕ} (hM : 0 < M) (k d : ℕ) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (b : Fin D.m) (z : ComplexModel n) :
    ballWeight (skodaPsi H a D c M k d w b) (lamOf c M k d) (ctr (n := n) (D.pt b)) z =
      multiplierWeight M (generatorLog (fun j => chartCoef H a D b d (w j)) z) *
        ENNReal.ofReal (Real.exp (-(((k : ℝ) - M * d) * phiW H a D b z))) := by
  have hx : ((M : ℝ) : EReal) * generatorLog (fun j => chartCoef H a D b d (w j)) z ≠ ⊤ :=
    coe_mul_ne_top (by exact_mod_cast hM) (generatorLog_ne_top _ _)
  rw [ballWeight, skodaPsi, add_assoc, ← EReal.coe_add, sub_add_cancel,
    multiplierWeight_add_coe one_pos hx,
    SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier.multiplierWeight_coe_mul,
    one_mul, one_mul]

/-! ### The density identities -/

/-- The family norm in chart `b`: `|w|²_{h^d} = |G_b|² N^d`, `N = |e_b|²_h`. -/
theorem familyNormSq_chart {b : Fin D.m} {x : SchemeComplexPoint f}
    (hx : x ∈ (D.chartA b).val.source)
    (hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) {d r : ℕ}
    (w : Fin r → SectionSpace f L d) :
    familyNormSq H a d w x = generatorNormSq (fun j => chartCoef H a D b d (w j))
      ((D.chartA b).val x) * H.frameNormSq (cFrame H a D b) x ^ d := by
  have hU := mem_cFrame_of_mem_region H a D hx hxz
  have hsz : (D.chartA b).val.symm ((D.chartA b).val x) = x := (D.chartA b).val.left_inv hx
  simp only [familyNormSq, generatorNormSq, chartCoef, hsz, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [H.sectionNormSq_frame a (cFrame H a D b) d (w j) x hU, Complex.normSq_eq_norm_sq]
  rfl

/-- **Density identity for sections of `L^m` with the weight `|w|^{-2c}`**, in chart `b`:
`|σ|²_{h^m} e^{-c log |w|²} = |f_b|² e^{-c log |G_b|²} e^{-(m - cd) φ_b}`. -/
theorem sectionDensity_chart {b : Fin D.m} {x : SchemeComplexPoint f}
    (hx : x ∈ (D.chartA b).val.source)
    (hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) {d r : ℕ}
    (w : Fin r → SectionSpace f L d) {c : ℝ} (hc : 0 < c) (m : ℕ) (σ : SectionSpace f L m) :
    ENNReal.ofReal (H.sectionNormSq a m σ x) * multiplierWeight c (familyLog H a d w x) =
      ENNReal.ofReal (‖chartCoef H a D b m σ ((D.chartA b).val x)‖ ^ 2) *
        multiplierWeight c (generatorLog (fun j => chartCoef H a D b d (w j))
          ((D.chartA b).val x)) *
        ENNReal.ofReal (Real.exp (-(((m : ℝ) - c * d) * phiW H a D b ((D.chartA b).val x)))) := by
  have hU := mem_cFrame_of_mem_region H a D hx hxz
  have hsz : (D.chartA b).val.symm ((D.chartA b).val x) = x := (D.chartA b).val.left_inv hx
  have hN : 0 < H.frameNormSq (cFrame H a D b) x := H.positive _ x hU
  have hφ := phiW_eq H a D (D.ball_subset_two b hxz)
  rw [hsz] at hφ
  rw [hφ, H.sectionNormSq_frame a (cFrame H a D b) m σ x hU, familyLog,
    familyNormSq_chart H a D hx hxz w, generatorLog_eq_log_sum, Complex.normSq_eq_norm_sq]
  have hcoef : sectionFrameCoefficient f n E (cFrame H a D b) m σ x =
      chartCoef H a D b m σ ((D.chartA b).val x) := by
    simp only [chartCoef, hsz]
  change ENNReal.ofReal (‖sectionFrameCoefficient f n E (cFrame H a D b) m σ x‖ ^ 2 * _) * _ = _
  rw [hcoef]
  exact weight_identity hN (generatorNormSq_nonneg _ _) hc m d _ (sq_nonneg _)

/-- The norm of a vector of `((L, h)^an)^{⊗ k}` in the frame of chart `b`:
`‖u‖² = |coef_b u|² N^k`, `N = |e_b|²_h`. -/
theorem norm_sq_chart {b : Fin D.m} {x : SchemeComplexPoint f}
    (hx : x ∈ (D.chartA b).val.source)
    (hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) (k : ℕ)
    (u : (twistedPower (anBundle H a) unit k).Fiber x) :
    ‖u‖ ^ 2 = ‖(D.frameE k b).val.continuousLinearMapAt ℂ x u‖ ^ 2 *
      H.frameNormSq (cFrame H a D b) x ^ k := by
  have hU := mem_cFrame_of_mem_region H a D hx hxz
  have hE := D.mem_frameE_baseSet (k := k) hx hxz
  have hbs := D.mem_baseSets_of_mem hx hxz
  rw [norm_eq_coef_mul_norm_frame (D.frameE k b).val hE u]
  have hfr := twistedPower_frame_norm (prefFrame (anBundle H a) (D.pt b))
    (prefFrame (unit (n := n) (M := SchemeComplexPoint f)) (D.pt b)) hbs.1 hbs.2 k
  have h1 : ‖(prefFrame (unit (n := n) (M := SchemeComplexPoint f)) (D.pt b)).val.symm x 1‖ = 1 :=
    SGPT.TestCurve.SkodaRWN.norm_unitAtlasFrame_symm_eq_one x
  have h2 : ‖(prefFrame (anBundle H a) (D.pt b)).val.symm x 1‖ ^ 2 =
      H.frameNormSq (cFrame H a D b) x :=
    schemeHermitianAtlasFrame_norm_sq f n E a H (cFrame H a D b) hU
  have hfr' : ‖(D.frameE k b).val.symm x 1‖ =
      ‖(prefFrame (anBundle H a) (D.pt b)).val.symm x 1‖ ^ k *
        ‖(prefFrame (unit (n := n) (M := SchemeComplexPoint f)) (D.pt b)).val.symm x 1‖ := hfr
  rw [hfr', h1, mul_one, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, h2]

/-- **Density identity of the gluing system**:
`|u|²_{h^k} |w|^{-2M}_{h^d} = |coef_b u|² e^{-Ψ_b - λ|z - z_b|²}`. -/
theorem skodaSystem_density (c : ℝ) {M : ℕ} (hM : 0 < M) (k d : ℕ) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (b : Fin D.m) (x : SchemeComplexPoint f)
    (u : (twistedPower (anBundle H a) unit k).Fiber x) (hx : x ∈ (D.chartA b).val.source)
    (hxz : (D.chartA b).val x ∈ ball (ctr (n := n) (D.pt b)) (D.R b)) :
    ENNReal.ofReal (‖u‖ ^ 2) * multiplierWeight M (familyLog H a d w x) =
      ENNReal.ofReal (‖(D.frameE k b).val.continuousLinearMapAt ℂ x u‖ ^ 2) *
        ballWeight (skodaPsi H a D c M k d w b) (lamOf c M k d) (ctr (n := n) (D.pt b))
          ((D.chartA b).val x) := by
  have hU := mem_cFrame_of_mem_region H a D hx hxz
  have hsz : (D.chartA b).val.symm ((D.chartA b).val x) = x := (D.chartA b).val.left_inv hx
  have hN : 0 < H.frameNormSq (cFrame H a D b) x := H.positive _ x hU
  have hφ := phiW_eq H a D (D.ball_subset_two b hxz)
  rw [hsz] at hφ
  rw [ballWeight_skodaPsi H a D c hM k d w b, hφ, norm_sq_chart H a D hx hxz k u, familyLog,
    familyNormSq_chart H a D hx hxz w, generatorLog_eq_log_sum]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have := weight_identity hN (generatorNormSq_nonneg (fun j => chartCoef H a D b d (w j))
    ((D.chartA b).val x)) hM' k d
    (‖(D.frameE k b).val.continuousLinearMapAt ℂ x u‖ ^ 2) (sq_nonneg _)
  rw [this, mul_assoc]
  rfl

/-- **The gluing system of `L^k` with the Skoda weight** `|w|^{-2M}_{h^d}`: the charts, frames,
partition of unity and density bounds of the cover data `D`, the local weights `Ψ_b` and the
curvature constant `λ = (k - Md) c`. -/
def skodaSystem {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d < k) {r : ℕ}
    (w : Fin r → SectionSpace f L d) :
    GluingSystem n (SchemeComplexPoint f) μ (twistedPower (anBundle H a) unit k).Fiber
      (fun x => multiplierWeight M (familyLog H a d w x)) (Fin D.m) where
  chart b := (D.chartA b).val
  center b := ctr (n := n) (D.pt b)
  r' b := D.R b / 4
  r b := D.R b / 2
  R := D.R
  r'_pos b := by linarith [D.R_pos b]
  r'_lt_r b := by linarith [D.R_pos b]
  r_lt_R b := by linarith [D.R_pos b]
  closedBall_subset := D.closedBall_subset_target
  cover x := by
    have hne : ∑ b, D.χ b x ≠ 0 := by rw [D.sum_χ x]; exact one_ne_zero
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨b, D.tsupport_χ b (subset_tsupport _ hb)⟩
  coef b x := (D.frameE k b).val.continuousLinearMapAt ℂ x
  frame b x := (D.frameE k b).val.symm x 1
  coef_frame b x hx hxz := trivialization_coef_frame _ (D.mem_frameE_baseSet hx hxz)
  eq_coef_smul_frame b x u hx hxz :=
    trivialization_eq_coef_smul_frame _ (D.mem_frameE_baseSet hx hxz) u
  transition_holo i l := by
    refine differentiableOn_coef_frame (D.frameE k i).val (D.frameE k l).val (D.chartA l)
      (fun z hz => D.ball_subset_target l hz.1) fun z hz =>
        ⟨D.mem_frameE_baseSet hz.2.1 hz.2.2, ?_⟩
    have hs : (D.chartA l).val.symm z ∈ (D.chartA l).val.source :=
      (D.chartA l).val.map_target (D.ball_subset_target l hz.1)
    exact D.mem_frameE_baseSet hs
      (by rw [(D.chartA l).val.right_inv (D.ball_subset_target l hz.1)]; exact hz.1)
  chart_holo i l := by
    refine (RegularPatchNeighborhood.differentiableOn_chartTransition (D.chartA l)
      (D.chartA i)).mono fun z hz => ?_
    exact ⟨D.ball_subset_target l hz.1, hz.2.1⟩
  dens b z := ENNReal.ofReal (D.dens b z)
  A := ENNReal.ofReal D.Aμ
  A_ne_top := ENNReal.ofReal_ne_top
  dens_le b z hz := ENNReal.ofReal_le_ofReal (D.dens_le b z hz)
  one_le_A_mul_dens b z hz := by
    rw [← ENNReal.ofReal_mul D.Aμ_pos.le, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (D.one_le b z hz)
  map_measure b g hg :=
    setLIntegral_chart_ball (D.chartA b) (D.dens_cont b) (D.dens_map b) isOpen_ball
      (D.ball_subset_target b) hg
  Ψ := skodaPsi H a D c M k d w
  Ψ_psh := skodaPsi_psh H a D hcL hM hMk.le w
  lam := lamOf c M k d
  lam_pos := mul_pos (by linarith) hc
  density_eq b x u hx hxz := skodaSystem_density H a D c hM k d w b x u hx hxz
  χ := D.χ
  χ_smooth i l := D.χ_smooth i (D.chartA l)
  χ_nonneg := D.χ_nonneg
  sum_χ := D.sum_χ
  tsupport_χ b := (D.tsupport_χ b).trans fun x hx =>
    ⟨hx.1, ball_subset_ball (by linarith [D.R_pos b]) hx.2⟩
  M := D.M
  dbar_χ_le := D.dbar_χ_le

/-- **The contraction factor is at most `1/4`** once `λ ≥ D.lam`. -/
theorem skodaSystem_kappa_le {c : ℝ}
    (hcL : ∀ b : Fin D.m, ∀ z ∈ ball (ctr (n := n) (D.pt b)) (D.R b), ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ leviForm (phiW H a D b) z v) (hc : 0 < c)
    {M k d : ℕ} (hM : 0 < M) (hMk : (M : ℝ) * d < k) {r : ℕ}
    (w : Fin r → SectionSpace f L d) (hlam : D.lam ≤ lamOf c M k d) :
    (skodaSystem H a D hcL hc hM hMk w).kappa ≤ ENNReal.ofReal (1 / 4) := by
  simp only [GluingSystem.kappa, skodaSystem, Fintype.card_fin]
  have hlam0 : 0 < lamOf c M k d := mul_pos (by linarith) hc
  have hA := D.Aμ_pos
  have hM' : (D.m : ℝ) * D.M ≤ (D.m : ℝ) * |D.M| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)
  calc (D.m : ℝ≥0∞) * (ENNReal.ofReal ((D.m : ℝ) * D.M) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / lamOf c M k d))))
      ≤ ENNReal.ofReal (D.m : ℝ) * (ENNReal.ofReal ((D.m : ℝ) * |D.M|) * (ENNReal.ofReal D.Aμ *
        (ENNReal.ofReal D.Aμ * ENNReal.ofReal (2 / lamOf c M k d)))) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
    _ = ENNReal.ofReal ((D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ *
          (2 / lamOf c M k d))))) := by
        rw [← ENNReal.ofReal_mul hA.le, ← ENNReal.ofReal_mul hA.le,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ) * |D.M|),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (D.m : ℝ))]
    _ ≤ ENNReal.ofReal (1 / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hx : 0 ≤ (D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2 := by positivity
        have hle : 8 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) ≤ lamOf c M k d := by
          have := D.lam_pos
          rw [CoverData.lam] at hlam
          linarith
        have : (D.m : ℝ) * ((D.m : ℝ) * |D.M| * (D.Aμ * (D.Aμ * (2 / lamOf c M k d)))) =
            2 * ((D.m : ℝ) ^ 2 * |D.M| * D.Aμ ^ 2) / lamOf c M k d := by
          field_simp
        rw [this, div_le_iff₀ hlam0]
        linarith

end System

end SGPT.TestCurve.GlobalSkoda
