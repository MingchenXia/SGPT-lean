import SGPT.TestCurve.SkodaRWNBernsteinMarkov
import SGPT.TestCurve.SkodaRWNContinuity
import SGPT.TestCurve.RWNObstacleIGood
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationChartBranch

/-!
# [RWN14, Proposition 7.11] from its two analytic inputs

Input (a) of `rmk:PhongSturm` (chapter *Test curves*) is `RWNSkodaClause`:
`P_θ[ψ_τ] = ψ_τ` for `τ < τ(𝓕)`, where `ψ_τ = usc sup_k k⁻¹ Γ^{𝓕,k}_τ` is the obstacle of
`ex:RWN` (Ross–Witt Nyström [RWN14, Proposition 7.11]; the footnote to `ex:RWN` cites it for
`L` ample). The proof of [RWN14] has two analytic inputs:

* the **Ohsawa–Takegoshi/Demailly point extension** for the sections of `L^k`: for
  `φ ∈ PSH(X, θ - δω)` there are, for `k ≥ k₀(δ)`, sections `σ ∈ H⁰(X, L^k)` with
  `∫ |σ|²_{h^k} e^{-kφ} dμ ≤ C |σ(x)|²_{h^k} e^{-kφ(x)}`, `C = C(δ)`
  (`SchemePointExtension`; the analytic statement is the proved
  `SGPT.PSH.GlobalL2.globalPointExtension`, and its transfer to the *algebraic* sections
  `SectionSpace f L k` is GAGA for `H⁰(X, L^k)`, which is open in this project);
* the **Skoda inclusion** `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for `τ' < τ < τ(𝓕)` and
  `k ≥ k₀(τ, τ')` (`SkodaInclusion`; for the finitely generated filtration of an ample test
  configuration this is the Skoda division theorem [RWN14, Theorem 7.10] on `X × ℂ`, which is
  not formalized).

This file proves the remaining part of [RWN14, Proposition 7.11]: for a positively curved metric
(`θ = c₁(L, h)` Kähler) and a finite smooth positive volume `μ`,

`SchemePointExtension` and `SkodaInclusion 𝓕` imply `RWNSkodaClause 𝓕`

(`rwnSkodaClause_of_pointExtension_of_skodaInclusion`), and consequently `rmk:PhongSturm` for
`μ = (dd^c φ)ⁿ` (`phongSturmRemark_of_pointExtension_of_skodaInclusion`), using the
Bernstein–Markov property proved in `SkodaRWNBernsteinMarkov`.

## The argument

Let `η ≤ 0` be `θ`-psh with `η ≤ ψ_τ + C₁`, `x` a point with `η(x) > -∞`, and `ε ∈ (0, 1)`.
The weight `φ = (1 - ε) η` lies in `PSH(X, θ - εθ)`. The point extension gives, for `k` large,
`σ ∈ H⁰(X, L^k)` with `∫ |σ|² e^{-kφ} dμ ≤ C |σ(x)|² e^{-kφ(x)}`. Since `φ ≤ 0`, the `L²` norm of
`σ` is at most the right-hand side, and the Bernstein–Markov property bounds `sup |σ|²` by
`A e^{εk}` times it (`coe_le_rawObstacle_of_membership`): if `σ ∈ 𝓕^{kτ'}_k`, the normalized
section gives `k⁻¹ Γ^{𝓕,k}_{τ'}(x) ≥ (1 - ε) η(x) - ε - k⁻¹ log (AC)`.

* For `τ₀ ≤ -C` (`𝓕^{kτ₀}_k = H⁰(X, L^k)`) and `η = 0` this gives `ψ_{τ₀} = 0`
  (`obstacle_nonneg_of_le_neg_bound`), hence clause (b) of `ex:RWN`, `Γ^𝓕_{τ₀} = V_θ`, for a
  positively curved metric (`rwnMinimalClause_of_pointExtension`).
* By concavity of the obstacle, `(1 - ε) ψ_τ = (1 - ε) ψ_τ + ε ψ_{τ₀} ≤ ψ_{τ_ε}` with
  `τ_ε = (1 - ε) τ + ε τ₀`; so `∫ |σ|² e^{-kψ_{τ_ε}} dμ < ∞` and the Skoda inclusion gives
  `σ ∈ 𝓕^{kτ'}_k` for `τ' < τ_ε`. Hence `η ≤ ψ_{τ'}` for every `τ' < τ` (`ε → 0`), and `η ≤ ψ_τ`
  by left continuity (`le_obstacle_of_forall_lt`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.SkodaRWN

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
  SGPT.TestCurve.TestConfig
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open scoped Topology ENNReal

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance skodaRedTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance skodaRedCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance skodaRedManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance skodaRedMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance skodaRedBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}

/-! ### The two analytic inputs -/

/-- **Uniform `L²` extension from a point for the algebraic sections of `L^k`** (statement).
For a Kähler form `ω` on `X^{an}`, `θ = c₁(L, h)` and every `δ > 0` there are `k₀` and `C > 0`
such that for all `k ≥ k₀`, all `φ ∈ PSH(X, θ - δω)` and all `x` with `φ(x) > -∞` there is
`σ ∈ H⁰(X, L^k)` with `σ(x) ≠ 0` and
`∫_X |σ|²_{h^k} e^{-kφ} dμ ≤ C |σ(x)|²_{h^k} e^{-kφ(x)}`.

This is the Ohsawa–Takegoshi point extension (Xia, *Foundations of pluripotential theory*,
`thm:compact-point-extension`; the book's `thm:OT_ext` for `Y = {x}`), proved for the holomorphic
sections of a Hermitian holomorphic line bundle in `SGPT.PSH.GlobalL2.globalPointExtension`,
together with GAGA for `H⁰(X, L^k)` (to obtain an *algebraic* section). -/
def SchemePointExtension (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)
    (μ : Measure (SchemeComplexPoint f))
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f)) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  ∀ δ : ℝ, 0 < δ → ∃ (k₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ k : ℕ, k₀ ≤ k →
    ∀ φ : SchemeComplexPoint f → EReal,
      IsThetaPshPotential (H.curvature a - δ • omega.form).val φ →
    ∀ x : SchemeComplexPoint f, φ x ≠ ⊥ → ∃ σ : SectionSpace f L k,
      H.sectionNormSq a k σ x ≠ 0 ∧
      ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) * multiplierWeight (k : ℝ) (φ y) ∂μ ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (H.sectionNormSq a k σ x) * multiplierWeight (k : ℝ) (φ x))

/-- **The Skoda inclusion** for a filtration `𝓕` of `R(X, L)` (statement): for
`τ' < τ < τ(𝓕)` there is `k₀` such that for `k ≥ k₀` every `σ ∈ H⁰(X, L^k)` with
`∫_X |σ|²_{h^k} e^{-kψ_τ} dμ < ∞` (i.e. `σ ∈ H⁰(X, L^k ⊗ 𝓘(kψ_τ))`, `ψ_τ` the obstacle of
`ex:RWN`) lies in `𝓕^{kτ'}_k`.

For the finitely generated filtration of an ample test configuration this is the content of the
Skoda division step of [RWN14, Proposition 7.11] ([RWN14, Theorem 7.10], applied on `X × ℂ` to
the generators `t^{-λ_i} s_i` of the Rees algebra). -/
def SkodaInclusion (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (μ : Measure (SchemeComplexPoint f)) : Prop :=
  ∀ τ' τ : ℝ, τ' < τ → (τ : EReal) < F.slope → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∀ σ : SectionSpace f L k,
      ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
        multiplierWeight (k : ℝ) (F.obstacle H τ y) ∂μ < ⊤ →
      σ ∈ F.piece ((k : ℝ) * τ') k

/-! ### Elementary facts on the weights -/

theorem multiplierWeight_zero (c : ℝ) : multiplierWeight c 0 = 1 := by
  rw [← EReal.coe_zero, multiplierWeight_coe]
  simp

theorem one_le_multiplierWeight {c : ℝ} (hc : 0 ≤ c) {u : EReal} (hu : u ≤ 0) :
    1 ≤ multiplierWeight c u := by
  rw [← multiplierWeight_zero c]
  exact multiplierWeight_antitone hc hu

/-- If `u ≤ v + s` then `e^{-cv} ≤ e^{cs} e^{-cu}`. -/
theorem multiplierWeight_le_of_le_add_coe {c : ℝ} (hc : 0 < c) {u v : EReal} {s : ℝ}
    (h : u ≤ v + (s : EReal)) :
    multiplierWeight c v ≤ ENNReal.ofReal (Real.exp (c * s)) * multiplierWeight c u := by
  have h1 := multiplierWeight_antitone hc.le h
  rw [QuantitativeRegularizationChartBranch.multiplierWeight_add_coe hc] at h1
  calc multiplierWeight c v
      = ENNReal.ofReal (Real.exp (c * s)) *
          (ENNReal.ofReal (Real.exp (-(c * s))) * multiplierWeight c v) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (c * s)) * multiplierWeight c u := mul_le_mul' le_rfl h1

variable [IsIntegral X]
variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
  (μ : Measure (SchemeComplexPoint f)) [IsFiniteMeasure μ]

/-! ### Sections of prescribed size in the filtration -/

/-- **The Bergman-type lower bound.** Let `θ = c₁(L, h)` be Kähler, `μ` Bernstein–Markov, and
assume the point extension. Let `η ≤ 0` be `θ`-psh, `ε ∈ (0, 1)`, and suppose that for `k` large
every `σ ∈ H⁰(X, L^k)` with `∫ |σ|² e^{-k(1-ε)η} dμ < ∞` lies in `𝓕^{kτ'}_k`. Then at every point
`x` with `η(x) = r > -∞`: `(1 - ε) r - ε ≤ sup_k k⁻¹ Γ^{𝓕,k}_{τ'}(x)`. -/
theorem coe_le_rawObstacle_of_membership (hBM : IsBernsteinMarkov H a μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {η : SchemeComplexPoint f → EReal}
    (hη : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val η)
    (hη0 : η ≤ 0) {τ' : ℝ}
    (hmem : ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k → ∀ σ : SectionSpace f L k,
      ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
        multiplierWeight (k : ℝ) (((1 - ε : ℝ) : EReal) * η y) ∂μ < ⊤ →
      σ ∈ F.piece ((k : ℝ) * τ') k)
    {x : SchemeComplexPoint f} {r : ℝ} (hx : η x = (r : EReal)) :
    (((1 - ε) * r - ε : ℝ) : EReal) ≤ F.rawObstacle H τ' x := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have h1ε : 0 < 1 - ε := by linarith
  set φ : SchemeComplexPoint f → EReal := fun y => ((1 - ε : ℝ) : EReal) * η y with hφ
  have hφpsh : IsThetaPshPotential
      (H.curvature a - ε • (curvatureKahlerBackground H a hK).form).val φ := by
    have h := PotentialMassComparison.isThetaPshPotential_smul hη h1ε
    have hform : H.curvature a - ε • (curvatureKahlerBackground H a hK).form =
        (1 - ε) • H.curvature a := by
      change H.curvature a - ε • H.curvature a = _
      rw [sub_smul, one_smul]
    rw [hform]
    exact h
  have hφ0 : ∀ y, φ y ≤ 0 := fun y => by
    have h := mul_le_mul_of_nonneg_left (hη0 y) (EReal.coe_nonneg.mpr h1ε.le)
    rw [Pi.zero_apply, mul_zero] at h
    exact h
  have hφx : φ x = (((1 - ε) * r : ℝ) : EReal) := by
    rw [hφ]
    simp only [hx, EReal.coe_mul]
  obtain ⟨k₀, C, hC, hext⟩ := hPE ε hε0
  obtain ⟨A, hA, hbm⟩ := hBM ε hε0
  obtain ⟨k₁, hk₁⟩ := hmem
  have hmain : ∀ k : ℕ, max (max k₀ k₁) 1 ≤ k →
      (((1 - ε) * r - ε - Real.log (A * C) / k : ℝ) : EReal) ≤ F.rawObstacle H τ' x := by
    intro k hk
    have hk0 : k₀ ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
    have hk1 : k₁ ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
    have hkpos : 0 < k := (le_max_right _ _).trans hk
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    obtain ⟨σ, hσx, hσ⟩ := hext k hk0 φ hφpsh x (by rw [hφx]; exact EReal.coe_ne_bot _)
    have hNx : 0 < H.sectionNormSq a k σ x :=
      lt_of_le_of_ne (H.sectionNormSq_nonneg a k σ x) (Ne.symm hσx)
    rw [hφx, multiplierWeight_coe] at hσ
    set B₀ : ℝ := C * (H.sectionNormSq a k σ x * Real.exp (-((k : ℝ) * ((1 - ε) * r)))) with hB₀
    have hB₀pos : 0 < B₀ := mul_pos hC (mul_pos hNx (Real.exp_pos _))
    have hσ' : ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
        multiplierWeight (k : ℝ) (φ y) ∂μ ≤ ENNReal.ofReal B₀ := by
      rw [hB₀, ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul hNx.le]
      exact hσ
    -- membership in the filtration
    have hmemσ : σ ∈ F.piece ((k : ℝ) * τ') k :=
      hk₁ k hk1 σ (hσ'.trans_lt ENNReal.ofReal_lt_top)
    -- the `L²` norm
    have hL2 : ∫ y, H.sectionNormSq a k σ y ∂μ ≤ B₀ := by
      have hint := integrable_sectionNormSq H a μ k σ
      have hnn : 0 ≤ᵐ[μ] fun p => H.sectionNormSq a k σ p :=
        Eventually.of_forall fun p => H.sectionNormSq_nonneg a k σ p
      have h1 : ENNReal.ofReal (∫ y, H.sectionNormSq a k σ y ∂μ) ≤ ENNReal.ofReal B₀ := by
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
        refine le_trans (lintegral_mono fun y => ?_) hσ'
        calc ENNReal.ofReal (H.sectionNormSq a k σ y)
            = ENNReal.ofReal (H.sectionNormSq a k σ y) * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal (H.sectionNormSq a k σ y) * multiplierWeight (k : ℝ) (φ y) :=
            mul_le_mul' le_rfl (one_le_multiplierWeight (Nat.cast_nonneg k) (hφ0 y))
      exact (ENNReal.ofReal_le_ofReal_iff hB₀pos.le).mp h1
    -- the sup norm
    set D : ℝ := A * Real.exp (ε * k) * B₀ with hD
    have hDpos : 0 < D := mul_pos (mul_pos hA (Real.exp_pos _)) hB₀pos
    have hsup : ∀ q, H.sectionNormSq a k σ q ≤ D := fun q =>
      (hbm k σ q).trans (mul_le_mul_of_nonneg_left hL2 (mul_pos hA (Real.exp_pos _)).le)
    -- the normalized section
    set c : ℂ := (((Real.sqrt D)⁻¹ : ℝ) : ℂ) with hc
    have hnc : Complex.normSq c = D⁻¹ := by
      rw [hc, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt hDpos.le]
    have hsnorm : ∀ q, H.sectionNormSq a k (c • σ) q = D⁻¹ * H.sectionNormSq a k σ q :=
      fun q => by rw [H.sectionNormSq_smul a k c σ q, hnc]
    have hnmem : c • σ ∈ F.normalizedSections H k τ' := by
      refine ⟨Submodule.smul_mem _ c hmemσ, fun q => ?_⟩
      rw [hsnorm]
      calc D⁻¹ * H.sectionNormSq a k σ q ≤ D⁻¹ * D :=
            mul_le_mul_of_nonneg_left (hsup q) (inv_nonneg.mpr hDpos.le)
        _ = 1 := inv_mul_cancel₀ hDpos.ne'
    have hsp : H.sectionLogNormSq a k (c • σ) x ≤ F.sectionPotential H k τ' x := by
      rw [F.sectionPotential_eq_raw H k]
      exact le_iSup (fun s' : F.normalizedSections H k τ' => H.sectionLogNormSq a k s'.1 x)
        ⟨c • σ, hnmem⟩
    have hval : H.sectionLogNormSq a k (c • σ) x =
        ((Real.log (D⁻¹ * H.sectionNormSq a k σ x) : ℝ) : EReal) := by
      change ENNReal.log (ENNReal.ofReal (H.sectionNormSq a k (c • σ) x)) = _
      rw [hsnorm, ENNReal.log_ofReal_of_pos (mul_pos (inv_pos.mpr hDpos) hNx)]
    have hlog : Real.log (D⁻¹ * H.sectionNormSq a k σ x) =
        (k : ℝ) * ((1 - ε) * r) - ε * k - Real.log (A * C) := by
      have hexp : D⁻¹ * H.sectionNormSq a k σ x =
          Real.exp ((k : ℝ) * ((1 - ε) * r) - ε * k - Real.log (A * C)) := by
        rw [Real.exp_sub, Real.exp_sub, Real.exp_log (mul_pos hA hC), hD, hB₀, Real.exp_neg]
        have h1 := (Real.exp_pos ((k : ℝ) * ((1 - ε) * r))).ne'
        have h2 := (Real.exp_pos (ε * k)).ne'
        field_simp
      rw [hexp, Real.log_exp]
    rw [hval, hlog] at hsp
    have hdiv := EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkR.le) hsp
    rw [← EReal.coe_div] at hdiv
    have hraw : F.sectionPotential H k τ' x / ((k : ℝ) : EReal) ≤ F.rawObstacle H τ' x :=
      le_iSup₂ (f := fun (k' : ℕ) (_ : 0 < k') => F.normalizedPotential H k' τ' x) k hkpos
    refine le_trans (EReal.coe_le_coe_iff.mpr (le_of_eq ?_)) (hdiv.trans hraw)
    field_simp
  have hlim : Tendsto (fun k : ℕ => (1 - ε) * r - ε - Real.log (A * C) / k) atTop
      (𝓝 ((1 - ε) * r - ε)) := by
    have h := (tendsto_const_nhds (x := (1 - ε) * r - ε)).sub
      ((tendsto_const_nhds (x := Real.log (A * C))).div_atTop tendsto_natCast_atTop_atTop)
    simpa using h
  exact ereal_le_of_tendsto_coe hlim (eventually_atTop.mpr ⟨_, hmain⟩)

/-- For `τ₀ ≤ -C` (`C` the constant of `eq:Flinearlybdd`), the obstacle `ψ_{τ₀}` is `≥ 0` (hence
`= 0 = V_θ`), if `θ = c₁(L, h)` is Kähler, `μ` is Bernstein–Markov and the point extension
holds: the sections of `L^k` separate the sup norm from the value at a point up to `e^{o(k)}`. -/
theorem obstacle_nonneg_of_le_neg_bound (hBM : IsBernsteinMarkov H a μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK))
    {τ₀ : ℝ} (hτ₀ : τ₀ ≤ -(F.bound : ℝ)) (x : SchemeComplexPoint f) :
    0 ≤ F.obstacle H τ₀ x := by
  let := E.isSeparated
  let := E.quasiCompact
  have h0psh : IsThetaPshPotential (H.curvature a).val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff (H.curvature a)).mpr
      (curvatureKahlerBackground H a hK).isSemipositive
  have hkey : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (((1 - ε) * 0 - ε : ℝ) : EReal) ≤ F.rawObstacle H τ₀ x := fun ε hε0 hε1 =>
    coe_le_rawObstacle_of_membership F H μ hBM hK hPE hε0 hε1 h0psh (fun _ => le_rfl)
      ⟨1, fun k hk σ _ => by
        rw [F.piece_eq_top_of_le_neg_bound hτ₀ hk]
        exact Submodule.mem_top⟩ (x := x) (r := 0) rfl
  have hlim : Tendsto (fun j : ℕ => (1 - 1 / ((j : ℝ) + 1) / 2) * 0 - 1 / ((j : ℝ) + 1) / 2)
      atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_half_inv_succ |>.mul_const 0).sub
      tendsto_half_inv_succ
    simpa using h
  have h := ereal_le_of_tendsto_coe hlim (Eventually.of_forall fun j =>
    hkey _ (half_inv_succ_pos j) (half_inv_succ_lt_one j))
  rw [EReal.coe_zero] at h
  exact h.trans (le_uscRegularization _ x)

/-- **Clause (b) of `ex:RWN` (`eq:Gammatautheta`) for a positively curved metric**, from the
point extension: `Γ^𝓕_τ = V_θ` for `τ ≤ -C`. Here `V_θ = 0` since `θ = c₁(L, h)` is Kähler, and
`ψ_τ = 0` by `obstacle_nonneg_of_le_neg_bound`. -/
theorem rwnMinimalClause_of_pointExtension (hBM : IsBernsteinMarkov H a μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNMinimalClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  intro τ hτ
  have h0psh : IsThetaPshPotential (H.curvature a).val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff (H.curvature a)).mpr
      (curvatureKahlerBackground H a hK).isSemipositive
  have hψ : F.obstacle H τ = fun _ => (0 : EReal) := funext fun y =>
    le_antisymm (F.obstacle_le_zero H τ y)
      (obstacle_nonneg_of_le_neg_bound F H μ hBM hK hPE hτ y)
  change singularityEnvelope (H.curvature a).val (F.obstacle H τ) = _
  rw [hψ]
  apply le_antisymm
  · intro x
    refine (uscRegularization_le (g := fun _ => (0 : EReal)) upperSemicontinuous_const
      (fun y => ?_) x).trans (le_thetaPshSupremum h0psh (fun _ => le_rfl) x)
    exact (singularitySupremum_le_thetaPshSupremum _ _ y).trans (thetaPshSupremum_le_zero _ y)
  · intro x
    exact (thetaPshSupremum_le_zero _ x).trans
      (self_le_singularityEnvelope h0psh (fun _ => le_rfl) x)

/-! ### Competitors of the envelope lie below the obstacle -/

/-- **The inequality of [RWN14, Proposition 7.11]**: under the point extension and the Skoda
inclusion, for `θ = c₁(L, h)` Kähler and `μ` Bernstein–Markov, every `θ`-psh `η ≤ 0` that is
more singular than `ψ_τ` (`τ < τ(𝓕)`) satisfies `η ≤ ψ_τ`. -/
theorem le_obstacle_of_moreSingular (hBM : IsBernsteinMarkov H a μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK))
    (hSI : SkodaInclusion F H μ) {τ : ℝ} (hτ : (τ : EReal) < F.slope)
    {η : SchemeComplexPoint f → EReal}
    (hη : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val η)
    (hη0 : η ≤ 0) (hsing : MoreSingularOn η (F.obstacle H τ) univ) :
    η ≤ F.obstacle H τ := by
  let := E.isSeparated
  let := E.quasiCompact
  refine le_obstacle_of_forall_lt F H hτ hη fun τ' hτ' x => ?_
  obtain ⟨C₁, hC₁⟩ := hsing
  -- a parameter below `-C` and below `τ`
  set τ₀ : ℝ := min τ (-(F.bound : ℝ)) - 1 with hτ₀
  have hτ₀τ : τ₀ < τ := by
    have := min_le_left τ (-(F.bound : ℝ))
    linarith
  have hτ₀b : τ₀ ≤ -(F.bound : ℝ) := by
    have := min_le_right τ (-(F.bound : ℝ))
    linarith
  have hψ₀ : ∀ y, F.obstacle H τ₀ y = 0 := fun y =>
    le_antisymm (F.obstacle_le_zero H τ₀ y)
      (obstacle_nonneg_of_le_neg_bound F H μ hBM hK hPE hτ₀b y)
  rcases eq_bot_or_bot_lt (η x) with hb | hb
  · rw [hb]; exact bot_le
  have hηtop : η x ≠ ⊤ := fun ht => by
    have h := hη0 x
    rw [ht] at h
    exact absurd h (by simp)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, η x = (r : EReal) :=
    ⟨(η x).toReal, (EReal.coe_toReal hηtop hb.ne').symm⟩
  -- the admissible range of `ε`
  set ε₀ : ℝ := min 1 ((τ - τ') / (τ - τ₀)) with hε₀
  have hττ₀ : 0 < τ - τ₀ := by linarith
  have hε₀pos : 0 < ε₀ := lt_min one_pos (div_pos (by linarith) hττ₀)
  have hkey : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (((1 - ε) * r - ε : ℝ) : EReal) ≤ F.rawObstacle H τ' x := by
    intro ε hε0 hεlt
    have hε1 : ε < 1 := hεlt.trans_le (min_le_left _ _)
    have h1ε : 0 < 1 - ε := by linarith
    have hεfrac : ε < (τ - τ') / (τ - τ₀) := hεlt.trans_le (min_le_right _ _)
    -- the interpolated parameter `τ_ε = (1 - ε) τ + ε τ₀ ∈ (τ', τ)`
    set τε : ℝ := (1 - ε) * τ + (1 - (1 - ε)) * τ₀ with hτε
    have hτ'τε : τ' < τε := by
      have h := (lt_div_iff₀ hττ₀).mp hεfrac
      rw [hτε]
      nlinarith
    have hτετ : τε < τ := by
      rw [hτε]
      nlinarith
    have hτεs : (τε : EReal) < F.slope := (EReal.coe_lt_coe_iff.mpr hτετ).trans hτ
    -- `(1 - ε) η ≤ ψ_{τ_ε} + (1 - ε) C₁`
    have hle : ∀ y, ((1 - ε : ℝ) : EReal) * η y ≤
        F.obstacle H τε y + (((1 - ε) * C₁ : ℝ) : EReal) := by
      intro y
      have h1 : ((1 - ε : ℝ) : EReal) * η y ≤
          ((1 - ε : ℝ) : EReal) * (F.obstacle H τ y + (C₁ : EReal)) :=
        mul_le_mul_of_nonneg_left (hC₁ y (mem_univ y)) (EReal.coe_nonneg.mpr h1ε.le)
      rw [ThetaPshConvexCombination.coe_mul_add_coe h1ε] at h1
      have hc := F.obstacle_concave H (τ₀ := τ₀) (τ₁ := τ) hτ₀τ hτ h1ε (by linarith) y
      rw [ThetaPshConvexCombination.convexComb_apply, hψ₀ y, mul_zero, add_zero] at hc
      exact h1.trans (add_le_add hc le_rfl)
    obtain ⟨k₀, hk₀⟩ := hSI τ' τε hτ'τε hτεs
    refine coe_le_rawObstacle_of_membership F H μ hBM hK hPE hε0 hε1 hη hη0
      ⟨max k₀ 1, fun k hk σ hfin => ?_⟩ hr
    have hk0 : k₀ ≤ k := (le_max_left _ _).trans hk
    have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr ((le_max_right _ _).trans hk)
    refine hk₀ k hk0 σ ?_
    have hconst : ENNReal.ofReal (Real.exp ((k : ℝ) * ((1 - ε) * C₁))) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    calc ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
          multiplierWeight (k : ℝ) (F.obstacle H τε y) ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal (Real.exp ((k : ℝ) * ((1 - ε) * C₁))) *
            (ENNReal.ofReal (H.sectionNormSq a k σ y) *
              multiplierWeight (k : ℝ) (((1 - ε : ℝ) : EReal) * η y)) ∂μ := by
          refine lintegral_mono fun y => ?_
          have hw := multiplierWeight_le_of_le_add_coe hkR (hle y)
          calc ENNReal.ofReal (H.sectionNormSq a k σ y) *
                multiplierWeight (k : ℝ) (F.obstacle H τε y)
              ≤ ENNReal.ofReal (H.sectionNormSq a k σ y) *
                  (ENNReal.ofReal (Real.exp ((k : ℝ) * ((1 - ε) * C₁))) *
                    multiplierWeight (k : ℝ) (((1 - ε : ℝ) : EReal) * η y)) :=
                mul_le_mul' le_rfl hw
            _ = _ := by ring
      _ = ENNReal.ofReal (Real.exp ((k : ℝ) * ((1 - ε) * C₁))) *
            ∫⁻ y, ENNReal.ofReal (H.sectionNormSq a k σ y) *
              multiplierWeight (k : ℝ) (((1 - ε : ℝ) : EReal) * η y) ∂μ :=
          lintegral_const_mul' _ _ hconst
      _ < ⊤ := ENNReal.mul_lt_top hconst.lt_top hfin
  -- `ε → 0`
  rw [hr]
  have hlim : Tendsto (fun j : ℕ => (1 - ε₀ * (1 / ((j : ℝ) + 1) / 2)) * r -
      ε₀ * (1 / ((j : ℝ) + 1) / 2)) atTop (𝓝 r) := by
    have ht := tendsto_half_inv_succ.const_mul ε₀
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub ht |>.mul_const r).sub ht
    simpa using h
  refine (ereal_le_of_tendsto_coe hlim (Eventually.of_forall fun j => ?_)).trans
    (le_uscRegularization _ x)
  refine hkey _ (mul_pos hε₀pos (half_inv_succ_pos j)) ?_
  calc ε₀ * (1 / ((j : ℝ) + 1) / 2) < ε₀ * 1 :=
        mul_lt_mul_of_pos_left (half_inv_succ_lt_one j) hε₀pos
    _ = ε₀ := mul_one _

/-! ### [RWN14, Proposition 7.11] and `rmk:PhongSturm` -/

/-- **[RWN14, Proposition 7.11] from its analytic inputs**: for a positively curved metric
(`θ = c₁(L, h)` Kähler) and a finite smooth positive volume `μ`, the point extension for the
sections of `L^k` and the Skoda inclusion for `𝓕` imply `P_θ[ψ_τ] = ψ_τ` for all `τ < τ(𝓕)`. -/
theorem rwnSkodaClause_of_pointExtension_of_skodaInclusion
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a μ (curvatureKahlerBackground H a hK))
    (hSI : SkodaInclusion F H μ) : RWNSkodaClause H F := by
  let := E.isSeparated
  let := E.quasiCompact
  have hBM := isBernsteinMarkov_of_isSmoothPositiveVolume H a μ hμ
  intro τ hτ
  apply le_antisymm
  · change singularityEnvelope (H.curvature a).val (F.obstacle H τ) ≤ F.obstacle H τ
    refine (uscRegularization_sSup_le_iff (upperSemicontinuous_uscRegularization _)).mpr ?_
    rintro η ⟨⟨hη, hη0⟩, hsing⟩
    exact le_obstacle_of_moreSingular F H μ hBM hK hPE hSI hτ hη hη0 hsing
  · change F.obstacle H τ ≤ singularityEnvelope (H.curvature a).val (F.obstacle H τ)
    exact self_le_singularityEnvelope (F.obstacle_isThetaPshPotential H hτ)
      (F.obstacle_le_zero H τ)

omit [IsFiniteMeasure μ] in
/-- **`rmk:PhongSturm` for `μ = (dd^c φ)ⁿ` from the two analytic inputs of
[RWN14, Proposition 7.11]**: let `L` be ample and `h = e^{-φ}` positively curved, `μ = (dd^c φ)ⁿ`
(`curvatureVolume`). If the point extension holds for the sections of `L^k` and the Skoda
inclusion holds for the filtrations of the ample test configurations of `(X, L)` (finitely
generated normalized `ℤ`-filtrations), then for every such test configuration the geodesic ray
`Γ^{𝓕*}` is the Phong–Sturm ray. The Bernstein–Markov property of `μ` is proved
(`isBernsteinMarkov_curvatureVolume`). -/
theorem phongSturmRemark_of_pointExtension_of_skodaInclusion
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hPE : SchemePointExtension H a (curvatureVolume H a hK) (curvatureKahlerBackground H a hK))
    (hSI : ∀ (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤),
      SkodaInclusion (G.fgFiltration hG h0) H (curvatureVolume H a hK)) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_skoda P (isBernsteinMarkov_curvatureVolume H a H a hK) fun G hG h0 =>
    rwnSkodaClause_of_pointExtension_of_skodaInclusion (G.fgFiltration hG h0) H
      (curvatureVolume H a hK) (isSmoothPositiveVolume_curvatureVolume H a hK) hK hPE
      (hSI G hG h0)

end SGPT.TestCurve.SkodaRWN
