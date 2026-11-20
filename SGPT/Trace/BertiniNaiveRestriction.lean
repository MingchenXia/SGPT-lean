import SGPT.Trace.BertiniProductModel
import SGPT.Trace.NaiveRestriction
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularKahlerCurrent
import SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound
import SGPT.Foundations.Analysis.Pending.SkodaIntegrability
import SGPT.Foundations.Analysis.Pending.ActualUnitMultiplierLelongBound
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier
import SGPT.Foundations.Analysis.Pending.QuasiEquisingularApproximationDemailly
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import SGPT.Foundations.Analysis.Pending.KahlerCurrentMax

/-!
# The naive restriction does not preserve quasi-equisingular approximations

Source `ex:naive_res2` (`chapter_trace.tex`): consider the psh function of two variables
`φ(z, w) = (-log(-log |z|²)) ∨ log |w|²`. Take an arbitrary quasi-equisingular approximation
`(φ_j)_j`. Then each `φ_j` is locally bounded since `ν(φ, (0,0)) = 0`. Consider the
restrictions to `H = {z = 0}`: `φ_j|_H` is still bounded, while `φ|_H(w) = log |w|²`. In other
words the restrictions `φ_j|_H` fail to be a quasi-equisingular approximation of `φ|_H`.

The book's example is local ("Both examples below are local, but can easily be globalized
since the singularities are isolated"), and quasi-equisingular approximations are a global
notion. We use the global model `X = ℙ¹ × ℙ¹` (`SGPT.Trace.BertiniModel`), which contains the
affine chart `ℂ²`, with the `ω`-psh potential

  `φ(x) = max (LL(x₁), log(|Z₁|²/‖Z‖²)(x₂))`,

where `LL = SGPT.Toric.projectiveLogLogPotential` is the log-log potential of `ex:loglogsing`
(chart expression `-log(-log |z|²) - log(1 + |z|²)` near `0`). In the affine chart near the
origin `φ = (-log(-log|z|²) - log(1+|z|²)) ∨ (log|w|² - log(1+|w|²))`, the book's function up
to the bounded smooth terms `log(1 + |·|²)`; its only pole is the origin. The curve `H` is
`{o} × ℙ¹`, embedded by `w ↦ (o, w)`.

Main results:

* `SGPT.Trace.BertiniNaiveRes.lelongNumber_naiveResPotential_origin`: `ν(φ, (0,0)) = 0`
  (native and book normalization);
* `SGPT.Trace.BertiniNaiveRes.exists_qea_naiveResPotential`: quasi-equisingular
  approximations of `φ` exist (the statements below are not vacuous);
* `SGPT.Trace.BertiniNaiveRes.qea_locallyBounded`: every term `φ_j` of every
  quasi-equisingular approximation is locally bounded on `X`;
* `SGPT.Trace.BertiniNaiveRes.naiveResPotential_restriction`: `φ|_H = log(|Z₁|²/‖Z‖²)`, whose
  chart expression is `log |w|² - log(1 + |w|²)`;
* `SGPT.Trace.BertiniNaiveRes.qea_restriction_bounded`: each `φ_j|_H` is bounded;
* `SGPT.Trace.BertiniNaiveRes.not_qea_restriction`: `(φ_j|_H)_j` is not a
  quasi-equisingular approximation of `φ|_H`, for any choice of backgrounds and errors on
  `H ≅ ℙ¹` (while it does decrease to `φ|_H` and has analytic singularities,
  `decreasesPointwiseTo_restriction`, `hasManifoldAnalyticSingularityType_restriction`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.Trace.BertiniNaiveRes

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
  SquaredLogLelongSourceNormalization
open SGPT.Toric SGPT.Trace.BertiniModel

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-! ### Elementary facts on `ℙ¹` -/

private theorem finiteChart_origin : projectiveModelChart false projectiveOrigin = 0 := by
  apply (projectiveModelChart false).right_inv
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

private theorem origin_mem_finiteChart :
    projectiveOrigin ∈ (projectiveModelChart false).source := by
  apply (projectiveModelChart false).map_target
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

/-- The logarithmic potential `log(|Z₁|²/‖Z‖²)` of `ℙ¹` is finite off the origin. -/
theorem projectiveLogSingularity_ne_bot {p : P1} (hp : p ≠ projectiveOrigin) :
    projectiveLogSingularity p ≠ ⊥ := by
  obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
  have hp' : (projectiveModelChart b).symm (projectiveModelChart b p) = p :=
    (projectiveModelChart b).left_inv hb
  have hval := chartFunction_logSingularity b (projectiveModelChart b p)
  change projectiveLogSingularity ((projectiveModelChart b).symm _) = _ at hval
  rw [hp'] at hval
  rw [hval]
  cases b
  · have hz : (projectiveModelChart false p) 0 ≠ 0 := by
      intro h0
      apply hp
      have hz0 : projectiveModelChart false p = 0 := by
        ext i
        fin_cases i
        simpa using h0
      rw [← hp', hz0]
      rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [logNormSq_of_ne_zero hz, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _
  · simp only [↓reduceIte, zero_sub]
    rw [← EReal.coe_neg]
    exact EReal.coe_ne_bot _

/-- The log-log potential is finite off the origin. -/
theorem projectiveLogLogPotential_ne_bot {p : P1} (hp : p ≠ projectiveOrigin) :
    projectiveLogLogPotential p ≠ ⊥ := by
  intro h
  have hle := projectiveLogSingularity_le_logLog_add_neg_two p
  rw [h, EReal.bot_add] at hle
  exact projectiveLogSingularity_ne_bot hp (le_bot_iff.mp hle)

/-! ### The potential and its local form -/

/-- The global model of the book's `φ(z, w) = (-log(-log|z|²)) ∨ log|w|²` on `ℙ¹ × ℙ¹`. -/
def naiveResPotential (x : P1 × P1) : EReal :=
  max (projectiveLogLogPotential x.1) (projectiveLogSingularity x.2)

/-- `φ` is `ω`-psh, `ω = pr₁^* ω_FS + pr₂^* ω_FS`. -/
theorem isThetaPshPotential_naiveResPotential :
    IsThetaPshPotential omegaX.form.val naiveResPotential :=
  IsThetaPshPotential.max (isThetaPshPotential_comp_fst isThetaPshPotential_projectiveLogLogPotential)
    (isThetaPshPotential_comp_snd isThetaPshPotential_logSingularity)

/-- The local form of `φ` in the affine chart `ℂ² ⊆ ℙ¹ × ℙ¹`: for `0 < |z|² < e^{-λ}`,
`φ(z, w) = (-log(-log|z|²) - log(1+|z|²)) ∨ (log|w|² - log(1+|w|²))`. -/
theorem chartFunction_naiveResPotential {z w : ComplexModel 1} (hz : z 0 ≠ 0)
    (hzsmall : Real.log (‖z 0‖ ^ 2) ≤ -logLogLambda) :
    chartFunction naiveResPotential originChart (prodModelEquiv 1 1 (z, w)) =
      max (((-Real.log (-Real.log (‖z 0‖ ^ 2)) - Real.log (1 + ‖z 0‖ ^ 2) : ℝ) : EReal))
        (logNormSq (w 0) - (projectiveFSPotential w : EReal)) := by
  rw [chartFunction_prodNativeChart]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  unfold naiveResPotential
  have h2 := chartFunction_logSingularity false w
  change projectiveLogSingularity ((projectiveModelChart false).symm w) = _ at h2
  rw [h2, projectiveLogLogPotential_finite hz, logLogProfile, if_pos hzsmall]
  simp

/-- The only pole of `φ` is the origin. -/
theorem naiveResPotential_ne_bot {x : P1 × P1} (hx : x ≠ origin) : naiveResPotential x ≠ ⊥ := by
  intro h
  rw [naiveResPotential, max_eq_bot] at h
  by_cases h1 : x.1 = projectiveOrigin
  · by_cases h2 : x.2 = projectiveOrigin
    · exact hx (Prod.ext h1 h2)
    · exact projectiveLogSingularity_ne_bot h2 h.2
  · exact projectiveLogLogPotential_ne_bot h1 h.1

/-! ### The Lelong number at the origin -/

private theorem exists_log_add_log_two_le (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → Real.log t + Real.log 2 ≤ ε * t := by
  let K : ℝ := Real.log (2 / ε) + Real.log 2
  refine ⟨max 1 (2 * |K| / ε + 1), by positivity, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htK : 2 * |K| / ε + 1 ≤ t := (le_max_right _ _).trans ht
  have htpos : 0 < t := by linarith
  have hsplit : Real.log t = Real.log (ε / 2 * t) + Real.log (2 / ε) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hle := Real.log_le_sub_one_of_pos (show 0 < ε / 2 * t by positivity)
  have hK : K ≤ ε / 2 * t := by
    have h1 : 2 * |K| / ε ≤ t := by linarith
    have h2 : |K| ≤ ε / 2 * t := by
      rw [div_le_iff₀ hε] at h1
      nlinarith [abs_nonneg K]
    exact (le_abs_self K).trans h2
  have : Real.log t + Real.log 2 ≤ ε / 2 * t - 1 + K := by
    simp only [K]
    linarith
  nlinarith

/-- The finite-chart expression of the log-log potential is bounded below by `ε log |z|²`
near the origin, for every `ε > 0` (the computation behind `ν(LL, 0) = 0`). -/
theorem eventually_scaled_logNormSq_le_logLog (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel 1),
      (ε : EReal) * logNormSq (z 0) ≤
        projectiveLogLogPotential ((projectiveModelChart false).symm z) := by
  obtain ⟨T, hT, hTle⟩ := exists_log_add_log_two_le ε hε
  let T' : ℝ := max T (logLogLambda + 1)
  have hcont : Continuous fun z : ComplexModel 1 => ‖z 0‖ ^ 2 := by fun_prop
  have hO : IsOpen {z : ComplexModel 1 | ‖z 0‖ ^ 2 < min (Real.exp (-T')) 1} :=
    isOpen_lt hcont continuous_const
  have h0 : (0 : ComplexModel 1) ∈
      {z : ComplexModel 1 | ‖z 0‖ ^ 2 < min (Real.exp (-T')) 1} := by
    simp only [mem_ofPred_eq, PiLp.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact lt_min (Real.exp_pos _) one_pos
  filter_upwards [hO.mem_nhds h0] with z hzsmall
  by_cases hz0 : z 0 = 0
  · rw [hz0, logNormSq_zero, EReal.coe_mul_bot_of_pos hε]
    exact bot_le
  set s : ℝ := ‖z 0‖ ^ 2 with hs
  have hspos : 0 < s := pow_pos (norm_pos_iff.mpr hz0) 2
  have hsexp : s < Real.exp (-T') := lt_of_lt_of_le hzsmall (min_le_left _ _)
  have hL : Real.log s < -T' := by
    have := Real.log_lt_log hspos hsexp
    rwa [Real.log_exp] at this
  have hT'T : T ≤ T' := le_max_left _ _
  have hT'lam : logLogLambda + 1 ≤ T' := le_max_right _ _
  have hcut : Real.log s ≤ -logLogLambda := by linarith
  rw [projectiveLogLogPotential_finite hz0, logLogProfile, if_pos hcut]
  have hlhs : (ε : EReal) * logNormSq (z 0) = ((ε * Real.log s : ℝ) : EReal) := by
    rw [logNormSq, ENNReal.log_ofReal_of_pos hspos, ← EReal.coe_mul]
  rw [hlhs]
  apply EReal.coe_le_coe_iff.mpr
  set t : ℝ := -Real.log s with ht
  have htT : T ≤ t := by linarith
  have hlog1 : Real.log (1 + s) ≤ Real.log 2 := Real.log_le_log (by linarith) (by
    have : s < 1 := lt_of_lt_of_le hzsmall (min_le_right _ _)
    linarith)
  have hkey := hTle t htT
  have : ε * Real.log s = -(ε * t) := by rw [ht]; ring
  rw [this]
  linarith

private theorem prodModelEquiv_symm_fst_zero (y : ComplexModel (1 + 1)) :
    ((prodModelEquiv 1 1).symm y).1 0 = y 0 := by
  simp only [prodModelEquiv, ContinuousLinearEquiv.symm_symm]
  rfl

private theorem originChart_origin : originChart.val origin = 0 := by
  change prodModelEquiv 1 1 (projectiveModelChart false projectiveOrigin,
    projectiveModelChart false projectiveOrigin) = 0
  rw [finiteChart_origin]
  simp

private theorem origin_mem_originChart : origin ∈ originChart.val.source := by
  change origin ∈ (prodChart (projectiveModelChart false) (projectiveModelChart false)).source
  rw [prodChart_source]
  exact ⟨origin_mem_finiteChart, origin_mem_finiteChart⟩

/-- Source `ex:naive_res2`: `ν(φ, (0,0)) = 0` (native normalization). -/
theorem lelongNumber_naiveResPotential_origin :
    lelongNumber (n := 1 + 1) naiveResPotential origin = 0 := by
  apply le_antisymm _ bot_le
  -- `φ ≥ LL ∘ pr₁`
  have hmono := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := 1 + 1)
    (u := fun x : P1 × P1 => projectiveLogLogPotential x.1) (v := naiveResPotential)
    (x := origin) (Eventually.of_forall fun y => le_max_left _ _)
  refine hmono.trans ?_
  rw [← LelongChartReaderInvariance.lelongNumber_chartFunction_eq originChart
    origin_mem_originChart, originChart_origin]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε2 : 0 < ε / 2 := half_pos hε
  have hε2R : (0 : ℝ) < ((ε / 2 : ℝ≥0) : ℝ) := by exact_mod_cast hε2
  have hcont : Continuous fun y : ComplexModel (1 + 1) => ((prodModelEquiv 1 1).symm y).1 :=
    continuous_fst.comp (prodModelEquiv 1 1).symm.continuous
  have h0 : ((prodModelEquiv 1 1).symm (0 : ComplexModel (1 + 1))).1 = 0 := by simp
  have hev : ∀ᶠ y in 𝓝 (0 : ComplexModel (1 + 1)),
      (((ε / 2 : ℝ≥0) : ℝ) : EReal) * logNormSq (y 0) ≤
        chartFunction (fun x : P1 × P1 => projectiveLogLogPotential x.1) originChart y := by
    have := hcont.continuousAt.eventually
      (h0 ▸ eventually_scaled_logNormSq_le_logLog _ hε2R)
    filter_upwards [this] with y hy
    rw [prodModelEquiv_symm_fst_zero] at hy
    exact hy
  have hle := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := 1 + 1)
    (eventually_nhdsWithin_of_eventually_nhds hev)
  have hval := SGPT.Okounkov.lelongNumber_scaled_logNormSq_eq (n := 1 + 1) (0 : Fin (1 + 1))
    (x := (0 : ComplexModel (1 + 1))) (by simp) hε2
  rw [hval] at hle
  calc _ ≤ 2 * ((ε / 2 : ℝ≥0) : ℝ≥0∞) := hle
    _ = 0 + (ε : ℝ≥0∞) := by
      rw [zero_add, ENNReal.coe_div (by norm_num), ENNReal.coe_ofNat,
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-- Source `ex:naive_res2`: `ν(φ, (0,0)) = 0` in the book's normalization. -/
theorem squaredLogLelongNumber_naiveResPotential_origin :
    squaredLogLelongNumber (n := 1 + 1) naiveResPotential origin = 0 := by
  have h := lelongNumber_eq_two_mul_squaredLog (n := 1 + 1) (by norm_num)
    naiveResPotential origin
  rw [lelongNumber_naiveResPotential_origin] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-! ### Quasi-equisingular approximations of `φ` -/

/-- Quasi-equisingular approximations of `φ` exist (Demailly), so the statements about an
arbitrary one are not vacuous. -/
theorem exists_qea_naiveResPotential :
    ∃ ε : ℕ → ℝ, ∃ φSeq : ℕ → P1 × P1 → EReal,
      IsQuasiEquisingularApproximation omegaX omegaX.form naiveResPotential ε φSeq :=
  QuasiEquisingularApproximationDemailly.exists_quasiEquisingularApproximation omegaX
    omegaX.form isThetaPshPotential_naiveResPotential

theorem le_of_qea {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) (j : ℕ)
    (x : P1 × P1) : naiveResPotential x ≤ φSeq j x :=
  Antitone.le_of_tendsto (hQ.2.2.2.2.1.1 x) (hQ.2.2.2.2.1.2 x) j

/-- Source `ex:naive_res2`: no term of a quasi-equisingular approximation of `φ` has a pole. -/
theorem qea_ne_bot {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) (j : ℕ)
    (x : P1 × P1) : φSeq j x ≠ ⊥ := by
  by_cases hx : x = origin
  · subst hx
    intro hbot
    have htype := hQ.2.2.2.1 j (complexChartAt (n := 1 + 1) origin)
      ((complexChartAt (n := 1 + 1) origin).val origin)
      ((complexChartAt (n := 1 + 1) origin).val.map_source (mem_complexChartAt_source _))
    have hpos := QuasiEquisingularKahlerCurrent.lelongNumber_pos_of_hasAnalyticSingularityTypeAt
      htype hbot
    have hmono := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := 1 + 1)
      (u := naiveResPotential) (v := φSeq j) (x := origin)
      (Eventually.of_forall fun y => le_of_qea hQ j y)
    rw [lelongNumber_naiveResPotential_origin] at hmono
    exact (lt_of_lt_of_le hpos hmono).ne' rfl
  · intro hbot
    exact naiveResPotential_ne_bot hx (le_bot_iff.mp (hbot ▸ le_of_qea hQ j x))

/-- Source `ex:naive_res2`: each term `φ_j` of an arbitrary quasi-equisingular approximation of
`φ` is locally bounded (on all of `ℙ¹ × ℙ¹`, in particular near the origin). -/
theorem qea_locallyBounded {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) (j : ℕ)
    (x : P1 × P1) : ∃ N ∈ 𝓝 x, IsBoundedPotentialOn (φSeq j) N :=
  AnalyticSingularityLocalBound.exists_isBoundedPotentialOn_of_analyticSingularityType
    (hQ.2.2.2.1 j) (qea_ne_bot hQ j x)

/-! ### The restriction to `H = {z = 0}` -/

/-- The curve `H = {z = 0} = {o} × ℙ¹`. -/
def ιH (w : P1) : P1 × P1 := (projectiveOrigin, w)

theorem contMDiff_ιH :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (1 + 1)) ∞ ιH :=
  contMDiff_prodMk contMDiff_const contMDiff_id

/-- Source `ex:naive_res2`: `φ|_H = log(|Z₁|²/‖Z‖²)`, whose chart expression is
`log |w|² - log(1 + |w|²)` (`chartFunction_logSingularity`): the book's `log |w|²`. -/
theorem naiveResPotential_restriction :
    (fun w => naiveResPotential (ιH w)) = projectiveLogSingularity := by
  funext w
  simp [naiveResPotential, ιH, projectiveLogLogPotential_origin_eq_bot]

/-- Source `ex:naive_res2`: each restriction `φ_j|_H` is bounded. -/
theorem qea_restriction_bounded {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) (j : ℕ) :
    IsBoundedPotentialOn (fun w => φSeq j (ιH w)) univ := by
  have hloc : ∀ w : P1, ∃ N ∈ 𝓝 w, IsBoundedPotentialOn (fun w => φSeq j (ιH w)) N := by
    intro w
    obtain ⟨N, hN, a, b, hab⟩ := qea_locallyBounded hQ j (ιH w)
    exact ⟨ιH ⁻¹' N, contMDiff_ιH.continuous.continuousAt hN, a, b, fun y hy => hab _ hy⟩
  choose N hN a b hab using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover N (fun w _ => hN w)
  refine ⟨t.inf' ?_ a, t.sup' ?_ b, fun y _ => ?_⟩
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simpa [h] using ht.2 (mem_univ projectiveOrigin)
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simpa [h] using ht.2 (mem_univ projectiveOrigin)
  obtain ⟨w, hwt, hyw⟩ := mem_iUnion₂.mp (ht.2 (mem_univ y))
  obtain ⟨h1, h2⟩ := hab w y hyw
  exact ⟨(EReal.coe_le_coe_iff.mpr (Finset.inf'_le a hwt)).trans h1,
    h2.trans (EReal.coe_le_coe_iff.mpr (Finset.le_sup' b hwt))⟩

/-- The restricted sequence does decrease to `φ|_H`. -/
theorem decreasesPointwiseTo_restriction {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) :
    DecreasesPointwiseTo (fun j w => φSeq j (ιH w)) (fun w => naiveResPotential (ιH w)) :=
  ⟨fun w => hQ.2.2.2.2.1.1 (ιH w), fun w => hQ.2.2.2.2.1.2 (ιH w)⟩

/-- The restricted terms have analytic singularities. -/
theorem hasManifoldAnalyticSingularityType_restriction
    {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq) (j : ℕ) :
    HasManifoldAnalyticSingularityType (n := 1) (fun w => φSeq j (ιH w)) :=
  AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp contMDiff_ιH
    (hQ.2.2.2.1 j)

/-- Source `ex:naive_res2`: the restrictions `φ_j|_H` of an arbitrary quasi-equisingular
approximation of `φ` fail to be a quasi-equisingular approximation of `φ|_H`, whatever the
backgrounds `ω_H`, `θ_H` and errors `ε_H` on `H ≅ ℙ¹`. Indeed `1 ∈ 𝓘(3 φ_j|_H)` (`φ_j|_H` is
bounded) but `1 ∉ 𝓘(2 φ|_H) = 𝓘(2 log |w|²)` at the origin. -/
theorem not_qea_restriction {omega : KahlerBackground (1 + 1) (P1 × P1)}
    {θ : ClosedRealOneOneForm (1 + 1) (P1 × P1)} {ε : ℕ → ℝ} {φSeq : ℕ → P1 × P1 → EReal}
    (hQ : IsQuasiEquisingularApproximation omega θ naiveResPotential ε φSeq)
    (omegaH : KahlerBackground 1 P1) (θH : ClosedRealOneOneForm 1 P1) (εH : ℕ → ℝ) :
    ¬ IsQuasiEquisingularApproximation omegaH θH (fun w => naiveResPotential (ιH w)) εH
      (fun j w => φSeq j (ιH w)) := by
  intro hR
  obtain ⟨k, hk⟩ := (hR.2.2.2.2.2 2 3 (by norm_num) (by norm_num)).exists
  have hle := PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_multiplierIdealIncluded hk
  -- `1 ∈ 𝓘(3 φ_k|_H)` at the origin of `H`
  have hpsh : ThetaPlurisubharmonic (θH + εH k • omegaH.form).val (fun w => φSeq k (ιH w)) :=
    (hR.2.2.1 k).1
  have hν : lelongNumber (n := 1) (fun w => φSeq k (ιH w)) projectiveOrigin = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hpos
    exact qea_ne_bot hQ k (ιH projectiveOrigin)
      (eq_bot_of_lelongNumber_pos (by norm_num) hpsh hpos)
  have hunit := SkodaIntegrability.one_mem_multiplierIdeal_of_lelongNumber_lt hpsh
    (c := 3) (by norm_num) (x := projectiveOrigin) (by
      rw [hν]
      exact ENNReal.ofReal_pos.mpr (by norm_num))
  have hunit2 := hle projectiveOrigin (fun _ => (1 : ℂ)) hunit
  rw [naiveResPotential_restriction] at hunit2
  have hbound := ActualUnitMultiplierLelongBound.lelongNumber_le_of_unit_multiplierIdeal
    (by norm_num : 0 < 1) hunit2
  rw [lelongNumber_projectiveLogSingularity_origin, finrank_real_of_complex] at hbound
  norm_num [ComplexModel] at hbound

end SGPT.Trace.BertiniNaiveRes
