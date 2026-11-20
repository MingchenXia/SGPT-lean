import SGPT.Trace.PointTrace
import SGPT.Toric.ProjectiveLineNativePotential
import SGPT.Toric.ProjectiveSingularityRelations

/-!
# The naive restriction of a log-log singularity

Source `ex:naive_res1` (`chapter_trace.tex`): consider `φ` with log-log singularities
as in `ex:loglogsing`; locally `φ(z) = -log(-log |z|²)`. Then `ν(φ, 0) = 0` but
`φ|_0 = -∞`, so the naive restriction of `φ` to the point `0` is not defined.

We take for `φ` the potential of `ex:loglogsing` itself, the `ω_FS`-psh function
`SGPT.Toric.projectiveLogLogPotential` on `ℙ¹`, whose chart expression near the origin
is `-log(-log |z|²) - log(1 + |z|²)`.

Main results:

* `SGPT.Trace.lelongNumber_projectiveLogLogPotential_origin`: `ν(φ, 0) = 0` (both
  the native and the source-normalized Lelong numbers);
* `SGPT.Trace.projectiveLogLogPotential_origin_eq_bot`: `φ(0) = -∞`;
* `SGPT.Trace.not_isQPSH_naiveRestriction_projectiveLogLog`: the naive restriction
  `φ|_{{0}}` is not quasi-psh on the point `{0}`;
* `SGPT.Trace.projectiveLogLog_trace_origin_const`: nevertheless every real constant is
  a trace operator of `φ` along `{0}` (source `chapter_trace:example:6`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal NNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.Pending
  NaturalSubmanifoldSourceTraceDefinition SquaredLogLelongSourceNormalization
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Toric

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

private theorem finiteChart_origin : projectiveModelChart false projectiveOrigin = 0 := by
  apply (projectiveModelChart false).right_inv
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

private theorem origin_mem_finiteChart :
    projectiveOrigin ∈ (projectiveModelChart false).source := by
  apply (projectiveModelChart false).map_target
  simp [projectiveModelChart, projectiveQuotientScalarChart_target]

/-- An elementary estimate: for every `ε > 0` there is `T` with
`log t + log 2 ≤ ε t` for all `t ≥ T`. -/
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

/-- The chart expression of the log-log potential is bounded below by `ε log |z|²`
near the origin, for every `ε > 0`. -/
private theorem eventually_scaled_log_le_chartFunction (ε : ℝ≥0) (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[≠] (0 : ComplexModel 1),
      ((ε : ℝ) : EReal) * logNormSq (z 0) ≤
        chartFunction projectiveLogLogPotential (projectiveNativeChart false) z := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨T, hT, hTle⟩ := exists_log_add_log_two_le (ε : ℝ) hεR
  let T' : ℝ := max T (logLogLambda + 1)
  have hcont : Continuous fun z : ComplexModel 1 => ‖z 0‖ ^ 2 := by fun_prop
  have hO : IsOpen {z : ComplexModel 1 | ‖z 0‖ ^ 2 < min (Real.exp (-T')) 1} :=
    isOpen_lt hcont continuous_const
  have h0 : (0 : ComplexModel 1) ∈ {z : ComplexModel 1 | ‖z 0‖ ^ 2 < min (Real.exp (-T')) 1} := by
    simp only [mem_ofPred_eq, PiLp.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    exact lt_min (Real.exp_pos _) one_pos
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hO.mem_nhds h0),
    self_mem_nhdsWithin] with z hzsmall hzne
  have hz0 : z 0 ≠ 0 := by
    intro h
    apply hzne
    ext i
    fin_cases i
    simpa using h
  set s : ℝ := ‖z 0‖ ^ 2 with hs
  have hspos : 0 < s := pow_pos (norm_pos_iff.mpr hz0) 2
  have hsexp : s < Real.exp (-T') := lt_of_lt_of_le hzsmall (min_le_left _ _)
  have hs1 : s < 1 := lt_of_lt_of_le hzsmall (min_le_right _ _)
  have hL : Real.log s < -T' := by
    have := Real.log_lt_log hspos hsexp
    rwa [Real.log_exp] at this
  have hT'T : T ≤ T' := le_max_left _ _
  have hT'lam : logLogLambda + 1 ≤ T' := le_max_right _ _
  have hcut : Real.log s ≤ -logLogLambda := by linarith
  -- the right-hand side
  have hrhs : chartFunction projectiveLogLogPotential (projectiveNativeChart false) z =
      ((-Real.log (-Real.log s) - Real.log (1 + s) : ℝ) : EReal) := by
    change projectiveLogLogPotential ((projectiveModelChart false).symm z) = _
    rw [projectiveLogLogPotential_finite hz0, logLogProfile, if_pos hcut]
  -- the left-hand side
  have hlhs : ((ε : ℝ) : EReal) * logNormSq (z 0) = (((ε : ℝ) * Real.log s : ℝ) : EReal) := by
    rw [logNormSq, ENNReal.log_ofReal_of_pos hspos, ← EReal.coe_mul]
  rw [hrhs, hlhs]
  apply EReal.coe_le_coe_iff.mpr
  set t : ℝ := -Real.log s with ht
  have htT : T ≤ t := by linarith
  have hlog1 : Real.log (1 + s) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  have hkey := hTle t htT
  have : (ε : ℝ) * Real.log s = -((ε : ℝ) * t) := by rw [ht]; ring
  rw [this]
  linarith

/-- Source `ex:naive_res1`: the log-log potential of `ex:loglogsing` has Lelong
number `0` at the origin. -/
theorem lelongNumber_projectiveLogLogPotential_origin :
    lelongNumber (n := 1) projectiveLogLogPotential projectiveOrigin = 0 := by
  have hchart := LelongChartReaderInvariance.lelongNumber_chartFunction_eq
    (u := projectiveLogLogPotential) (projectiveNativeChart false) origin_mem_finiteChart
  rw [projectiveNativeChart_val, finiteChart_origin] at hchart
  rw [← hchart]
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε2 : 0 < ε / 2 := half_pos hε
  have hmono := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := 1)
    (eventually_scaled_log_le_chartFunction (ε / 2) hε2)
  have hval := SGPT.Okounkov.lelongNumber_scaled_logNormSq_eq (0 : Fin 1)
    (x := (0 : ComplexModel 1)) (by simp) hε2
  rw [hval] at hmono
  calc lelongNumber (n := 1)
        (chartFunction projectiveLogLogPotential (projectiveNativeChart false)) 0
      ≤ 2 * ((ε / 2 : ℝ≥0) : ℝ≥0∞) := hmono
    _ = 0 + (ε : ℝ≥0∞) := by
      rw [zero_add, ENNReal.coe_div (by norm_num), ENNReal.coe_ofNat,
        ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-- Source `ex:naive_res1`, with the book's normalization of the Lelong number. -/
theorem squaredLogLelongNumber_projectiveLogLogPotential_origin :
    squaredLogLelongNumber (n := 1) projectiveLogLogPotential projectiveOrigin = 0 := by
  have h := lelongNumber_eq_two_mul_squaredLog (n := 1) (by norm_num)
    projectiveLogLogPotential projectiveOrigin
  rw [lelongNumber_projectiveLogLogPotential_origin] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- Source `ex:naive_res1`: `φ(0) = -∞`. -/
theorem projectiveLogLogPotential_origin_eq_bot :
    projectiveLogLogPotential projectiveOrigin = ⊥ :=
  projectiveLogLogPotential_origin

/-- The log-log potential is quasi-psh on `ℙ¹`. -/
theorem isQPSH_projectiveLogLogPotential :
    (ofFixedModel 1 P1).IsQPSH projectiveLogLogPotential := by
  refine ⟨nativeClosedFormToAtlas projectiveNativeFSBackground.form, ?_⟩
  rw [isThetaPSH_iff_nativeThetaPotential]
  simpa only [sourceNativeAtlasForm_roundTrip] using isThetaPshPotential_projectiveLogLogPotential

/-- Source `ex:naive_res1`: the naive restriction of `φ` to the point `{0}` (with the
complex structure induced from `ℙ¹`) is identically `-∞`, hence not quasi-psh: the
naive restriction is not defined. -/
theorem not_isQPSH_naiveRestriction_projectiveLogLog :
    let hW := DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := 1)
      projectiveOrigin
    letI := SubmanifoldChartedSpace.chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
    haveI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
      (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
    ¬ (ofFixedModel 0 ({projectiveOrigin} : Set P1)).IsQPSH
      (fun y => projectiveLogLogPotential y) := by
  intro hW
  let := SubmanifoldChartedSpace.chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace
    (SubmanifoldChartedSpace.le_of_isClosedConnectedSubmanifold hW) hW.2.2
  intro h
  have hfin := (isQPSH_iff_finite_of_dim_zero _).mp h ⟨projectiveOrigin, rfl⟩
  exact hfin.2 projectiveLogLogPotential_origin

/-- Source `ex:naive_res1` together with `chapter_trace:example:6`: although the naive
restriction to `{0}` is not defined, every real constant is a trace operator of the
log-log potential along `{0}`. -/
theorem projectiveLogLog_trace_origin_const (c : ℝ) :
    IsNaturalSourceTraceRepresentative projectiveNativeFSBackground
      (DominationLogResolution.isClosedConnectedSubmanifold_singleton (k := 1) projectiveOrigin)
      projectiveLogLogPotential (fun _ => (c : EReal)) :=
  isNaturalSourceTraceRepresentative_singleton_const_of_lelong projectiveNativeFSBackground
    projectiveOrigin isQPSH_projectiveLogLogPotential
    squaredLogLelongNumber_projectiveLogLogPotential_origin c

end SGPT.Trace
