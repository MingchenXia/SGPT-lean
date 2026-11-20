import SGPT.Trace.BertiniNaiveRestriction
import SGPT.Trace.SmoothTarget
import SGPT.Toric.ProjectiveSingularityRelations
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence

/-!
# The trace operator is not continuous along increasing sequences

Source `ex:trace:L407` (`chapter_trace.tex`): the trace operator is not continuous along
increasing sequences. On `X = ℙ²` with `ω_FS`, `Y ≅ ℙ¹` the line `{z₂ = 0}`, take an increasing
sequence `(φ_j)_j` in `PSH(X, ω_FS)` whose potentials near `(0,0)` are
`log |z₁|² ∨ (j⁻¹ log |z₂|²) + O(1)`. Their pointwise restrictions to `Y` are
`log |z₁|² + O(1)`, while `log |z₁|² ∨ (j⁻¹ log |z₂|²) → 0` almost everywhere; so the trace is
not continuous along `(φ_j)_j`.

**Global model.** The example is local near `(0,0)`. We realise it on the compact Kähler
surface `X = ℙ¹ × ℙ¹` (`SGPT.Trace.BertiniModel`, product Fubini–Study form `ω`), which
contains the same affine chart `ℂ²` with coordinates `(z₁, z₂)`; `Y = ℙ¹ × {o}` is the curve
`{z₂ = 0}`, embedded by `w ↦ (w, o)`. With `L = log(|Z₁|²/‖Z‖²)` the logarithmic potential of
`ℙ¹` (chart expression `log |z|² - log(1 + |z|²)`) we take

  `φ_j(x) = max (L(x₁), (j+1)⁻¹ L(x₂))`,

an increasing sequence in `PSH(X, ω)` with the book's local form near the origin
(`chartFunction_incSeq`; we index from `j = 0`, with exponent `(j+1)⁻¹`). The literal
`ℙ²` of the book is not available as a complex manifold in this project.

Main results:

* `SGPT.Trace.BertiniIncreasing.isSourceTraceRepresentativeAlong_comp_of_analytic`
  (general): for a potential with analytic singularities and generic Lelong number `0`
  along a smooth target, the naive restriction is itself a trace operator;
* `isThetaPshPotential_incSeq`, `monotone_incSeq`, `chartFunction_incSeq`: the sequence;
* `incSeq_restriction`: `φ_j|_Y = L` (`= log |z₁|² + O(1)`);
* `tendsto_incSeq_of_ne`, `ae_tendsto_chartFunction_incSeq`: `φ_j → 0` off `Y`, and almost
  everywhere in the affine chart;
* `isSourceTraceRepresentativeAlong_incSeq`, `isSourceTraceRepresentativeAlong_zero`: `L` is
  a trace of every `φ_j`, `0` is a trace of the limit `0`;
* `not_tendsto_trace_incSeq`: for every big class `η` on `Y` and all trace operators
  `τ_j` of `φ_j` and `τ` of the limit `0` in `PSH(Y, η)`, `τ_j ↛ τ` in `d_{S,η}`;
  `not_tendsto_trace_incSeq_fubiniStudy` instantiates it with the traces `L` and `0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.Trace.BertiniIncreasing

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ProductComplexManifold
  SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
  SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
open SGPT.Toric SGPT.Trace.BertiniModel

/-! ### The naive restriction of an analytic-singularity potential is a trace -/

section General

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- If `u` is `ω`-psh with analytic singularities and generic Lelong number `0` along the smooth
target `ι : V → M`, and its restriction is not identically `-∞` locally, then the naive
restriction `u ∘ ι` is itself a trace operator of `u` (with the constant quasi-equisingular
approximation `u_j = u` and an admissible target background). Together with
`SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic` (source `ex:resanalyt`) this
identifies the trace class of `u`. -/
theorem isSourceTraceRepresentativeAlong_comp_of_analytic
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {u : M → EReal} (hu : IsThetaPshPotential omega.form.val u)
    (hA : HasManifoldAnalyticSingularityType (n := n) u)
    (hne : LocallyNondegenerate (fun y => u (ι y)))
    (hgen : sourceGenericLelongNumber (n := n) ι u = 0) :
    IsSourceTraceRepresentativeAlong omega omegaV hι u (fun y => u (ι y)) := by
  have happ := isQuasiEquisingularApproximation_const omega omega.form hu hA
  obtain ⟨C, hC, hadm, -⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin hι omega
      omegaV omega.form (ε := fun _ => (0 : ℝ)) antitone_const
  let β : KahlerBackground k V := KahlerBackground.smul hC omegaV
  have hβ : β.form = C • omegaV.form := rfl
  have hpull : ThetaPlurisubharmonic
      (ClosedRealOneOneForm.pullback hι omega.form).val (fun y => u (ι y)) :=
    GlobalPotentialPullback.thetaPlurisubharmonic_comp hι hu.1
  have hdom : (β.form - ClosedRealOneOneForm.pullback hι omega.form).val.IsSemipositive := by
    have h := hadm.2 0
    simp only [zero_smul, add_zero] at h
    exact h
  have hτ : IsThetaPshPotential β.form.val (fun y => u (ι y)) := by
    have h := LocalPotentials.thetaPlurisubharmonic_add_of_semipositive hpull hdom
    rw [add_sub_cancel] at h
    exact ⟨h, hne⟩
  refine ⟨hgen, omega.form, fun _ => 0, fun _ => u, happ, β, hβ ▸ hadm, hτ,
    fun _ => hτ, ?_⟩
  exact @tendsto_const_nhds (ThetaPshL1 β.form.val)
    (singularityPseudoMetricSpace omegaV β.form
      (PluripolarCapacityDichotomy.isBigClass_kahler β)).toUniformSpace.toTopologicalSpace
    ℕ _ atTop

end General

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-! ### The increasing sequence -/

/-- The exponent `(j+1)⁻¹`. -/
def expo (j : ℕ) : ℚ := 1 / ((j : ℚ) + 1)

theorem expo_pos (j : ℕ) : 0 < expo j := by unfold expo; positivity

theorem expo_le_one (j : ℕ) : (expo j : ℝ) ≤ 1 := by
  unfold expo
  push_cast
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem expo_antitone : Antitone fun j => (expo j : ℝ) := by
  intro i j hij
  unfold expo
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 1

theorem tendsto_expo : Tendsto (fun j => (expo j : ℝ)) atTop (𝓝 0) := by
  unfold expo
  push_cast
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The global model of the book's `log |z₁|² ∨ (j⁻¹ log |z₂|²)` on `ℙ¹ × ℙ¹`. -/
def incSeq (j : ℕ) (x : P1 × P1) : EReal :=
  max (projectiveLogSingularity x.1) (((expo j : ℝ) : EReal) * projectiveLogSingularity x.2)

/-- Each `φ_j` lies in `PSH(X, ω)`. -/
theorem isThetaPshPotential_incSeq (j : ℕ) :
    IsThetaPshPotential omegaX.form.val (incSeq j) :=
  IsThetaPshPotential.max (isThetaPshPotential_comp_fst isThetaPshPotential_logSingularity)
    (isThetaPshPotential_comp_snd (isThetaPshPotential_smul_logSingularity
      (by exact_mod_cast expo_pos j) (expo_le_one j)))

/-- The logarithmic potential is nonpositive. -/
theorem projectiveLogSingularity_nonpos (p : P1) : projectiveLogSingularity p ≤ 0 := by
  obtain ⟨b, hb⟩ := projectiveLineAtlas.cover p
  have hp' : (projectiveModelChart b).symm (projectiveModelChart b p) = p :=
    (projectiveModelChart b).left_inv hb
  have hval := chartFunction_logSingularity b (projectiveModelChart b p)
  change projectiveLogSingularity ((projectiveModelChart b).symm _) = _ at hval
  rw [hp'] at hval
  rw [hval]
  set z := projectiveModelChart b p
  have hF : 0 ≤ projectiveFSPotential z := by
    unfold projectiveFSPotential
    exact Real.log_nonneg (by linarith [Complex.normSq_nonneg (projectiveModelEquiv.symm z)])
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hz : z 0 = 0
    · rw [hz, logNormSq_zero, EReal.bot_sub]
      exact bot_le
    rw [logNormSq_of_ne_zero hz, ← EReal.coe_sub, EReal.coe_nonpos]
    have hFz : projectiveFSPotential z = Real.log (1 + ‖z 0‖ ^ 2) := by
      unfold projectiveFSPotential
      rw [projectiveModelEquiv_symm_apply, Complex.normSq_eq_norm_sq]
    rw [hFz]
    have h1 : 0 < ‖z 0‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
    linarith [Real.log_le_log h1 (by linarith : ‖z 0‖ ^ 2 ≤ 1 + ‖z 0‖ ^ 2)]
  · simp only [↓reduceIte, zero_sub]
    rw [← EReal.coe_neg, EReal.coe_nonpos]
    linarith

/-- The sequence `(φ_j)_j` is increasing. -/
theorem monotone_incSeq (x : P1 × P1) : Monotone fun j => incSeq j x := by
  intro i j hij
  apply max_le_max le_rfl
  have hL := projectiveLogSingularity_nonpos x.2
  have hc := expo_antitone hij
  rcases eq_or_ne (projectiveLogSingularity x.2) ⊥ with hb | hb
  · rw [hb, EReal.coe_mul_bot_of_pos (by exact_mod_cast expo_pos i)]
    exact bot_le
  have ht : projectiveLogSingularity x.2 ≠ ⊤ := projectiveLogSingularity_ne_top x.2
  lift projectiveLogSingularity x.2 to ℝ using ⟨ht, hb⟩ with r
  rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hr : r ≤ 0 := EReal.coe_nonpos.mp hL
  nlinarith

/-- The local form of `φ_j` in the affine chart `ℂ² ⊆ ℙ¹ × ℙ¹`:
`φ_j(z₁, z₂) = (log|z₁|² - log(1+|z₁|²)) ∨ ((j+1)⁻¹ (log|z₂|² - log(1+|z₂|²)))`,
i.e. `log |z₁|² ∨ ((j+1)⁻¹ log |z₂|²) + O(1)`. -/
theorem chartFunction_incSeq (j : ℕ) (z w : ComplexModel 1) :
    chartFunction (incSeq j) originChart (prodModelEquiv 1 1 (z, w)) =
      max (logNormSq (z 0) - (projectiveFSPotential z : EReal))
        (((expo j : ℝ) : EReal) * (logNormSq (w 0) - (projectiveFSPotential w : EReal))) := by
  rw [chartFunction_prodNativeChart]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  unfold incSeq
  have h1 := chartFunction_logSingularity false z
  have h2 := chartFunction_logSingularity false w
  change projectiveLogSingularity ((projectiveModelChart false).symm z) = _ at h1
  change projectiveLogSingularity ((projectiveModelChart false).symm w) = _ at h2
  rw [h1, h2]
  simp

/-- Each `φ_j` has analytic singularities (`log |z₁|² ∨ (j⁻¹ log |z₂|²) =
j⁻¹ log(|z₁|^{2j} + |z₂|²) + O(1)`). -/
theorem hasManifoldAnalyticSingularityType_incSeq (j : ℕ) :
    HasManifoldAnalyticSingularityType (n := 1 + 1) (incSeq j) := by
  have h1 := AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
    (contMDiff_fst (X := P1) (Y := P1) (n := 1) (m := 1))
    hasManifoldAnalyticSingularityType_logSingularity
  have h2 := AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp
    (contMDiff_snd (X := P1) (Y := P1) (n := 1) (m := 1))
    hasManifoldAnalyticSingularityType_logSingularity
  intro e z hz
  exact RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max (h1 e z hz)
    (QuasiEquisingularRationalScaling.hasAnalyticSingularityTypeAt_pos_rat_smul (h2 e z hz)
      (expo_pos j))

/-! ### Restriction to `Y = {z₂ = 0}` and the pointwise limit -/

/-- The curve `Y = {z₂ = 0} = ℙ¹ × {o}`. -/
def ιY (w : P1) : P1 × P1 := (w, projectiveOrigin)

theorem contMDiff_ιY :
    ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (1 + 1)) ∞ ιY :=
  contMDiff_prodMk contMDiff_id contMDiff_const

/-- Source `ex:trace:L407`: the pointwise restriction of every `φ_j` to `Y` is `L`, i.e.
`log |z₁|² + O(1)` near the origin. -/
theorem incSeq_restriction (j : ℕ) : (fun w => incSeq j (ιY w)) = projectiveLogSingularity := by
  funext w
  simp [incSeq, ιY, projectiveLogSingularity_origin,
    EReal.coe_mul_bot_of_pos (show (0 : ℝ) < expo j by exact_mod_cast expo_pos j)]

/-- Off the curve `Y`, `φ_j → 0`. -/
theorem tendsto_incSeq_of_ne {x : P1 × P1} (hx : x.2 ≠ projectiveOrigin) :
    Tendsto (fun j => incSeq j x) atTop (𝓝 0) := by
  have hb := BertiniNaiveRes.projectiveLogSingularity_ne_bot hx
  have ht := projectiveLogSingularity_ne_top x.2
  have h1 := projectiveLogSingularity_nonpos x.1
  unfold incSeq
  lift projectiveLogSingularity x.2 to ℝ using ⟨ht, hb⟩ with r
  have hlim : Tendsto (fun j => ((expo j : ℝ) : EReal) * (r : EReal)) atTop (𝓝 0) := by
    have : Tendsto (fun j => ((expo j : ℝ) * r : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_expo.mul_const r
    have h := EReal.tendsto_coe.mpr this
    simpa only [EReal.coe_mul, EReal.coe_zero] using h
  have hmax := (tendsto_const_nhds (x := projectiveLogSingularity x.1)).max hlim
  rwa [max_eq_right h1] at hmax

/-- Source `ex:trace:L407`: in the affine chart, `log |z₁|² ∨ (j⁻¹ log |z₂|²) + O(1) → 0`
almost everywhere (everywhere off the line `{z₂ = 0}`). -/
theorem ae_tendsto_chartFunction_incSeq :
    ∀ᵐ y ∂(volume : Measure (ComplexModel (1 + 1))),
      Tendsto (fun j => chartFunction (incSeq j) originChart y) atTop (𝓝 0) := by
  let ℓ : ComplexModel (1 + 1) →ₗ[ℂ] ℂ :=
    (EuclideanSpace.proj (1 : Fin (1 + 1)) : ComplexModel (1 + 1) →L[ℂ] ℂ).toLinearMap
  have hker : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single (1 : Fin (1 + 1)) (1 : ℂ) ∈ LinearMap.ker ℓ := by
      rw [h]; exact Submodule.mem_top
    simp [ℓ] at hmem
  have hnull : volume ((LinearMap.ker ℓ : Submodule ℂ (ComplexModel (1 + 1))) :
      Set (ComplexModel (1 + 1))) = 0 :=
    Measure.addHaar_submodule volume ((LinearMap.ker ℓ).restrictScalars ℝ) (by
      intro h
      apply hker
      rw [eq_top_iff]
      intro v _
      have : v ∈ (LinearMap.ker ℓ).restrictScalars ℝ := by rw [h]; exact Submodule.mem_top
      exact this)
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro y hy
  simp only [mem_ofPred_eq] at hy
  change ℓ y = 0
  by_contra hne
  apply hy
  have hx : ((projectiveModelChart false).symm ((prodModelEquiv 1 1).symm y).1,
      (projectiveModelChart false).symm ((prodModelEquiv 1 1).symm y).2).2 ≠ projectiveOrigin := by
    intro h
    apply hne
    have h' : (projectiveModelChart false).symm ((prodModelEquiv 1 1).symm y).2 =
        (projectiveModelChart false).symm 0 := h
    have hinj := (projectiveModelChart false).symm.injOn (by
      simp [projectiveModelChart, projectiveQuotientScalarChart_target]) (by
      simp [projectiveModelChart, projectiveQuotientScalarChart_target]) h'
    have : ((prodModelEquiv 1 1).symm y).2 0 = 0 := by rw [hinj]; rfl
    simp only [prodModelEquiv, ContinuousLinearEquiv.symm_symm] at this
    exact this
  exact tendsto_incSeq_of_ne hx

/-! ### Traces of `φ_j` and of the limit `0` -/

theorem lelongNumber_eq_zero_of_ne_bot {u : P1 × P1 → EReal}
    (hu : IsThetaPshPotential omegaX.form.val u) {x : P1 × P1} (hx : u x ≠ ⊥) :
    lelongNumber (n := 1 + 1) u x = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_not_gt
  intro hpos
  exact hx (eq_bot_of_lelongNumber_pos (by norm_num) hu.1 hpos)

theorem sourceGenericLelongNumber_eq_zero_of_ne_bot {u : P1 × P1 → EReal}
    (hu : IsThetaPshPotential omegaX.form.val u) {y : P1} (hy : u (ιY y) ≠ ⊥) :
    sourceGenericLelongNumber (n := 1 + 1) ιY u = 0 := by
  apply le_antisymm _ bot_le
  have h := lelongNumber_eq_two_mul_squaredLog (n := 1 + 1) (by norm_num) u (ιY y)
  rw [lelongNumber_eq_zero_of_ne_bot hu hy] at h
  have h0 : squaredLogLelongNumber (n := 1 + 1) u (ιY y) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  exact (iInf_le _ y).trans h0.le

/-- Source `ex:trace:L407`: `ν(φ_j, Y) = 0`. -/
theorem sourceGenericLelongNumber_incSeq (j : ℕ) :
    sourceGenericLelongNumber (n := 1 + 1) ιY (incSeq j) = 0 :=
  sourceGenericLelongNumber_eq_zero_of_ne_bot (isThetaPshPotential_incSeq j)
    (y := projectiveInfinity) (by
      rw [show incSeq j (ιY projectiveInfinity) = projectiveLogSingularity projectiveInfinity from
        congrFun (incSeq_restriction j) _, projectiveLogSingularity_infinity]
      exact EReal.zero_ne_bot)

/-- The pointwise restriction `L` is a trace operator of every `φ_j` along `Y`. -/
theorem isSourceTraceRepresentativeAlong_incSeq (omegaV : KahlerBackground 1 P1) (j : ℕ) :
    IsSourceTraceRepresentativeAlong omegaX omegaV contMDiff_ιY (incSeq j)
      projectiveLogSingularity := by
  have h := isSourceTraceRepresentativeAlong_comp_of_analytic omegaX omegaV contMDiff_ιY
    (isThetaPshPotential_incSeq j) (hasManifoldAnalyticSingularityType_incSeq j)
    (by rw [incSeq_restriction]; exact isThetaPshPotential_logSingularity.2)
    (sourceGenericLelongNumber_incSeq j)
  rwa [incSeq_restriction] at h

/-- `0` (the limit of `φ_j`) has the trace `0` along `Y`. -/
theorem isSourceTraceRepresentativeAlong_zero (omegaV : KahlerBackground 1 P1) :
    IsSourceTraceRepresentativeAlong omegaX omegaV contMDiff_ιY (fun _ => 0) (fun _ => 0) := by
  have hz : IsThetaPshPotential omegaX.form.val (fun _ : P1 × P1 => (0 : EReal)) :=
    PluripolarCapacityDichotomy.isThetaPshPotential_zero omegaX
  have hA : HasManifoldAnalyticSingularityType (n := 1 + 1) (fun _ : P1 × P1 => (0 : EReal)) := by
    simpa using QuasiEquisingularComparison.hasManifoldAnalyticSingularityType_const
      (n := 1 + 1) (M := P1 × P1) (0 : ℝ)
  exact isSourceTraceRepresentativeAlong_comp_of_analytic omegaX omegaV contMDiff_ιY hz hA
    (fun x U _ hxU => ⟨x, hxU, EReal.zero_ne_bot⟩)
    (sourceGenericLelongNumber_eq_zero_of_ne_bot hz (y := projectiveOrigin) EReal.zero_ne_bot)

/-! ### Non-continuity -/

private theorem sourcePEquivalent_trans {u v w : P1 → EReal}
    (huv : SourcePEquivalent (n := 1) u v) (hvw : SourcePEquivalent (n := 1) v w) :
    SourcePEquivalent (n := 1) u w :=
  ⟨SourcePOrder.trans projectiveNativeFSBackground huv.1 hvw.1,
    SourcePOrder.trans projectiveNativeFSBackground hvw.2 huv.2⟩

private theorem sourcePEquivalent_symm {u v : P1 → EReal}
    (huv : SourcePEquivalent (n := 1) u v) : SourcePEquivalent (n := 1) v u :=
  ⟨huv.2, huv.1⟩

/-- Source `ex:trace:L407`: the trace operator is not continuous along the increasing
sequence `(φ_j)_j`. For every Kähler `ω_Y` and big `η` on `Y`, all trace operators
`τ_j ∈ PSH(Y, η)` of `φ_j` and `τ ∈ PSH(Y, η)` of the limit `0` (with arbitrary auxiliary
choices), `τ_j` does not converge to `τ` in `d_{S,η}`: every `τ_j ∼_P L` and `τ ∼_P 0`, while
`L ≁_P 0`. -/
theorem not_tendsto_trace_incSeq (omegaV : KahlerBackground 1 P1)
    (η : ClosedRealOneOneForm 1 P1) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τ : ℕ → ThetaPshL1 η.val) (τ₀ : ThetaPshL1 η.val)
    {omegai : ℕ → KahlerBackground (1 + 1) (P1 × P1)} {omegaVi : ℕ → KahlerBackground 1 P1}
    {omega₀ : KahlerBackground (1 + 1) (P1 × P1)} {omegaV₀ : KahlerBackground 1 P1}
    (hT : ∀ j, IsSourceTraceRepresentativeAlong (omegai j) (omegaVi j) contMDiff_ιY
      (incSeq j) (τ j).val)
    (hT₀ : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ contMDiff_ιY (fun _ => 0) τ₀.val) :
    ¬ Tendsto τ atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace τ₀) := by
  let := singularityPseudoMetricSpace omegaV η hη
  intro hlim
  have hP : ∀ j, SourcePEquivalent (n := 1) (τ j).val projectiveLogSingularity := by
    intro j
    have h := sourcePEquivalent_trace_restriction_of_analytic (by norm_num) (omegaVi j)
      contMDiff_ιY (hT j) (hasManifoldAnalyticSingularityType_incSeq j)
    rwa [incSeq_restriction] at h
  have hP₀ : SourcePEquivalent (n := 1) τ₀.val (fun _ => 0) := by
    have hA : HasManifoldAnalyticSingularityType (n := 1 + 1)
        (fun _ : P1 × P1 => (0 : EReal)) := by
      simpa using QuasiEquisingularComparison.hasManifoldAnalyticSingularityType_const
        (n := 1 + 1) (M := P1 × P1) (0 : ℝ)
    exact sourcePEquivalent_trace_restriction_of_analytic (by norm_num) omegaV₀ contMDiff_ιY
      hT₀ hA
  -- the singularity distance is the pseudometric distance
  have hdist : ∀ a b : ThetaPshL1 η.val,
      singularityDistance omegaV η hη a.val b.val = (dist a b : EReal) := by
    intro a b
    obtain ⟨m, _, _, _, hD⟩ := exists_tendsto_singularityDistance omegaV η hη a.property
      b.property
    have hd : dist a b = m := by
      simpa only [hD, EReal.toReal_coe] using dist_eq_singularityDistance_toReal omegaV η hη a b
    rw [hd]
    exact hD
  have hzero : ∀ j, dist (τ 0) (τ j) = 0 := by
    intro j
    have hPj : SourcePEquivalent (n := 1) (τ 0).val (τ j).val :=
      sourcePEquivalent_trans (hP 0) (sourcePEquivalent_symm (hP j))
    have h := (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omegaV η hη (τ 0).property (τ j).property).mpr hPj
    rw [hdist] at h
    exact_mod_cast h
  have htend : Tendsto (fun j => dist (τ j) τ₀) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.mp hlim)
  have hle : ∀ j, dist (τ 0) τ₀ ≤ dist (τ j) τ₀ := by
    intro j
    calc dist (τ 0) τ₀ ≤ dist (τ 0) (τ j) + dist (τ j) τ₀ := dist_triangle _ _ _
      _ = dist (τ j) τ₀ := by rw [hzero j, zero_add]
  have h0 : dist (τ 0) τ₀ = 0 :=
    le_antisymm (ge_of_tendsto htend (Eventually.of_forall hle)) dist_nonneg
  have hP0 : SourcePEquivalent (n := 1) (τ 0).val τ₀.val := by
    apply (SingularCanonicalDistanceZeroPEquivalence.singularityDistance_eq_zero_iff_sourcePEquivalent
      omegaV η hη (τ 0).property τ₀.property).mp
    rw [hdist, h0]
    rfl
  have hbad : SourcePEquivalent (n := 1) projectiveLogSingularity (fun _ => 0) :=
    sourcePEquivalent_trans (sourcePEquivalent_symm (hP 0)) (sourcePEquivalent_trans hP0 hP₀)
  exact not_sourcePEquivalent_projectiveLogSingularity_zero hbad

/-- Instance of `not_tendsto_trace_incSeq` with the trace `L` of every `φ_j`
(`isSourceTraceRepresentativeAlong_incSeq`) and the trace `0` of the limit, both in
`PSH(Y, ω_FS)`: the statement is not vacuous. -/
theorem not_tendsto_trace_incSeq_fubiniStudy :
    ¬ Tendsto (fun _ : ℕ => (⟨projectiveLogSingularity, isThetaPshPotential_logSingularity⟩ :
        ThetaPshL1 projectiveNativeFSBackground.form.val)) atTop
      (@nhds (ThetaPshL1 projectiveNativeFSBackground.form.val)
        (singularityPseudoMetricSpace projectiveNativeFSBackground
          projectiveNativeFSBackground.form
          (PluripolarCapacityDichotomy.isBigClass_kahler projectiveNativeFSBackground)).toUniformSpace.toTopologicalSpace
        ⟨fun _ => 0, PluripolarCapacityDichotomy.isThetaPshPotential_zero _⟩) :=
  not_tendsto_trace_incSeq projectiveNativeFSBackground projectiveNativeFSBackground.form
    (PluripolarCapacityDichotomy.isBigClass_kahler projectiveNativeFSBackground) _ _
    (fun j => isSourceTraceRepresentativeAlong_incSeq projectiveNativeFSBackground j)
    (isSourceTraceRepresentativeAlong_zero projectiveNativeFSBackground)

end SGPT.Trace.BertiniIncreasing
