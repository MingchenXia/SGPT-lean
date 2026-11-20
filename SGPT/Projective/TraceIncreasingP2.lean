import SGPT.Projective.Sections
import SGPT.Projective.Maps
import SGPT.Trace.BertiniIncreasingTrace

/-!
# The trace operator is not continuous along increasing sequences: the model `X = ℙ²`

Source `ex:trace:L407` (`chapter_trace.tex`): *Let `X = ℙ²` with coordinates `(z₁, z₂)` on
`ℂ² ⊆ X`, `ω_FS` the Fubini–Study metric, and `Y ≅ ℙ¹` the curve `{z₂ = 0}`.  Consider an
increasing sequence `(φ_j)_j` in `PSH(X, ω_FS)` whose potentials near `(0,0)` are
`log |z₁|² ∨ (j⁻¹ log |z₂|²) + O(1)`.  The pointwise restrictions to `Y` are
`log |z₁|² + O(1)`; on the other hand `log |z₁|² ∨ (j⁻¹ log |z₂|²) → 0` almost everywhere.  So
the trace operator is not continuous along `(φ_j)_j`.*

This file realises the example on the book's model: `X = ℙ² = ComplexProjectiveSpace 2` with its
Fubini–Study Kähler form `ω_FS` (`SGPT.Projective.ComplexProjectiveSpace.fsBackground`), the
affine chart `ℂ² = U_0 = {Z_0 ≠ 0}` with coordinates `(z₁, z₂) = (Z₁/Z₀, Z₂/Z₀)`
(`originChart`), and `Y = {Z₂ = 0}` (the closure of `{z₂ = 0}`), parametrised by the native
projective line via `ιY [a : b] = [b : a : 0]` (`range_ιY`, `injective_ιY`; on the finite chart
`w ↦ (w, 0)`, `ιY_finite`).  With `L_i = log(|Z_i|²/‖Z‖²)` (`coordLog i`) we take

  `φ_j = max (L₁, (j+1)⁻¹ L₂)`

(indexed from `j = 0`); its chart expression is
`(log |z₁|² - F) ∨ ((j+1)⁻¹ (log |z₂|² - F))`, `F = log(1 + |z₁|² + |z₂|²)` smooth
(`chartFunction_incSeq`), i.e. the book's `log |z₁|² ∨ (j⁻¹ log |z₂|²) + O(1)`.

The proofs follow the `ℙ¹ × ℙ¹` model of lane S23 (`SGPT.Trace.BertiniIncreasing`), whose
general lemma `isSourceTraceRepresentativeAlong_comp_of_analytic` (the naive restriction of a
potential with analytic singularities and generic Lelong number `0` is a trace) is reused.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace SGPT.Projective.TraceIncreasingP2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
  SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
  SGPT.Foundations.Analysis.FirstPass.TraceBackground
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition SquaredLogLelongSourceNormalization
  SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
open SGPT.Toric SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.BertiniIncreasing (expo expo_pos expo_le_one expo_antitone tendsto_expo
  isSourceTraceRepresentativeAlong_comp_of_analytic)

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)
local notation "P2" => ComplexProjectiveSpace 2

/-- The Fubini–Study Kähler background of `ℙ²`. -/
abbrev omegaP2 : KahlerBackground 2 P2 := fsBackground

/-! ### The increasing sequence -/

/-- `φ_j = max (log(|Z₁|²/‖Z‖²), (j+1)⁻¹ log(|Z₂|²/‖Z‖²))` on `ℙ²`. -/
def incSeq (j : ℕ) (p : P2) : EReal :=
  max (coordLog 1 p) (((expo j : ℝ) : EReal) * coordLog 2 p)

/-- Each `φ_j` lies in `PSH(ℙ², ω_FS)`. -/
theorem isThetaPshPotential_incSeq (j : ℕ) :
    IsThetaPshPotential omegaP2.form.val (incSeq j) :=
  IsThetaPshPotential.max (isThetaPshPotential_coordLog 1)
    (isThetaPshPotential_smul_coordLog 2 (by exact_mod_cast expo_pos j) (expo_le_one j))

/-- The sequence `(φ_j)_j` is increasing. -/
theorem monotone_incSeq (p : P2) : Monotone fun j => incSeq j p := by
  intro i j hij
  apply max_le_max le_rfl
  have hL := coordLog_nonpos 2 p
  have hc := expo_antitone hij
  rcases eq_or_ne (coordLog 2 p) ⊥ with hb | hb
  · rw [hb, EReal.coe_mul_bot_of_pos (by exact_mod_cast expo_pos i)]
    exact bot_le
  have ht : coordLog 2 p ≠ ⊤ := coordLog_ne_top 2 p
  lift coordLog 2 p to ℝ using ⟨ht, hb⟩ with x
  rw [← EReal.coe_mul, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hx : x ≤ 0 := EReal.coe_nonpos.mp hL
  nlinarith

/-- The affine chart `ℂ² = U_0 = {Z₀ ≠ 0} ⊆ ℙ²`, `[Z] ↦ (z₁, z₂) = (Z₁/Z₀, Z₂/Z₀)` (in the
model `ComplexModel 2` the coordinates are indexed `z 0 = z₁`, `z 1 = z₂`). -/
def originChart : ComplexChart 2 P2 := ⟨affineChart 0, affineChart_mem_atlas 0⟩

/-- The Fubini–Study potential of `ℂ² ⊆ ℙ²`: `F(z) = log(1 + |z₁|² + |z₂|²)`. -/
theorem fsPotential_eq (z : ComplexModel 2) :
    fsPotential z = Real.log (1 + ‖z 0‖ ^ 2 + ‖z 1‖ ^ 2) := by
  rw [fsPotential, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, add_assoc]

/-- The local form of `φ_j` on `ℂ² ⊆ ℙ²`:
`φ_j(z₁, z₂) = (log |z₁|² - F) ∨ ((j+1)⁻¹ (log |z₂|² - F))` with `F = log(1 + |z₁|² + |z₂|²)`
smooth, i.e. `log |z₁|² ∨ ((j+1)⁻¹ log |z₂|²) + O(1)`. -/
theorem chartFunction_incSeq (j : ℕ) (z : ComplexModel 2) :
    chartFunction (incSeq j) originChart z =
      max (logNormSq (z 0) - (fsPotential z : EReal))
        (((expo j : ℝ) : EReal) * (logNormSq (z 1) - (fsPotential z : EReal))) := by
  change incSeq j (affinePoint 0 z) = _
  have h1 := coordLog_affinePoint_succAbove (0 : Fin 3) 0 z
  have h2 := coordLog_affinePoint_succAbove (0 : Fin 3) 1 z
  simp only [Fin.succAbove_zero] at h1 h2
  rw [incSeq]
  exact congrArg₂ max h1 (congrArg _ h2)

private theorem sub_coe_le {a : EReal} {F : ℝ} (hF : 0 ≤ F) : a - (F : EReal) ≤ a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- The `O(1)` of the book, upper half: `φ_j ≤ log |z₁|² ∨ ((j+1)⁻¹ log |z₂|²)` on `ℂ²`. -/
theorem chartFunction_incSeq_le (j : ℕ) (z : ComplexModel 2) :
    chartFunction (incSeq j) originChart z ≤
      max (logNormSq (z 0)) (((expo j : ℝ) : EReal) * logNormSq (z 1)) := by
  rw [chartFunction_incSeq]
  have hF := fsPotential_nonneg z
  have hc : (0 : ℝ) < expo j := by exact_mod_cast expo_pos j
  apply max_le_max
  · exact sub_coe_le hF
  · exact mul_le_mul_of_nonneg_left (sub_coe_le hF) (EReal.coe_nonneg.mpr hc.le)

/-- The `O(1)` of the book, lower half:
`log |z₁|² ∨ ((j+1)⁻¹ log |z₂|²) ≤ φ_j + log(1 + |z₁|² + |z₂|²)` on `ℂ²`; the correction
`F = log(1 + ‖z‖²)` is smooth, hence bounded near `(0,0)`. -/
theorem le_chartFunction_incSeq_add (j : ℕ) (z : ComplexModel 2) :
    max (logNormSq (z 0)) (((expo j : ℝ) : EReal) * logNormSq (z 1)) ≤
      chartFunction (incSeq j) originChart z + (fsPotential z : EReal) := by
  rw [chartFunction_incSeq]
  have hF := fsPotential_nonneg z
  have hc : (0 : ℝ) < expo j := by exact_mod_cast expo_pos j
  have hc1 := expo_le_one j
  apply max_le
  · calc logNormSq (z 0) = logNormSq (z 0) - (fsPotential z : EReal) + (fsPotential z : EReal) :=
          EReal.sub_add_cancel.symm
      _ ≤ _ := add_le_add_left (le_max_left _ _) _
  · rcases eq_or_ne (logNormSq (z 1)) ⊥ with hb | hb
    · rw [hb, EReal.coe_mul_bot_of_pos hc]
      exact bot_le
    have ht : logNormSq (z 1) ≠ ⊤ := logNormSq_ne_top _
    lift logNormSq (z 1) to ℝ using ⟨ht, hb⟩ with x
    calc ((expo j : ℝ) : EReal) * (x : EReal)
        ≤ ((expo j : ℝ) : EReal) * ((x : EReal) - (fsPotential z : EReal)) +
            (fsPotential z : EReal) := by
          rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
            EReal.coe_le_coe_iff]
          nlinarith
      _ ≤ _ := add_le_add_left (le_max_right _ _) _

/-- Each `φ_j` has analytic singularities. -/
theorem hasManifoldAnalyticSingularityType_incSeq (j : ℕ) :
    HasManifoldAnalyticSingularityType (n := 2) (incSeq j) := by
  intro e z hz
  exact RationalAnalyticMaximum.hasAnalyticSingularityTypeAt_max
    (hasManifoldAnalyticSingularityType_coordLog 1 e z hz)
    (hasManifoldAnalyticSingularityType_smul_coordLog 2 (expo_pos j) e z hz)

/-! ### The curve `Y = {z₂ = 0}` -/

/-- The linear map `(a, b) ↦ (b, a, 0)`. -/
def lineLinear : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 1, v 0, 0]
  map_add' v w := by ext m; fin_cases m <;> simp
  map_smul' c v := by ext m; fin_cases m <;> simp

theorem lineLinear_injective : Function.Injective lineLinear := by
  intro v w h
  have h0 := congrFun h 1
  have h1 := congrFun h 0
  simp [lineLinear] at h0 h1
  ext m
  fin_cases m
  · exact h0
  · exact h1

/-- The embedding `ι : ℙ¹ → ℙ²`, `[a : b] ↦ [b : a : 0]`, of the curve `Y = {Z₂ = 0}`. -/
def ιY : P1 → P2 := linearMap lineLinear lineLinear_injective ∘ fromNativeLine

theorem contMDiff_ιY : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 2) ∞ ιY :=
  (contMDiff_linearMap _ _).comp contMDiff_fromNativeLine

theorem lineLinear_ne_zero {v : Fin 2 → ℂ} (hv : v ≠ 0) : lineLinear v ≠ 0 := by
  simpa using lineLinear_injective.ne hv

theorem ιY_mk (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    ιY (Projectivization.mk ℂ v hv) = mk (lineLinear v) (lineLinear_ne_zero hv) := by
  change linearMap lineLinear lineLinear_injective (mk v hv) = _
  exact linearMap_mk _ _ v hv

theorem injective_ιY : Function.Injective ιY :=
  (Projectivization.map_injective lineLinear lineLinear_injective).comp Function.injective_id

/-- `Y = ι(ℙ¹)` is the line `{Z₂ = 0}` of `ℙ²`. -/
theorem range_ιY : range ιY = {p : P2 | p.rep 2 = 0} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Projectivization.ind with
    | h v hv =>
      rw [mem_ofPred_eq, ιY_mk]
      obtain ⟨c, _, hc⟩ := rep_smul (mk (lineLinear v) (lineLinear_ne_zero hv)) _ rfl
      rw [hc]
      simp [lineLinear]
  · intro hp
    have hp' : p.rep 2 = 0 := hp
    have hv : ![p.rep 1, p.rep 0] ≠ 0 := by
      intro h
      apply p.rep_ne_zero
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp at h0 h1
      ext m
      fin_cases m
      · exact h1
      · exact h0
      · exact hp'
    refine ⟨Projectivization.mk ℂ ![p.rep 1, p.rep 0] hv, ?_⟩
    rw [ιY_mk]
    conv_rhs => rw [← mk_rep p]
    congr 1
    ext m
    fin_cases m
    · rfl
    · rfl
    · exact hp'.symm

/-- On the finite chart, `ι` is `w ↦ (z₁, z₂) = (w, 0)`. -/
theorem ιY_finite (w : ComplexModel 1) :
    ιY ((projectiveModelChart false).symm w) = affinePoint 0 (WithLp.toLp 2 ![w 0, 0]) := by
  rw [projectiveModelChart_symm_eq_mk, ιY_mk, affinePoint]
  apply (mk_eq_mk_iff _ _).mpr
  refine ⟨1, ?_⟩
  ext m
  fin_cases m <;> simp [lineLinear, projectiveAffineLift, affineLift, projectiveModelEquiv_symm_apply]

/-! ### The pointwise restriction -/

/-- The logarithmic potential `log(|Z₀|²/‖Z‖²)` of the native `ℙ¹` in homogeneous
coordinates. -/
theorem projectiveLogSingularity_mk (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveLogSingularity (Projectivization.mk ℂ v hv) =
      ENNReal.log (ENNReal.ofReal (‖v 0‖ ^ 2 / (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2))) := by
  set p := Projectivization.mk ℂ v hv
  have hmem : v ∈ p.submodule := by
    rw [Projectivization.submodule_mk]
    exact Submodule.mem_span_singleton_self _
  have hne : (⟨v, hmem⟩ : p.submodule) ≠ 0 := fun h => hv (congrArg Subtype.val h)
  rw [projectiveLogSingularity, projectiveCoordinateMetricLog,
    projectiveFiberMetric_eq_ratio p _ ⟨v, hmem⟩ hne, projectiveCoordinateSection_apply,
    div_pow, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

theorem coordLog_one_ιY (q : P1) : coordLog 1 (ιY q) = projectiveLogSingularity q := by
  induction q using Projectivization.ind with
  | h v hv =>
    rw [ιY_mk, coordLog_mk, projectiveLogSingularity_mk]
    congr 3
    simp [homNormSq, Fin.sum_univ_three, lineLinear]
    ring

theorem coordLog_two_ιY (q : P1) : coordLog 2 (ιY q) = ⊥ := by
  induction q using Projectivization.ind with
  | h v hv =>
    rw [ιY_mk, coordLog_mk_eq_bot_iff]
    simp [lineLinear]

/-- `L₂ = log(|Z₂|²/‖Z‖²)` is `-∞` exactly on `Y`. -/
theorem coordLog_two_eq_bot_iff (p : P2) : coordLog 2 p = ⊥ ↔ p ∈ range ιY := by
  rw [range_ιY, mem_ofPred_eq]
  conv_lhs => rw [← mk_rep p]
  exact coordLog_mk_eq_bot_iff 2 _ _

/-- Source `ex:trace:L407`: the pointwise restriction of every `φ_j` to `Y` is
`L = log(|Z₁|²/‖Z‖²)|_Y`, i.e. `log |z₁|² + O(1)` near the origin. -/
theorem incSeq_restriction (j : ℕ) :
    (fun q => incSeq j (ιY q)) = projectiveLogSingularity := by
  funext q
  rw [incSeq, coordLog_one_ιY, coordLog_two_ιY,
    EReal.coe_mul_bot_of_pos (show (0 : ℝ) < expo j by exact_mod_cast expo_pos j)]
  exact max_bot_right _

/-- Source `ex:trace:L407`, in coordinates: on `Y ∩ ℂ² = {z₂ = 0}`,
`φ_j(z₁, 0) = log |z₁|² - log(1 + |z₁|²)`, i.e. `log |z₁|² + O(1)`. -/
theorem incSeq_restriction_chart (j : ℕ) (w : ℂ) :
    chartFunction (incSeq j) originChart (WithLp.toLp 2 ![w, 0]) =
      logNormSq w - ((Real.log (1 + ‖w‖ ^ 2) : ℝ) : EReal) := by
  rw [chartFunction_incSeq, fsPotential_eq]
  have hc : (0 : ℝ) < expo j := by exact_mod_cast expo_pos j
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  change max _ (((expo j : ℝ) : EReal) * (logNormSq (0 : ℂ) - _)) = _
  rw [logNormSq_zero, EReal.bot_sub, EReal.coe_mul_bot_of_pos hc]
  exact max_bot_right _

/-- Off the curve `Y`, `φ_j → 0`. -/
theorem tendsto_incSeq_of_not_mem {x : P2} (hx : x ∉ range ιY) :
    Tendsto (fun j => incSeq j x) atTop (𝓝 0) := by
  have hb : coordLog 2 x ≠ ⊥ := fun h => hx ((coordLog_two_eq_bot_iff x).mp h)
  have ht := coordLog_ne_top 2 x
  have h1 := coordLog_nonpos 1 x
  unfold incSeq
  lift coordLog 2 x to ℝ using ⟨ht, hb⟩ with r
  have hlim : Tendsto (fun j => ((expo j : ℝ) : EReal) * (r : EReal)) atTop (𝓝 0) := by
    have : Tendsto (fun j => ((expo j : ℝ) * r : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_expo.mul_const r
    have h := EReal.tendsto_coe.mpr this
    simpa only [EReal.coe_mul, EReal.coe_zero] using h
  have hmax := (tendsto_const_nhds (x := coordLog 1 x)).max hlim
  rwa [max_eq_right h1] at hmax

/-- Source `ex:trace:L407`: on `ℂ² ⊆ ℙ²`, `log |z₁|² ∨ (j⁻¹ log |z₂|²) + O(1) → 0` almost
everywhere (everywhere off the line `{z₂ = 0}`). -/
theorem ae_tendsto_chartFunction_incSeq :
    ∀ᵐ y ∂(volume : Measure (ComplexModel 2)),
      Tendsto (fun j => chartFunction (incSeq j) originChart y) atTop (𝓝 0) := by
  let ℓ : ComplexModel 2 →ₗ[ℂ] ℂ :=
    (EuclideanSpace.proj (1 : Fin 2) : ComplexModel 2 →L[ℂ] ℂ).toLinearMap
  have hker : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single (1 : Fin 2) (1 : ℂ) ∈ LinearMap.ker ℓ := by
      rw [h]; exact Submodule.mem_top
    simp [ℓ] at hmem
  have hnull : volume ((LinearMap.ker ℓ : Submodule ℂ (ComplexModel 2)) :
      Set (ComplexModel 2)) = 0 :=
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
  apply tendsto_incSeq_of_not_mem
  intro hmem
  rw [← coordLog_two_eq_bot_iff] at hmem
  change coordLog 2 (mk (affineLift 0 y) (affineLift_ne_zero 0 y)) = ⊥ at hmem
  rw [coordLog_mk_eq_bot_iff] at hmem
  apply hne
  have h2 : (2 : Fin 3) = (0 : Fin 3).succAbove 1 := rfl
  rw [h2, affineLift_succAbove] at hmem
  exact hmem

/-! ### Traces of `φ_j` and of the limit `0` -/

theorem lelongNumber_eq_zero_of_ne_bot {u : P2 → EReal}
    (hu : IsThetaPshPotential omegaP2.form.val u) {x : P2} (hx : u x ≠ ⊥) :
    lelongNumber (n := 2) u x = 0 := by
  apply le_antisymm _ bot_le
  apply le_of_not_gt
  intro hpos
  exact hx (eq_bot_of_lelongNumber_pos (by norm_num) hu.1 hpos)

theorem sourceGenericLelongNumber_eq_zero_of_ne_bot {u : P2 → EReal}
    (hu : IsThetaPshPotential omegaP2.form.val u) {y : P1} (hy : u (ιY y) ≠ ⊥) :
    sourceGenericLelongNumber (n := 2) ιY u = 0 := by
  apply le_antisymm _ bot_le
  have h := lelongNumber_eq_two_mul_squaredLog (n := 2) (by norm_num) u (ιY y)
  rw [lelongNumber_eq_zero_of_ne_bot hu hy] at h
  have h0 : squaredLogLelongNumber (n := 2) u (ιY y) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left (by norm_num)
  exact (iInf_le _ y).trans h0.le

/-- Source `ex:trace:L407`: `ν(φ_j, Y) = 0`. -/
theorem sourceGenericLelongNumber_incSeq (j : ℕ) :
    sourceGenericLelongNumber (n := 2) ιY (incSeq j) = 0 :=
  sourceGenericLelongNumber_eq_zero_of_ne_bot (isThetaPshPotential_incSeq j)
    (y := projectiveInfinity) (by
      rw [show incSeq j (ιY projectiveInfinity) = projectiveLogSingularity projectiveInfinity from
        congrFun (incSeq_restriction j) _, projectiveLogSingularity_infinity]
      exact EReal.zero_ne_bot)

/-- The pointwise restriction `L` is a trace operator of every `φ_j` along `Y`. -/
theorem isSourceTraceRepresentativeAlong_incSeq (omegaV : KahlerBackground 1 P1) (j : ℕ) :
    IsSourceTraceRepresentativeAlong omegaP2 omegaV contMDiff_ιY (incSeq j)
      projectiveLogSingularity := by
  have h := isSourceTraceRepresentativeAlong_comp_of_analytic omegaP2 omegaV contMDiff_ιY
    (isThetaPshPotential_incSeq j) (hasManifoldAnalyticSingularityType_incSeq j)
    (by rw [incSeq_restriction]; exact SGPT.Trace.BertiniModel.isThetaPshPotential_logSingularity.2)
    (sourceGenericLelongNumber_incSeq j)
  rwa [incSeq_restriction] at h

/-- `0` (the limit of `φ_j`) has the trace `0` along `Y`. -/
theorem isSourceTraceRepresentativeAlong_zero (omegaV : KahlerBackground 1 P1) :
    IsSourceTraceRepresentativeAlong omegaP2 omegaV contMDiff_ιY (fun _ => 0) (fun _ => 0) := by
  have hz : IsThetaPshPotential omegaP2.form.val (fun _ : P2 => (0 : EReal)) :=
    PluripolarCapacityDichotomy.isThetaPshPotential_zero omegaP2
  have hA : HasManifoldAnalyticSingularityType (n := 2) (fun _ : P2 => (0 : EReal)) := by
    simpa using QuasiEquisingularComparison.hasManifoldAnalyticSingularityType_const
      (n := 2) (M := P2) (0 : ℝ)
  exact isSourceTraceRepresentativeAlong_comp_of_analytic omegaP2 omegaV contMDiff_ιY hz hA
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

/-- Source `ex:trace:L407` on `X = ℙ²`: the trace operator is not continuous along the
increasing sequence `(φ_j)_j`.  For every Kähler form `ω_Y` and big class `η` on `Y ≅ ℙ¹`, all
trace operators `τ_j ∈ PSH(Y, η)` of `φ_j` and `τ ∈ PSH(Y, η)` of the limit `0` (with
arbitrary auxiliary choices), `τ_j` does not converge to `τ` in `d_{S,η}`: every `τ_j ∼_P L`
and `τ ∼_P 0`, while `L ≁_P 0`. -/
theorem not_tendsto_trace_incSeq (omegaV : KahlerBackground 1 P1)
    (η : ClosedRealOneOneForm 1 P1) (hη : IsBigClass (RealBottChern.ofRepresentative η))
    (τ : ℕ → ThetaPshL1 η.val) (τ₀ : ThetaPshL1 η.val)
    {omegai : ℕ → KahlerBackground 2 P2} {omegaVi : ℕ → KahlerBackground 1 P1}
    {omega₀ : KahlerBackground 2 P2} {omegaV₀ : KahlerBackground 1 P1}
    (hT : ∀ j, IsSourceTraceRepresentativeAlong (omegai j) (omegaVi j) contMDiff_ιY
      (incSeq j) (τ j).val)
    (hT₀ : IsSourceTraceRepresentativeAlong omega₀ omegaV₀ contMDiff_ιY (fun _ => 0) τ₀.val) :
    ¬ Tendsto τ atTop (@nhds (ThetaPshL1 η.val)
      (singularityPseudoMetricSpace omegaV η hη).toUniformSpace.toTopologicalSpace τ₀) := by
  let := singularityPseudoMetricSpace omegaV η hη
  intro hlim
  have hP : ∀ j, SourcePEquivalent (n := 1) (τ j).val projectiveLogSingularity := by
    intro j
    have h := SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic (by norm_num)
      (omegaVi j) contMDiff_ιY (hT j) (hasManifoldAnalyticSingularityType_incSeq j)
    rwa [incSeq_restriction] at h
  have hP₀ : SourcePEquivalent (n := 1) τ₀.val (fun _ => 0) := by
    have hA : HasManifoldAnalyticSingularityType (n := 2) (fun _ : P2 => (0 : EReal)) := by
      simpa using QuasiEquisingularComparison.hasManifoldAnalyticSingularityType_const
        (n := 2) (M := P2) (0 : ℝ)
    exact SGPT.Trace.sourcePEquivalent_trace_restriction_of_analytic (by norm_num) omegaV₀
      contMDiff_ιY hT₀ hA
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
    ¬ Tendsto (fun _ : ℕ => (⟨projectiveLogSingularity,
        SGPT.Trace.BertiniModel.isThetaPshPotential_logSingularity⟩ :
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

end SGPT.Projective.TraceIncreasingP2
