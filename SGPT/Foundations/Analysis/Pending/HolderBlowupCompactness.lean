import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Compactness for the blow-up sequences of Simon's proof of the Schauder estimates

Let `E` be a finite-dimensional real normed space and `w_i : E → ℝ` (`i : ι`) functions of class
`C²` whose second derivatives vanish at `0` and are uniformly `(K, α)`-Hölder (`α > 0`).  Along any
ultrafilter `U` on `ι` there is a `C²` function `V` with `D²w_i(x) → D²V(x)` for every `x`
(`exists_contDiff_two_tendsto_fderiv_fderiv`).

The functions are normalised by subtracting their first-order Taylor polynomial at `0`; then
`|D²v_i(x)| ≤ K|x|^α`, `|Dv_i(x)| ≤ K|x|^{1+α}`, `|v_i(x)| ≤ K|x|^{2+α}`, so the pointwise limits
along `U` exist (compactness of closed balls), the families `Dv_i`, `D²v_i` are equicontinuous, so
the convergence is locally uniform (`tendstoLocallyUniformly_of_equicontinuous`, from the
Arzelà–Ascoli machinery `EquicontinuousOn.tendsto_uniformOnFun_iff_pi`), and the limits of the
derivatives are the derivatives of the limit (`hasFDerivAt_of_tendstoLocallyUniformlyOn`).

Ultrafilter limits replace the diagonal subsequences of Székelyhidi's proof of Theorem 2.8
(`szekelyhidi-extremal:page-0046`: "on each fixed ball we can extract a convergent subsequence in `C²`.
By a diagonal argument we obtain a function `G : ℝⁿ → ℝ` which on each fixed ball is a `C²`-limit of a
subsequence"), and Theorem 2.7 (`page-0044`, Arzelà–Ascoli).

Part L2.6 of the linear track for Yau's theorem.
-/

noncomputable section

open Set Filter Topology Metric

namespace SGPT.Foundations.Analysis.Pending.HolderBlowupCompactness

/-- **Pointwise convergence of an equicontinuous family is locally uniform.** -/
theorem tendstoLocallyUniformly_of_equicontinuous {X Y ι : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [UniformSpace Y] {F : ι → X → Y} {f : X → Y} {l : Filter ι}
    (hF : Equicontinuous F) (h : ∀ x, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    TendstoLocallyUniformly F f l := by
  rw [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  have hcov : ⋃₀ {K : Set X | IsCompact K} = univ :=
    eq_univ_of_forall fun x => mem_sUnion.2 ⟨{x}, isCompact_singleton, rfl⟩
  have h1 := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi (𝔖 := {K : Set X | IsCompact K})
    (fun K hK => hK) hcov (fun K _ => hF.equicontinuousOn K) l f).2 (tendsto_pi_nhds.2 h)
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 h1) K hK

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Bounded families have limits along an ultrafilter (closed balls of a finite-dimensional space
are compact). -/
theorem exists_tendsto_of_norm_le {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] {ι : Type*} (U : Ultrafilter ι) (f : ι → Y) {r : ℝ}
    (hf : ∀ i, ‖f i‖ ≤ r) : ∃ a, Tendsto f U (𝓝 a) := by
  obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : Y) r).ultrafilter_le_nhds (U.map f)
    (by
      rw [le_principal_iff, Ultrafilter.mem_coe, Ultrafilter.mem_map]
      exact Filter.Eventually.of_forall fun i => by simpa using hf i)
  refine ⟨a, ?_⟩
  rw [Ultrafilter.coe_map] at ha
  exact ha

/-- **Blow-up compactness**: `C²` functions with `D²w_i(0) = 0` and uniformly `(K, α)`-Hölder second
derivatives (`α > 0`) have, along any ultrafilter, a `C²` limit `V` with `D²w_i(x) → D²V(x)` for
every `x`. -/
theorem exists_contDiff_two_tendsto_fderiv_fderiv {ι : Type*} (U : Ultrafilter ι) (w : ι → E → ℝ)
    (hw : ∀ i, ContDiff ℝ 2 (w i)) {K α : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hH : ∀ i z z', ‖fderiv ℝ (fderiv ℝ (w i)) z - fderiv ℝ (fderiv ℝ (w i)) z'‖ ≤
      K * ‖z - z'‖ ^ α)
    (h0 : ∀ i, fderiv ℝ (fderiv ℝ (w i)) 0 = 0) :
    ∃ V : E → ℝ, ContDiff ℝ 2 V ∧
      ∀ x, Tendsto (fun i => fderiv ℝ (fderiv ℝ (w i)) x) U (𝓝 (fderiv ℝ (fderiv ℝ V) x)) := by
  set D2 : ι → E → E →L[ℝ] E →L[ℝ] ℝ := fun i => fderiv ℝ (fderiv ℝ (w i)) with hD2
  set D1 : ι → E → E →L[ℝ] ℝ := fun i x => fderiv ℝ (w i) x - fderiv ℝ (w i) 0 with hD1
  set v : ι → E → ℝ := fun i x => w i x - w i 0 - fderiv ℝ (w i) 0 x with hv
  have hw1 : ∀ i, Differentiable ℝ (w i) := fun i => (hw i).differentiable (by norm_num)
  have hDw : ∀ i, ContDiff ℝ 1 (fderiv ℝ (w i)) := fun i => (hw i).fderiv_right (by norm_num)
  have hD2c : ∀ i, Continuous (D2 i) := fun i => (hDw i).continuous_fderiv one_ne_zero
  have hvd : ∀ i x, HasFDerivAt (v i) (D1 i x) x := fun i x => by
    exact ((hw1 i x).hasFDerivAt.sub_const (w i 0)).sub (fderiv ℝ (w i) 0).hasFDerivAt
  have hD1d : ∀ i x, HasFDerivAt (D1 i) (D2 i x) x := fun i x => by
    simpa only [hD1, hD2] using
      ((hDw i).differentiable one_ne_zero x).hasFDerivAt.sub_const (fderiv ℝ (w i) 0)
  have hD1_0 : ∀ i, D1 i 0 = 0 := fun i => sub_self _
  have hv0 : ∀ i, v i 0 = 0 := fun i => by simp [hv]
  -- bounds
  have hb2 : ∀ i x, ‖D2 i x‖ ≤ K * ‖x‖ ^ α := fun i x => by
    have := hH i x 0
    rwa [h0, sub_zero, sub_zero] at this
  have hb2R : ∀ i (R : ℝ) x, ‖x‖ ≤ R → ‖D2 i x‖ ≤ K * R ^ α := fun i R x hx =>
    (hb2 i x).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hx hα.le) hK)
  have hb1R : ∀ i (R : ℝ) x, ‖x‖ ≤ R → ‖D1 i x‖ ≤ K * R ^ α * ‖x‖ := fun i R x hx => by
    have := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := D1 i) (fun z _ => (hD1d i z).hasFDerivWithinAt)
      (fun z hz => hb2R i R z (by simpa using hz))
      (mem_closedBall_self ((norm_nonneg x).trans hx)) (by simpa using hx)
    rwa [hD1_0, sub_zero, sub_zero] at this
  have hb0R : ∀ i (R : ℝ) x, ‖x‖ ≤ R → ‖v i x‖ ≤ K * R ^ α * R * ‖x‖ := fun i R x hx => by
    have hR : 0 ≤ R := (norm_nonneg x).trans hx
    have := (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := v i) (fun z _ => (hvd i z).hasFDerivWithinAt)
      (fun z hz => by
        have hz' : ‖z‖ ≤ R := by simpa using hz
        exact (hb1R i R z hz').trans (mul_le_mul_of_nonneg_left hz' (by positivity)))
      (mem_closedBall_self hR) (by simpa using hx)
    rwa [hv0, sub_zero, sub_zero] at this
  -- pointwise limits along `U`
  have hlim2 : ∀ x, ∃ a, Tendsto (fun i => D2 i x) U (𝓝 a) := fun x => by
    obtain ⟨a, ha⟩ := exists_tendsto_of_norm_le (Y := E →L[ℝ] E →L[ℝ] ℝ) U (fun i => D2 i x)
      fun i => hb2 i x
    exact ⟨a, ha⟩
  have hlim1 : ∀ x, ∃ a, Tendsto (fun i => D1 i x) U (𝓝 a) := fun x => by
    obtain ⟨a, ha⟩ := exists_tendsto_of_norm_le (Y := E →L[ℝ] ℝ) U (fun i => D1 i x)
      fun i => hb1R i ‖x‖ x le_rfl
    exact ⟨a, ha⟩
  have hlim0 : ∀ x, ∃ a, Tendsto (fun i => v i x) U (𝓝 a) := fun x =>
    exists_tendsto_of_norm_le (Y := ℝ) U _ fun i => hb0R i ‖x‖ x le_rfl
  choose W2 hW2 using hlim2
  choose W1 hW1 using hlim1
  choose W0 hW0 using hlim0
  -- equicontinuity
  have hrpow : Tendsto (fun t : ℝ => K * t ^ α) (𝓝 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).const_mul K
    rwa [Real.zero_rpow hα.ne', mul_zero] at h
  have heq2 : Equicontinuous D2 :=
    Metric.equicontinuous_of_continuity_modulus (fun t => K * t ^ α) hrpow D2 fun x y i => by
      rw [dist_eq_norm x y]
      exact (dist_eq_norm (D2 i x) (D2 i y)).trans_le (hH i x y)
  have heq1 : Equicontinuous D1 := by
    intro x₀
    refine Metric.equicontinuousAt_of_continuity_modulus
      (fun x => K * (‖x₀‖ + 1) ^ α * dist x₀ x) ?_ D1 ?_
    · have h := (((continuous_const : Continuous fun _ : E => x₀).dist continuous_id).tendsto
        x₀).const_mul (K * (‖x₀‖ + 1) ^ α)
      simpa using h
    · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx i
      have := (convex_ball x₀ 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := D1 i) (fun z _ => (hD1d i z).hasFDerivWithinAt)
        (fun z hz => hb2R i (‖x₀‖ + 1) z (by
          have := norm_le_norm_add_norm_sub' z x₀
          rw [mem_ball, dist_eq_norm] at hz
          linarith))
        hx (mem_ball_self one_pos)
      rw [dist_eq_norm x₀ x]
      exact (dist_eq_norm (D1 i x₀) (D1 i x)).trans_le this
  -- locally uniform convergence and the derivatives of the limits
  have hu2 := tendstoLocallyUniformly_of_equicontinuous heq2 hW2
  have hu1 := tendstoLocallyUniformly_of_equicontinuous heq1 hW1
  have hd0 : ∀ x, HasFDerivAt W0 (W1 x) x := fun x =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hu1)
      (fun i x _ => hvd i x) (fun x _ => hW0 x) (mem_univ x)
  have hd1 : ∀ x, HasFDerivAt W1 (W2 x) x := fun x =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hu2)
      (fun i x _ => hD1d i x) (fun x _ => hW1 x) (mem_univ x)
  have hc2 : Continuous W2 := hu2.continuous (Frequently.of_forall hD2c)
  have hfd0 : fderiv ℝ W0 = W1 := funext fun x => (hd0 x).fderiv
  have hfd1 : fderiv ℝ W1 = W2 := funext fun x => (hd1 x).fderiv
  refine ⟨W0, ?_, fun x => ?_⟩
  · have h1 : ContDiff ℝ 1 W1 :=
      contDiff_one_iff_fderiv.2 ⟨fun x => (hd1 x).differentiableAt, by rw [hfd1]; exact hc2⟩
    have h2 : ContDiff ℝ (1 + 1) W0 :=
      contDiff_succ_iff_fderiv.2 ⟨fun x => (hd0 x).differentiableAt, by simp, by rw [hfd0]; exact h1⟩
    exact h2
  · rw [hfd0, hfd1]
    exact hW2 x

end SGPT.Foundations.Analysis.Pending.HolderBlowupCompactness
