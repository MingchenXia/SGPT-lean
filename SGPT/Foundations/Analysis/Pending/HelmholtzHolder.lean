import SGPT.Foundations.Analysis.Pending.SchwartzHelmholtz
import SGPT.Foundations.Analysis.Pending.WholeSpaceMaxPrinciple
import SGPT.Foundations.Analysis.Pending.HolderMollification
import SGPT.Foundations.Analysis.Pending.HolderBlowupCompactness
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Solving `Δu - μu = f` for bounded Hölder data on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`,
`0 < α < 1` and `μ > 0`.  For every bounded `α`-Hölder function `f : E → ℝ` there is a bounded
`C²` function `u` with bounded `α`-Hölder second derivative solving `Δu - μu = f`
(`exists_laplacian_sub_eq_of_holder`), where `Δu = hessTrace b 1 (D²u)`.

Proof: approximate `f` by the smooth compactly supported functions
`fₙ = χ(·/n) · (φ_{1/n} ⋆ f)` (`exists_smooth_approx`: a cut-off times a mollification), which are
bounded by `|f|_0` with uniformly bounded Hölder seminorms and converge to `f` pointwise; solve
`Δuₙ - μuₙ = fₙ` with Schwartz functions (`SchwartzHelmholtz`); the maximum principle and the
Schauder estimate (`SchauderWholeSpace.exists_schauder_estimate`) bound `uₙ`, `Duₙ`, `D²uₙ` and
`[D²uₙ]_α` uniformly; along an ultrafilter `uₙ`, `Duₙ`, `D²uₙ` converge pointwise to `u`, `Du`,
`D²u` for a `C²` function `u` (`exists_contDiff_two_tendsto_of_bounded`, the bounded analogue of
`HolderBlowupCompactness`), and the equation passes to the limit.

This is the starting point of the method of continuity that solves `L u - μ u = f` on the whole
space (the linear elliptic estimates, L2.10; blueprint
`bou:helmholtz-whole-space`, `bou:kahler-laplacian-solvability`).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ContDiff RealInnerProductSpace Convolution

namespace SGPT.Foundations.Analysis.Pending.HelmholtzHolder

open EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceMaxPrinciple
  HolderBlowupCompactness

/-! ### Compactness for bounded families -/

section Compactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Compactness of bounded families in `C^{2,α}`**: `C²` functions `w_i` with `w_i`, `Dw_i`,
`D²w_i` bounded by `K` and `D²w_i` uniformly `(K, α)`-Hölder have, along any ultrafilter, a `C²`
limit `V` with `w_i → V`, `Dw_i → DV`, `D²w_i → D²V` pointwise. -/
theorem exists_contDiff_two_tendsto_of_bounded {ι : Type*} (U : Ultrafilter ι) (w : ι → E → ℝ)
    (hw : ∀ i, ContDiff ℝ 2 (w i)) {K α : ℝ} (hα : 0 < α)
    (h0 : ∀ i x, |w i x| ≤ K) (h1 : ∀ i x, ‖fderiv ℝ (w i) x‖ ≤ K)
    (h2 : ∀ i x, ‖fderiv ℝ (fderiv ℝ (w i)) x‖ ≤ K)
    (hH : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (w i)) x - fderiv ℝ (fderiv ℝ (w i)) y‖ ≤
      K * ‖x - y‖ ^ α) :
    ∃ V : E → ℝ, ContDiff ℝ 2 V ∧ (∀ x, Tendsto (fun i => w i x) U (𝓝 (V x))) ∧
      (∀ x, Tendsto (fun i => fderiv ℝ (w i) x) U (𝓝 (fderiv ℝ V x))) ∧
      ∀ x, Tendsto (fun i => fderiv ℝ (fderiv ℝ (w i)) x) U (𝓝 (fderiv ℝ (fderiv ℝ V) x)) := by
  set D2 : ι → E → E →L[ℝ] E →L[ℝ] ℝ := fun i => fderiv ℝ (fderiv ℝ (w i)) with hD2
  set D1 : ι → E → E →L[ℝ] ℝ := fun i => fderiv ℝ (w i) with hD1
  have hw1 : ∀ i, Differentiable ℝ (w i) := fun i => (hw i).differentiable (by norm_num)
  have hDw : ∀ i, ContDiff ℝ 1 (fderiv ℝ (w i)) := fun i => (hw i).fderiv_right (by norm_num)
  have hD2c : ∀ i, Continuous (D2 i) := fun i => (hDw i).continuous_fderiv one_ne_zero
  have hwd : ∀ i x, HasFDerivAt (w i) (D1 i x) x := fun i x => (hw1 i x).hasFDerivAt
  have hD1d : ∀ i x, HasFDerivAt (D1 i) (D2 i x) x := fun i x =>
    ((hDw i).differentiable one_ne_zero x).hasFDerivAt
  -- pointwise limits along `U`
  have hlim2 : ∀ x, ∃ a, Tendsto (fun i => D2 i x) U (𝓝 a) := fun x =>
    exists_tendsto_of_norm_le (Y := E →L[ℝ] E →L[ℝ] ℝ) U (fun i => D2 i x) fun i => h2 i x
  have hlim1 : ∀ x, ∃ a, Tendsto (fun i => D1 i x) U (𝓝 a) := fun x =>
    exists_tendsto_of_norm_le (Y := E →L[ℝ] ℝ) U (fun i => D1 i x) fun i => h1 i x
  have hlim0 : ∀ x, ∃ a, Tendsto (fun i => w i x) U (𝓝 a) := fun x =>
    exists_tendsto_of_norm_le (Y := ℝ) U _ fun i => by rw [Real.norm_eq_abs]; exact h0 i x
  choose W2 hW2 using hlim2
  choose W1 hW1 using hlim1
  choose W0 hW0 using hlim0
  -- equicontinuity
  have hlin : Tendsto (fun t : ℝ => K * t) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul K
  have hrpow : Tendsto (fun t : ℝ => K * t ^ α) (𝓝 0) (𝓝 0) := by
    have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).const_mul K
    rwa [Real.zero_rpow hα.ne', mul_zero] at h
  have heq2 : Equicontinuous D2 :=
    Metric.equicontinuous_of_continuity_modulus (fun t => K * t ^ α) hrpow D2 fun x y i => by
      rw [dist_eq_norm x y]
      exact (dist_eq_norm (D2 i x) (D2 i y)).trans_le (hH i x y)
  have heq1 : Equicontinuous D1 :=
    Metric.equicontinuous_of_continuity_modulus (fun t => K * t) hlin D1 fun x y i => by
      rw [dist_eq_norm x y, dist_eq_norm (D1 i x) (D1 i y)]
      have := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (f := D1 i) (fun z _ => (hD1d i z).hasFDerivWithinAt) (fun z _ => h2 i z)
        (mem_univ y) (mem_univ x)
      exact this
  have hu2 := tendstoLocallyUniformly_of_equicontinuous heq2 hW2
  have hu1 := tendstoLocallyUniformly_of_equicontinuous heq1 hW1
  have hd0 : ∀ x, HasFDerivAt W0 (W1 x) x := fun x =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hu1)
      (fun i x _ => hwd i x) (fun x _ => hW0 x) (mem_univ x)
  have hd1 : ∀ x, HasFDerivAt W1 (W2 x) x := fun x =>
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hu2)
      (fun i x _ => hD1d i x) (fun x _ => hW1 x) (mem_univ x)
  have hc2 : Continuous W2 := hu2.continuous (Frequently.of_forall hD2c)
  have hfd0 : fderiv ℝ W0 = W1 := funext fun x => (hd0 x).fderiv
  have hfd1 : fderiv ℝ W1 = W2 := funext fun x => (hd1 x).fderiv
  refine ⟨W0, ?_, hW0, fun x => ?_, fun x => ?_⟩
  · have h1' : ContDiff ℝ 1 W1 :=
      contDiff_one_iff_fderiv.2 ⟨fun x => (hd1 x).differentiableAt, by rw [hfd1]; exact hc2⟩
    have h2' : ContDiff ℝ (1 + 1) W0 :=
      contDiff_succ_iff_fderiv.2 ⟨fun x => (hd0 x).differentiableAt, by simp,
        by rw [hfd0]; exact h1'⟩
    exact h2'
  · rw [hfd0]; exact hW1 x
  · rw [hfd0, hfd1]; exact hW2 x

end Compactness

/-! ### Smooth compactly supported approximation of bounded Hölder functions -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A smooth cut-off `χ` (`χ = 1` on the unit ball, `0 ≤ χ ≤ 1`, compact support) is Lipschitz. -/
theorem exists_lipschitz_cutoff :
    ∃ χ : E → ℝ, ∃ L : ℝ, 0 ≤ L ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧
      ∀ x y, |χ x - χ y| ≤ L * ‖x - y‖ := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : ContDiff ℝ ∞ (φ : E → ℝ) := φ.contDiff
  have hc : HasCompactSupport (φ : E → ℝ) := φ.hasCompactSupport
  obtain ⟨L, hL⟩ := ((hs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ)))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  refine ⟨φ, L, hL0, hs, hc, fun x => ⟨φ.nonneg, φ.le_one⟩, fun x hx => ?_, fun x y => ?_⟩
  · exact φ.one_of_mem_closedBall (by simpa using hx)
  · have := (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => (hs.differentiable (by norm_num)) z) (fun z _ => hL z) (mem_univ y) (mem_univ x)
    rwa [Real.norm_eq_abs] at this

/-- **Smooth compactly supported approximation**: a bounded `(M, α)`-Hölder function `f` is the
pointwise limit of smooth compactly supported functions `gₙ` with `|gₙ| ≤ |f|_0` and
`[gₙ]_α ≤ M + K |f|_0`, `K` depending only on `E`. -/
theorem exists_smooth_approx {f : E → ℝ} {F M α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hM0 : 0 ≤ M)
    (hF : ∀ x, |f x| ≤ F) (hM : ∀ x y, |f x - f y| ≤ M * ‖x - y‖ ^ α) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n x, |g n x| ≤ F) ∧ (∀ n x y, |g n x - g n y| ≤ (M + K * F) * ‖x - y‖ ^ α) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
  obtain ⟨χ, L, hL0, hχs, hχc, hχ01, hχ1, hχL⟩ := exists_lipschitz_cutoff (E := E)
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have hfc : Continuous f := by
    refine Metric.continuous_iff.2 fun x ε hε => ?_
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, M * δ ^ α < ε := by
      have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα0.le)).tendsto).const_mul M
      rw [Real.zero_rpow hα0.ne', mul_zero] at h
      obtain ⟨δ, hδ, h'⟩ := Metric.eventually_nhds_iff.1 (h.eventually (gt_mem_nhds hε))
      have hδ2 : dist (δ / 2) 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
        linarith
      exact ⟨δ / 2, by positivity, h' hδ2⟩
    refine ⟨δ, hδ0, fun y hy => ?_⟩
    rw [Real.dist_eq]
    calc |f y - f x| ≤ M * ‖y - x‖ ^ α := hM y x
      _ ≤ M * δ ^ α := by
          gcongr; rw [← dist_eq_norm]; exact hy.le
      _ < ε := hδ
  have hHol : HolderWith M.toNNReal α.toNNReal f := HolderWith.of_dist_le fun x y => by
    rw [Real.coe_toNNReal _ hM0, Real.coe_toNNReal _ hα0.le, Real.dist_eq, dist_eq_norm]
    exact hM x y
  -- the mollifiers
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (2 * (n + 1)), 1 / (n + 1), by positivity, by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by positivity)]; linarith⟩
  set ρ : ℕ → E → ℝ := fun n => (φ n).normed volume with hρ
  set m : ℕ → E → ℝ := fun n => ρ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f with hm
  have hρ0 : ∀ n t, 0 ≤ ρ n t := fun n t => (φ n).nonneg_normed t
  have hρi : ∀ n, Integrable (ρ n) volume := fun n => (φ n).integrable_normed
  have hρc : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous_normed
  have hρ1 : ∀ n, ∫ t, ρ n t = 1 := fun n => (φ n).integral_normed
  have hρR : ∀ (n : ℕ) t, 1 / ((n : ℝ) + 1) < ‖t‖ → ρ n t = 0 := fun n t ht => by
    have : t ∉ Function.support (ρ n) := by
      rw [hρ, (φ n).support_normed_eq, mem_ball, dist_zero_right]; exact not_lt.2 ht.le
    simpa using this
  have hmF : ∀ n x, |m n x| ≤ F := fun n x => by
    have := HolderMollification.norm_convolution_le (hρ0 n) (hρi n) (hρ1 n)
      (u := f) (A := F) (fun y => by rw [Real.norm_eq_abs]; exact hF y) x
    rwa [Real.norm_eq_abs] at this
  have hmM : ∀ n x y, |m n x - m n y| ≤ M * ‖x - y‖ ^ α := fun n x y => by
    have := HolderMollification.dist_convolution_le (hρ0 n) (hρi n) (hρc n) (hρ1 n) hfc
      (A := F) (fun y => by rw [Real.norm_eq_abs]; exact hF y) hHol x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ hM0, Real.coe_toNNReal _ hα0.le, dist_eq_norm] at this
  have hms : ∀ n, ContDiff ℝ ∞ (m n) := fun n =>
    HolderMollification.contDiff_convolution (φ n).hasCompactSupport_normed
      (φ n).contDiff_normed hfc.locallyIntegrable
  have hmconv : ∀ x, Tendsto (fun n => m n x) atTop (𝓝 (f x)) := fun x => by
    have hb : ∀ n : ℕ, |m n x - f x| ≤ M * (1 / ((n : ℝ) + 1)) ^ α := fun n => by
      have := HolderMollification.norm_convolution_sub_le (hρ0 n) (hρi n) (hρc n) (hρ1 n)
        (hρR n) hfc (A := F) (fun y => by rw [Real.norm_eq_abs]; exact hF y) hHol x
      rwa [Real.norm_eq_abs, Real.coe_toNNReal _ hM0, Real.coe_toNNReal _ hα0.le] at this
    have h0 : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1)) ^ α) atTop (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 α (Or.inr hα0.le)).tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat).const_mul M
      rwa [Function.comp_def, Real.zero_rpow hα0.ne', mul_zero] at h
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [Real.norm_eq_abs]; exact hb n
  -- the cut-offs `χ(x / (n + 1))`
  set c : ℕ → E → ℝ := fun n x => χ (((n : ℝ) + 1)⁻¹ • x) with hc
  have hcL : ∀ (n : ℕ) x y, |c n x - c n y| ≤ L * ‖x - y‖ := fun n x y => by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc |c n x - c n y| ≤ L * ‖((n : ℝ) + 1)⁻¹ • x - ((n : ℝ) + 1)⁻¹ • y‖ := hχL _ _
      _ = L * (((n : ℝ) + 1)⁻¹ * ‖x - y‖) := by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_pos.2 hn).le]
      _ ≤ L * (1 * ‖x - y‖) := by
          gcongr; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
      _ = L * ‖x - y‖ := by ring
  have hcH : ∀ (n : ℕ) x y, |c n x - c n y| ≤ (L + 2 * 1) * ‖x - y‖ ^ α := fun n x y => by
    have := norm_sub_le_rpow_of_lipschitz_of_bound (g := c n) hL0 hα0.le hα1
      (fun x y => by rw [Real.norm_eq_abs]; exact hcL n x y)
      (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2) x y
    rwa [Real.norm_eq_abs] at this
  refine ⟨L + 2, by positivity, fun n x => c n x * m n x, fun n => ?_, fun n => ?_,
    fun n x => ?_, fun n x y => ?_, fun x => ?_⟩
  · exact (hχs.comp (contDiff_const_smul _)).mul (hms n)
  · exact (hχc.comp_smul (inv_ne_zero (by positivity))).mul_right
  · rw [abs_mul, abs_of_nonneg (hχ01 _).1]
    calc χ _ * |m n x| ≤ 1 * F := mul_le_mul (hχ01 _).2 (hmF n x) (abs_nonneg _) zero_le_one
      _ = F := one_mul F
  · have hsplit : c n x * m n x - c n y * m n y =
        c n x * (m n x - m n y) + (c n x - c n y) * m n y := by ring
    rw [hsplit]
    have hp : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    calc |c n x * (m n x - m n y) + (c n x - c n y) * m n y|
        ≤ |c n x| * |m n x - m n y| + |c n x - c n y| * |m n y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (M * ‖x - y‖ ^ α) + ((L + 2 * 1) * ‖x - y‖ ^ α) * F := by
          gcongr
          · rw [abs_of_nonneg (hχ01 _).1]; exact (hχ01 _).2
          · exact hmM n x y
          · exact hcH n x y
          · exact hmF n y
      _ = (M + (L + 2) * F) * ‖x - y‖ ^ α := by ring
  · have hev : ∀ᶠ n in atTop, c n x * m n x = m n x := by
      obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : ‖((n : ℝ) + 1)⁻¹ • x‖ ≤ 1 := by
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hpos).le, inv_mul_le_iff₀ hpos, mul_one]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [hc, hχ1 _ hn', one_mul]
    exact (hmconv x).congr' (hev.mono fun n hn => hn.symm)

end Approx

/-! ### `Δ - μ` on bounded Hölder data -/

section Helmholtz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- The constant coefficient field `a = 1` is in the class `IsEllipticCoeff · 1 Λ α` for
`Λ ≥ 1`. -/
theorem isEllipticCoeff_id {Λ α : ℝ} (hΛ : 1 ≤ Λ) :
    IsEllipticCoeff (fun _ : E => ContinuousLinearMap.id ℝ E) 1 Λ α where
  symm _ _ _ := rfl
  elliptic _ v := by simp
  bound _ := (ContinuousLinearMap.norm_id_le).trans hΛ
  holder _ _ := by
    simp only [sub_self, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

theorem ellipticOp_id_const (c : ℝ) (u : E → ℝ) (x : E) :
    ellipticOp b (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 0) (fun _ => c) u x =
      hessTrace b (ContinuousLinearMap.id ℝ E) (fderiv ℝ (fderiv ℝ u) x) + c * u x := by
  simp [ellipticOp]

/-- A function with bounded second and third derivatives has an `α`-Hölder second derivative. -/
theorem exists_holder_fderiv_fderiv {u : E → ℝ} (hu : ContDiff ℝ 3 u) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) {B₂ B₃ : ℝ} (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ B₂)
    (h3 : ∀ x, ‖iteratedFDeriv ℝ 3 u x‖ ≤ B₃) :
    ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ (B₃ + 2 * B₂) * ‖x - y‖ ^ α := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 u) :=
    hu.differentiable_iteratedFDeriv (by norm_num)
  have hD3 : ∀ x, ‖fderiv ℝ (iteratedFDeriv ℝ 2 u) x‖ ≤ B₃ := fun x => by
    rw [norm_fderiv_iteratedFDeriv]; exact h3 x
  have hB3 : 0 ≤ B₃ := (norm_nonneg _).trans (h3 0)
  have hlip : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ B₃ * ‖x - y‖ :=
    fun x y => by
      rw [← HolderInterpolation.norm_iteratedFDeriv_two_sub]
      exact (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hd z) (fun z _ => hD3 z) (mem_univ y) (mem_univ x)
  exact norm_sub_le_rpow_of_lipschitz_of_bound (Y := E →L[ℝ] E →L[ℝ] ℝ) hB3 hα0 hα1 hlip
    (fun x => by rw [← HolderInterpolation.norm_iteratedFDeriv_two]; exact h2 x)

/-- **`Δ - μ` is onto the bounded Hölder functions** (`μ > 0`, `0 < α < 1`): for every
`f` with `|f| ≤ F` and `[f]_α ≤ M` there is a `C²` function `u` with bounded `α`-Hölder second
derivative, `μ |u| ≤ F` and `Δu - μu = f`. -/
theorem exists_laplacian_sub_eq_of_holder {α μ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hμ : 0 < μ)
    {f : E → ℝ} {F M : ℝ} (hM0 : 0 ≤ M) (hF : ∀ x, |f x| ≤ F)
    (hM : ∀ x y, |f x - f y| ≤ M * ‖x - y‖ ^ α) :
    ∃ u : E → ℝ, ContDiff ℝ 2 u ∧
      (∃ H : ℝ, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) ∧
      (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) ∧ (∀ x, μ * |u x| ≤ F) ∧
      ∀ x, hessTrace b (ContinuousLinearMap.id ℝ E) (fderiv ℝ (fderiv ℝ u) x) - μ * u x = f x := by
  obtain ⟨K, hK0, g, hgs, hgc, hgF, hgH, hgconv⟩ := exists_smooth_approx hα0 hα1.le hM0 hF hM
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  choose u hus hub hueq using fun n => SchwartzHelmholtz.exists_contDiff_laplacian_sub_eq b hμ
    (hgs n) (hgc n)
  have hu2 : ∀ n, ContDiff ℝ 2 (u n) := fun n => contDiff_infty.1 (hus n) 2
  have hu3 : ∀ n, ContDiff ℝ 3 (u n) := fun n => contDiff_infty.1 (hus n) 3
  have hop : ∀ n x, ellipticOp b (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 0)
      (fun _ => -μ) (u n) x = g n x := fun n x => by
    rw [ellipticOp_id_const, ← hueq n x]; ring
  -- the uniform estimates
  obtain ⟨C, hC, hS⟩ := exists_schauder_estimate (Λ := 1 + μ) b one_pos hα0 hα1
  have ha : IsEllipticCoeff (fun _ : E => ContinuousLinearMap.id ℝ E) 1 (1 + μ) α :=
    isEllipticCoeff_id (by linarith)
  have hβc : IsLowerCoeff (fun _ : E => (0 : E)) (fun _ => -μ) (1 + μ) α := by
    refine ⟨fun _ => ?_, fun _ _ => ?_, fun _ => ?_, fun _ _ => ?_⟩
    · simp; linarith
    · simp only [sub_self, norm_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [abs_neg, abs_of_pos hμ]; linarith
    · simp only [sub_self, abs_zero]
      exact mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  have hmax : ∀ n x, μ * |u n x| ≤ F := fun n x => by
    have hsub : ∀ y, |ellipticOp b (fun _ => ContinuousLinearMap.id ℝ E) (fun _ => 0) (fun _ => 0)
        (u n) y - μ * u n y| ≤ F := fun y => by
      rw [ellipticOp_id_const, zero_mul, add_zero, hueq n y]; exact hgF n y
    obtain ⟨C0, hC0⟩ := hub n 0
    exact mul_abs_le_of_ellipticOp_sub b (fun _ _ _ => rfl)
      (fun _ v => real_inner_self_nonneg) (fun _ => ContinuousLinearMap.norm_id_le)
      (fun _ => by simp) (fun _ => le_rfl) hμ (hu2 n)
      ⟨C0, fun y => by have := hC0 y; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this⟩
      hsub x
  set K₀ : ℝ := C * (M + K * F + F / μ) with hK₀
  have hest : ∀ n, (∀ x y, ‖fderiv ℝ (fderiv ℝ (u n)) x - fderiv ℝ (fderiv ℝ (u n)) y‖ ≤
      K₀ * ‖x - y‖ ^ α) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ (u n)) x‖ ≤ K₀) ∧
      (∀ x, ‖fderiv ℝ (u n) x‖ ≤ K₀) := fun n => by
    obtain ⟨B₂, hB₂⟩ := hub n 2
    obtain ⟨B₃, hB₃⟩ := hub n 3
    have hHol := exists_holder_fderiv_fderiv (hu3 n) hα0.le hα1.le hB₂ hB₃
    exact hS _ _ _ ha hβc (u n) (hu2 n) ⟨_, hHol⟩
      ⟨B₂, fun x => by rw [← HolderInterpolation.norm_iteratedFDeriv_two]; exact hB₂ x⟩
      (F / μ) (M + K * F) (by positivity)
      (fun x => by rw [le_div_iff₀ hμ, mul_comm]; exact hmax n x)
      (fun x y => by rw [hop, hop]; exact hgH n x y)
  -- the limit along an ultrafilter
  set K₁ : ℝ := max (F / μ) K₀ with hK₁
  obtain ⟨V, hV2, hV0, hV1, hVD2⟩ := exists_contDiff_two_tendsto_of_bounded (hyperfilter ℕ) u hu2
    (K := K₁) hα0
    (fun n x => (by rw [le_div_iff₀ hμ, mul_comm]; exact hmax n x : |u n x| ≤ F / μ).trans
      (le_max_left _ _))
    (fun n x => ((hest n).2.2 x).trans (le_max_right _ _))
    (fun n x => ((hest n).2.1 x).trans (le_max_right _ _))
    (fun n x y => ((hest n).1 x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _)))
  have hU : ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
    hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  refine ⟨V, hV2, ⟨K₀, fun x y => ?_⟩, ⟨K₀, fun x => ?_⟩, fun x => ?_, fun x => ?_⟩
  · refine le_of_tendsto (SchauderBlowup.tendsto_norm_sub_aux (Y := E →L[ℝ] E →L[ℝ] ℝ)
      (hVD2 x) (hVD2 y)) (Eventually.of_forall fun n => (hest n).1 x y)
  · exact le_of_tendsto (SchauderBlowup.tendsto_norm_aux (Y := E →L[ℝ] E →L[ℝ] ℝ) (hVD2 x))
      (Eventually.of_forall fun n => (hest n).2.1 x)
  · exact le_of_tendsto (((hV0 x).abs).const_mul μ) (Eventually.of_forall fun n => hmax n x)
  · have hL : Tendsto (fun n => hessTrace b (ContinuousLinearMap.id ℝ E)
        (fderiv ℝ (fderiv ℝ (u n)) x) - μ * u n x) (hyperfilter ℕ)
        (𝓝 (hessTrace b (ContinuousLinearMap.id ℝ E) (fderiv ℝ (fderiv ℝ V) x) - μ * V x)) :=
      (((continuous_hessTrace b _).tendsto _).comp (hVD2 x)).sub ((hV0 x).const_mul μ)
    have hR : Tendsto (fun n => g n x) (hyperfilter ℕ) (𝓝 (f x)) := (hgconv x).mono_left hU
    exact tendsto_nhds_unique (hL.congr fun n => hueq n x) hR

end Helmholtz

end SGPT.Foundations.Analysis.Pending.HelmholtzHolder
