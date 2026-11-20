import SGPT.Okounkov.TranscendentalWNConvFLStatement
import SGPT.Okounkov.TranscendentalWNLipschitz

/-!
# Corollary 7.6 of WN21 from Lemma 7.5

Blueprint `claude-tok-wn-fl`, node `tok-wn-fl:strict-lipschitz`; source WN21 §7, Corollary 7.6.

`strictLipschitz_of_strictDiscLaplacian : StrictDiscLaplacianStatement F → StrictLipschitzStatement F`.

For `x` near `x₀ ∉ Z` and `z` over `(x, t)`, `0 < |t| ≤ e^{-k/2}/2`, let `σ` be the disc over `x`
through `z` (`σ 0 = ι x`, `σ t = z`) and `f = v_k ∘ σ`.  By Lemma 7.5 (`StrictDiscLaplacianStatement`),
`|f + k| ≤ C` on the closed disc of radius `R = e^{-k/2}`, where `f` is the uniform limit of `C²`
functions `u_j` with `-C ≤ Δ u_j ≤ C e^k`.  The rescaled function `h(w) = (f(R w) + k)/C₁`
(`C₁ = max C 1`) satisfies `|h| ≤ 1` on the closed unit disc and `|∫ h Δφ| ≤ ∫ |φ|` for test
functions `φ` (Green's identity `∫ u Δφ = ∫ Δu φ` for the approximants, whose rescaled Laplacians
`R² (Δ u_j)(R w)/C₁` lie in `[-1, 1]`), so WN-LIP (`lipschitzOfLaplacianStatement`) gives
`|h(w) - h(0)| ≤ A |w|` for `|w| ≤ 1/2`, i.e. `|v_k(z) - v_k(ι x)| ≤ C₁ A e^{k/2} |t|`.

Auxiliary: `integral_mul_laplacian_eq` (Green's identity on `ℂ`) and `laplacian_comp_smul`
(`Δ (u ∘ (R •)) = R² (Δ u) ∘ (R •)`).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Metric Laplacian Complex
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Okounkov.TranscendentalMain

/-! ### Calculus on `ℂ` -/

section Calculus

/-- The Laplacian of a rescaling: `Δ (u ∘ (R •)) = R² (Δ u) ∘ (R •)`. -/
theorem laplacian_comp_smul {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (R : ℝ) (y : ℂ) :
    Δ (fun t => f (R • t)) y = R ^ 2 * Δ f (R • y) := by
  have hcomp : (fun t => f (R • t)) = f ∘ (R • ContinuousLinearMap.id ℝ ℂ) := by
    funext t
    simp
  rw [hcomp, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ hf _ le_rfl]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have key : ∀ v : ℂ, (fun i : Fin 2 => (R • ContinuousLinearMap.id ℝ ℂ) (![v, v] i)) =
      fun i => R • ![v, v] i := fun v => by
    funext i
    simp
  have hy : (R • ContinuousLinearMap.id ℝ ℂ) y = R • y := by simp
  rw [key, key, hy, ContinuousMultilinearMap.map_smul_univ, ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

/-- One direction of Green's identity: `∫ u ∂_v∂_v φ = ∫ ∂_v∂_v u φ`. -/
theorem integral_mul_fderiv_fderiv_eq {u φ : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (v : ℂ) :
    ∫ z, u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v =
      ∫ z, fderiv ℝ (fun y => fderiv ℝ u y v) z v * φ z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hu1 : ContDiff ℝ 1 (fun y => fderiv ℝ u y v) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hφ1 : ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) :=
    (hφ2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hu0 : Continuous u := hu.continuous
  have hφ0 : Continuous φ := hφ.continuous
  have hDu : Continuous fun y => fderiv ℝ u y v := hu1.continuous
  have hDφ : Continuous fun y => fderiv ℝ φ y v := hφ1.continuous
  have hDDu : Continuous fun z => fderiv ℝ (fun y => fderiv ℝ u y v) z v :=
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDDφ : Continuous fun z => fderiv ℝ (fun y => fderiv ℝ φ y v) z v :=
    (hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDφ : HasCompactSupport fun y => fderiv ℝ φ y v := hφc.fderiv_apply (𝕜 := ℝ) v
  have hcDDφ : HasCompactSupport fun z => fderiv ℝ (fun y => fderiv ℝ φ y v) z v :=
    hcDφ.fderiv_apply (𝕜 := ℝ) v
  -- first integration by parts
  have h1 : ∫ z, u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v =
      -∫ z, fderiv ℝ u z v * fderiv ℝ φ z v :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hDu.mul hDφ).integrable_of_hasCompactSupport hcDφ.mul_left)
      ((hu0.mul hDDφ).integrable_of_hasCompactSupport hcDDφ.mul_left)
      ((hu0.mul hDφ).integrable_of_hasCompactSupport hcDφ.mul_left)
      (fun x _ => (hu.differentiable (by norm_num)) x)
      (fun x _ => (hφ1.differentiable one_ne_zero) x)
  -- second integration by parts
  have h2 : ∫ z, fderiv ℝ u z v * fderiv ℝ φ z v =
      -∫ z, fderiv ℝ (fun y => fderiv ℝ u y v) z v * φ z :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hDDu.mul hφ0).integrable_of_hasCompactSupport hφc.mul_left)
      ((hDu.mul hDφ).integrable_of_hasCompactSupport hcDφ.mul_left)
      ((hDu.mul hφ0).integrable_of_hasCompactSupport hφc.mul_left)
      (fun x _ => (hu1.differentiable one_ne_zero) x)
      (fun x _ => (hφ2.differentiable (by norm_num)) x)
  rw [h1, h2, neg_neg]

/-- **Green's identity on `ℂ`**: `∫ u Δφ = ∫ Δu φ` for `u` of class `C²` and `φ` smooth with
compact support. -/
theorem integral_mul_laplacian_eq {u φ : ℂ → ℝ} (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ z, u z * Δ φ z = ∫ z, Δ u z * φ z := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcont : ∀ v : ℂ, Continuous fun z => u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v := by
    intro v
    exact hu.continuous.mul ((((hφ2.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hsupp : ∀ v : ℂ, HasCompactSupport fun z =>
      u z * fderiv ℝ (fun y => fderiv ℝ φ y v) z v := fun v =>
    ((hφc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v).mul_left
  have hcont' : ∀ v : ℂ, Continuous fun z => fderiv ℝ (fun y => fderiv ℝ u y v) z v * φ z := by
    intro v
    exact ((((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const).mul hφ.continuous
  have hsupp' : ∀ v : ℂ, HasCompactSupport fun z =>
      fderiv ℝ (fun y => fderiv ℝ u y v) z v * φ z := fun v => hφc.mul_left
  have hL : (fun z => u z * Δ φ z) = fun z =>
      u z * fderiv ℝ (fun y => fderiv ℝ φ y 1) z 1 + u z * fderiv ℝ (fun y => fderiv ℝ φ y I) z I := by
    funext z
    rw [Lipschitz.laplacian_eq_fderiv_fderiv hφ2, mul_add]
  have hR : (fun z => Δ u z * φ z) = fun z =>
      fderiv ℝ (fun y => fderiv ℝ u y 1) z 1 * φ z + fderiv ℝ (fun y => fderiv ℝ u y I) z I * φ z := by
    funext z
    rw [Lipschitz.laplacian_eq_fderiv_fderiv hu, add_mul]
  rw [hL, hR, integral_add ((hcont 1).integrable_of_hasCompactSupport (hsupp 1))
      ((hcont I).integrable_of_hasCompactSupport (hsupp I)),
    integral_add ((hcont' 1).integrable_of_hasCompactSupport (hsupp' 1))
      ((hcont' I).integrable_of_hasCompactSupport (hsupp' I)),
    integral_mul_fderiv_fderiv_eq hu hφ hφc 1, integral_mul_fderiv_fderiv_eq hu hφ hφc I]

/-- The Laplacian of a smooth function vanishes off its topological support. -/
theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {w : ℂ}
    (hw : w ∉ tsupport φ) : Δ φ w = 0 := by
  rw [Lipschitz.laplacian_eq_fderiv_fderiv hφ]
  have h1 : ∀ v : ℂ, w ∉ tsupport (fun y => fderiv ℝ φ y v) := fun v h =>
    hw (tsupport_fderiv_apply_subset ℝ v h)
  rw [fderiv_of_notMem_tsupport ℝ (h1 1), fderiv_of_notMem_tsupport ℝ (h1 I)]
  simp

/-- **The distributional Laplacian bound of a uniform limit.**  If `f` is the uniform limit on
the closed disc of radius `R > 0` of `C²` functions `u_j` with `|R² Δ u_j| ≤ C₁` on the open disc,
then `h(w) = (f(R w) + a)/C₁` satisfies `|∫ h Δφ| ≤ ∫ |φ|` for every smooth `φ` with compact support
in the unit disc. -/
theorem abs_integral_mul_laplacian_le_of_tendstoUniformlyOn {f : ℂ → ℝ} {u : ℕ → ℂ → ℝ}
    {R C₁ a : ℝ} (hR : 0 < R) (hC₁ : 0 < C₁) (hu : ∀ j, ContDiff ℝ 2 (u j))
    (hconv : TendstoUniformlyOn u f atTop (closedBall 0 R))
    (hΔ : ∀ j, ∀ t ∈ ball (0 : ℂ) R, |R ^ 2 * Δ (u j) t| ≤ C₁)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ ball 0 1) :
    |∫ w, (f (R • w) + a) / C₁ * Δ φ w| ≤ ∫ w, |φ w| := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hΔφc : Continuous (Δ φ) := (Lipschitz.contDiff_laplacian hφ).continuous
  have hΔφ0 : ∀ w, w ∉ ball (0 : ℂ) 1 → Δ φ w = 0 := fun w hw =>
    laplacian_eq_zero_of_notMem_tsupport hφ2 fun h => hw (hφs h)
  have hΔφs : HasCompactSupport (Δ φ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 1) ?_
    intro w hw
    by_contra h
    exact hw (hΔφ0 w fun h' => h (ball_subset_closedBall h'))
  have hΔφi : Integrable (Δ φ) := hΔφc.integrable_of_hasCompactSupport hΔφs
  have hφi : Integrable fun w => |φ w| :=
    (hφ.continuous.abs).integrable_of_hasCompactSupport hφc.abs
  set hj : ℕ → ℂ → ℝ := fun j w => (u j (R • w) + a) / C₁ with hhj
  set h : ℂ → ℝ := fun w => (f (R • w) + a) / C₁ with hh
  have hmaps : MapsTo (fun w : ℂ => R • w) (closedBall 0 1) (closedBall 0 R) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR.le] at *
    nlinarith
  -- the approximants
  have hsm : ContDiff ℝ 2 (fun w : ℂ => R • w) := contDiff_id.const_smul R
  have hjcont : ∀ j, ContDiff ℝ 2 (hj j) := fun j =>
    (((hu j).comp hsm).add contDiff_const).div_const C₁
  have hjb : ∀ j, |∫ w, hj j w * Δ φ w| ≤ ∫ w, |φ w| := by
    intro j
    rw [integral_mul_laplacian_eq (hjcont j) hφ hφc, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hφi (Eventually.of_forall fun w => ?_)
    have hlap : Δ (hj j) w = R ^ 2 * Δ (u j) (R • w) / C₁ := by
      set G : ℂ → ℝ := (C₁⁻¹ • u j) + fun _ => C₁⁻¹ * a with hG
      have hGc : ContDiff ℝ 2 G := ((hu j).const_smul C₁⁻¹).add contDiff_const
      have h1 : hj j = fun w => G (R • w) := by
        funext t
        simp only [hhj, hG, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have h2 : Δ G (R • w) = C₁⁻¹ * Δ (u j) (R • w) := by
        rw [hG, ContDiffAt.laplacian_add (show ContDiffAt ℝ 2 (C₁⁻¹ • u j) (R • w) from
            ((hu j).const_smul C₁⁻¹).contDiffAt) contDiffAt_const,
          InnerProductSpace.laplacian_smul _ (hu j).contDiffAt]
        simp
      rw [h1, laplacian_comp_smul hGc, h2]
      ring
    rw [Real.norm_eq_abs, abs_mul, hlap]
    by_cases hw : w ∈ ball (0 : ℂ) 1
    · have hRw : R • w ∈ ball (0 : ℂ) R := by
        rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hR.le] at *
        nlinarith
      have hb := hΔ j _ hRw
      rw [abs_div, abs_of_pos hC₁]
      calc |R ^ 2 * Δ (u j) (R • w)| / C₁ * |φ w| ≤ C₁ / C₁ * |φ w| := by
            gcongr
        _ = |φ w| := by rw [div_self hC₁.ne', one_mul]
    · have : φ w = 0 := image_eq_zero_of_notMem_tsupport fun h' => hw (hφs h')
      simp [this]
  -- integrability of `h Δφ`
  have hcontOn : ContinuousOn h (closedBall 0 1) := by
    have hfc : ContinuousOn f (closedBall 0 R) := hconv.continuousOn
      (Frequently.of_forall fun j => (hu j).continuous.continuousOn)
    exact ((hfc.comp (continuous_const_smul R).continuousOn hmaps).add continuousOn_const).div_const C₁
  have hhi : Integrable fun w => h w * Δ φ w := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall 0 1)
      ((hcontOn.mul hΔφc.continuousOn).integrableOn_compact (isCompact_closedBall 0 1)) ?_
    intro w hw
    rw [hΔφ0 w fun h' => hw (ball_subset_closedBall h'), mul_zero]
  have hjI : ∀ j, Integrable fun w => hj j w * Δ φ w := fun j =>
    ((hjcont j).continuous.mul hΔφc).integrable_of_hasCompactSupport hΔφs.mul_left
  -- passage to the limit
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set M : ℝ := ∫ w, |Δ φ w| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  set η : ℝ := δ / (M + 1) * C₁ with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨j, hjclose⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv η hη0).exists
  have hdiff : |∫ w, (h w - hj j w) * Δ φ w| ≤ δ := by
    have hbound : ∀ w, ‖(h w - hj j w) * Δ φ w‖ ≤ δ / (M + 1) * |Δ φ w| := by
      intro w
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hw : w ∈ closedBall (0 : ℂ) 1
      · have h1 := hjclose (R • w) (hmaps hw)
        rw [Real.dist_eq] at h1
        have h2 : |h w - hj j w| = |f (R • w) - u j (R • w)| / C₁ := by
          rw [hh, hhj, ← sub_div, abs_div, abs_of_pos hC₁]
          congr 1
          ring_nf
        have h3 : |h w - hj j w| ≤ δ / (M + 1) := by
          rw [h2, div_le_iff₀ hC₁]
          linarith
        exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      · rw [hΔφ0 w fun h' => hw (ball_subset_closedBall h')]
        simp
    rw [← Real.norm_eq_abs]
    calc ‖∫ w, (h w - hj j w) * Δ φ w‖ ≤ ∫ w, δ / (M + 1) * |Δ φ w| :=
          norm_integral_le_of_norm_le (hΔφi.abs.const_mul _) (Eventually.of_forall hbound)
      _ = δ / (M + 1) * M := integral_const_mul _ _
      _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
  have hsubI : Integrable fun w => (h w - hj j w) * Δ φ w :=
    (hhi.sub (hjI j)).congr (Eventually.of_forall fun w => by simp only [Pi.sub_apply]; ring)
  have hsplit : ∫ w, h w * Δ φ w = (∫ w, hj j w * Δ φ w) + ∫ w, (h w - hj j w) * Δ φ w := by
    rw [← integral_add (hjI j) hsubI]
    congr 1
    funext w
    ring
  calc |∫ w, h w * Δ φ w| ≤ |(∫ w, hj j w * Δ φ w)| + |∫ w, (h w - hj j w) * Δ φ w| := by
        rw [hsplit]
        exact abs_add_le _ _
    _ ≤ (∫ w, |φ w|) + δ := add_le_add (hjb j) hdiff

end Calculus

/-! ### Corollary 7.6 -/

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- **`tok-wn-fl:strict-lipschitz`** (WN21 Corollary 7.6) from Lemma 7.5 along the discs
(`StrictDiscLaplacianStatement`) and the Lipschitz bound of functions with bounded Laplacian
(WN-LIP, `lipschitzOfLaplacianStatement`). -/
theorem strictLipschitz_of_strictDiscLaplacian (hD : StrictDiscLaplacianStatement F) :
    StrictLipschitzStatement F := by
  intro E hE hE0 𝒳 _ _ _ μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε Ψ hΨ hVΨ 𝒵 _ _ _ π hπ
    D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ x₀ hx₀ hΨx₀
  set Θ := deformationForm F hμ.contMDiff θ b c Eℰ + ε • η'.form with hΘ
  obtain ⟨U, hUo, hx₀U, C, k₀, hC⟩ := hD E hE hE0 𝒳 μ hμ Eℰ hEℰ θ b c hc hcb hξ hξc ι hι hμι η' ε hε
    Ψ hΨ hVΨ 𝒵 π hπ D' h hh h𝒵c h𝒵conn hExc hΨπ hK χ hχ x₀ hx₀ hΨx₀
  obtain ⟨A, hA⟩ := lipschitzOfLaplacianStatement
  set C₁ : ℝ := max C 1 with hC₁
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC₁ : C ≤ C₁ := le_max_left _ _
  refine ⟨U, hUo, hx₀U, C + C₁ * |A|, k₀, fun k hk x hx => ?_⟩
  -- points over `(x, t)`
  have hpre : ∀ t : ℂ, ∃ y : 𝒳, μ y = (x, affineLinePoint t) := by
    intro t
    by_cases ht : t = 0
    · exact ⟨ι x, by rw [hμι, ht, affineLinePoint_zero]⟩
    · obtain ⟨s, -, hs, -⟩ := exists_fibreSection F hμ (affineLinePoint_ne_projectiveZero ht)
      exact ⟨s x, hs x⟩
  choose σ₀ hσ₀ using hpre
  have hg : Continuous (cutoffObstacle μ χ k) :=
    (continuous_cutoffObstacleLine hχ k).comp (continuous_snd.comp hμ.continuous)
  set v : 𝒳 → EReal := prescribedEnvelope Θ (cutoffObstacle μ χ k) Ψ with hv
  have hvtop : ∀ z, v z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (prescribedEnvelope_le hg z)
  set R : ℝ := Real.exp (-(k : ℝ) / 2) with hR
  have hR0 : 0 < R := Real.exp_pos _
  -- the disc through a point `z` over `(x, t₁)`
  have hdisc : ∀ (t₁ : ℂ) (z : 𝒳), μ z = (x, affineLinePoint t₁) → ∃ σ : ℂ → 𝒳,
      (∀ t, μ (σ t) = (x, affineLinePoint t)) ∧ σ t₁ = z ∧ (t₁ ≠ 0 → σ 0 = ι x) := by
    intro t₁ z hz
    classical
    refine ⟨fun t => if t = t₁ then z else if t = 0 then ι x else σ₀ t, fun t => ?_, by simp,
      fun h0 => by simp [Ne.symm h0]⟩
    by_cases h1 : t = t₁
    · simp [h1, hz]
    · by_cases h0 : t = 0
      · subst h0
        simp [h1, hμι, affineLinePoint_zero]
      · simp [h1, h0, hσ₀]
  -- the bound at the centre
  have hR1 : ‖(0 : ℂ)‖ ≤ R := by simp [hR0.le]
  obtain ⟨σc, hσc, hσc0, -⟩ := hdisc 0 (ι x) (by rw [hμι, affineLinePoint_zero])
  have hc0 := ((hC k hk x hx σc hσc).1 0 hR1)
  rw [hσc0] at hc0
  have hCnn : 0 ≤ C := (abs_nonneg _).trans hc0.2
  have hιreal : v (ι x) = (((v (ι x)).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (hvtop _) hc0.1).symm
  refine ⟨?_, fun t ht0 htR z hz => ?_⟩
  · rw [hιreal, EReal.coe_le_coe_iff]
    have := (abs_le.mp hc0.2).1
    have : 0 ≤ C₁ * |A| := mul_nonneg hC₁0.le (abs_nonneg _)
    linarith
  -- the disc through `z`
  obtain ⟨σ, hσ, hσt, hσ0⟩ := hdisc t z hz
  have hσ0' := hσ0 ht0
  obtain ⟨hbd, uj, hu2, hconv, hΔ⟩ := hC k hk x hx σ hσ
  have htR' : ‖t‖ ≤ R := by linarith [norm_nonneg t]
  have hzbot : v z ≠ ⊥ := by
    have := (hbd t htR').1
    rwa [hσt] at this
  set f : ℂ → ℝ := fun t => (v (σ t)).toReal with hf
  have hR2 : R ^ 2 = Real.exp (-(k : ℝ)) := by
    rw [hR, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hek : Real.exp (-(k : ℝ)) * Real.exp k = 1 := by
    rw [← Real.exp_add]
    simp
  have hek1 : Real.exp (-(k : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith)
  have hΔ' : ∀ j, ∀ t ∈ ball (0 : ℂ) R, |R ^ 2 * Δ (uj j) t| ≤ C₁ := by
    intro j t ht
    obtain ⟨h1, h2⟩ := hΔ j t ht
    rw [hR2, abs_le]
    have hpos : 0 < Real.exp (-(k : ℝ)) := Real.exp_pos _
    constructor
    · have : -C ≤ Real.exp (-(k : ℝ)) * Δ (uj j) t := by
        have h3 : Real.exp (-(k : ℝ)) * (-C) ≤ Real.exp (-(k : ℝ)) * Δ (uj j) t :=
          mul_le_mul_of_nonneg_left h1 hpos.le
        nlinarith
      linarith
    · have h3 : Real.exp (-(k : ℝ)) * Δ (uj j) t ≤ Real.exp (-(k : ℝ)) * (C * Real.exp k) :=
        mul_le_mul_of_nonneg_left h2 hpos.le
      have h4 : Real.exp (-(k : ℝ)) * (C * Real.exp k) = C := by
        rw [mul_comm C, ← mul_assoc, hek, one_mul]
      linarith
  -- the rescaled function
  set hfun : ℂ → ℝ := fun w => (f (R • w) + k) / C₁ with hhfun
  have hmaps : MapsTo (fun w : ℂ => R • w) (closedBall 0 1) (closedBall 0 R) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hR0.le] at *
    nlinarith
  have hfc : ContinuousOn f (closedBall 0 R) := hconv.continuousOn
    (Frequently.of_forall fun j => (hu2 j).continuous.continuousOn)
  have hcont : ContinuousOn hfun (closedBall 0 1) :=
    ((hfc.comp (continuous_const_smul R).continuousOn hmaps).add continuousOn_const).div_const C₁
  have hbound : ∀ w ∈ closedBall (0 : ℂ) 1, |hfun w| ≤ 1 := by
    intro w hw
    have h1 := (hbd (R • w) (by simpa using hmaps hw)).2
    rw [hhfun, abs_div, abs_of_pos hC₁0, div_le_one hC₁0]
    exact h1.trans hCC₁
  have hlap := abs_integral_mul_laplacian_le_of_tendstoUniformlyOn (a := (k : ℝ)) hR0 hC₁0 hu2
    hconv hΔ'
  have hlip := hA hfun hcont hbound (fun φ hφ hφc hφs => hlap φ hφ hφc hφs) (R⁻¹ • t) (by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), inv_mul_le_iff₀ hR0]
    linarith)
  have hRt : R • (R⁻¹ • t) = t := by rw [smul_smul, mul_inv_cancel₀ hR0.ne', one_smul]
  simp only [hhfun, hRt, smul_zero] at hlip
  rw [← sub_div, abs_div, abs_of_pos hC₁0, div_le_iff₀ hC₁0] at hlip
  have hf0 : f 0 = (v (ι x)).toReal := by simp only [hf, hσ0']
  have hft : f t = (v z).toReal := by simp only [hf, hσt]
  have hsub : f t + k - (f 0 + k) = (v z).toReal - (v (ι x)).toReal := by
    rw [hf0, hft]
    ring
  rw [hsub] at hlip
  have hnorm : ‖R⁻¹ • t‖ = Real.exp ((k : ℝ) / 2) * ‖t‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR0.le), hR, ← Real.exp_neg]
    congr 2
    ring
  rw [hnorm] at hlip
  have hA' : A * (Real.exp ((k : ℝ) / 2) * ‖t‖) ≤ |A| * (Real.exp ((k : ℝ) / 2) * ‖t‖) :=
    mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
  have hCe : 0 ≤ C * Real.exp ((k : ℝ) / 2) * ‖t‖ := by positivity
  refine ⟨hzbot, ?_⟩
  calc |(v z).toReal - (v (ι x)).toReal| ≤ A * (Real.exp ((k : ℝ) / 2) * ‖t‖) * C₁ := hlip
    _ ≤ |A| * (Real.exp ((k : ℝ) / 2) * ‖t‖) * C₁ := mul_le_mul_of_nonneg_right hA' hC₁0.le
    _ ≤ (C + C₁ * |A|) * Real.exp ((k : ℝ) / 2) * ‖t‖ := by nlinarith

end SGPT.Okounkov.TranscendentalWN
