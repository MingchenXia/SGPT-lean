import SGPT.Envelopes.TosC11cChart
import SGPT.Foundations.Analysis.Pending.HolderMollification
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Mollification of `C^{1,1}` functions in a chart

Lane TOS-C11c (`claude-tos-c11c`, node `tos-c11c:mollify`).  Source: Xia, *Foundations of
pluripotential theory*, proof of `thm:kahler-real-c11-envelope` ("using convolution in finitely many
charts and a smooth partition of unity, we obtain smooth functions `f_{j,ρ}` that converge to `f_j` in
`C¹` as `ρ → 0` and have uniformly bounded covariant Hessians; indeed, the second derivatives of such a
partitioned convolution are the cutoffs times the convolutions of the bounded weak second derivatives
of `f_j`, plus terms that involve only the values and first derivatives"), for SGPT `thm:Tos_C11`.

Everything here is in `ℂⁿ = ComplexModel n`:

* `exists_mollify` — a `C¹` function with `|u| ≤ A`, `‖Du‖ ≤ G` and `L`-Lipschitz derivative has, for
  every `ρ > 0`, a smooth mollification `g` with `|g| ≤ A`, `‖Dg‖ ≤ G`, `‖D²g‖ ≤ L` and `|g - u| ≤ Gρ`
  (TN's `HolderMollification`: mollification commutes with `D` and preserves sup norms and Lipschitz
  constants).
* `exists_cutoff` — smooth Urysohn functions between a closed and an open set.
* `cutoff_mul_bounds` — a cutoff `ψ` supported in `K₃` times a function `g` with `C^{1,1}` bounds on the
  closed `δ`-thickening of `K₃` (Lipschitz bounds only along segments inside it) is a globally `C¹`
  function with bounded, globally Lipschitz derivative, with explicit constants.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal Convolution Manifold

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HolderMollification

variable {n : ℕ}

/-- **Mollification with bounds** (FPT, proof of `thm:kahler-real-c11-envelope`): a `C¹` function `u`
on `ℂⁿ` with `|u| ≤ A`, `‖Du‖ ≤ G` and `L`-Lipschitz `Du` has, for every `ρ > 0`, a smooth `g` with
`|g| ≤ A`, `‖Dg‖ ≤ G`, `‖D²g‖ ≤ L` and `|g - u| ≤ G ρ`. -/
theorem exists_mollify {u : ComplexModel n → ℝ} (hu : ContDiff ℝ 1 u) {A G L : ℝ} (hG0 : 0 ≤ G)
    (hL0 : 0 ≤ L) (hA : ∀ x, |u x| ≤ A) (hG : ∀ x, ‖fderiv ℝ u x‖ ≤ G)
    (hL : ∀ x y, ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ L * ‖x - y‖) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : ComplexModel n → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, |g x| ≤ A) ∧
      (∀ x, ‖fderiv ℝ g x‖ ≤ G) ∧ (∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ L) ∧
      ∀ x, |g x - u x| ≤ G * ρ := by
  let b : ContDiffBump (0 : ComplexModel n) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  set φ : ComplexModel n → ℝ := b.normed volume with hφ
  have hφ0 : ∀ t, 0 ≤ φ t := b.nonneg_normed
  have hφi : Integrable φ volume := b.integrable_normed
  have hφc : Continuous φ := b.continuous_normed
  have hφ1 : ∫ t, φ t = 1 := b.integral_normed
  have hφs : ContDiff ℝ ∞ φ := b.contDiff_normed
  have hφcs : HasCompactSupport φ := b.hasCompactSupport_normed
  have hφR : ∀ t, ρ < ‖t‖ → φ t = 0 := by
    intro t ht
    have : t ∉ Function.support φ := by
      rw [hφ, b.support_normed_eq]
      simp only [mem_ball, dist_zero_right, not_lt]
      exact ht.le
    exact Function.notMem_support.mp this
  set g : ComplexModel n → ℝ := φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u with hgdef
  have hA' : ∀ x, ‖u x‖ ≤ A := fun x => by rw [Real.norm_eq_abs]; exact hA x
  have hderiv : ∀ x, HasFDerivAt g
      ((φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ u) x) x :=
    fun x => hasFDerivAt_convolution_of_bounded hφi hφc hu hA' hG x
  have hfd : fderiv ℝ g = φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ u :=
    funext fun x => (hderiv x).fderiv
  have hDuc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hDuH : HolderWith L.toNNReal 1 (fderiv ℝ u) :=
    holderWith_one.mpr (LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.coe_toNNReal L hL0, dist_eq_norm, dist_eq_norm]
      exact hL x y)
  have huH : HolderWith G.toNNReal 1 u :=
    holderWith_one.mpr (lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by norm_num))
      fun x => by rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal G hG0]; exact hG x)
  refine ⟨g, contDiff_convolution hφcs hφs hu.continuous.locallyIntegrable, fun x => ?_,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [← Real.norm_eq_abs]; exact norm_convolution_le hφ0 hφi hφ1 hA' x
  · rw [hfd]; exact norm_convolution_le hφ0 hφi hφ1 hG x
  · have hlip : HolderWith L.toNNReal 1 (fderiv ℝ g) := by
      rw [hfd]; exact holderWith_convolution hφ0 hφi hφc hφ1 hDuc hG hDuH
    have := norm_fderiv_le_of_lipschitz ℝ (holderWith_one.mp hlip) (x₀ := x)
    rwa [Real.coe_toNNReal L hL0] at this
  · rw [← Real.norm_eq_abs]
    have := norm_convolution_sub_le hφ0 hφi hφc hφ1 hφR hu.continuous hA' huH x
    rwa [NNReal.coe_one, Real.rpow_one, Real.coe_toNNReal G hG0] at this

/-- **Smooth Urysohn functions** in `ℂⁿ`: for a closed `s` inside an open `t` there is a smooth
`ψ : ℂⁿ → [0, 1]` equal to `1` on `s` and to `0` outside `t`. -/
theorem exists_cutoff {s t : Set (ComplexModel n)} (hs : IsClosed s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ ψ : ComplexModel n → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ x ∈ s, ψ x = 1) ∧
      (∀ x, x ∉ t → ψ x = 0) ∧ ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1 := by
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (𝓘(ℝ, ComplexModel n)) (n := (⊤ : ℕ∞)) ht.isClosed_compl hs
    (disjoint_compl_left_iff_subset.mpr hst)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, fun x hx => hf1 hx, fun x hx => hf0 hx,
    fun x => hf01 x⟩

/-- **A cutoff times a `C^{1,1}` function.**  Let `ψ` be smooth with values in `[-1, 1]`, support in
`K₃` and `‖Dψ‖, ‖D²ψ‖ ≤ Cψ`, and let `g` be `C¹` on an open `U` containing the closed
`δ`-thickening `K₄` of `K₃`, with `|g| ≤ B`, `‖Dg‖ ≤ G` on `K₄` and `‖Dg(x) - Dg(y)‖ ≤ L‖x - y‖` for
`x, y ∈ K₄` with `[x, y] ⊆ K₄`.  Then `h = ψ g` is globally `C¹` with `|h| ≤ B`,
`‖Dh‖ ≤ B Cψ + G`, and `Dh` is Lipschitz with constant `L + 2G Cψ + B Cψ + 2(B Cψ + G)/δ`. -/
theorem cutoff_mul_bounds {U K₃ : Set (ComplexModel n)} {δ : ℝ} (hδ : 0 < δ) (hU : IsOpen U)
    (hKU : cthickening δ K₃ ⊆ U) {ψ : ComplexModel n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ K₃) (hψ1 : ∀ x, |ψ x| ≤ 1) {Cψ : ℝ}
    (hCψ1 : ∀ x, ‖fderiv ℝ ψ x‖ ≤ Cψ) (hCψ2 : ∀ x, ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ Cψ)
    {g : ComplexModel n → ℝ} (hg : ContDiffOn ℝ 1 g U) {B G L : ℝ} (hB0 : 0 ≤ B) (hG0 : 0 ≤ G)
    (hL0 : 0 ≤ L) (hB : ∀ x ∈ cthickening δ K₃, |g x| ≤ B) (hG : ∀ x ∈ cthickening δ K₃, ‖fderiv ℝ g x‖ ≤ G)
    (hL : ∀ x ∈ cthickening δ K₃, ∀ y ∈ cthickening δ K₃, segment ℝ x y ⊆ cthickening δ K₃ →
      ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ L * ‖x - y‖) :
    ContDiff ℝ 1 (fun x => ψ x * g x) ∧ (∀ x, |ψ x * g x| ≤ B) ∧
      (∀ x, ‖fderiv ℝ (fun x => ψ x * g x) x‖ ≤ B * Cψ + G) ∧
      ∀ x y, ‖fderiv ℝ (fun x => ψ x * g x) x - fderiv ℝ (fun x => ψ x * g x) y‖ ≤
        (L + 2 * G * Cψ + B * Cψ + 2 * (B * Cψ + G) / δ) * ‖x - y‖ := by
  set K₄ := cthickening δ K₃ with hK₄
  set h : ComplexModel n → ℝ := fun x => ψ x * g x with hh
  have hK34 : K₃ ⊆ K₄ := self_subset_cthickening K₃
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ1 0)
  -- outside the support of `ψ`, `h` vanishes near the point
  have hzero : ∀ z, z ∉ tsupport ψ → h =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hz] with w hw
    simp [hh, image_eq_zero_of_notMem_tsupport hw]
  have hcases : ∀ z, z ∈ U ∨ z ∉ tsupport ψ := fun z => by
    by_cases hz : z ∈ tsupport ψ
    · exact Or.inl (hKU (hK34 (hψs hz)))
    · exact Or.inr hz
  have hdiffg : ∀ z ∈ U, DifferentiableAt ℝ g z := fun z hz =>
    (hg.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hdiffψ : ∀ z, DifferentiableAt ℝ ψ z := fun z => hψ.differentiable (by simp) z
  have hformula : ∀ z ∈ U, fderiv ℝ h z = ψ z • fderiv ℝ g z + g z • fderiv ℝ ψ z :=
    fun z hz => fderiv_mul (hdiffψ z) (hdiffg z hz)
  have hfzero : ∀ z, z ∉ tsupport ψ → fderiv ℝ h z = 0 := fun z hz => by
    rw [(hzero z hz).fderiv_eq, fderiv_const_apply]
  -- smoothness
  have hsmooth : ContDiff ℝ 1 h := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases hcases z with hz | hz
    · exact (hψ.contDiffAt.of_le (by simp)).mul (hg.contDiffAt (hU.mem_nhds hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  -- the value bound
  have hval : ∀ x, |h x| ≤ B := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · simp only [hh, abs_mul]
      calc |ψ x| * |g x| ≤ 1 * B :=
            mul_le_mul (hψ1 x) (hB x (hK34 (hψs hx))) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
    · simp [hh, image_eq_zero_of_notMem_tsupport hx, hB0]
  -- the derivative bound
  have hder : ∀ x, ‖fderiv ℝ h x‖ ≤ B * Cψ + G := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hxK := hK34 (hψs hx)
      rw [hformula x (hKU hxK)]
      calc _ ≤ ‖ψ x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ ψ x‖ := norm_add_le _ _
        _ = |ψ x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ ψ x‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ 1 * G + B * Cψ := add_le_add
            (mul_le_mul (hψ1 x) (hG x hxK) (norm_nonneg _) zero_le_one)
            (mul_le_mul (hB x hxK) (hCψ1 x) (norm_nonneg _) hB0)
        _ = B * Cψ + G := by ring
    · rw [hfzero x hx, norm_zero]; positivity
  -- global Lipschitz bounds for `ψ` and `Dψ`
  have hψlip : ∀ x y, |ψ x - ψ y| ≤ Cψ * ‖x - y‖ := by
    intro x y
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (fun z _ => hdiffψ z)
      (fun z _ => hCψ1 z) convex_univ (mem_univ y) (mem_univ x)
    rwa [Real.norm_eq_abs] at this
  have hDψlip : ∀ x y, ‖fderiv ℝ ψ x - fderiv ℝ ψ y‖ ≤ Cψ * ‖x - y‖ := by
    intro x y
    have hD : Differentiable ℝ (fderiv ℝ ψ) :=
      (contDiff_infty_iff_fderiv.mp hψ).2.differentiable (by simp)
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (fun z _ => hD z)
      (fun z _ => hCψ2 z) convex_univ (mem_univ y) (mem_univ x)
  refine ⟨hsmooth, hval, hder, fun x y => ?_⟩
  set L' := L + 2 * G * Cψ + B * Cψ + 2 * (B * Cψ + G) / δ with hL'
  have hM0 : 0 ≤ B * Cψ + G := by positivity
  have hL'0 : 0 ≤ L' := by rw [hL']; positivity
  by_cases hfar : δ ≤ ‖x - y‖
  · calc ‖fderiv ℝ h x - fderiv ℝ h y‖ ≤ ‖fderiv ℝ h x‖ + ‖fderiv ℝ h y‖ := norm_sub_le _ _
      _ ≤ 2 * (B * Cψ + G) := by linarith [hder x, hder y]
      _ = (2 * (B * Cψ + G) / δ) * δ := by field_simp
      _ ≤ (2 * (B * Cψ + G) / δ) * ‖x - y‖ := mul_le_mul_of_nonneg_left hfar (by positivity)
      _ ≤ L' * ‖x - y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [hL']
          have : 0 ≤ L + 2 * G * Cψ + B * Cψ := by positivity
          linarith
  rw [not_le] at hfar
  by_cases hsupp : x ∈ tsupport ψ ∨ y ∈ tsupport ψ
  · -- both points and the segment lie in `K₄`
    have hball : ∃ p ∈ K₃, x ∈ ball p δ ∧ y ∈ ball p δ := by
      rcases hsupp with hx | hy
      · exact ⟨x, hψs hx, mem_ball_self hδ, by rw [mem_ball, dist_comm, dist_eq_norm]; exact hfar⟩
      · exact ⟨y, hψs hy, by rw [mem_ball, dist_eq_norm]; exact hfar, mem_ball_self hδ⟩
    obtain ⟨p, hp, hxp, hyp⟩ := hball
    have hbK : ball p δ ⊆ K₄ :=
      (ball_subset_thickening hp δ).trans (thickening_subset_cthickening δ K₃)
    have hseg : segment ℝ x y ⊆ K₄ := ((convex_ball p δ).segment_subset hxp hyp).trans hbK
    have hxK : x ∈ K₄ := hbK hxp
    have hyK : y ∈ K₄ := hbK hyp
    rw [hformula x (hKU hxK), hformula y (hKU hyK)]
    have hgxy : |g x - g y| ≤ G * ‖x - y‖ := by
      have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := segment ℝ x y)
        (fun z hz => hdiffg z (hKU (hseg hz))) (fun z hz => hG z (hseg hz)) (convex_segment x y)
        (right_mem_segment ℝ x y) (left_mem_segment ℝ x y)
      rwa [Real.norm_eq_abs] at this
    have hdecomp : (ψ x • fderiv ℝ g x + g x • fderiv ℝ ψ x) -
        (ψ y • fderiv ℝ g y + g y • fderiv ℝ ψ y) =
        ψ x • (fderiv ℝ g x - fderiv ℝ g y) + (ψ x - ψ y) • fderiv ℝ g y +
          g x • (fderiv ℝ ψ x - fderiv ℝ ψ y) + (g x - g y) • fderiv ℝ ψ y := by
      simp only [smul_sub, sub_smul]; abel
    rw [hdecomp]
    have h1 : ‖ψ x • (fderiv ℝ g x - fderiv ℝ g y)‖ ≤ L * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |ψ x| * ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ 1 * (L * ‖x - y‖) :=
            mul_le_mul (hψ1 x) (hL x hxK y hyK hseg) (norm_nonneg _) zero_le_one
        _ = L * ‖x - y‖ := one_mul _
    have h2 : ‖(ψ x - ψ y) • fderiv ℝ g y‖ ≤ Cψ * ‖x - y‖ * G := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hψlip x y) (hG y hyK) (norm_nonneg _) (by positivity)
    have h3 : ‖g x • (fderiv ℝ ψ x - fderiv ℝ ψ y)‖ ≤ B * (Cψ * ‖x - y‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hB x hxK) (hDψlip x y) (norm_nonneg _) hB0
    have h4 : ‖(g x - g y) • fderiv ℝ ψ y‖ ≤ G * ‖x - y‖ * Cψ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hgxy (hCψ1 y) (norm_nonneg _) (by positivity)
    have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hextra : 0 ≤ 2 * (B * Cψ + G) / δ * ‖x - y‖ := by positivity
    calc _ ≤ ‖ψ x • (fderiv ℝ g x - fderiv ℝ g y)‖ + ‖(ψ x - ψ y) • fderiv ℝ g y‖ +
          ‖g x • (fderiv ℝ ψ x - fderiv ℝ ψ y)‖ + ‖(g x - g y) • fderiv ℝ ψ y‖ :=
          (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
            (add_le_add_left (norm_add_le _ _) _)) _) |>.trans (le_of_eq (by ring))
      _ ≤ L * ‖x - y‖ + Cψ * ‖x - y‖ * G + B * (Cψ * ‖x - y‖) + G * ‖x - y‖ * Cψ := by
          linarith
      _ ≤ L' * ‖x - y‖ := by rw [hL']; nlinarith
  · rw [not_or] at hsupp
    rw [hfzero x hsupp.1, hfzero y hsupp.2, sub_zero, norm_zero]
    positivity

end SGPT.Envelopes.TosC11c
