import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! Fixed actual translates and degree shifts disappear uniformly in upper point bounds.
Blueprint: okounkov-fixed-translate-upper-control.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SGPT.Okounkov.FixedTranslateUpperControl
open Set Filter Metric
open scoped Topology

/-- Upper point control from ONE actual fixed shift and genuine compact-set Hausdorff convergence. -/
theorem eventually_near_of_fixed_translate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (F : ℕ → Set E) (hFc : ∀ i, IsCompact (F i)) (hFne : ∀ i, (F i).Nonempty)
    (hlim : Tendsto (fun i => hausdorffDist (F i) K) atTop (𝓝 0))
    (Q : ℕ → Set E) (j : ℕ) (w : E)
    (hupper : ∀ i, ∀ᶠ k : ℕ in atTop, ∀ x ∈ Q k,
      ((k+j : ℕ) : ℝ)⁻¹ • (x+w) ∈ F i) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ Q k,
      ∃ z ∈ K, dist ((k : ℝ)⁻¹ • x) z ≤ η := by
  intro η hη
  obtain ⟨i,hi⟩ := ((tendsto_order.mp hlim).2 (η/2) (by linarith)).exists
  obtain ⟨R,hR,hbound⟩ := (hFc i).isBounded.subset_closedBall_lt 0 (0 : E)
  have hsmall : ∀ᶠ k : ℕ in atTop, ((j : ℝ)*R+‖w‖)/(k : ℝ)<η/2 :=
    (tendsto_order.mp (tendsto_const_div_atTop_nhds_zero_nat ((j : ℝ)*R+‖w‖))).2
      (η/2) (by linarith)
  filter_upwards [hupper i,hsmall,eventually_gt_atTop 0] with k hk hs hk0 x hx
  let y : E := ((k+j : ℕ) : ℝ)⁻¹ • (x+w)
  have hy : y ∈ F i := hk x hx
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hkj : ((k+j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.add_pos_left hk0 j).ne'
  have hxy : x = ((k+j : ℕ) : ℝ) • y - w := by
    dsimp only [y]
    rw [smul_inv_smul₀ hkj]
    abel
  have hid : (k : ℝ)⁻¹ • x - y = (k : ℝ)⁻¹ • ((j : ℝ) • y - w) := by
    have he : (k : ℝ)⁻¹ * ((k+j : ℕ) : ℝ) = 1 + (k : ℝ)⁻¹ * (j : ℝ) := by
      push_cast
      field_simp
    calc
      _ = (k : ℝ)⁻¹ • (((k+j : ℕ) : ℝ) • y - w) - y :=
        congrArg (fun z : E => (k : ℝ)⁻¹ • z - y) hxy
      _ = _ := by
        simp only [smul_sub,smul_smul,he,add_smul,one_smul]
        abel
  have hdist : dist ((k : ℝ)⁻¹ • x) y ≤ ((j : ℝ)*R+‖w‖)/(k : ℝ) := by
    rw [dist_eq_norm,hid,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (by exact_mod_cast hk0)]
    calc
      _ ≤ (k : ℝ)⁻¹ * (‖(j : ℝ) • y‖+‖w‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (by positivity))
      _ ≤ (k : ℝ)⁻¹ * ((j : ℝ)*R+‖w‖) := by
        gcongr
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg j)]
        exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall,dist_zero_right] using hbound hy)
          (Nat.cast_nonneg j)
      _ = _ := by rw [div_eq_mul_inv,mul_comm]
  have hfinite : hausdorffEDist (F i) K ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (hFne i) hKne (hFc i).isBounded hKc.isBounded
  obtain ⟨z,hz,hdz⟩ := exists_dist_lt_of_hausdorffDist_lt hy hi hfinite
  exact ⟨z,hz,(dist_triangle _ y z).trans (by linarith)⟩
end SGPT.Okounkov.FixedTranslateUpperControl
