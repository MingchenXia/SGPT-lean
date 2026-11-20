import SGPT.NPP.DN9Center

/-!
# The joint Levi estimate for smooth plurisubharmonic potentials, uniformly over a compact set

Lane DN9 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, estimate
`eq:chern-potential-joint-bound`, "all bounds are uniform over the centres").

`smoothJointEstimate : SmoothJointEstimate N`: for chart data `(Φ, O, α, U, K)` there are
`r₁, c, A₁, A₂` such that for every centre `z ∈ K`, `0 < |w| < r₁` and every `C²` function `p`
plurisubharmonic on `B(z, c|w|)`, with `S = localSmoothing Φ α p`,

  `L[(z, w) ↦ S(z, |w|)](v, η) ≥ -A₁ |w|² |v|² λ(2|w|) - A₂ (|v|² + |v||η|) λ(|w|)`,
  `λ(t) = t ∂_t S(z, t)`.

Proof: compactness gives adapted fibre maps with uniform constants at all centres of `K`
(`exists_uniform_centerData`, from `SGPT.NPP.DN9.exists_local_centerData`); at a centre the chart
smoothing is DN4's `jointSmoothing` (translated), whose Levi form is bounded by
`SGPT.NPP.DN4.CenterData.leviForm_joint_ge`; DN3's slopes of the radial mean of
`p(z + F(0, ·))` are the slopes of `S(z, ·)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN9

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.NPP.DN5

variable {N : ℕ}

/-! ### Monotonicity of the centre data; finite minima -/

theorem centerData_mono {F : ComplexModel N → ComplexModel N → ComplexModel N}
    {δ r M₀ M₁ M₂ δ' r' M₀' M₁' M₂' : ℝ} (hD : DN4.CenterData F δ r M₀ M₁ M₂) (hδ' : 0 < δ')
    (hδδ : δ' ≤ δ) (hr' : 0 < r') (hrr : r' ≤ r) (h0 : M₀ ≤ M₀') (h1 : M₁ ≤ M₁')
    (h2 : M₂ ≤ M₂') : DN4.CenterData F δ' r' M₀' M₁' M₂' where
  δ_pos := hδ'
  r₁_pos := hr'
  smooth := hD.smooth
  holo z hz := (hD.holo z (ball_subset_ball hδδ hz)).mono (ball_subset_ball hrr)
  map_zero z hz := hD.map_zero z (ball_subset_ball hδδ hz)
  center := hD.center
  inv ξ hξ := hD.inv ξ (ball_subset_ball hrr hξ)
  inv_bound ξ hξ := (hD.inv_bound ξ (ball_subset_ball hrr hξ)).trans h0
  d1_bound ξ hξ := (hD.d1_bound ξ (ball_subset_ball hrr hξ)).trans h1
  d2_bound ξ hξ := (hD.d2_bound ξ (ball_subset_ball hrr hξ)).trans h2

theorem exists_pos_le_finset {X : Type*} (t : Finset X) {f : X → ℝ} (hf : ∀ x ∈ t, 0 < f x) :
    ∃ c > 0, ∀ x ∈ t, c ≤ f x := by
  have hs : 0 ≤ ∑ x ∈ t, (f x)⁻¹ := Finset.sum_nonneg fun x hx => (inv_pos.2 (hf x hx)).le
  refine ⟨(∑ x ∈ t, (f x)⁻¹ + 1)⁻¹, inv_pos.2 (by linarith), fun x hx => ?_⟩
  rw [← inv_inv (f x)]
  apply inv_anti₀ (inv_pos.2 (hf x hx))
  have := Finset.single_le_sum (f := fun y => (f y)⁻¹) (fun y hy => (inv_pos.2 (hf y hy)).le) hx
  linarith

variable {α : ComplexModel N → (ComplexModel N) [⋀^Fin 2]→L[ℝ] ℝ}
  {Φ : ComplexModel N → ComplexModel N → ComplexModel N}

/-- **Adapted fibre maps at all centres of `K`, with uniform constants** (compactness). -/
theorem exists_uniform_centerData {O : Set (ComplexModel N × ComplexModel N)}
    {U K : Set (ComplexModel N)} (hD : ChartData Φ O α U K) :
    ∃ σ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ z₀ ∈ K,
      ∃ F : ComplexModel N → ComplexModel N → ComplexModel N,
        DN4.CenterData F σ σ M M M ∧
        ∀ z' ∈ ball z₀ σ, ∀ (p : ComplexModel N → ℝ) (w : ℂ), ‖w‖ < σ →
          localSmoothing Φ α p z' ‖w‖ = DN4.jointSmoothing F (fun y => p (z₀ + y)) (z' - z₀, w) := by
  have hloc := fun z₁ (hz₁ : z₁ ∈ K) => exists_local_centerData hD hz₁
  choose! ε hε σ hσ M hM0 hF using hloc
  obtain ⟨t, htK, hcover⟩ := hD.2.2.2.2.1.elim_nhds_subcover (fun z₁ => ball z₁ (ε z₁))
    (fun z₁ hz₁ => ball_mem_nhds z₁ (hε z₁ hz₁))
  obtain ⟨σ₀, hσ₀, hσ₀le⟩ := exists_pos_le_finset t (f := σ) fun x hx => hσ x (htK x hx)
  set M₀ := ∑ x ∈ t, M x
  have hM₀le : ∀ x ∈ t, M x ≤ M₀ := fun x hx =>
    Finset.single_le_sum (f := M) (fun y hy => hM0 y (htK y hy)) hx
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg fun y hy => hM0 y (htK y hy)
  refine ⟨σ₀, hσ₀, M₀, hM₀, fun z₀ hz₀ => ?_⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hz₀)
  obtain ⟨F, hFc, hrep⟩ := hF x (htK x hxt) z₀ hzx
  refine ⟨F, centerData_mono hFc hσ₀ (hσ₀le x hxt) hσ₀ (hσ₀le x hxt) (hM₀le x hxt)
    (hM₀le x hxt) (hM₀le x hxt), fun z' hz' p w hw => ?_⟩
  exact hrep z' (ball_subset_ball (hσ₀le x hxt) hz') p w (hw.trans_le (hσ₀le x hxt))

/-- **FPT `eq:chern-potential-joint-bound` for smooth plurisubharmonic potentials, uniformly over
a compact set of centres**. -/
theorem smoothJointEstimate : SmoothJointEstimate N := by
  intro Φ O α U K hD
  obtain ⟨σ, hσ, M, hM, hcen⟩ := exists_uniform_centerData hD
  refine ⟨σ / 12, 2 * M + 1,
    (((N : ℝ) ^ 2 * (5 * (288 * M * M / σ ^ 2))) ^ 2 * (DN3.weightConst N / 8)),
    4 * (N : ℝ) ^ 2 * DN4.KR M M M σ, by positivity, by positivity, ?_, ?_, ?_⟩
  · have := DN3.weightConst_pos (n := N)
    positivity
  · unfold DN4.KR
    positivity
  intro z hz w hw0 hw p hp hpsh v η
  obtain ⟨F, hF, hrep⟩ := hcen z hz
  have hwσ : ‖w‖ < σ := by linarith
  have hw2σ : 2 * ‖w‖ < σ := by linarith
  have hw0' : w ≠ 0 := norm_pos_iff.mp hw0
  have hq : ContDiff ℝ 2 (fun y => p (z + y)) := hp.comp (contDiff_const.add contDiff_id)
  -- the Levi form at the centre
  have hLevi : leviForm (fun x : ComplexModel N × ℂ => localSmoothing Φ α p x.1 ‖x.2‖) (z, w)
      (v, η) = leviForm (DN4.jointSmoothing F (fun y => p (z + y))) ((0 : ComplexModel N), w)
        (v, η) := by
    have hev : (fun x : ComplexModel N × ℂ => localSmoothing Φ α p x.1 ‖x.2‖) =ᶠ[𝓝 (z, w)]
        fun x => DN4.jointSmoothing F (fun y => p (z + y)) (x - (z, 0)) := by
      have hmem : ball z σ ×ˢ ball (0 : ℂ) σ ∈ 𝓝 (z, w) :=
        prod_mem_nhds (ball_mem_nhds z hσ) (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hwσ))
      filter_upwards [hmem] with x hx
      rw [hrep x.1 hx.1 p x.2 (mem_ball_zero_iff.mp hx.2)]
      congr 1
      ext <;> simp
    rw [leviForm_congr hev, leviForm_comp_sub]
    congr 1
    ext <;> simp
  -- the slopes
  have hg1 : ContDiff ℝ 1 (fun ξ => (fun y => p (z + y)) (F 0 ξ)) :=
    (hq.comp (hF.smooth2.comp (contDiff_const.prodMk contDiff_id))).of_le (by norm_num)
  have hslope : ∀ t : ℝ, 0 < t → t < σ →
      DN3.radialSlope (fun ξ => (fun y => p (z + y)) (F 0 ξ)) t =
        t * deriv (localSmoothing Φ α p z) t := by
    intro t ht htσ
    rw [DN3.radialSlope_eq_mul_deriv hg1]
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioo_mem_nhds ht htσ] with t' ht'
    have h := hrep z (mem_ball_self hσ) p (t' : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'.1]; exact ht'.2)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht'.1, sub_self] at h
    rw [h]
    unfold DN3.radialMean DN4.jointSmoothing
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Complex.coe_smul, DN3.kernel]
  -- plurisubharmonicity near the centre
  have hpshF : ∀ ξ ∈ closedBall (0 : ComplexModel N) (2 * ‖w‖), ∀ u,
      0 ≤ leviForm (fun y => p (z + y)) (F 0 ξ) u := by
    intro ξ hξ u
    rw [leviForm_comp_add_left]
    apply hpsh
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hξσ : ξ ∈ ball (0 : ComplexModel N) σ := by
      rw [mem_closedBall, dist_zero_right] at hξ
      rw [mem_ball, dist_zero_right]; linarith
    have hbound : ‖F 0 ξ - F 0 0‖ ≤ M * ‖ξ - 0‖ :=
      (convex_ball (0 : ComplexModel N) σ).norm_image_sub_le_of_norm_fderiv_le
        (fun x hx => hF.holo0.differentiableAt (isOpen_ball.mem_nhds hx))
        (fun x hx => hF.norm_fderiv_F0_le hx) (mem_ball_self hσ) hξσ
    rw [hF.map_zero 0 (mem_ball_self hσ), sub_zero, sub_zero] at hbound
    rw [mem_closedBall, dist_zero_right] at hξ
    calc ‖F 0 ξ‖ ≤ M * ‖ξ‖ := hbound
      _ ≤ M * (2 * ‖w‖) := mul_le_mul_of_nonneg_left hξ hM
      _ < (2 * M + 1) * ‖w‖ := by nlinarith
  have hmain := hF.leviForm_joint_ge (w₀ := w) (by linarith) hw0' hq hpshF v η
  rw [hslope ‖w‖ hw0 hwσ, hslope (2 * ‖w‖) (by positivity) hw2σ] at hmain
  rw [hLevi]
  linarith

end SGPT.NPP.DN9
