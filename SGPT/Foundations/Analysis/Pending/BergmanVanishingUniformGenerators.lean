import SGPT.Foundations.Analysis.Pending.BergmanGenerators

set_option autoImplicit false

/-! # Genuine uniform Bergman generators with pointwise vanishing constraints

A common-domain closed-subspace adaptation for the infinite holomorphic equation
step in Siu's theorem; no analytic-set or closedness certificate is an input.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BergmanVanishingUniformGenerators

open FirstPass BergmanGenerators

noncomputable section

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]
  {z : ComplexModel n} {R : ℝ} {w : ComplexModel n → ℝ≥0∞}

/-- Finitely many original constrained members dominate all original constrained
members on one internally produced ball, for an arbitrary pointwise zero set. -/
theorem exists_uniform_generators (Z : Set (ComplexModel n)) (hR : 0 < R)
    (hw : AEMeasurable w (volume.restrict (ball z (2 * R)))) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (r K : ℝ), 0 < r ∧
      (∀ l, g l ∈ bergmanUnitBall z R w ∧
        ∀ x ∈ Z ∩ ball z (2 * R), g l x = 0) ∧
      ∀ f ∈ bergmanUnitBall z R w, (∀ x ∈ Z ∩ ball z (2 * R), f x = 0) →
        ∀ y ∈ ball z r, ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2 := by
  classical
  let X : Set (ComplexModel n → ℂ) := {f | f ∈ bergmanUnitBall z R w ∧
    ∀ x ∈ Z ∩ ball z (2 * R), f x = 0}
  have hz2R : z ∈ ball z (2 * R) := mem_ball_self (by linarith)
  obtain ⟨N, g, hgX, hgen⟩ := exists_finite_germ_generators X z fun f hf =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz2R) fun y hy =>
      hf.1.1.differentiableAt (isOpen_ball.mem_nhds hy)
  obtain ⟨L, hL0, hL⟩ := exists_norm_le_of_mem_bergmanUnitBall hR hδ hlow
  have hTB : closedBall z R ⊆ ball z (2 * R) := closedBall_subset_ball_two_mul hR
  have : CompactSpace (closedBall z R) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall z R)
  let ev : ∀ f ∈ X, C(closedBall z R, ℂ) := fun f hf =>
    ⟨fun x => f x, (hf.1.1.continuousOn.mono hTB).domRestrict⟩
  let S : Set C(closedBall z R, ℂ) := {h | ∃ f ∈ X, ∀ x, h x = f x}
  have hSc : IsClosed S := by
    refine isClosed_of_closure_subset fun h hh => ?_
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hh
    choose F hFX hFu using hu
    obtain ⟨ψ, G, hψ, hGX, hGt⟩ := exists_subseq_tendsto_mem_bergmanUnitBall hw hδ hlow (fun i => (hFX i).1)
    have hGzero : ∀ x ∈ Z ∩ ball z (2 * R), G x = 0 := by
      intro x hx
      have hzero : Tendsto (fun i => F (ψ i) x) atTop (𝓝 (0 : ℂ)) := by
        convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)) using 1
        ext i
        exact (hFX (ψ i)).2 x hx
      exact tendsto_nhds_unique (hGt x hx.2) hzero
    refine ⟨G, ⟨hGX, hGzero⟩, fun x => ?_⟩
    have h1 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (h x)) :=
      ((continuous_eval_const x).tendsto h).comp (hlim.comp hψ.tendsto_atTop)
    have h2 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (G x)) := by
      simpa only [hFu] using hGt x (hTB x.2)
    exact tendsto_nhds_unique h1 h2
  have : CompleteSpace S := hSc.completeSpace_coe
  have hzeroX : (0 : ComplexModel n → ℂ) ∈ X :=
    ⟨zero_mem_bergmanUnitBall, fun _ _ => rfl⟩
  have : Nonempty S := ⟨⟨ev 0 hzeroX, 0, hzeroX, fun _ => rfl⟩⟩
  let A : ℕ → Set S := fun j => {h | ∀ y : closedBall z R,
    (y : ComplexModel n) ∈ ball z (R / (j + 1)) →
      ‖(h : C(closedBall z R, ℂ)) y‖ ^ 2 ≤ (j + 1) * ∑ l, ‖g l y‖ ^ 2}
  have hAc : ∀ j, IsClosed (A j) := by
    intro j
    simp only [A, ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (((continuous_eval_const y).comp
        continuous_subtype_val).norm.pow 2) continuous_const
  have hsum0 : ∀ y : ComplexModel n, 0 ≤ ∑ l, ‖g l y‖ ^ 2 := fun y =>
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have hAU : ⋃ j, A j = univ := by
    refine eq_univ_of_forall fun h => mem_iUnion.mpr ?_
    obtain ⟨f, hfX, hfh⟩ := h.2
    obtain ⟨r, hr, K, hK⟩ := hgen f hfX
    obtain ⟨j, hj⟩ := exists_nat_gt (max K (R / r))
    refine ⟨j, fun y hy => ?_⟩
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have hyr : (y : ComplexModel n) ∈ ball z r := by
      refine ball_subset_ball ?_ hy
      rw [div_le_iff₀ hj1]
      have h' := (le_max_right K (R / r)).trans hj.le
      rw [div_le_iff₀ hr] at h'
      nlinarith
    rw [hfh y]
    exact (hK y hyr).trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_left K (R / r)]) (hsum0 y))
  obtain ⟨j, h0, hh0⟩ := nonempty_interior_of_iUnion_of_closed hAc hAU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hh0)
  obtain ⟨f0, hf0X, hf0h⟩ := h0.2
  set t : ℝ := ε / (2 * (2 * L + ε)) with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    nlinarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  refine ⟨N, g, R / (j + 1), 4 * (j + 1) / t ^ 2, by positivity, hgX, fun f hf hfzero y hy => ?_⟩
  have hfX : f ∈ X := ⟨hf, hfzero⟩
  let ft : ComplexModel n → ℂ := fun x => (1 - t : ℂ) * f0 x + (t : ℂ) * f x
  have hftX : ft ∈ X := by
    refine ⟨convex_mem_bergmanUnitBall hw hf0X.1 hf htpos.le ht1, ?_⟩
    intro x hx
    simp only [ft, hf0X.2 x hx, hfzero x hx, mul_zero, add_zero]
  have hyT : y ∈ closedBall z R := by
    refine ball_subset_closedBall.trans (closedBall_subset_closedBall ?_) hy
    exact div_le_self hR.le (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  let hft : S := ⟨ev ft hftX, ft, hftX, fun _ => rfl⟩
  have hdist : dist hft h0 < ε := by
    rw [Subtype.dist_eq]
    have hle : dist (ev ft hftX) (h0 : C(closedBall z R, ℂ)) ≤ t * (2 * L) := by
      refine (ContinuousMap.dist_le (by positivity)).mpr fun x => ?_
      rw [hf0h x, dist_eq_norm]
      change ‖(1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x‖ ≤ _
      rw [show (1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x = (t : ℂ) * (f x - f0 x) by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      linarith [hL f hf x x.2, hL f0 hf0X.1 x x.2]
    refine hle.trans_lt ?_
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have h1 := hball hdist ⟨y, hyT⟩ hy
  have h2 := interior_subset hh0 ⟨y, hyT⟩ hy
  rw [hf0h] at h2
  change ‖ft y‖ ^ 2 ≤ _ at h1
  have htri : t * ‖f y‖ ≤ ‖ft y‖ + ‖f0 y‖ := by
    have heq : (t : ℂ) * f y = ft y - (1 - t : ℂ) * f0 y := by simp only [ft]; ring
    have hn : ‖(t : ℂ) * f y‖ = t * ‖f y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
    rw [← hn, heq]
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, show ((1 - t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (f0 y)]
  have hsq : t ^ 2 * ‖f y‖ ^ 2 ≤ 4 * (j + 1) * ∑ l, ‖g l y‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) htri 2
    nlinarith [sq_nonneg (‖ft y‖ - ‖f0 y‖)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

end
end SGPT.Foundations.Analysis.Pending.BergmanVanishingUniformGenerators
