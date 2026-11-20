import SGPT.Foundations.Analysis.Pending.BergmanGenerators

set_option autoImplicit false

/-!
# Original weighted Bergman generators at arbitrary interior points

`exists_uniform_generators_at` selects functions from the same original weighted
unit ball. The comparison point may be any interior point of the original domain.
The smaller ball is used only for the supremum-norm restriction space; the closedness
argument retains Montel--Fatou compactness on the entire original weighted domain.

This is the fixed-domain finite-generation step needed for the all-point jet
criterion in Demailly, *Analytic Methods*, Corollary 14.3.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BergmanInteriorUniformGenerators

noncomputable section

open FirstPass BergmanGenerators

variable {n : ℕ} [MeasurableSpace (ComplexModel n)] [BorelSpace (ComplexModel n)]

/-- Finite members of the original weighted ball dominate all original members near
any prescribed interior point, with one radius and one constant. -/
theorem exists_uniform_generators_at {z p : ComplexModel n} {R : ℝ}
    {w : ComplexModel n → ℝ≥0∞} (hR : 0 < R)
    (hw : AEMeasurable w (volume.restrict (ball z (2 * R)))) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y)
    (hp : p ∈ ball z (2 * R)) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel n → ℂ) (r K : ℝ), 0 < r ∧
      (∀ l, g l ∈ bergmanUnitBall z R w) ∧
      ∀ f ∈ bergmanUnitBall z R w, ∀ y ∈ ball p r,
        ‖f y‖ ^ 2 ≤ K * ∑ l, ‖g l y‖ ^ 2 := by
  classical
  set X := bergmanUnitBall z R w with hX
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.mp isOpen_ball p hp
  set s : ℝ := min ρ R / 4 with hsdef
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsub : ball p (2 * s) ⊆ ball z (2 * R) := by
    refine (ball_subset_ball ?_).trans hρD
    have := min_le_left ρ R
    dsimp [s]
    linarith
  have hlocal : ∀ f ∈ X, f ∈ bergmanUnitBall p s w := by
    intro f hf
    exact ⟨hf.1.mono hsub, (lintegral_mono_set hsub).trans hf.2⟩
  obtain ⟨N, g, hgX, hgen⟩ := exists_finite_germ_generators X p fun f hf =>
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hp) fun y hy =>
      hf.1.differentiableAt (isOpen_ball.mem_nhds hy)
  obtain ⟨L, hL0, hLp⟩ := exists_norm_le_of_mem_bergmanUnitBall hs hδ
    (fun y hy => hlow y (hsub hy))
  have hL : ∀ f ∈ X, ∀ x ∈ closedBall p s, ‖f x‖ ≤ L :=
    fun f hf x hx => hLp f (hlocal f hf) x hx
  have hTB : closedBall p s ⊆ ball z (2 * R) :=
    (closedBall_subset_ball_two_mul hs).trans hsub
  have : CompactSpace (closedBall p s) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall p s)
  let ev : ∀ f ∈ X, C(closedBall p s, ℂ) := fun f hf =>
    ⟨fun x => f x, (hf.1.continuousOn.mono hTB).domRestrict⟩
  let S : Set C(closedBall p s, ℂ) := {h | ∃ f ∈ X, ∀ x, h x = f x}
  have hSc : IsClosed S := by
    refine isClosed_of_closure_subset fun h hh => ?_
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hh
    choose F hFX hFu using hu
    obtain ⟨ψ, G, hψ, hGX, hGt⟩ := exists_subseq_tendsto_mem_bergmanUnitBall hw hδ hlow hFX
    refine ⟨G, hGX, fun x => ?_⟩
    have h1 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (h x)) :=
      ((continuous_eval_const x).tendsto h).comp (hlim.comp hψ.tendsto_atTop)
    have h2 : Tendsto (fun i => u (ψ i) x) atTop (𝓝 (G x)) := by
      simpa only [hFu] using hGt x (hTB x.2)
    exact tendsto_nhds_unique h1 h2
  have : CompleteSpace S := hSc.completeSpace_coe
  have : Nonempty S := ⟨⟨ev 0 zero_mem_bergmanUnitBall, 0, zero_mem_bergmanUnitBall,
    fun _ => rfl⟩⟩
  let A : ℕ → Set S := fun j => {h | ∀ y : closedBall p s,
    (y : ComplexModel n) ∈ ball p (s / (j + 1)) →
      ‖(h : C(closedBall p s, ℂ)) y‖ ^ 2 ≤ (j + 1) * ∑ l, ‖g l y‖ ^ 2}
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
    obtain ⟨j, hj⟩ := exists_nat_gt (max K (s / r))
    refine ⟨j, fun y hy => ?_⟩
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    have hyr : (y : ComplexModel n) ∈ ball p r := by
      refine ball_subset_ball ?_ hy
      rw [div_le_iff₀ hj1]
      have h' := (le_max_right K (s / r)).trans hj.le
      rw [div_le_iff₀ hr] at h'
      nlinarith
    rw [hfh y]
    exact (hK y hyr).trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_left K (s / r)]) (hsum0 y))
  obtain ⟨j, h0, hh0⟩ := nonempty_interior_of_iUnion_of_closed hAc hAU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hh0)
  obtain ⟨f0, hf0X, hf0h⟩ := h0.2
  set t : ℝ := ε / (2 * (2 * L + ε)) with ht
  have htpos : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    nlinarith
  have hj1 : (0 : ℝ) < j + 1 := by positivity
  refine ⟨N, g, s / (j + 1), 4 * (j + 1) / t ^ 2, by positivity, hgX, fun f hf y hy => ?_⟩
  let ft : ComplexModel n → ℂ := fun x => (1 - t : ℂ) * f0 x + (t : ℂ) * f x
  have hftX : ft ∈ X := convex_mem_bergmanUnitBall hw hf0X hf htpos.le ht1
  have hyT : y ∈ closedBall p s := by
    refine ball_subset_closedBall.trans (closedBall_subset_closedBall ?_) hy
    exact div_le_self hs.le (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
  let hft : S := ⟨ev ft hftX, ft, hftX, fun _ => rfl⟩
  have hdist : dist hft h0 < ε := by
    rw [Subtype.dist_eq]
    have hle : dist (ev ft hftX) (h0 : C(closedBall p s, ℂ)) ≤ t * (2 * L) := by
      refine (ContinuousMap.dist_le (by positivity)).mpr fun x => ?_
      rw [hf0h x, dist_eq_norm]
      change ‖(1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x‖ ≤ _
      rw [show (1 - t : ℂ) * f0 x + (t : ℂ) * f x - f0 x = (t : ℂ) * (f x - f0 x) by ring,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le]
      gcongr
      refine (norm_sub_le _ _).trans ?_
      linarith [hL f hf x x.2, hL f0 hf0X x x.2]
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

end SGPT.Foundations.Analysis.Pending.BergmanInteriorUniformGenerators
