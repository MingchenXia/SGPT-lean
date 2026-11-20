import SGPT.Foundations.Analysis.Pending.ActualHolomorphicFiniteJetGrowth
import SGPT.Foundations.Analysis.Pending.HolomorphicTaylorTail

set_option autoImplicit false

/-! # Actual finite tangential order under all higher normal perturbations -/

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.HolomorphicHighNormalPerturbationOrder

open FirstPass HolomorphicTaylorTail CoordinatePlaneDivision

noncomputable section

private theorem analyticAt_of_eventually_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {f : E → ℂ} {p : E}
    (hf : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ f z) : AnalyticAt ℂ f p := by
  obtain ⟨U, hUf, hU, hp⟩ := _root_.eventually_nhds_iff.mp hf
  exact HolomorphicAnalytic.analyticAt_of_differentiableOn hU
    (fun z hz => (hUf z hz).differentiableWithinAt) hp

private theorem exists_unit_of_high_perturbation {n : ℕ}
    {H : ComplexModel n → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ H z)
    (v e : ComplexModel n) {k : ℕ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (hline : ∀ᶠ t in 𝓝 (0 : ℂ), H (t • v) = t ^ k * h t)
    (L : ℕ) (hL : k < L) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), H (t • v + t ^ L • e) = t ^ k * u t := by
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le k) hL
  obtain ⟨G, hG, heq⟩ := exists_taylor_tail hH e 1
  let c : ℂ → ComplexModel n × ℂ := fun t => (t • v, t ^ L)
  have hc : Differentiable ℂ c :=
    (differentiable_id.smul_const v).prodMk (differentiable_id.pow L)
  have hc0 : c 0 = (0, 0) := by simp [c, Nat.ne_of_gt hLpos]
  have hct : Tendsto c (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [hc0] using hc.continuous.continuousAt.tendsto (x := (0 : ℂ))
  have hGc : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun t => G (c t)) t := by
    filter_upwards [hct.eventually hG] with t ht
    exact ht.comp t (hc t)
  have hGca := analyticAt_of_eventually_differentiableAt hGc
  let u : ℂ → ℂ := fun t => h t + t ^ (L - k) * G (c t)
  refine ⟨u, hh.add ((analyticAt_id.pow (L - k)).mul hGca), ?_, ?_⟩
  · simpa [u, Nat.ne_of_gt (Nat.sub_pos_of_lt hL)] using hh0
  · filter_upwards [hline, hct.eventually heq] with t ht he
    have htaylor : H (t • v + t ^ L • e) = H (t • v) + t ^ L * G (c t) := by
      simpa only [c, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one,
        inv_one, List.replicate_zero, iterDeriv_nil, one_mul, pow_zero,
        mul_one, pow_one] using he
    rw [htaylor, ht]
    dsimp only [u]
    rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hL.le]

/-- The original hyperplane-nonzero holomorphic germ supplies a finite
tangential order before all later normal weights, without an order input. -/
theorem exists_tangential_order_before_all_high_normal_weights {m : ℕ}
    {H : ComplexModel (m + 2) → ℂ}
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ H z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)),
      z (Fin.last (m + 1)) = 0 ∧ H z ≠ 0) :
    ∃ (k : ℕ) (v : ComplexModel (m + 2)),
      v ≠ 0 ∧ v (Fin.last (m + 1)) = 0 ∧
      ∀ (e : ComplexModel (m + 2)) (L : ℕ), k < L → ∃ u : ℂ → ℂ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        ∀ᶠ t in 𝓝 (0 : ℂ),
          H (t • v + t ^ L • e) =
            t ^ k * u t := by
  classical
  let j : Fin (m + 2) := Fin.last (m + 1)
  suffices ∃ (k : ℕ) (v : ComplexModel (m + 2)) (h : ℂ → ℂ),
      v ≠ 0 ∧ v j = 0 ∧ AnalyticAt ℂ h 0 ∧ h 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), H (t • v) = t ^ k * h t by
    obtain ⟨k, v, h, hv, hvj, hh, hh0, hline⟩ := this
    exact ⟨k, v, hv, hvj, fun e L hL => exists_unit_of_high_perturbation hH v e hh hh0 hline L hL⟩
  by_cases hH0 : H 0 ≠ 0
  · let v : ComplexModel (m + 2) := EuclideanSpace.single (0 : Fin (m + 2)) (1 : ℂ)
    have hij : (0 : Fin (m + 2)) ≠ j := by
      intro he
      have hval := congrArg Fin.val he
      simp only [j, Fin.val_zero, Fin.val_last] at hval
      omega
    have han := analyticAt_of_eventually_differentiableAt hH
    have hlin : AnalyticAt ℂ (fun t : ℂ => t • v) 0 :=
      analyticAt_id.smul analyticAt_const
    have hh : AnalyticAt ℂ (fun t : ℂ => H (t • v)) 0 := by
      have han' : AnalyticAt ℂ H ((0 : ℂ) • v) := by
        simpa only [zero_smul] using han
      exact AnalyticAt.comp (g := H) (f := fun t : ℂ => t • v) han' hlin
    refine ⟨0, v, (fun t => H (t • v)), by simp [v], ?_, hh, ?_, ?_⟩
    · simp [v, Ne.symm hij]
    · simpa only [zero_smul] using hH0
    · exact Eventually.of_forall fun t => by simp
  · have hHzero : H 0 = 0 := not_ne_iff.mp hH0
    let P : ComplexModel (m + 2) → ComplexModel (m + 2) := fun z => setCoord z j 0
    have hPd : Differentiable ℂ P :=
      (differentiable_setCoord j).comp (differentiable_id.prodMk (differentiable_const 0))
    have hP0 : P 0 = 0 := by ext i; simp [P]
    have hPt : Tendsto P (𝓝 0) (𝓝 0) := by
      simpa only [hP0] using hPd.continuous.continuousAt.tendsto (x := (0 : ComplexModel (m + 2)))
    let F : ComplexModel (m + 2) → ℂ := fun z => H (P z)
    have hF : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ F z := by
      filter_upwards [hPt.eventually hH] with z hz
      exact hz.comp z (hPd z)
    have hFnon : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), F z = 0 := by
      intro hfzero
      obtain ⟨z, hz, hfz⟩ := (hne.and_eventually hfzero).exists
      have hPz : P z = z := by
        dsimp only [P]
        rw [← hz.1, setCoord_self]
      exact hz.2 (by simpa only [F, hPz] using hfz)
    obtain ⟨k, i, _, _, C, _, _, w, h, _, hh, hh0, hline⟩ :=
      ActualHolomorphicFiniteJetGrowth.exists_finite_family_jet_growth
        (fun _ : Fin 1 => F) (fun _ => hF) ⟨0, hFnon⟩
    let v : ComplexModel (m + 2) := P w
    have hPv (t : ℂ) : P (t • w) = t • v := by
      ext l
      simp [P, v, setCoord_apply, PiLp.smul_apply]
    have hline' : ∀ᶠ t in 𝓝 (0 : ℂ), H (t • v) = t ^ k * h t := by
      filter_upwards [hline] with t ht
      simpa only [F, hPv] using ht
    have hv : v ≠ 0 := by
      intro hvzero
      have hz : ∀ᶠ t in 𝓝 (0 : ℂ), t ^ k * h t = 0 := by
        filter_upwards [hline'] with t ht
        simpa only [hvzero, smul_zero, hHzero] using ht.symm
      have hunit : ∀ᶠ t in 𝓝 (0 : ℂ), h t ≠ 0 :=
        hh.continuousAt.tendsto.eventually (isOpen_compl_singleton.mem_nhds hh0)
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hz.and hunit)
      let t : ℂ := (r / 2 : ℝ)
      have ht0 : t ≠ 0 := by
        dsimp only [t]
        exact_mod_cast (half_pos hr).ne'
      have htm : t ∈ ball (0 : ℂ) r := by
        simp only [mem_ball_zero_iff, t, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hr)]
        exact half_lt_self hr
      obtain ⟨heq, hnon⟩ := hball t htm
      exact (mul_ne_zero (pow_ne_zero k ht0) hnon) heq
    refine ⟨k, v, h, hv, ?_, hh, hh0, hline'⟩
    simp [v, P]

end
end SGPT.Foundations.Analysis.Pending.HolomorphicHighNormalPerturbationOrder
