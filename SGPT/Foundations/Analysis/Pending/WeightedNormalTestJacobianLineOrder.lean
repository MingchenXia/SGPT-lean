import SGPT.Foundations.Analysis.Pending.HolomorphicNormalOrderDiscrepancy
import SGPT.Foundations.Analysis.Pending.HolomorphicHighNormalPerturbationOrder
import SGPT.Foundations.Analysis.Pending.WeightedAffineMonomialMultiplierPullback

set_option autoImplicit false

/-! # The original test supplies actual weighted Jacobian line orders -/

open Set Filter Metric
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.WeightedNormalTestJacobianLineOrder

open FirstPass DivisorialChangeOfVariables WeightedAffineMonomialMultiplierPullback

noncomputable section

/-- The original nonzero test supplies its actual normal factor and weighted
charts before every later normal weight; all Jacobian line factors are produced. -/
theorem exists_charts_before_all_weighted_jacobian_line_orders {m : ℕ}
    {f : ComplexModel (m + 2) → ℂ}
    (hf : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ f z)
    (hne : ∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), f z ≠ 0) :
    ∃ (b : ℕ) (H : ComplexModel (m + 2) → ℂ),
      (∀ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), DifferentiableAt ℂ H z) ∧
      f =ᶠ[𝓝 0] (fun z => z (Fin.last (m + 1)) ^ b * H z) ∧
      (∃ᶠ z in 𝓝 (0 : ComplexModel (m + 2)), z (Fin.last (m + 1)) = 0 ∧ H z ≠ 0) ∧
      ∃ (k : ℕ) (p : Fin (m + 2)) (c : ComplexModel (m + 2)),
        p ≠ Fin.last (m + 1) ∧ c (Fin.last (m + 1)) = 1 ∧ c p = 1 ∧
        ∀ L : ℕ, k < L →
          let a : Fin (m + 2) → ℕ := fun i => if i = Fin.last (m + 1) then L else 1
          ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
            ∀ᶠ t in 𝓝 (0 : ℂ),
              f (affineMonomial a c p (t • EuclideanSpace.single p (1 : ℂ))) *
                complexJacobian (affineMonomial a c p)
                  (t • EuclideanSpace.single p (1 : ℂ)) =
                    t ^ (L * b + k + L + m) * u t := by
  classical
  let j : Fin (m + 2) := Fin.last (m + 1)
  let e : ComplexModel (m + 2) := EuclideanSpace.single j (1 : ℂ)
  obtain ⟨b, H, hH, hfact, hfreq⟩ :=
    HolomorphicNormalOrderDiscrepancy.exists_finite_normal_order_of_nonzero_germ hf hne
  refine ⟨b, H, hH, hfact, hfreq, ?_⟩
  obtain ⟨k, v, hv, hvj, hunitall⟩ :=
    HolomorphicHighNormalPerturbationOrder.exists_tangential_order_before_all_high_normal_weights
      hH hfreq
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 2), v p ≠ 0 := by
    by_contra hn
    apply hv
    ext i
    exact not_ne_iff.mp (not_exists.mp hn i)
  have hpj : p ≠ j := by
    intro he
    exact hp (he ▸ hvj)
  let β : ℂ := v p
  have hβ : β ≠ 0 := hp
  let d : ComplexModel (m + 2) := β⁻¹ • v
  have hdj : d j = 0 := by simp [d, hvj, j]
  have hdp : d p = 1 := by simp [d, β, hp]
  let c : ComplexModel (m + 2) := d + e
  have hcj : c j = 1 := by simp [c, e, hdj]
  have hcp : c p = 1 := by simp [c, e, hdp, hpj]
  refine ⟨k, p, c, hpj, hcj, hcp, ?_⟩
  intro L hL
  let a : Fin (m + 2) → ℕ := fun i => if i = j then L else 1
  let ep : ComplexModel (m + 2) := EuclideanSpace.single p (1 : ℂ)
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le k) hL
  obtain ⟨h, hh, hh0, heqH⟩ := hunitall (β ^ L • e) L hL
  let s : ℂ → ℂ := fun t => β⁻¹ * t
  have hsc : Continuous s := continuous_const.mul continuous_id
  have hs : Tendsto s (𝓝 0) (𝓝 0) := by
    simpa only [s, mul_zero] using hsc.continuousAt.tendsto (x := (0 : ℂ))
  have hscale (t : ℂ) : s t • v + s t ^ L • (β ^ L • e) = t • d + t ^ L • e := by
    dsimp only [s, d]
    rw [smul_smul, smul_smul, mul_pow]
    have hpowers : β⁻¹ ^ L * β ^ L = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hβ, one_pow]
    have hcoeff : (β⁻¹ ^ L * t ^ L) * β ^ L = t ^ L := by
      calc
        _ = t ^ L * (β⁻¹ ^ L * β ^ L) := by ring
        _ = _ := by rw [hpowers, mul_one]
    rw [hcoeff, mul_comm β⁻¹ t]
  let u : ℂ → ℂ := fun t => β⁻¹ ^ k * h (s t)
  have hha : AnalyticAt ℂ h (s 0) := by simpa [s] using hh
  have hsa : AnalyticAt ℂ s 0 := analyticAt_const.mul analyticAt_id
  have hua : AnalyticAt ℂ u 0 := analyticAt_const.mul
    (AnalyticAt.comp (g := h) (f := s) hha hsa)
  have hu0 : u 0 ≠ 0 := by
    simpa [u, s] using mul_ne_zero (pow_ne_zero k (inv_ne_zero hβ)) hh0
  have hlineH : ∀ᶠ t in 𝓝 (0 : ℂ),
      H (t • d + t ^ L • e) = t ^ k * u t := by
    filter_upwards [hs.eventually heqH] with t ht
    rw [hscale] at ht
    rw [ht]
    dsimp only [u, s]
    rw [mul_pow]
    ring
  have hcurve (t : ℂ) : affineMonomial a c p (t • ep) = t • d + t ^ L • e := by
    ext i
    by_cases hip : i = p
    · subst i
      simp [affineMonomial, e, ep, hdp, hpj]
    · by_cases hij : i = j
      · subst i
        simp [affineMonomial, a, e, ep, c, hdj, Ne.symm hpj]
      · simp [affineMonomial, a, e, ep, c, hip, hij]
  have himagec : Continuous (fun t : ℂ => t • d + t ^ L • e) :=
    (continuous_id.smul continuous_const).add
      ((continuous_id.pow L).smul continuous_const)
  have himage : Tendsto (fun t : ℂ => t • d + t ^ L • e) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul, zero_pow (Nat.ne_of_gt hLpos), add_zero] using
      himagec.continuousAt.tendsto (x := (0 : ℂ))
  have hlineF : ∀ᶠ t in 𝓝 (0 : ℂ),
      f (affineMonomial a c p (t • ep)) = t ^ (L * b + k) * u t := by
    filter_upwards [himage.eventually hfact, hlineH] with t htf hth
    rw [hcurve, htf]
    have hcoord : (t • d + t ^ L • e) j = t ^ L := by simp [e, hdj]
    rw [hcoord, hth, ← pow_mul, ← mul_assoc, ← pow_add]
  have hjmem : j ∈ (Finset.univ : Finset (Fin (m + 2))).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpj, Finset.mem_univ j⟩
  have hother : ∑ i ∈ ((Finset.univ : Finset (Fin (m + 2))).erase p).erase j, a i = m := by
    calc
      _ = ∑ i ∈ ((Finset.univ : Finset (Fin (m + 2))).erase p).erase j, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact if_neg (Finset.mem_erase.mp hi).1
      _ = m := by
        simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hjmem,
          Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
        omega
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin (m + 2))).erase p, a i = L + m := by
    rw [← Finset.sum_erase_add _ _ hjmem, hother]
    simp only [a, if_true]
    omega
  have hJac (t : ℂ) : complexJacobian (affineMonomial a c p) (t • ep) = t ^ (L + m) := by
    rw [(geometry_affineMonomial a c p).2.1 (t • ep), hsum]
    congr 1
    simp [ep]
  refine ⟨u, hua, hu0, ?_⟩
  filter_upwards [hlineF] with t ht
  change f (affineMonomial a c p (t • ep)) *
    complexJacobian (affineMonomial a c p) (t • ep) = _
  rw [ht, hJac]
  calc
    _ = (t ^ (L * b + k) * t ^ (L + m)) * u t := by ring
    _ = _ := by rw [← pow_add]; simp only [Nat.add_assoc]

end
end SGPT.Foundations.Analysis.Pending.WeightedNormalTestJacobianLineOrder
