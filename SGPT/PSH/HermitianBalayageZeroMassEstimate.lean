import SGPT.PSH.HermitianBalayageMixedRecurrence
import SGPT.PSH.HermitianBalayageEnvelope

/-!
# Mass estimate from an actual nearby homogeneous replacement

The full nearby-trace estimate is applied twice: first with the replacement
as old potential on a smaller ball, then in the original order to bound
its lower traces. The replacement's top mass is zero, so every surviving
term contains a factor of the potential gap. Every measure below is the
canonical mixed Bedford--Taylor measure of the displayed actual potentials.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open scoped Topology Distributions

private theorem canonicalMeasure_eq_of_tuple_eq {N : ℕ} {Ω : Opens (ComplexModel N)}
    {f g : Fin N → ComplexModel N → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i))
    (hg : ∀ i, IsLocallyBoundedPshOn Ω (g i)) (h : f = g) :
    canonicalMixedBedfordTaylorMeasure Ω f hf = canonicalMixedBedfordTaylorMeasure Ω g hg := by
  subst h
  rfl

/-- The same pure trace is obtained by calling a potential old or new. -/
theorem nearbyMixedMeasure_old_eq_new {N : ℕ} {Ω : Opens (ComplexModel N)}
    {u v : ComplexModel N → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) (j : ℕ) :
    nearbyMixedMeasure Ω u v hu hv j 0 = nearbyMixedMeasure Ω v u hv hu 0 j := by
  apply canonicalMeasure_eq_of_tuple_eq
  funext i
  simp only [mixedTuple, Nat.add_zero, Nat.zero_add, Nat.not_lt_zero, ↓reduceIte]
  split_ifs <;> rfl

/-- The full old-potential trace is the actual canonical scalar
Bedford--Taylor measure, including in dimension zero. -/
theorem nearbyMixedMeasure_old_top_eq {N : ℕ} {Ω : Opens (ComplexModel N)}
    {u v : ComplexModel N → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hv : IsLocallyBoundedPshOn Ω v) :
    nearbyMixedMeasure Ω u v hu hv N 0 =
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu := by
  calc
    nearbyMixedMeasure Ω u v hu hv N 0 =
        canonicalMixedBedfordTaylorMeasure Ω (fun _ => u) (fun _ => hu) := by
      apply canonicalMeasure_eq_of_tuple_eq
      funext i
      simp [mixedTuple, i.isLt]
    _ = _ := canonicalMixedBedfordTaylorMeasure_diagonal Ω u hu

/-- An actual zero-top-mass replacement within gap `κ r²` gives an
`O(κ)` bound by only the old-potential lower traces. The coefficient is
chosen before the coordinate domain, potentials, center and radius. -/
theorem exists_nearby_zero_mass_estimate (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → κ ≤ 1 → closedBall a ((3 / 4 : ℝ) * r) ⊆ Ω →
        ∀ (u v : ComplexModel (n + 1) → ℝ), Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a ((3 / 4 : ℝ) * r), |v x - u x| ≤ κ * r ^ 2) →
            nearbyMixedMeasure Ω u v hu hv 0 (n + 1) (ball a r) = 0 →
              (nearbyMixedMeasure Ω u v hu hv (n + 1) 0 (closedBall a (r / 4))).toReal ≤
                C * κ * ∑ l ∈ Finset.range (n + 1),
                  (nearbyMixedMeasure Ω u v hu hv l 0
                    (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_nearby_bounded_mixed_trace_estimate n
  let d := n + 1
  refine ⟨c ^ 2 * (d : ℝ) * 4 ^ d, by positivity, ?_⟩
  intro Ω a r κ hr hκ hκ1 hball u v hum hvm hu hv hclose hzero
  let μ := nearbyMixedMeasure Ω u v hu hv
  let σ := nearbyMixedMeasure Ω v u hv hu
  let O := closedBall a ((3 / 4 : ℝ) * r)
  let H := closedBall a (r / 2)
  let Q := closedBall a ((3 / 4 : ℝ) * (r / 2))
  let J : ℝ := ∑ l ∈ Finset.range d, (μ l 0 O).toReal
  have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hHO : H ⊆ O := closedBall_subset_closedBall (by linarith)
  have hQH : Q ⊆ H := closedBall_subset_closedBall (by linarith)
  have hQO : Q ⊆ O := hQH.trans hHO
  have hμO (j m : ℕ) : μ j m O ≠ ⊤ :=
    (nearbyMixedMeasure_finiteOnCompacts hu hv j m (isCompact_closedBall _ _) hball).ne
  have hμH (j m : ℕ) : μ j m H ≠ ⊤ :=
    ne_top_of_le_ne_top (hμO j m) (measure_mono hHO)
  have hpure (j : ℕ) : σ j 0 = μ 0 j := nearbyMixedMeasure_old_eq_new hv hu j
  have hlow (l : ℕ) (hl : l < d) : (σ l 0 Q).toReal ≤ c * J := by
    rw [hpure]
    have hsingle : (μ 0 l H).toReal ≤
        ∑ j ∈ Finset.range (l + 1), (μ j (l - j) H).toReal := by
      have h := Finset.single_le_sum
        (s := Finset.range (l + 1)) (f := fun j => (μ j (l - j) H).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.mpr (Nat.succ_pos l))
      simpa using h
    have hnear := hc Ω a r κ hr hκ hball u v hum hvm hu hv hclose l (by omega)
    have hweights : (∑ p ∈ Finset.range (l + 1), κ ^ (l - p) * (μ p 0 O).toReal) ≤ J := by
      calc
        (∑ p ∈ Finset.range (l + 1), κ ^ (l - p) * (μ p 0 O).toReal) ≤
            ∑ p ∈ Finset.range (l + 1), (μ p 0 O).toReal := by
          apply Finset.sum_le_sum
          intro p _
          exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hκ hκ1) ENNReal.toReal_nonneg).trans_eq
            (one_mul _)
        _ ≤ J := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (by omega)) (fun _ _ _ => ENNReal.toReal_nonneg)
    exact (ENNReal.toReal_mono (hμH 0 l) (measure_mono hQH)).trans
      (hsingle.trans (hnear.trans (mul_le_mul_of_nonneg_left hweights hc0)))
  have hsmall := hc Ω a (r / 2) (4 * κ) (by positivity) (by positivity)
    (hQO.trans hball) v u hvm hum hv hu (fun x hx => by
      rw [abs_sub_comm]
      have he : (4 * κ) * (r / 2) ^ 2 = κ * r ^ 2 := by ring
      rw [he]
      exact hclose x (hQO hx)) d le_rfl
  have hsingle : (μ d 0 (closedBall a (r / 4))).toReal ≤
      ∑ j ∈ Finset.range (d + 1), (σ j (d - j) (closedBall a ((r / 2) / 2))).toReal := by
    have h := Finset.single_le_sum
      (s := Finset.range (d + 1))
      (f := fun j => (σ j (d - j) (closedBall a ((r / 2) / 2))).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.mpr (Nat.succ_pos d))
    have he : μ d 0 = σ 0 d := nearbyMixedMeasure_old_eq_new hu hv d
    simp only [Nat.sub_zero, ← he, show (r / 2) / 2 = r / 4 by ring] at h
    simpa only [show (r / 2) / 2 = r / 4 by ring] using h
  have hσzero : σ d 0 Q = 0 := by
    rw [hpure]
    apply measure_mono_null ?_ hzero
    exact closedBall_subset_ball (by linarith)
  have hweight (l : ℕ) (hl : l < d) : (4 * κ) ^ (d - l) ≤ 4 ^ d * κ := by
    have he : d - l = (d - l - 1) + 1 := by omega
    have hκpow : κ ^ (d - l) ≤ κ := by
      rw [he, pow_succ]
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hκ hκ1) hκ).trans_eq (one_mul _)
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega))
      hκpow (pow_nonneg hκ _) (by positivity)
  have hsum : (∑ l ∈ Finset.range (d + 1), (4 * κ) ^ (d - l) * (σ l 0 Q).toReal) ≤
      (d : ℝ) * (4 ^ d * κ * (c * J)) := by
    rw [Finset.sum_range_succ, hσzero]
    simp only [ENNReal.toReal_zero, mul_zero, add_zero]
    calc
      (∑ l ∈ Finset.range d, (4 * κ) ^ (d - l) * (σ l 0 Q).toReal) ≤
          ∑ _l ∈ Finset.range d, 4 ^ d * κ * (c * J) := by
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul (hweight l (Finset.mem_range.mp hl))
          (hlow l (Finset.mem_range.mp hl)) ENNReal.toReal_nonneg (by positivity)
      _ = (d : ℝ) * (4 ^ d * κ * (c * J)) := by simp
  calc
    (μ d 0 (closedBall a (r / 4))).toReal ≤
        c * ∑ l ∈ Finset.range (d + 1), (4 * κ) ^ (d - l) * (σ l 0 Q).toReal :=
      hsingle.trans hsmall
    _ ≤ c * ((d : ℝ) * (4 ^ d * κ * (c * J))) := mul_le_mul_of_nonneg_left hsum hc0
    _ = (c ^ 2 * (d : ℝ) * 4 ^ d) * κ * J := by ring

/-- The scalar interface consumes the actual homogeneous replacement
measure supplied by ordinary balayage. Its zero mass is transported by
uniqueness of the genuine Bedford--Taylor limit. -/
theorem exists_nearby_homogeneous_mass_estimate (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → κ ≤ 1 → closedBall a ((3 / 4 : ℝ) * r) ⊆ Ω →
        ∀ (u v : ComplexModel (n + 1) → ℝ), Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a ((3 / 4 : ℝ) * r), |v x - u x| ≤ κ * r ^ 2) →
            ∀ τ : Measure (ComplexModel (n + 1)), IsBTLimit Ω (fun _ => v) τ →
              τ (ball a r) = 0 →
              (SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu
                (closedBall a (r / 4))).toReal ≤
                C * κ * ∑ l ∈ Finset.range (n + 1),
                  (nearbyMixedMeasure Ω u v hu hv l 0
                    (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_nearby_zero_mass_estimate n
  refine ⟨C, hC0, ?_⟩
  intro Ω a r κ hr hκ hκ1 hball u v hum hvm hu hv hclose τ hτ hτzero
  have heq := hτ.unique (isBTLimit_canonicalBedfordTaylorMeasure hv)
  have hzero : nearbyMixedMeasure Ω u v hu hv 0 (n + 1) (ball a r) = 0 := by
    rw [← nearbyMixedMeasure_old_eq_new hv hu, nearbyMixedMeasure_old_top_eq hv hu, ← heq]
    exact hτzero
  have h := hC Ω a r κ hr hκ hκ1 hball u v hum hvm hu hv hclose hzero
  rw [nearbyMixedMeasure_old_top_eq hu hv] at h
  exact h

end SGPT.PSH.HermitianBalayage
