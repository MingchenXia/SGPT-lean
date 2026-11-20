import SGPT.PSH.HermitianBalayageMixedTrace
import SGPT.PSH.HermitianBalayageTuple

/-!
# The nearby-trace recurrence for genuine mixed measures

Every measure is the canonical Bedford--Taylor measure of the indicated
tuple: old-potential slots, new-potential slots, then normalized Euclidean
slots. Replacing one new-potential slot by the old potential or by the
Euclidean slot gives the two terms of the nearby-trace recurrence.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology Distributions

variable {N : ℕ} {Ω : Opens (ComplexModel N)}

/-- Every slot of the displayed mixed tuple is an actual bounded PSH function. -/
theorem locallyBoundedPsh_mixedTuple {L : ℕ} {u v : ComplexModel N → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) (j m : ℕ) :
    ∀ i : Fin L, IsLocallyBoundedPshOn Ω
      ((mixedTuple u v HermitianProducts.flatQuadratic j m : Fin L → ComplexModel N → ℝ) i) := by
  intro i
  simp only [mixedTuple]
  split_ifs
  · exact hu
  · exact hv
  · exact locallyBoundedPsh_flatQuadratic Ω

/-- The actual mixed measure with `j` old slots and `m` new slots; all
remaining slots are the normalized Euclidean quadratic. -/
def nearbyMixedMeasure (Ω : Opens (ComplexModel N)) (u v : ComplexModel N → ℝ)
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) (j m : ℕ) :
    Measure (ComplexModel N) :=
  canonicalMixedBedfordTaylorMeasure Ω
    (mixedTuple u v HermitianProducts.flatQuadratic j m)
    (locallyBoundedPsh_mixedTuple hu hv j m)

theorem nearbyMixedMeasure_finiteOnCompacts {u v : ComplexModel N → ℝ}
    (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v) (j m : ℕ)
    {K : Set (ComplexModel N)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    nearbyMixedMeasure Ω u v hu hv j m K < ⊤ :=
  canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
    (locallyBoundedPsh_mixedTuple hu hv j m) hK hKΩ

private theorem canonicalMeasure_eq_of_tuple_eq
    {f g : Fin N → ComplexModel N → ℝ}
    (hf : ∀ i, IsLocallyBoundedPshOn Ω (f i))
    (hg : ∀ i, IsLocallyBoundedPshOn Ω (g i)) (h : f = g) :
    canonicalMixedBedfordTaylorMeasure Ω f hf = canonicalMixedBedfordTaylorMeasure Ω g hg := by
  subst h
  rfl

/-- The two-branch nearby-trace recurrence, with every measure produced
from the actual potentials and a constant independent of their values,
the center, radius and coordinate domain. -/
theorem exists_nearbyMixedMeasure_ball_recurrence {n : ℕ} {t₀ t₁ : ℝ}
    (ht₀ : 0 < t₀) (htt : t₀ < t₁) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → closedBall a (t₁ * r) ⊆ Ω →
        ∀ (u v : ComplexModel (n + 1) → ℝ), Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a (t₁ * r), |v x - u x| ≤ κ * r ^ 2) →
            ∀ j m : ℕ, j + (m + 1) ≤ n + 1 →
              (nearbyMixedMeasure Ω u v hu hv j (m + 1) (closedBall a (t₀ * r))).toReal ≤
                (nearbyMixedMeasure Ω u v hu hv (j + 1) m (closedBall a (t₁ * r))).toReal +
                  C * κ * (nearbyMixedMeasure Ω u v hu hv j m
                    (closedBall a (t₁ * r))).toReal := by
  obtain ⟨C, hC0, hC⟩ := exists_one_slot_canonicalMixed_ball_mass_le (n := n) ht₀ htt
  refine ⟨C, hC0, ?_⟩
  intro Ω a r κ hr hκ hball u v hum hvm hu hv hclose j m hjm
  let f : Fin n → ComplexModel (n + 1) → ℝ :=
    mixedTuple u v HermitianProducts.flatQuadratic j m
  have hf : ∀ i, IsLocallyBoundedPshOn Ω (f i) :=
    locallyBoundedPsh_mixedTuple hu hv j m
  let p : Fin (n + 1) := ⟨j, by omega⟩
  have hvTuple : p.insertNth v f =
      (mixedTuple u v HermitianProducts.flatQuadratic j (m + 1) :
        Fin (n + 1) → ComplexModel (n + 1) → ℝ) :=
    mixedTuple_insert_new _ _ _ j m hjm
  have huTuple : p.insertNth u f =
      (mixedTuple u v HermitianProducts.flatQuadratic (j + 1) m :
        Fin (n + 1) → ComplexModel (n + 1) → ℝ) :=
    mixedTuple_insert_old _ _ _ j m hjm
  have hqTuple : (Fin.last n).insertNth HermitianProducts.flatQuadratic f =
      (mixedTuple u v HermitianProducts.flatQuadratic j m :
        Fin (n + 1) → ComplexModel (n + 1) → ℝ) :=
    mixedTuple_insert_flat_last _ _ _ j m (by omega)
  have hμv : canonicalMixedBedfordTaylorMeasure Ω (p.insertNth v f)
        (locallyBoundedPsh_insertNth hf p hv) = nearbyMixedMeasure Ω u v hu hv j (m + 1) := by
    exact canonicalMeasure_eq_of_tuple_eq (locallyBoundedPsh_insertNth hf p hv)
      (locallyBoundedPsh_mixedTuple hu hv j (m + 1)) hvTuple
  have hμu : canonicalMixedBedfordTaylorMeasure Ω (p.insertNth u f)
        (locallyBoundedPsh_insertNth hf p hu) = nearbyMixedMeasure Ω u v hu hv (j + 1) m := by
    exact canonicalMeasure_eq_of_tuple_eq (locallyBoundedPsh_insertNth hf p hu)
      (locallyBoundedPsh_mixedTuple hu hv (j + 1) m) huTuple
  have hμq : (remainingMixedCurrent_positive_closed hf).1.traceMeasure =
      nearbyMixedMeasure Ω u v hu hv j m := by
    rw [← canonicalMixedMeasure_insertNth_flat_eq_trace hf (Fin.last n)]
    exact canonicalMeasure_eq_of_tuple_eq
      (locallyBoundedPsh_insertNth hf (Fin.last n) (locallyBoundedPsh_flatQuadratic Ω))
      (locallyBoundedPsh_mixedTuple hu hv j m) hqTuple
  have h := hC Ω a r κ hr hκ hball f hf p u v hum hvm hu hv hclose
  rw [hμv, hμu, hμq] at h
  exact h

/-- Fixed dimension-only radius ratios from one half to three quarters. -/
def traceRadiusRatio (d i : ℕ) : ℝ := 1 / 2 + (i : ℝ) / (4 * d)

theorem traceRadiusRatio_pos {d : ℕ} (hd : 0 < d) (i : ℕ) :
    0 < traceRadiusRatio d i := by
  unfold traceRadiusRatio
  positivity

theorem traceRadiusRatio_strict {d : ℕ} (hd : 0 < d) (i : ℕ) :
    traceRadiusRatio d i < traceRadiusRatio d (i + 1) := by
  have hden : 0 < (4 * d : ℝ) := by positivity
  have hq : (i : ℝ) / (4 * d) < ((i + 1 : ℕ) : ℝ) / (4 * d) :=
    div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hden
  unfold traceRadiusRatio
  linarith

theorem traceRadiusRatio_le {d i : ℕ} (hd : 0 < d) (hi : i ≤ d) :
    traceRadiusRatio d i ≤ 3 / 4 := by
  have hden : 0 < (4 * d : ℝ) := by positivity
  have hq : (i : ℝ) / (4 * d) ≤ (d : ℝ) / (4 * d) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hi) hden.le
  have he : (d : ℝ) / (4 * d) = 1 / 4 := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    field_simp
  unfold traceRadiusRatio
  rw [he] at hq
  linarith

/-- The full nearby bounded-potential trace estimate. The inner radius is
one half and every right-hand mass is taken on the compact three-quarter
ball, so no finiteness at the boundary of the coordinate domain is assumed.
All lower trace degrees retain their exact powers of the potential gap. -/
theorem exists_nearby_bounded_mixed_trace_estimate (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Opens (ComplexModel (n + 1))) (a : ComplexModel (n + 1)) (r κ : ℝ),
        0 < r → 0 ≤ κ → closedBall a ((3 / 4 : ℝ) * r) ⊆ Ω →
        ∀ (u v : ComplexModel (n + 1) → ℝ), Measurable u → Measurable v →
          ∀ (hu : IsLocallyBoundedPshOn Ω u) (hv : IsLocallyBoundedPshOn Ω v),
            (∀ x ∈ closedBall a ((3 / 4 : ℝ) * r), |v x - u x| ≤ κ * r ^ 2) →
            ∀ k : ℕ, k ≤ n + 1 →
              (∑ j ∈ Finset.range (k + 1),
                (nearbyMixedMeasure Ω u v hu hv j (k - j) (closedBall a (r / 2))).toReal) ≤
                C * ∑ l ∈ Finset.range (k + 1), κ ^ (k - l) *
                  (nearbyMixedMeasure Ω u v hu hv l 0
                    (closedBall a ((3 / 4 : ℝ) * r))).toReal := by
  classical
  let d := n + 1
  have hd : 0 < d := Nat.succ_pos n
  let hdata := fun i : Fin d => exists_nearbyMixedMeasure_ball_recurrence
    (n := n) (traceRadiusRatio_pos hd i) (traceRadiusRatio_strict hd i)
  choose c hc0 hc using hdata
  let A : ℝ := ∑ i : Fin d, c i
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hc0 i
  have hcA : ∀ i, c i ≤ A := fun i => Finset.single_le_sum
    (fun j _ => hc0 j) (Finset.mem_univ i)
  refine ⟨(d + 1 : ℝ) * (1 + A) ^ d, mul_nonneg (by positivity) (pow_nonneg (by linarith) _), ?_⟩
  intro Ω a r κ hr hκ hball u v hum hvm hu hv hclose k hkd
  let μ := nearbyMixedMeasure Ω u v hu hv
  let K : ℕ → Set (ComplexModel d) := fun i => closedBall a (traceRadiusRatio d i * r)
  let O : Set (ComplexModel d) := closedBall a ((3 / 4 : ℝ) * r)
  have hKO : ∀ i, i ≤ d → K i ⊆ O := fun i hi =>
    closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (traceRadiusRatio_le hd hi) hr.le)
  have hμO : ∀ j m, μ j m O < ⊤ := fun j m =>
    nearbyMixedMeasure_finiteOnCompacts hu hv j m (isCompact_closedBall _ _) hball
  let J : ℕ → ℝ := fun j => if j ≤ d then (μ j 0 O).toReal else 0
  let I : ℕ → ℕ → ℕ → ℝ := fun i j m =>
    if i + m ≤ d ∧ j + m ≤ d then (μ j m (K i)).toReal else 0
  have hJ : ∀ j, 0 ≤ J j := by
    intro j
    dsimp only [J]
    split_ifs <;> positivity
  have hI : ∀ i j m, 0 ≤ I i j m := by
    intro i j m
    dsimp only [I]
    split_ifs <;> positivity
  have hbase : ∀ i j, I i j 0 ≤ J j := by
    intro i j
    by_cases hvalid : i + 0 ≤ d ∧ j + 0 ≤ d
    · have hi : i ≤ d := by omega
      have hj : j ≤ d := by omega
      simp only [I, J, if_pos hvalid, if_pos hj]
      exact ENNReal.toReal_mono (hμO j 0).ne (measure_mono (hKO i hi))
    · simp only [I, if_neg hvalid]
      exact hJ j
  have hstep : ∀ i j m, I i j (m + 1) ≤
      I (i + 1) (j + 1) m + (A * κ) * I (i + 1) j m := by
    intro i j m
    by_cases hvalid : i + (m + 1) ≤ d ∧ j + (m + 1) ≤ d
    · have hi : i < d := by omega
      have hi1 : i + 1 ≤ d := by omega
      have hjm : j + (m + 1) ≤ n + 1 := hvalid.2
      have hleft : i + 1 + m ≤ d ∧ j + 1 + m ≤ d := by omega
      have hright : i + 1 + m ≤ d ∧ j + m ≤ d := by omega
      have h := hc ⟨i, hi⟩ Ω a r κ hr hκ ((hKO (i + 1) hi1).trans hball)
        u v hum hvm hu hv (fun x hx => hclose x (hKO (i + 1) hi1 hx)) j m hjm
      have hconst : c ⟨i, hi⟩ * κ * (μ j m (K (i + 1))).toReal ≤
          A * κ * (μ j m (K (i + 1))).toReal :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hcA ⟨i, hi⟩) hκ)
          ENNReal.toReal_nonneg
      simp only [I, if_pos hvalid, if_pos hleft, if_pos hright]
      exact h.trans (add_le_add le_rfl hconst)
    · simp only [I, if_neg hvalid]
      exact add_nonneg (hI _ _ _) (mul_nonneg (mul_nonneg hA hκ) (hI _ _ _))
  have hsum := trace_recursion_sum_le I J hA hκ hJ hbase hstep k 0
  have hleft : (∑ j ∈ Finset.range (k + 1), I 0 j (k - j)) =
      ∑ j ∈ Finset.range (k + 1), (μ j (k - j) (closedBall a (r / 2))).toReal := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hvalid : 0 + (k - j) ≤ d ∧ j + (k - j) ≤ d := by omega
    simp only [I, if_pos hvalid, K, traceRadiusRatio, Nat.cast_zero, zero_div, add_zero]
    congr 3
    ring
  have hright : weightedTraceSum κ J k =
      ∑ l ∈ Finset.range (k + 1), κ ^ (k - l) * (μ l 0 O).toReal := by
    unfold weightedTraceSum
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlk : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    simp only [J, if_pos (show l ≤ d by omega)]
  rw [hleft, hright] at hsum
  have hdegree : (k + 1 : ℝ) * (1 + A) ^ k ≤ (d + 1 : ℝ) * (1 + A) ^ d :=
    mul_le_mul (by exact_mod_cast Nat.succ_le_succ hkd)
      (pow_le_pow_right₀ (by linarith) hkd) (pow_nonneg (by linarith) _) (by positivity)
  exact hsum.trans (mul_le_mul_of_nonneg_right hdegree
    (Finset.sum_nonneg fun l _ => mul_nonneg (pow_nonneg hκ _) ENNReal.toReal_nonneg))

end SGPT.PSH.HermitianBalayage
