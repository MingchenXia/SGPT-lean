import SGPT.Foundations.Analysis.Pending.SingularCanonicalOrderedMixedMassDistance
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassComparison
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteMaximumChains

set_option autoImplicit false

/-! # Actual finite maximum chains in the singularity pseudometric

SGPT PDF0229 Step 1 of Proposition 6.2.3. Genuine ordered canonical
distance identities give the two maximum defects exactly as the actual
mixed mass join gap. Its proved source bound and native triangle then
produce the exact weighted finite sum. The existing pure finite-tail
maximum is reused. No model, E1, or positive original mass is assumed;
infinite tail envelopes and the full sandwich remain separate.
-/

open Set
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteMaximumChains

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus RelativeEnergy
  ActualMixedMassJoinGap SingularMinimalCanonicalRay SingularCanonicalSingularityDistance
  SingularCanonicalOrderedMixedMassDistance SingularCanonicalSingularityMassComparison
  SingularModelDarvasFiniteMaximumChains ThetaPshL1Topology

noncomputable section

private theorem weighted_chain_bound {X : Type*} [PseudoMetricSpace X]
    (C : ℝ) (hC : 0 ≤ C) (u : ℕ → X) (W : ℕ → ℕ → X)
    (hzero : ∀ i, W i 0 = u i)
    (hstep : ∀ i k, dist (u i) (W i (k + 1)) ≤ C * dist (u i) (W (i + 1) k))
    (i k : ℕ) :
    dist (u i) (W i k) ≤ ∑ r ∈ Finset.range k,
      C ^ (r + 1) * dist (u (i + r)) (u (i + r + 1)) := by
  induction k generalizing i with
  | zero => simp only [hzero, dist_self, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ k ih =>
    have hsum := ih (i + 1)
    have htotal : dist (u i) (W (i + 1) k) ≤ dist (u i) (u (i + 1)) +
        ∑ r ∈ Finset.range k, C ^ (r + 1) *
          dist (u (i + 1 + r)) (u (i + 1 + r + 1)) :=
      (dist_triangle (u i) (u (i + 1)) (W (i + 1) k)).trans (add_le_add le_rfl hsum)
    calc
      dist (u i) (W i (k + 1)) ≤ C * dist (u i) (W (i + 1) k) := hstep i k
      _ ≤ C * (dist (u i) (u (i + 1)) + ∑ r ∈ Finset.range k,
          C ^ (r + 1) * dist (u (i + 1 + r)) (u (i + 1 + r + 1))) :=
        mul_le_mul_of_nonneg_left htotal hC
      _ = _ := by
        rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
        simp only [Nat.add_zero, zero_add, pow_one]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        rw [show i + 1 + r = i + (r + 1) by omega]
        rw [pow_succ]
        ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The actual two ordered maximum defects equal the genuine mass join gap,
so its source bound gives the native maximum distance sum estimate. -/
theorem dist_max_sum_le_mul (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    let Z : ThetaPshL1 θ.val :=
      ⟨fun x => max (u.val x) (v.val x), IsThetaPshPotential.max u.property v.property⟩
    dist u Z + dist v Z ≤
      (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * dist u v := by
  let := singularityPseudoMetricSpace omega θ hbig
  let Z : ThetaPshL1 θ.val :=
    ⟨fun x => max (u.val x) (v.val x), IsThetaPshPotential.max u.property v.property⟩
  let hp := (isModelPotential_thetaPshSupremum omega θ hbig).plurisubharmonic
  let mass : ThetaPshL1 θ.val → Fin (n + 1) → ℝ := fun a j =>
    (endpointMixedMass θ (thetaPshSupremum θ.val) a.val hp a.property j).toReal
  have hU : dist u Z = (∑ j : Fin (n + 1), (mass Z j - mass u j)) / (n + 1 : ℝ) := by
    rw [dist_eq_singularityDistance_toReal omega θ hbig]
    simpa only [EReal.toReal_coe] using congrArg EReal.toReal
      (singularityDistance_eq_mixedMass_sub_of_le omega θ hbig u.property Z.property
        (fun x => le_max_left _ _))
  have hV : dist v Z = (∑ j : Fin (n + 1), (mass Z j - mass v j)) / (n + 1 : ℝ) := by
    rw [dist_eq_singularityDistance_toReal omega θ hbig]
    simpa only [EReal.toReal_coe] using congrArg EReal.toReal
      (singularityDistance_eq_mixedMass_sub_of_le omega θ hbig v.property Z.property
        (fun x => le_max_right _ _))
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig u.property v.property
  have hJ := (singularityDistance_le_mixedMassJoinGap_le omega θ hbig u.property v.property).2
  rw [hm, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hJ
  have hdist : dist u v = m := by
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hm, EReal.toReal_coe]
  rw [hdist]
  calc
    dist u Z + dist v Z = mixedMassJoinGap hp u.property v.property := by
      rw [hU, hV]
      unfold mixedMassJoinGap
      rw [← add_div, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      change (mass Z j - mass u j) + (mass Z j - mass v j) =
        2 * mass Z j - mass u j - mass v j
      ring
    _ ≤ _ := hJ

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Induction produces actual genuine PSH membership of the reused pure finite maximum. -/
theorem isThetaPshPotential_finiteTailMaximum {θ : ClosedRealOneOneForm n M}
    {u : ℕ → M → EReal} (hu : ∀ j, IsThetaPshPotential θ.val (u j)) (i k : ℕ) :
    IsThetaPshPotential θ.val (finiteTailMaximum u i k) := by
  induction k generalizing i with
  | zero => exact hu i
  | succ k ih => exact IsThetaPshPotential.max (hu i) (ih (i + 1))

/-- Native triangle and the actual maximum bound produce the exact source
finite weighted sum, with a genuine native maximum at every length. -/
theorem dist_finiteTailMaximum_le_weighted_sum (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u : ℕ → ThetaPshL1 θ.val) (i k : ℕ) :
    letI := singularityPseudoMetricSpace omega θ hbig
    let W : ThetaPshL1 θ.val :=
      ⟨finiteTailMaximum (fun j => (u j).val) i k,
        isThetaPshPotential_finiteTailMaximum (fun j => (u j).property) i k⟩
    dist (u i) W ≤ ∑ r ∈ Finset.range k,
      (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) ^ (r + 1) *
        dist (u (i + r)) (u (i + r + 1)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let W : ℕ → ℕ → ThetaPshL1 θ.val := fun i k =>
    ⟨finiteTailMaximum (fun j => (u j).val) i k,
      isThetaPshPotential_finiteTailMaximum (fun j => (u j).property) i k⟩
  change dist (u i) (W i k) ≤ ∑ r ∈ Finset.range k,
    C ^ (r + 1) * dist (u (i + r)) (u (i + r + 1))
  have hzero (i : ℕ) : W i 0 = u i := rfl
  apply weighted_chain_bound C hC u W hzero ?_ i k
  intro i k
  have hmax : dist (u i) (W i (k + 1)) + dist (W (i + 1) k) (W i (k + 1)) ≤
      C * dist (u i) (W (i + 1) k) :=
    dist_max_sum_le_mul omega θ hbig (u i) (W (i + 1) k)
  exact (le_add_of_nonneg_right dist_nonneg).trans hmax

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteMaximumChains
