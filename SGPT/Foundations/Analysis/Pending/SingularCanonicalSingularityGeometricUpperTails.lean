import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteMaximumChains
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailSupremumMajorants
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false

/-! # Genuine geometric upper tails without an incoming native limit

SGPT PDF0229 Step 1 upper-tail argument, independently strengthened by
removing the incoming target and native convergence premise. Actual bounded
regularization and actual finite-maximum increasing convergence internally
produce the genuine tails and their full distance bound. No Cauchy limit,
model, or mass conclusion is presumed.
-/

open Set Filter
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricUpperTails

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  IncreasingMixedDirectedNets SingularCanonicalSingularityDistance
  SingularCanonicalSingularityFiniteMaximumChains SingularModelDarvasFiniteMaximumChains
  SingularModelDarvasTailSupremumMajorants ThetaPshL1Topology

noncomputable section

private theorem geometric_sum_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, s ^ j) ≤ 1 / (1 - s) := by
  apply (le_div_iff₀ (sub_pos.mpr hs1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hs0 k]

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual uniform upper bounds and geometric native steps produce genuine
decreasing upper-tail envelopes and their exact native distance bound.
No target potential or convergence premise is supplied. -/
theorem exists_decreasing_majorants_of_geometric_steps
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val)
    {B A r : ℝ} (hB : ∀ i x, (ui i).val x ≤ (B : EReal))
    (hA : 0 ≤ A) (hr0 : 0 < r) (_hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) →
      ∃ ψ : ℕ → ThetaPshL1 θ.val,
        (∀ i, (ψ i).val = uscRegularization (⨆ j, (ui (i + j)).val)) ∧
        (∀ x, Antitone fun i => (ψ i).val x) ∧ (∀ i, (ui i).val ≤ (ψ i).val) ∧
        (∀ i, dist (ui i) (ψ i) ≤
          (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * A * r ^ i /
            (1 - (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hstep
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hψ (i : ℕ) : IsThetaPshPotential θ.val
      (uscRegularization (⨆ j, (ui (i + j)).val)) :=
    isThetaPshPotential_regularized_of_uniformlyBounded
      (fun j => (ui (i + j)).property) (fun j x => hB (i + j) x)
  let ψ : ℕ → ThetaPshL1 θ.val := fun i =>
    ⟨uscRegularization (⨆ j, (ui (i + j)).val), hψ i⟩
  have hanti : ∀ x, Antitone fun i => (ψ i).val x := by
    intro x
    apply antitone_nat_of_succ_le
    intro i
    apply uscRegularization_mono (g := ⨆ j, (ui (i + j)).val) ?_ x
    apply iSup_le
    intro j
    exact le_iSup_of_le (j + 1) (by rw [show i + 1 + j = i + (j + 1) by omega])
  have hle (i : ℕ) : (ui i).val ≤ (ψ i).val :=
    (show (ui i).val ≤ ⨆ j, (ui (i + j)).val from
      by simpa only [Nat.add_zero] using le_iSup (fun j => (ui (i + j)).val) 0).trans
      (le_uscRegularization _)
  have hdist (i : ℕ) : dist (ui i) (ψ i) ≤ C * A * r ^ i / (1 - C * r) := by
    let Mi : ℕ → ThetaPshL1 θ.val := fun k =>
      ⟨finiteTailMaximum (fun j => (ui j).val) i k,
        isThetaPshPotential_finiteTailMaximum (fun j => (ui j).property) i k⟩
    have hMC (k : ℕ) (x : M) : (Mi k).val x ≤ (B : EReal) := by
      have htail : (⨆ j, (ui (i + j)).val) ≤ fun _ => (B : EReal) :=
        iSup_le fun j x => hB (i + j) x
      have hmax : (Mi k).val ≤ ⨆ j, (ui (i + j)).val := by
        exact (le_iSup (finiteTailMaximum (fun j => (ui j).val) i) k).trans_eq
          (iSup_finiteTailMaximum_eq_iSup_tail (fun j => (ui j).val) i)
      exact (hmax x).trans (htail x)
    have hMi : Tendsto Mi atTop (𝓝 (ψ i)) := by
      have hm := SingularCanonicalSingularityIncreasing.tendsto_native_of_monotone_uniformlyBounded
        omega θ hbig Mi (fun k l hkl => finiteTailMaximum_monotone i hkl) hMC
      simpa only [Mi, iSup_finiteTailMaximum_eq_iSup_tail] using hm
    have hfinite (k : ℕ) : dist (ui i) (Mi k) ≤ C * A * r ^ i / (1 - C * r) := by
      have hw := dist_finiteTailMaximum_le_weighted_sum omega θ hbig ui i k
      calc
        _ ≤ ∑ a ∈ Finset.range k, C ^ (a + 1) * dist (ui (i + a)) (ui (i + a + 1)) := hw
        _ ≤ ∑ a ∈ Finset.range k, C ^ (a + 1) * (A * r ^ (i + a)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hstep (i + a)) (pow_nonneg hC0 (a + 1))
        _ = (C * A * r ^ i) * ∑ a ∈ Finset.range k, (C * r) ^ a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [pow_succ, pow_add r i a, mul_pow C r a]
          ring
        _ ≤ (C * A * r ^ i) * (1 / (1 - C * r)) :=
          mul_le_mul_of_nonneg_left (geometric_sum_le (mul_nonneg hC0 hr0.le) hrC k)
            (mul_nonneg (mul_nonneg hC0 hA) (pow_nonneg hr0.le i))
        _ = _ := by ring
    exact le_of_tendsto (tendsto_const_nhds.dist hMi) (Eventually.of_forall hfinite)
  exact ⟨ψ, fun _ => rfl, hanti, hle, hdist⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricUpperTails
