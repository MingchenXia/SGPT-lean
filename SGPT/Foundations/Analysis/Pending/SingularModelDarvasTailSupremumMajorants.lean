import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteMaximumChains
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneLimits
import SGPT.Foundations.Analysis.Pending.SingularModelBoundedSupremumEnergyClosure
import Mathlib.Algebra.Order.Field.GeomSum

set_option autoImplicit false

/-!
# Actual decreasing tail-supremum majorants

Xia SGPT PDF0168, upper-majorant part of Lemma 4.3.5.
Actual finite maxima exhaust the raw tail supremum. Native Cauchy supremum
control and actual bounded-family closure produce its genuine E1 membership.
Actual weighted finite bounds pass through the actual increasing metric limit,
giving the dimension-weighted geometric distance estimate and actual everywhere
pointwise convergence of the decreasing tail majorants.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailSupremumMajorants

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace SingularModelDarvasFiniteMaximumChains

noncomputable section

private theorem finiteTailMaximum_le_iSup_tail {X : Type*} (u : ℕ → X → EReal) (i k : ℕ) :
    finiteTailMaximum u i k ≤ ⨆ j, u (i + j) := by
  induction k generalizing i with
  | zero => simpa only [finiteTailMaximum, Nat.add_zero] using le_iSup (fun j => u (i + j)) 0
  | succ k ih =>
    intro x
    apply max_le
    · simpa only [iSup_apply, Nat.add_zero] using le_iSup (fun j => u (i + j) x) 0
    · apply (ih (i + 1) x).trans
      simp only [iSup_apply]
      apply iSup_le
      intro j
      exact le_iSup_of_le (j + 1) (by simp only [Nat.add_assoc, Nat.add_comm 1 j]; exact le_rfl)

private theorem last_le_finiteTailMaximum {X : Type*} (u : ℕ → X → EReal) (i k : ℕ) :
    u (i + k) ≤ finiteTailMaximum u i k := by
  induction k generalizing i with
  | zero => exact le_rfl
  | succ k ih =>
    intro x
    have h := ih (i + 1) x
    rw [show i + 1 + k = i + (k + 1) by omega] at h
    exact h.trans (le_max_right _ _)

/-- The actual finite maxima exhaust the actual raw tail supremum, including poles. -/
theorem iSup_finiteTailMaximum_eq_iSup_tail {X : Type*} (u : ℕ → X → EReal) (i : ℕ) :
    (⨆ k, finiteTailMaximum u i k) = ⨆ j, u (i + j) := by
  apply le_antisymm
  · exact iSup_le (finiteTailMaximum_le_iSup_tail u i)
  · apply iSup_le
    intro j
    exact (last_le_finiteTailMaximum u i j).trans (le_iSup (finiteTailMaximum u i) j)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual Cauchy control produces every genuine finite-energy regularized tail supremum. -/
theorem relativeFiniteEnergyPreceq_uscRegularization_tail_of_cauchySeq (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    CauchySeq ui → ∀ i,
      RelativeFiniteEnergyPreceq θ φ (uscRegularization (⨆ j, (ui (i + j)).val)) hφ := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  intro hc i
  obtain ⟨R, _, hR⟩ := SingularModelDarvasIncreasingCauchyLimit.exists_pos_bound_relativeD1_of_cauchySeq
    omega ui hc
  obtain ⟨C, hC⟩ := SingularModelDarvasSupremumControl.exists_uniform_upper_bound_of_relativeD1_le
    omega (fun j => (ui j).property) hR
  exact SingularModelBoundedSupremumEnergyClosure.relativeFiniteEnergyPreceq_uscRegularization_iSup
    omega (fun j => (ui (i + j)).property) (fun j x => hC (i + j) x)

private theorem geometric_sum_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, s ^ j) ≤ 1 / (1 - s) := by
  apply (le_div_iff₀ (sub_pos.mpr hs1)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hs0 k]

/-- Actual decreasing E1 tail majorants and their native and everywhere pointwise limits. -/
theorem exists_decreasing_majorants_of_geometric_steps_of_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    {A r : ℝ} (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) → Tendsto ui atTop (𝓝 u) →
      ∃ ψ : ℕ → ModelFiniteEnergyPotential θ φ hφ,
        (∀ i, (ψ i).val = uscRegularization (⨆ j, (ui (i + j)).val)) ∧
        (∀ x, Antitone fun i => (ψ i).val x) ∧ (∀ i, (ui i).val ≤ (ψ i).val) ∧
        (∀ i, dist (ui i) (ψ i) ≤
          (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * A * r ^ i /
            (1 - (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r)) ∧
        Tendsto ψ atTop (𝓝 u) ∧
        (∀ x, Tendsto (fun i => (ψ i).val x) atTop (𝓝 (u.val x))) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hstep hlim
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hψ := relativeFiniteEnergyPreceq_uscRegularization_tail_of_cauchySeq omega ui hlim.cauchySeq
  let ψ : ℕ → ModelFiniteEnergyPotential θ φ hφ := fun i =>
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
    let Mi : ℕ → ModelFiniteEnergyPotential θ φ hφ := fun k =>
      ⟨finiteTailMaximum (fun j => (ui j).val) i k,
        relativeFiniteEnergyPreceq_finiteTailMaximum omega (fun j => (ui j).property) i k⟩
    have hMi : Tendsto Mi atTop (𝓝 (ψ i)) := tendsto_iff_dist_tendsto_zero.mpr
      (SingularModelDarvasEnergyContinuity.relativeD1_tendsto_zero_of_directed_monotone_regularized
        omega (fun k => (Mi k).property) (ψ i).property
        (fun x k l hkl => finiteTailMaximum_monotone i hkl x)
        (by rw [iSup_finiteTailMaximum_eq_iSup_tail]))
    have hfinite (k : ℕ) : dist (ui i) (Mi k) ≤ C * A * r ^ i / (1 - C * r) := by
      have hw := relativeD1_finiteTailMaximum_le_weighted_sum omega (fun j => (ui j).property) i k
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
  have hpow : Tendsto (fun i : ℕ => r ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hbound := ((tendsto_const_nhds (x := C * A)).mul hpow).div_const (1 - C * r)
  simp only [mul_zero, zero_div] at hbound
  have hψlim : Tendsto ψ atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp hlim
    have hupper := hbound.add hd
    simp only [zero_add] at hupper
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hupper
    have hdi := hdist i
    rw [dist_comm (ui i) (ψ i)] at hdi
    exact (dist_triangle (ψ i) (ui i) u).trans (add_le_add hdi le_rfl))
  exact ⟨ψ, fun _ => rfl, hanti, hle, hdist, hψlim,
    SingularModelDarvasMonotoneLimits.pointwise_tendsto_of_antitone_native_tendsto
      omega ψ u hanti hψlim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailSupremumMajorants
