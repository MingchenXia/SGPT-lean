import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDecreasingCauchyLimit
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasRooftopContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Actual native Darvas metric completeness for every singular model

Xia SGPT PDF0165--0167 Theorem 4.3.2. This is the actual singular-model
instance of the finite-tail rooftop route, using the standard controlled
sequence completeness criterion. Both monotone Cauchy limit producers are
actual proved analytic theorems. No convergence, full-mass, limit-membership,
or completeness certificate is a premise of the final native theorem.
The generic arbitrary-rooftop-space Proposition 4.3.2 remains separate.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricCompleteness

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace SingularModelDarvasFiniteRooftopChains

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

omit [BorelSpace M] [ConnectedSpace M] in
private theorem finiteTailRooftop_succ_length_le_succ_start
    {u : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (u j) hφ) (k j : ℕ) :
    finiteTailRooftop θ u k (j + 1) ≤ finiteTailRooftop θ u (k + 1) j := by
  induction j with
  | zero =>
    simpa only [finiteTailRooftop, Nat.add_zero] using
      rooftop_le_right (hu k).1.plurisubharmonic (hu (k + 1)).1.plurisubharmonic
  | succ j ih =>
    change rooftop θ (finiteTailRooftop θ u k (j + 1)) (u (k + (j + 1) + 1)) ≤
      rooftop θ (finiteTailRooftop θ u (k + 1) j) (u (k + 1 + j + 1))
    rw [show k + (j + 1) + 1 = k + 1 + j + 1 by omega]
    exact rooftop_mono ih le_rfl

/-- The full actual finite-energy subtype is complete for its native actual Darvas uniformity. -/
theorem completeSpace_finiteEnergyMetricSpace (omega : KahlerBackground n M) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    CompleteSpace (ModelFiniteEnergyPotential θ φ hφ) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  apply Metric.complete_of_convergent_controlled_sequences (fun N => (1 / (2 : ℝ)) ^ N)
    (fun _ => by positivity)
  intro ui hfast
  let T : ℕ → ℕ → ModelFiniteEnergyPotential θ φ hφ := fun k j =>
    ⟨finiteTailRooftop θ (fun i => (ui i).val) k j,
      relativeFiniteEnergyPreceq_finiteTailRooftop omega (fun i => (ui i).property) k j⟩
  have hTstep (k j : ℕ) : dist (T k j) (T k (j + 1)) ≤
      (1 / (2 : ℝ)) ^ k * (1 / (2 : ℝ)) ^ j := by
    calc
      _ ≤ dist (ui (k + j)) (ui (k + j + 1)) :=
        relativeD1_finiteTailRooftop_step_le omega (fun i => (ui i).property) k j
      _ ≤ (1 / (2 : ℝ)) ^ (k + j) := (hfast (k + j) (k + j) (k + j + 1) le_rfl (Nat.le_succ _)).le
      _ = _ := pow_add _ _ _
  have hTcauchy (k : ℕ) : CauchySeq (T k) :=
    cauchySeq_of_le_geometric (1 / (2 : ℝ)) ((1 / (2 : ℝ)) ^ k) (by norm_num) (hTstep k)
  have hTanti (k : ℕ) : ∀ x, Antitone fun j => (T k j).val x := fun x i j hij =>
    finiteTailRooftop_antitone omega (fun i => (ui i).property) k hij x
  have hex (k : ℕ) := SingularModelDarvasDecreasingCauchyLimit.tendsto_iInf_of_antitone_cauchySeq
    omega (T k) (hTanti k) (hTcauchy k)
  choose hy hTy using hex
  let y : ℕ → ModelFiniteEnergyPotential θ φ hφ := fun k => ⟨⨅ j, (T k j).val, hy k⟩
  have hylimit (k : ℕ) : Tendsto (T k) atTop (𝓝 (y k)) := hTy k
  have hybound (k : ℕ) : dist (ui k) (y k) ≤ 2 * (1 / (2 : ℝ)) ^ k := by
    have h := dist_le_of_le_geometric_of_tendsto₀ (1 / (2 : ℝ)) ((1 / (2 : ℝ)) ^ k)
      (by norm_num) (hTstep k) (hylimit k)
    have hT0 : T k 0 = ui k := Subtype.ext rfl
    rw [hT0] at h
    norm_num at h
    nlinarith
  have hyinc (k : ℕ) : (y k).val ≤ (y (k + 1)).val :=
    SingularModelDarvasRooftopContinuity.le_of_tendsto_of_eventually_le omega
      ((hylimit k).comp (tendsto_add_atTop_nat 1)) (hylimit (k + 1))
      (Eventually.of_forall fun j =>
        finiteTailRooftop_succ_length_le_succ_start (fun i => (ui i).property) k j)
  have hymono : ∀ x, Monotone fun k => (y k).val x := fun x =>
    monotone_nat_of_le_succ fun k => hyinc k x
  have hystep (k : ℕ) : dist (y k) (y (k + 1)) ≤ 5 * (1 / (2 : ℝ)) ^ k := by
    have hmiddle : dist (ui k) (ui (k + 1)) ≤ (1 / (2 : ℝ)) ^ k :=
      (hfast k k (k + 1) le_rfl (Nat.le_succ _)).le
    have htri := (dist_triangle (y k) (ui k) (y (k + 1))).trans
      (add_le_add le_rfl (dist_triangle (ui k) (ui (k + 1)) (y (k + 1))))
    rw [dist_comm (y k) (ui k)] at htri
    have hb0 := hybound k
    have hb1 := hybound (k + 1)
    rw [pow_succ] at hb1
    nlinarith [pow_nonneg (by norm_num : 0 ≤ 1 / (2 : ℝ)) k]
  have hycauchy : CauchySeq y :=
    cauchySeq_of_le_geometric (1 / (2 : ℝ)) 5 (by norm_num) hystep
  obtain ⟨hY, hylim⟩ := SingularModelDarvasIncreasingCauchyLimit.tendsto_uscRegularization_iSup_of_monotone_cauchySeq
    omega y hymono hycauchy
  let Y : ModelFiniteEnergyPotential θ φ hφ := ⟨uscRegularization (⨆ k, (y k).val), hY⟩
  refine ⟨Y, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  have hpow : Tendsto (fun k : ℕ => (1 / (2 : ℝ)) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hydist : Tendsto (fun k => dist (y k) Y) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hylim
  have hupper := ((tendsto_const_nhds (x := (2 : ℝ))).mul hpow).add hydist
  simp only [mul_zero, zero_add] at hupper
  apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hupper
  exact (dist_triangle (ui k) (y k) Y).trans (add_le_add (hybound k) le_rfl)

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMetricCompleteness
