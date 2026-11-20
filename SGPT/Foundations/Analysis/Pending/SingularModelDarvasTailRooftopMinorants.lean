import SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneLimits
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasRooftopContinuity
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
# Actual increasing tail-rooftop minorants

Xia SGPT PDF0168--0169, the lower-minorant part of Lemma 4.3.5.
Actual geometric finite tail rooftops produce their genuine finite-energy
infima. Actual native closed order produces the increasing minorants.
The final consumer extracts its own strictly monotone fast subsequence from
arbitrary native convergence. Its AE conclusion explicitly uses chart Haar
volume; decreasing upper majorants and global-volume transport remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailRooftopMinorants

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace SingularModelDarvasFiniteRooftopChains

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Each actual finite tail rooftop, with actual finite-energy membership produced internally. -/
def finiteTailRooftopPotential (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (i k : ℕ) : ModelFiniteEnergyPotential θ φ hφ :=
  ⟨finiteTailRooftop θ (fun j => (ui j).val) i k,
    relativeFiniteEnergyPreceq_finiteTailRooftop omega (fun j => (ui j).property) i k⟩

omit [BorelSpace M] [ConnectedSpace M] in
private theorem finiteTailRooftop_shift_le
    {ui : ℕ → M → EReal} (hu : ∀ j, RelativeFiniteEnergyPreceq θ φ (ui j) hφ) (i k : ℕ) :
    finiteTailRooftop θ ui i (k + 1) ≤ finiteTailRooftop θ ui (i + 1) k := by
  induction k with
  | zero =>
    simpa only [finiteTailRooftop, Nat.add_zero] using
      rooftop_le_right (hu i).1.plurisubharmonic (hu (i + 1)).1.plurisubharmonic
  | succ k ih =>
    change rooftop θ (finiteTailRooftop θ ui i (k + 1)) (ui (i + (k + 1) + 1)) ≤
      rooftop θ (finiteTailRooftop θ ui (i + 1) k) (ui (i + 1 + k + 1))
    rw [show i + (k + 1) + 1 = i + 1 + k + 1 by omega]
    exact rooftop_mono ih le_rfl

/-- Actual geometric tail limits, their increasing order, and their quantitative distance bound. -/
theorem exists_tailRooftop_limits_of_geometric_steps (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) {A r : ℝ} (hr1 : r < 1) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) →
      ∃ η : ℕ → ModelFiniteEnergyPotential θ φ hφ,
        (∀ i, Tendsto (finiteTailRooftopPotential omega ui i) atTop (𝓝 (η i))) ∧
        (∀ i, (η i).val = ⨅ k, finiteTailRooftop θ (fun j => (ui j).val) i k) ∧
        (∀ i, (η i).val ≤ (ui i).val) ∧
        (∀ x, Monotone fun i => (η i).val x) ∧
        (∀ i, dist (ui i) (η i) ≤ A * r ^ i / (1 - r)) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hstep
  let T := finiteTailRooftopPotential omega ui
  have hTstep (i k : ℕ) : dist (T i k) (T i (k + 1)) ≤ (A * r ^ i) * r ^ k := by
    calc
      _ ≤ dist (ui (i + k)) (ui (i + k + 1)) :=
        relativeD1_finiteTailRooftop_step_le omega (fun j => (ui j).property) i k
      _ ≤ A * r ^ (i + k) := hstep (i + k)
      _ = _ := by rw [pow_add, mul_assoc]
  have hTcauchy (i : ℕ) : CauchySeq (T i) :=
    cauchySeq_of_le_geometric r (A * r ^ i) hr1 (hTstep i)
  have hTanti (i : ℕ) : ∀ x, Antitone fun k => (T i k).val x := fun x k l hkl =>
    finiteTailRooftop_antitone omega (fun j => (ui j).property) i hkl x
  have hex (i : ℕ) := SingularModelDarvasDecreasingCauchyLimit.tendsto_iInf_of_antitone_cauchySeq
    omega (T i) (hTanti i) (hTcauchy i)
  choose hη hηlim using hex
  let η : ℕ → ModelFiniteEnergyPotential θ φ hφ := fun i => ⟨⨅ k, (T i k).val, hη i⟩
  have hlim (i : ℕ) : Tendsto (T i) atTop (𝓝 (η i)) := hηlim i
  refine ⟨η, hlim, fun _ => rfl, ?_, ?_, ?_⟩
  · intro i
    exact iInf_le (fun k => (T i k).val) 0
  · intro x
    apply monotone_nat_of_le_succ
    intro i
    exact SingularModelDarvasRooftopContinuity.le_of_tendsto_of_eventually_le omega
      ((hlim i).comp (tendsto_add_atTop_nat 1)) (hlim (i + 1))
      (Eventually.of_forall fun k => finiteTailRooftop_shift_le (fun j => (ui j).property) i k) x
  · intro i
    exact dist_le_of_le_geometric_of_tendsto₀ r (A * r ^ i) hr1 (hTstep i) (hlim i)

/-- Geometric-step native convergence produces actual increasing minorants and their chart-Haar AE limit. -/
theorem exists_increasing_minorants_of_geometric_steps_of_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ)
    {A r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) → Tendsto ui atTop (𝓝 u) →
      ∃ η : ℕ → ModelFiniteEnergyPotential θ φ hφ,
        (∀ x, Monotone fun i => (η i).val x) ∧ (∀ i, (η i).val ≤ (ui i).val) ∧
        Tendsto η atTop (𝓝 u) ∧
        (∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
          Tendsto (fun i => chartFunction (η i).val e z) atTop (𝓝 (chartFunction u.val e z))) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hstep hui
  obtain ⟨η, _, _, hle, hm, hdist⟩ :=
    exists_tailRooftop_limits_of_geometric_steps omega ui hr1 hstep
  have hp : Tendsto (fun i : ℕ => r ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hbound := ((tendsto_const_nhds (x := A)).mul hp).div_const (1 - r)
  simp only [mul_zero, zero_div] at hbound
  have hη : Tendsto η atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp hui
    have hupper := hbound.add hd
    simp only [zero_add] at hupper
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) hupper
    have hdi := hdist i
    rw [dist_comm (ui i) (η i)] at hdi
    exact (dist_triangle (η i) (ui i) u).trans (add_le_add hdi le_rfl))
  exact ⟨η, hm, hle, hη, fun e =>
    SingularModelDarvasMonotoneLimits.ae_chart_tendsto_of_monotone_native_tendsto omega η u hm e hη⟩

/-- Every actual native convergent sequence has its own strict extraction and increasing actual minorants. -/
theorem exists_strictMono_increasing_minorants_of_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ η : ℕ → ModelFiniteEnergyPotential θ φ hφ,
        (∀ x, Monotone fun i => (η i).val x) ∧ (∀ i, (η i).val ≤ (ui (f i)).val) ∧
        Tendsto η atTop (𝓝 u) ∧
        (∀ e : ComplexChart n M, ∀ᵐ z ∂(volume.restrict e.val.target),
          Tendsto (fun i => chartFunction (η i).val e z) atTop (𝓝 (chartFunction u.val e z))) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  obtain ⟨f, hf, hfast⟩ := Metric.exists_subseq_bounded_of_cauchySeq ui hlim.cauchySeq
    (fun i => (1 / (2 : ℝ)) ^ i) (fun _ => by positivity)
  have hstep (i : ℕ) : dist (ui (f i)) (ui (f (i + 1))) ≤ 1 * (1 / (2 : ℝ)) ^ i := by
    simpa only [one_mul, dist_comm] using
      (hfast i (f (i + 1)) (hf.monotone (Nat.le_succ i))).le
  obtain ⟨η, hm, hle, hη, hae⟩ := exists_increasing_minorants_of_geometric_steps_of_tendsto
    omega (fun i => ui (f i)) u (by norm_num : 0 < 1 / (2 : ℝ)) (by norm_num : 1 / (2 : ℝ) < 1)
    hstep (hlim.comp hf.tendsto_atTop)
  exact ⟨f, hf, η, hm, hle, hη, hae⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailRooftopMinorants
