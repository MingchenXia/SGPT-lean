import SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailRooftopMinorants
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasTailSupremumMajorants
import SGPT.Foundations.Analysis.Pending.ChartHaarKahlerVolumeAE

set_option autoImplicit false

/-!
# Actual complete singular-model monotone sandwich subsequences

Xia SGPT PDF0167--0169, Lemma 4.3.5. A genuine strict Cauchy extraction at
the rate r=(2*C_n)^(-1) produces the same fast subsequence for the actual
tail-rooftop minorants and tail-supremum majorants. Their actual E1 membership,
native limits, everywhere upper limit, and actual global Kahler-volume lower
AE limit are all proved producers. No extraction, limit-membership, or
global-volume equivalence certificate is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneSandwich

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelDarvasMetricSpace IntegrationCurrent

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Full source Lemma 4.3.5 with actual native limits and actual global smooth-volume AE scope. -/
theorem exists_strictMono_monotone_sandwich_of_tendsto (omega : KahlerBackground n M)
    (ui : ℕ → ModelFiniteEnergyPotential θ φ hφ) (u : ModelFiniteEnergyPotential θ φ hφ) :
    letI := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
    letI : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
    letI : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
      (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) → ∃ f : ℕ → ℕ, StrictMono f ∧
      ∃ η ψ : ℕ → ModelFiniteEnergyPotential θ φ hφ,
        (∀ x, Monotone fun i => (η i).val x) ∧ (∀ x, Antitone fun i => (ψ i).val x) ∧
        (∀ i, (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ψ i).val) ∧
        Tendsto η atTop (𝓝 u) ∧ Tendsto ψ atTop (𝓝 u) ∧
        (∀ x, Tendsto (fun i => (ψ i).val x) atTop (𝓝 (u.val x))) ∧
        (∀ᵐ x ∂kahlerVolume omega, Tendsto (fun i => (η i).val x) atTop (𝓝 (u.val x))) := by
  let := finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega
  let : UniformSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace
  let : TopologicalSpace (ModelFiniteEnergyPotential θ φ hφ) :=
    (finiteEnergyMetricSpace (θ := θ) (φ := φ) (hφ := hφ) omega).toUniformSpace.toTopologicalSpace
  intro hlim
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC : 1 < C := by
    have hp : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hprod : (1 : ℝ) ≤ (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1) :=
      (by simpa only [one_mul] using mul_le_mul hp hn (by norm_num : (0 : ℝ) ≤ 1) (by positivity))
    dsimp [C]
    nlinarith
  have hCpos : 0 < C := zero_lt_one.trans hC
  have h2C : 0 < 2 * C := mul_pos (by norm_num) hCpos
  let r : ℝ := 1 / (2 * C)
  have hr0 : 0 < r := one_div_pos.mpr h2C
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_iff₀ h2C).mpr
    nlinarith
  have hrC : C * r < 1 := by
    have heq : C * r = 1 / (2 : ℝ) := by
      dsimp [r]
      field_simp [ne_of_gt hCpos]
    rw [heq]
    norm_num
  obtain ⟨f, hf, hfast⟩ := Metric.exists_subseq_bounded_of_cauchySeq ui hlim.cauchySeq
    (fun i => r ^ i) (fun _ => pow_pos hr0 _)
  let vi : ℕ → ModelFiniteEnergyPotential θ φ hφ := fun i => ui (f i)
  have hstep (i : ℕ) : dist (vi i) (vi (i + 1)) ≤ 1 * r ^ i := by
    simpa only [vi, one_mul, dist_comm] using
      (hfast i (f (i + 1)) (hf.monotone (Nat.le_succ i))).le
  have hvlim : Tendsto vi atTop (𝓝 u) := hlim.comp hf.tendsto_atTop
  obtain ⟨η, hm, hηle, hηlim, _⟩ :=
    SingularModelDarvasTailRooftopMinorants.exists_increasing_minorants_of_geometric_steps_of_tendsto
      omega vi u hr0 hr1 hstep hvlim
  obtain ⟨ψ, _, hanti, hψle, _, hψlim, hpoint⟩ :=
    SingularModelDarvasTailSupremumMajorants.exists_decreasing_majorants_of_geometric_steps_of_tendsto
      omega vi u (by norm_num : (0 : ℝ) ≤ 1) hr0 hr1 hrC hstep hvlim
  exact ⟨f, hf, η, ψ, hm, hanti, fun i => ⟨hηle i, hψle i⟩, hηlim, hψlim, hpoint,
    ChartHaarKahlerVolumeAE.ae_kahlerVolume_tendsto_of_monotone_native_tendsto omega η u hm hηlim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasMonotoneSandwich
