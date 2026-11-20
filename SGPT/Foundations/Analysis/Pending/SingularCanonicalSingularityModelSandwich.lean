import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricSandwich
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

/-! # Actual subsequence sandwiches for convergent model potentials

SGPT PDF0228--0231 Proposition 6.2.3, full natural sequence contract.
Actual native convergence yields Cauchy subsequence extraction; explicit
positive numerical choices produce the geometric smallness hypothesis
internally. Genuine tail geometry and both native limits follow from the
proved actual geometric sandwich, without an initial target-model or
desired limit certificate. General Cauchy completeness remains separate.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance SingularModelDarvasFiniteRooftopChains
  SingularCanonicalSingularityGeometricSandwich

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Native convergence and a genuine uniform stage mass bound internally
produce a strict subsequence and the actual monotone PSH sandwich. -/
theorem exists_strictMono_monotone_sandwich_of_tendsto
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ : ℝ}
    (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto ui atTop (𝓝 u) →
      ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ η ψ : ℕ → ThetaPshL1 θ.val,
        (∀ i, (η i).val = ⨅ k, finiteTailRooftop θ (fun j => (ui (f j)).val) i k) ∧
        (∀ i, (ψ i).val = uscRegularization (⨆ j, (ui (f (i + j))).val)) ∧
        (∀ i, IsModelPotential θ (η i).val) ∧ Monotone (fun i => (η i).val) ∧
        (∀ x, Antitone fun i => (ψ i).val x) ∧
        (∀ i, (η i).val ≤ (ui (f i)).val ∧ (ui (f i)).val ≤ (ψ i).val) ∧
        Tendsto η atTop (𝓝 u) ∧ Tendsto ψ atTop (𝓝 u) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hlim
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  let D : ℝ := 3 * ((n : ℝ) + 1) * C
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    have hp : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [C]
    nlinarith
  have hD : 0 < D := by dsimp [D]; positivity
  let r : ℝ := 1 / (2 * C)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by positivity : 0 < 2 * C)).mpr
    linarith
  have hCr : C * r = 1 / 2 := by
    dsimp [r]
    field_simp
  have hrC : C * r < 1 := by rw [hCr]; norm_num
  have hden : 0 < 1 - C * r := sub_pos.mpr hrC
  let B : ℝ := D * (C / (1 - C * r) + 1) / (1 - r)
  have hB : 0 < B := by dsimp [B]; positivity
  let A : ℝ := δ / (2 * B)
  have hA : 0 < A := by dsimp [A]; positivity
  have hsmall : D * A * (C / (1 - C * r) + 1) / (1 - r) < δ := by
    calc
      _ = A * B := by dsimp [B]; ring
      _ = δ / 2 := by dsimp [A]; field_simp
      _ < δ := by linarith
  obtain ⟨f, hf, hbound⟩ := Metric.exists_subseq_bounded_of_cauchySeq ui hlim.cauchySeq
    (fun i => A * r ^ i) (fun i => mul_pos hA (pow_pos hr0 i))
  have hstep (i : ℕ) : dist (ui (f i)) (ui (f (i + 1))) ≤ A * r ^ i := by
    rw [dist_comm]
    exact (hbound i (f (i + 1)) (hf.monotone (Nat.le_succ i))).le
  have hsub : Tendsto (fun i => ui (f i)) atTop (𝓝 u) := hlim.comp hf.tendsto_atTop
  obtain ⟨η, ψ, hηeq, hψeq, hηmodel, hηmono, hψanti, hbetween, hηlim, hψlim, _⟩ :=
    exists_monotone_sandwich_of_geometric_steps_of_tendsto omega θ hbig
      (fun i => ui (f i)) u (fun i => hmodels (f i)) hδ (fun i => hstage (f i))
      hA.le hr0 hr1 hrC hsmall hstep hsub
  exact ⟨f, hf, η, ψ, hηeq, hψeq, hηmodel, hηmono, hψanti, hbetween, hηlim, hψlim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelSandwich
