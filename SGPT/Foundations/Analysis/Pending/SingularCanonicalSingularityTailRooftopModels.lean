import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteRooftopModels
import SGPT.Foundations.Analysis.Pending.ActualDecreasingModelPositiveInfimum

set_option autoImplicit false

/-! # Actual positive increasing lower-tail rooftop models

SGPT PDF0230 Step 2.2 of Proposition 6.2.3, on the natural geometric
native-step domain with explicit numerical smallness. Actual finite
rooftop mass losses give internally positive bounds at each fixed tail;
the actual contact-first infimum producer constructs genuine models.
Their order, mass defect limit and target scalar mass limit are produced
without supplied rooftop, model or limit certificates. Identification of
the increasing regularized supremum and full sandwiches remains separate.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityTailRooftopModels

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeDarvasDistance DiagonalMass MixedMass ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularModelDarvasFiniteRooftopChains
  SingularCanonicalSingularityFiniteRooftopModels SingularCanonicalSingularityMassLipschitz
  ActualDecreasingModelPositiveInfimum

noncomputable section

private theorem geometric_loss_sum_le {L r : ℝ} (hL : 0 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (i k : ℕ) :
    (∑ j ∈ Finset.range k, L * r ^ (i + j)) ≤ L * r ^ i / (1 - r) := by
  have hgeom : (∑ j ∈ Finset.range k, r ^ j) ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg hr0 k]
  calc
    _ = (L * r ^ i) * ∑ j ∈ Finset.range k, r ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ ≤ (L * r ^ i) * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeom (mul_nonneg hL (pow_nonneg hr0 i))
    _ = _ := by ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem finiteTailRooftop_shift_le
    (θ : ClosedRealOneOneForm n M) (ui : ℕ → M → EReal)
    (hu : ∀ i, IsThetaPshPotential θ.val (ui i)) (i k : ℕ) :
    finiteTailRooftop θ ui i (k + 1) ≤ finiteTailRooftop θ ui (i + 1) k := by
  induction k with
  | zero =>
    simpa only [finiteTailRooftop, Nat.add_zero] using rooftop_le_right (hu i) (hu (i + 1))
  | succ k ih =>
    change rooftop θ (finiteTailRooftop θ ui i (k + 1)) (ui (i + (k + 1) + 1)) ≤
      rooftop θ (finiteTailRooftop θ ui (i + 1) k) (ui (i + 1 + k + 1))
    rw [show i + (k + 1) + 1 = i + 1 + k + 1 by omega]
    exact rooftop_mono ih le_rfl

/-- Actual positive finite rooftops internally construct increasing model
lower tails, their quantitative mass bounds and their true scalar limits. -/
theorem exists_increasing_rooftop_models_of_geometric_steps_of_tendsto
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val) {δ A r : ℝ}
    (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property)
    (hA : 0 ≤ A) (hr0 : 0 < r) (hr1 : r < 1)
    (hrC : (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * r < 1) :
    let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
    let D : ℝ := 3 * ((n : ℝ) + 1) * C
    let L : ℝ := D * A * (C / (1 - C * r) + 1)
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    L / (1 - r) < δ →
      (∀ i, dist (ui i) (ui (i + 1)) ≤ A * r ^ i) → Tendsto ui atTop (𝓝 u) →
      ∃ η : ℕ → ThetaPshL1 θ.val,
        (∀ i, (η i).val = ⨅ k, finiteTailRooftop θ (fun j => (ui j).val) i k) ∧
        (∀ i, IsModelPotential θ (η i).val) ∧
        Monotone (fun i => (η i).val) ∧ (∀ i, (η i).val ≤ (ui i).val) ∧
        (∀ i, 0 < δ - L * r ^ i / (1 - r) ∧
          (diagonalPotentialMass θ (ui i).val (ui i).property).toReal - L * r ^ i / (1 - r) ≤
            (diagonalPotentialMass θ (η i).val (η i).property).toReal ∧
          0 ≤ (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
            (diagonalPotentialMass θ (η i).val (η i).property).toReal ∧
          (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
              (diagonalPotentialMass θ (η i).val (η i).property).toReal ≤ L * r ^ i / (1 - r)) ∧
        Tendsto (fun i => (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
          (diagonalPotentialMass θ (η i).val (η i).property).toReal) atTop (𝓝 0) ∧
        Tendsto (fun i => (diagonalPotentialMass θ (η i).val (η i).property).toReal)
          atTop (𝓝 (diagonalPotentialMass θ u.val u.property).toReal) := by
  dsimp only
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  let D : ℝ := 3 * ((n : ℝ) + 1) * C
  let L : ℝ := D * A * (C / (1 - C * r) + 1)
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hsmall hstep hlim
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hden : 0 < 1 - C * r := sub_pos.mpr hrC
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hfinite {v : M → EReal} (hv : IsThetaPshPotential θ.val v) :
      diagonalPotentialMass θ v hv ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => hv.1)).ne
  have hstage' (i : ℕ) : δ ≤ (diagonalPotentialMass θ (ui i).val (ui i).property).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (hfinite (ui i).property)).mp (hstage i)
  obtain ⟨hchains, hanti⟩ := finiteTailRooftop_isModel_and_mass_lower_bound
    omega θ hbig ui u hmodels hδ hstage hA hr0 hr1 hrC hsmall hstep hlim
  let Q (i k : ℕ) := finiteTailRooftop θ (fun j => (ui j).val) i k
  have hQ (i k : ℕ) : IsModelPotential θ (Q i k) := (hchains i k).choose
  have hQmass (i k : ℕ) : (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
      (∑ j ∈ Finset.range k, L * r ^ (i + j)) ≤
      (diagonalPotentialMass θ (Q i k) (hQ i k).plurisubharmonic).toReal :=
    (hchains i k).choose_spec.2.1
  have hβ (i : ℕ) : L * r ^ i / (1 - r) ≤ L / (1 - r) := by
    apply div_le_div_of_nonneg_right ?_ (sub_pos.mpr hr1).le
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left (pow_le_one₀ hr0.le hr1.le) hL0)
  have hδi (i : ℕ) : 0 < δ - L * r ^ i / (1 - r) :=
    sub_pos.mpr ((hβ i).trans_lt hsmall)
  have hbound (i k : ℕ) : ENNReal.ofReal (δ - L * r ^ i / (1 - r)) ≤
      diagonalPotentialMass θ (Q i k) (hQ i k).plurisubharmonic := by
    apply ENNReal.ofReal_le_of_le_toReal
    have hsum := geometric_loss_sum_le hL0 hr0.le hr1 i k
    linarith [hQmass i k, hstage' i]
  have hη (i : ℕ) : IsModelPotential θ (⨅ k, Q i k) :=
    isModelPotential_iInf_of_uniform_positive_stage_mass omega (hQ i) (hanti i)
      (hδi i) (hbound i)
  let η : ℕ → ThetaPshL1 θ.val := fun i => ⟨⨅ k, Q i k, (hη i).plurisubharmonic⟩
  have hηle (i : ℕ) : (η i).val ≤ (ui i).val := by
    simpa only [η, Q, finiteTailRooftop] using (iInf_le (Q i) 0)
  have hηmono : Monotone (fun i => (η i).val) := by
    apply monotone_nat_of_le_succ
    intro i
    apply le_iInf
    intro k
    exact (iInf_le (Q i) (k + 1)).trans
      (finiteTailRooftop_shift_le θ (fun j => (ui j).val) (fun j => (ui j).property) i k)
  have hηmass (i : ℕ) : (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
      L * r ^ i / (1 - r) ≤ (diagonalPotentialMass θ (η i).val (η i).property).toReal := by
    have hlow : ∀ k, ENNReal.ofReal
        ((diagonalPotentialMass θ (ui i).val (ui i).property).toReal - L * r ^ i / (1 - r)) ≤
        diagonalPotentialMass θ (Q i k) (hQ i k).plurisubharmonic := by
      intro k
      apply ENNReal.ofReal_le_of_le_toReal
      have hsum := geometric_loss_sum_le hL0 hr0.le hr1 i k
      linarith [hQmass i k]
    have hm := le_diagonalPotentialMass_iInf_of_le_stage_masses omega (hQ i) (hanti i) hlow
    exact (ENNReal.ofReal_le_iff_le_toReal (hfinite (η i).property)).mp hm
  have hdefect (i : ℕ) :
      0 ≤ (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
        (diagonalPotentialMass θ (η i).val (η i).property).toReal ∧
      (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
        (diagonalPotentialMass θ (η i).val (η i).property).toReal ≤ L * r ^ i / (1 - r) := by
    have hm := diagonalPotentialMass_mono_of_kahler omega (η i).property (ui i).property
      (MoreSingularOn.of_le fun x _ => hηle i x)
    have hr := ENNReal.toReal_mono (hfinite (ui i).property) hm
    exact ⟨sub_nonneg.mpr hr, by linarith [hηmass i]⟩
  have hpow : Tendsto (fun i : ℕ => r ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hβlim := ((tendsto_const_nhds (x := L)).mul hpow).div_const (1 - r)
  simp only [mul_zero, zero_div] at hβlim
  have hdefectlim : Tendsto (fun i =>
      (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
        (diagonalPotentialMass θ (η i).val (η i).property).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun i => (hdefect i).1) (fun i => (hdefect i).2) hβlim
  have hmasslim := ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hlim
  have hηmasslim : Tendsto (fun i => (diagonalPotentialMass θ (η i).val (η i).property).toReal)
      atTop (𝓝 (diagonalPotentialMass θ u.val u.property).toReal) := by
    simpa only [Function.comp_apply, sub_sub_cancel, sub_zero] using hmasslim.sub hdefectlim
  exact ⟨η, fun _ => rfl, hη, hηmono, hηle,
    fun i => ⟨hδi i, hηmass i, (hdefect i).1, (hdefect i).2⟩, hdefectlim, hηmasslim⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityTailRooftopModels
