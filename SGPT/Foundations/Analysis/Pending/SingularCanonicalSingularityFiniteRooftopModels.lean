import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityTailSupremumMajorants
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondUnconditional
import SGPT.Foundations.Analysis.Pending.RooftopPshCriterion
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasFiniteRooftopChains

set_option autoImplicit false

/-! # Actual positive finite rooftop model chains

SGPT PDF0230, Step 2.1--2.2 of Proposition 6.2.3, adapted to natural
geometric native steps with an explicit numerical smallness condition.
Actual upper tails and mass Lipschitz control produce each mass loss;
the actual strict mass criterion and diamond produce genuine positive
finite rooftops. Actual envelope monotonicity and the rooftop universal
property supply their model identity without envelope idempotence.
Infinite lower tails and full subsequence sandwiches remain separate.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteRooftopModels

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  RelativeDarvasDistance DiagonalMass MixedMass SingularCanonicalSingularityDistance
  SingularCanonicalSingularityTailSupremumMajorants SingularCanonicalSingularityMassLipschitz
  SingularModelDarvasFiniteRooftopChains ThetaPshL1Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

omit [BorelSpace M] in
/-- The actual genuine positive rooftop of two actual models is a model;
its fixed point is produced by monotonicity and the universal property. -/
theorem isModelPotential_rooftop_of_positive_mass
    {θ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsModelPotential θ u) (hv : IsModelPotential θ v)
    (hq : IsThetaPshPotential θ.val (rooftop θ u v))
    (hqpos : 0 < diagonalPotentialMass θ (rooftop θ u v) hq) :
    IsModelPotential θ (rooftop θ u v) := by
  have hqu := rooftop_le_left hu.plurisubharmonic hv.plurisubharmonic
  have hqv := rooftop_le_right hu.plurisubharmonic hv.plurisubharmonic
  have hq0 : rooftop θ u v ≤ 0 := hqu.trans (by
    rw [hu.envelope_eq]
    exact singularityEnvelope_le_zero θ.val u)
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hq.1.hasSmoothLocalPotentials (rooftop θ u v) hq
  have hPu : singularityEnvelope θ.val (rooftop θ u v) ≤ u := by
    exact (singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hqu x)).trans_eq hu.envelope_eq.symm
  have hPv : singularityEnvelope θ.val (rooftop θ u v) ≤ v := by
    exact (singularityEnvelope_mono (θ := θ.val)
      (MoreSingularOn.of_le fun x _ => hqv x)).trans_eq hv.envelope_eq.symm
  have hPle : singularityEnvelope θ.val (rooftop θ u v) ≤ rooftop θ u v :=
    le_rooftopEnvelope hP (quasiEverywhere_of_forall fun x => le_min (hPu x) (hPv x))
  exact ⟨hq, le_antisymm (self_le_singularityEnvelope hq hq0) hPle, hqpos⟩

private theorem finite_rooftop_model_bounds
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (ui ψ : ℕ → ThetaPshL1 θ.val)
    (hmodels : ∀ i, IsModelPotential θ (ui i).val)
    (hle : ∀ j, (ui j).val ≤ (ψ j).val)
    (hnext : ∀ j, (ui (j + 1)).val ≤ (ψ j).val)
    {δ : ℝ} (hstage : ∀ i, δ ≤ (diagonalPotentialMass θ (ui i).val (ui i).property).toReal)
    (loss : ℕ → ℝ)
    (hsmall : ∀ i k, (∑ j ∈ Finset.range k, loss (i + j)) < δ)
    (hupper : ∀ j, (diagonalPotentialMass θ (ψ j).val (ψ j).property).toReal ≤
      (diagonalPotentialMass θ (ui (j + 1)).val (ui (j + 1)).property).toReal + loss j) :
    ∀ i k, ∃ hq : IsModelPotential θ (finiteTailRooftop θ (fun j => (ui j).val) i k),
      finiteTailRooftop θ (fun j => (ui j).val) i k ≤ (ui (i + k)).val ∧
      (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
          (∑ j ∈ Finset.range k, loss (i + j)) ≤
        (diagonalPotentialMass θ (finiteTailRooftop θ (fun j => (ui j).val) i k)
          hq.plurisubharmonic).toReal := by
  have hfinite {v : M → EReal} (hv : IsThetaPshPotential θ.val v) :
      diagonalPotentialMass θ v hv ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => hv.1)).ne
  intro i k
  induction k with
  | zero =>
    refine ⟨hmodels i, ?_, ?_⟩
    · simp only [finiteTailRooftop, Nat.add_zero, le_refl]
    · simp only [finiteTailRooftop, Finset.range_zero, Finset.sum_empty, sub_zero, le_refl]
  | succ k ih =>
    obtain ⟨hq, hlast, hmass⟩ := ih
    let q := finiteTailRooftop θ (fun j => (ui j).val) i k
    let v := (ui (i + k + 1)).val
    have hv : IsModelPotential θ v := hmodels (i + k + 1)
    have hmax : IsThetaPshPotential θ.val (fun x => max (q x) (v x)) :=
      IsThetaPshPotential.max hq.plurisubharmonic hv.plurisubharmonic
    have hmaxle : (fun x => max (q x) (v x)) ≤ (ψ (i + k)).val := by
      intro x
      exact max_le ((hlast x).trans (hle (i + k) x)) (hnext (i + k) x)
    have hmmax := diagonalPotentialMass_mono_of_kahler omega hmax (ψ (i + k)).property
      (MoreSingularOn.of_le fun x _ => hmaxle x)
    have hupper' := (ENNReal.toReal_mono (hfinite (ψ (i + k)).property) hmmax).trans
      (hupper (i + k))
    change (diagonalPotentialMass θ (fun x => max (q x) (v x)) hmax).toReal ≤
      (diagonalPotentialMass θ v hv.plurisubharmonic).toReal + loss (i + k) at hupper'
    have hsmall' := hsmall i (k + 1)
    rw [Finset.sum_range_succ] at hsmall'
    have hloss : loss (i + k) < (diagonalPotentialMass θ q hq.plurisubharmonic).toReal := by
      linarith [hstage i]
    have hgt : diagonalPotentialMass θ (fun x => max (q x) (v x)) hmax <
        diagonalPotentialMass θ q hq.plurisubharmonic +
          diagonalPotentialMass θ v hv.plurisubharmonic := by
      apply (ENNReal.toReal_lt_toReal (hfinite hmax)
        (ENNReal.add_ne_top.mpr ⟨hfinite hq.plurisubharmonic, hfinite hv.plurisubharmonic⟩)).mp
      rw [ENNReal.toReal_add (hfinite hq.plurisubharmonic) (hfinite hv.plurisubharmonic)]
      linarith
    have hroof := RooftopPshCriterion.isThetaPshPotential_rooftopEnvelope_min_of_mass_lt
      omega θ hq.plurisubharmonic hv.plurisubharmonic hgt
    have hdiamond := RooftopMassDiamondUnconditional.mass_add_mass_le_mass_max_add_mass_rooftop
      omega θ hq.plurisubharmonic hv.plurisubharmonic hmax hroof
    have hdiamond' := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfinite hmax, hfinite hroof⟩) hdiamond
    rw [ENNReal.toReal_add (hfinite hq.plurisubharmonic) (hfinite hv.plurisubharmonic),
      ENNReal.toReal_add (hfinite hmax) (hfinite hroof)] at hdiamond'
    change (diagonalPotentialMass θ q hq.plurisubharmonic).toReal +
        (diagonalPotentialMass θ v hv.plurisubharmonic).toReal ≤
      (diagonalPotentialMass θ (fun x => max (q x) (v x)) hmax).toReal +
        (diagonalPotentialMass θ (rooftop θ q v) hroof).toReal at hdiamond'
    have hmass' : (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
        (∑ j ∈ Finset.range (k + 1), loss (i + j)) ≤
        (diagonalPotentialMass θ (rooftop θ q v) hroof).toReal := by
      rw [Finset.sum_range_succ]
      linarith
    have hpos : 0 < diagonalPotentialMass θ (rooftop θ q v) hroof :=
      (ENNReal.toReal_pos_iff.mp ((sub_pos.mpr
        ((hsmall i (k + 1)).trans_le (hstage i))).trans_le hmass')).1
    exact ⟨isModelPotential_rooftop_of_positive_mass hq hv hroof hpos,
      rooftop_le_right hq.plurisubharmonic hv.plurisubharmonic, hmass'⟩

/-- Actual geometric native steps internally produce genuine positive model
finite rooftops and their quantitative cumulative actual mass loss. -/
theorem finiteTailRooftop_isModel_and_mass_lower_bound
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
      (∀ i k, ∃ hq : IsModelPotential θ
          (finiteTailRooftop θ (fun j => (ui j).val) i k),
        finiteTailRooftop θ (fun j => (ui j).val) i k ≤ (ui (i + k)).val ∧
        (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
            (∑ j ∈ Finset.range k, L * r ^ (i + j)) ≤
          (diagonalPotentialMass θ (finiteTailRooftop θ (fun j => (ui j).val) i k)
            hq.plurisubharmonic).toReal ∧
        0 < (diagonalPotentialMass θ (ui i).val (ui i).property).toReal -
          (∑ j ∈ Finset.range k, L * r ^ (i + j))) ∧
      ∀ i, Antitone (finiteTailRooftop θ (fun j => (ui j).val) i) := by
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
  have hfinite (a : ThetaPshL1 θ.val) : diagonalPotentialMass θ a.val a.property ≠ ⊤ :=
    (globalMixedMass_lt_top omega (fun _ : Fin n => a.property.1)).ne
  have hstage' (i : ℕ) : δ ≤ (diagonalPotentialMass θ (ui i).val (ui i).property).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (hfinite (ui i))).mp (hstage i)
  have hB : ∀ i x, (ui i).val x ≤ (0 : EReal) := by
    intro i
    rw [(hmodels i).envelope_eq]
    exact singularityEnvelope_le_zero θ.val (ui i).val
  obtain ⟨ψ, _, hanti, hle, hdist, _⟩ :=
    exists_decreasing_majorants_of_geometric_steps_of_tendsto omega θ hbig ui u hB
      hA hr0 hr1 hrC hstep hlim
  have hnext (j : ℕ) : (ui (j + 1)).val ≤ (ψ j).val :=
    fun x => (hle (j + 1) x).trans (hanti x (Nat.le_succ j))
  have hupper (j : ℕ) : (diagonalPotentialMass θ (ψ j).val (ψ j).property).toReal ≤
      (diagonalPotentialMass θ (ui (j + 1)).val (ui (j + 1)).property).toReal + L * r ^ j := by
    have habs := (abs_diagonalPotentialMass_sub_le omega θ hbig
      (ψ j).property (ui (j + 1)).property).2
    rw [← dist_eq_singularityDistance_toReal omega θ hbig] at habs
    have hmass := (le_abs_self ((diagonalPotentialMass θ (ψ j).val (ψ j).property).toReal -
      (diagonalPotentialMass θ (ui (j + 1)).val (ui (j + 1)).property).toReal)).trans habs
    have hdist' : dist (ψ j) (ui (j + 1)) ≤ C * A * r ^ j / (1 - C * r) + A * r ^ j := by
      have hd := hdist j
      rw [dist_comm (ui j) (ψ j)] at hd
      exact (dist_triangle (ψ j) (ui j) (ui (j + 1))).trans (add_le_add hd (hstep j))
    calc
      _ ≤ (diagonalPotentialMass θ (ui (j + 1)).val (ui (j + 1)).property).toReal +
          D * dist (ψ j) (ui (j + 1)) := by linarith
      _ ≤ (diagonalPotentialMass θ (ui (j + 1)).val (ui (j + 1)).property).toReal +
          D * (C * A * r ^ j / (1 - C * r) + A * r ^ j) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdist' hD0)
      _ = _ := by dsimp [L]; ring
  have hgeom (k : ℕ) : (∑ j ∈ Finset.range k, r ^ j) ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg hr0.le k]
  have hsum (i k : ℕ) : (∑ j ∈ Finset.range k, L * r ^ (i + j)) < δ := by
    by_cases hk : k = 0
    · simpa only [hk, Finset.range_zero, Finset.sum_empty] using hδ
    calc
      _ = (L * r ^ i) * ∑ j ∈ Finset.range k, r ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_add]
        ring
      _ ≤ (L * r ^ i) * (1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (hgeom k) (mul_nonneg hL0 (pow_nonneg hr0.le i))
      _ = (L * r ^ i) / (1 - r) := by ring
      _ ≤ L / (1 - r) := by
        apply div_le_div_of_nonneg_right ?_ (sub_pos.mpr hr1).le
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (pow_le_one₀ hr0.le hr1.le) hL0)
      _ < δ := hsmall
  have hchains := finite_rooftop_model_bounds omega θ ui ψ hmodels hle hnext
    hstage' (fun j => L * r ^ j) hsum hupper
  refine ⟨?_, ?_⟩
  · intro i k
    obtain ⟨hq, hlast, hmass⟩ := hchains i k
    exact ⟨hq, hlast, hmass, sub_pos.mpr ((hsum i k).trans_le (hstage' i))⟩
  · intro i
    apply antitone_nat_of_succ_le
    intro k
    exact rooftop_le_left (hchains i k).choose.plurisubharmonic (ui (i + k + 1)).property

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityFiniteRooftopModels
