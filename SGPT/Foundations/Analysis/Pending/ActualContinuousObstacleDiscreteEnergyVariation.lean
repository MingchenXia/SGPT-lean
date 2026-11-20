import SGPT.Foundations.Analysis.Pending.ActualContinuousSingularObstacleContact
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyOrderedComparison
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax
import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets

set_option autoImplicit false

/-! # Actual discrete one-sided singular rooftop energy variation

DDL survey arXiv2303.11584v2 Proposition 5.12, discrete negative direction.
Original rooftop/E1/contact/native mixed measures internally produced.
No variational maximizer or relative MA existence is asserted.
Complete mathematical blueprint preceded SOURCE.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualContinuousObstacleDiscreteEnergyVariation

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass RelativeDarvasDistance RelativePreceqClasses
  ActualContinuousSingularObstacleContact SingularModelFiniteEnergyGapMax
  SingularModelFiniteEnergyOrderedComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original rooftop of the continuously perturbed obstacle. -/
def perturbedRooftop (θ : ClosedRealOneOneForm n M)
    (u : M → EReal) (h : M → ℝ) (t : ℝ) : M → EReal :=
  rooftopEnvelope θ.val (fun x => u x + ((t * h x : ℝ) : EReal))

private theorem exists_abs_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {h : X → ℝ} (hh : Continuous h) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |h x| ≤ L := by
  obtain ⟨B, hB⟩ := (isCompact_range hh.abs).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun x =>
    (hB ⟨x, rfl⟩).trans (le_max_left _ _)⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {h : M → ℝ}
  {hφ : IsModelPotential θ φ}

/-- Genuine finite translation and actual upward E1 closure produce finite
energy of the actual roof; neither rooftop E1 nor contact is an input. -/
theorem relativeFiniteEnergyPreceq_perturbedRooftop (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    RelativeFiniteEnergyPreceq θ φ (perturbedRooftop θ u h t) hφ := by
  have hth : Continuous (fun x => t * h x) := continuous_const.mul hh
  have hth0 : ∀ x, t * h x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos ht (hh0 x)
  obtain ⟨L, _hL0, _hL, hp, hlo, hbelow, hhigh⟩ :=
    exists_genuine_rooftop_sandwich hn hbig hu.1.plurisubharmonic hu0 hth hth0
  have hpφ : RelativePSHPreceq θ φ (perturbedRooftop θ u h t) :=
    ⟨hp, (MoreSingularOn.of_le fun x _ => (hbelow x).trans (hhigh x)).trans
      hu.1.relativePSHPreceq.2⟩
  exact relativeFiniteEnergyPreceq_of_le omega
    (RelativeFiniteEnergyPreceq.add_const omega hu (-L)) hpφ hlo

omit [ConnectedSpace M] in
private theorem ae_ne_bot_diagonal {a b : M → EReal}
    (ha : IsThetaPshPotential θ.val a) (hb : IsThetaPshPotential θ.val b) :
    ∀ᵐ x ∂diagonalPotentialMeasure θ a ha, b x ≠ ⊥ := by
  apply ae_iff.mpr
  simpa only [not_not, diagonalPotentialMeasure] using
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin n => θ) (u := fun _ => a) (fun _ : Fin n => ha.1) hb

/-- Genuine original-obstacle contact and the actual ordered singular E1
endpoint comparison produce both real rooftop-energy slope bounds. -/
theorem energy_slope_bounds (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    t * (∫ x, h x ∂diagonalPotentialMeasure θ (perturbedRooftop θ u h t)
      (relativeFiniteEnergyPreceq_perturbedRooftop omega hn hbig hu hu0 hh hh0 ht).1.plurisubharmonic) ≤
      (energy θ φ hφ (perturbedRooftop θ u h t)).toReal - (energy θ φ hφ u).toReal ∧
    (energy θ φ hφ (perturbedRooftop θ u h t)).toReal - (energy θ φ hφ u).toReal ≤
      t * (∫ x, h x ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) := by
  let p : M → EReal := perturbedRooftop θ u h t
  have hpF := relativeFiniteEnergyPreceq_perturbedRooftop omega hn hbig hu hu0 hh hh0 ht
  have hp : IsThetaPshPotential θ.val p := hpF.1.plurisubharmonic
  have huP := hu.1.plurisubharmonic
  let μp := diagonalPotentialMeasure θ p hp
  let μu := diagonalPotentialMeasure θ u huP
  let g := fun x => canonicalERealDiffToReal (u x) (p x)
  have hth : Continuous (fun x => t * h x) := continuous_const.mul hh
  have hth0 : ∀ x, t * h x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos ht (hh0 x)
  obtain ⟨_L, _hL0, _hL, _hp, _hlo, hbelow, hhigh⟩ :=
    exists_genuine_rooftop_sandwich hn hbig huP hu0 hth hth0
  have hpu : p ≤ u := fun x => (hbelow x).trans (hhigh x)
  obtain ⟨_hpC, hcontact⟩ := exists_genuine_rooftop_and_contact hn hbig huP hu0 hth hth0
  have hc : μp {x | p x < u x + ((t * h x : ℝ) : EReal)} = 0 := hcontact
  have hcontactAE : ∀ᵐ x ∂μp, p x = u x + ((t * h x : ℝ) : EReal) := by
    have hnot : ∀ᵐ x ∂μp, ¬p x < u x + ((t * h x : ℝ) : EReal) :=
      ae_iff.mpr (by simpa only [not_not] using hc)
    filter_upwards [hnot] with x hx
    exact le_antisymm (hbelow x) (not_lt.mp hx)
  have hgAE : ∀ᵐ x ∂μp, g x = -(t * h x) := by
    filter_upwards [hcontactAE, ae_ne_bot_diagonal hp huP] with x hx hubot
    have hux : u x = ((u x).toReal : EReal) :=
      (EReal.coe_toReal (huP.1.quasiPlurisubharmonic.ne_top x) hubot).symm
    rw [hux, ← EReal.coe_add] at hx
    dsimp only [g]
    rw [hux, hx, canonicalERealDiffToReal_coe_coe]
    ring
  have hpint : (∫ x, g x ∂μp) = -(t * (∫ x, h x ∂μp)) := by
    calc (∫ x, g x ∂μp) = ∫ x, -(t * h x) ∂μp := integral_congr_ae hgAE
      _ = _ := by rw [integral_neg, integral_const_mul]
  have : IsFiniteMeasure μu := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ huP
  have hhi : Integrable h μu := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hh.continuousOn
  have hgi := SingularModelFiniteEnergyGapMax.integrable_canonicalDiff_diagonal_add omega hu hpF
  have hineqAE : ∀ᵐ x ∂μu, -(t * h x) ≤ g x := by
    filter_upwards [ae_ne_bot_diagonal huP huP, ae_ne_bot_diagonal huP hp]
      with x hubot hpbot
    have hux : u x = ((u x).toReal : EReal) :=
      (EReal.coe_toReal (huP.1.quasiPlurisubharmonic.ne_top x) hubot).symm
    have hpx : p x = ((p x).toReal : EReal) :=
      (EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpbot).symm
    have hle := hbelow x
    change p x ≤ u x + ((t * h x : ℝ) : EReal) at hle
    rw [hpx, hux, ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
    dsimp only [g]
    rw [hux, hpx, canonicalERealDiffToReal_coe_coe]
    linarith
  have hmono := integral_mono_ae (hhi.const_mul t).neg hgi.left_of_add_measure hineqAE
  change (∫ x, -(t * h x) ∂μu) ≤ (∫ x, g x ∂μu) at hmono
  rw [integral_neg, integral_const_mul] at hmono
  obtain ⟨ha, hb, _⟩ := integral_le_energy_sub_le_integral_le_mul omega hu hpF hpu
  change (∫ x, g x ∂μu) ≤ (energy θ φ hφ u).toReal - (energy θ φ hφ p).toReal at ha
  change (energy θ φ hφ u).toReal - (energy θ φ hφ p).toReal ≤ (∫ x, g x ∂μp) at hb
  rw [hpint] at hb
  change t * (∫ x, h x ∂μp) ≤ (energy θ φ hφ p).toReal - (energy θ φ hφ u).toReal ∧
    (energy θ φ hφ p).toReal - (energy θ φ hφ u).toReal ≤ t * (∫ x, h x ∂μu)
  constructor <;> linarith

/-- Original roofs at the canonical positive scales internally increase to
the original potential and have convergent actual continuous MA reads. -/
theorem exists_genuine_roofs_and_tendsto_integral (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : IsThetaPshPotential θ.val u) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) (q : C(M, ℝ)) :
    ∃ hp : ∀ j : ℕ, IsThetaPshPotential θ.val
        (perturbedRooftop θ u h (1 / ((j : ℝ) + 1))),
      (∀ x, Monotone fun j : ℕ => perturbedRooftop θ u h (1 / ((j : ℝ) + 1)) x) ∧
      (∀ x, (⨆ j : ℕ, perturbedRooftop θ u h (1 / ((j : ℝ) + 1)) x) = u x) ∧
      Tendsto (fun j : ℕ => ∫ x, q x ∂diagonalPotentialMeasure θ
        (perturbedRooftop θ u h (1 / ((j : ℝ) + 1))) (hp j)) atTop
        (𝓝 (∫ x, q x ∂diagonalPotentialMeasure θ u hu)) := by
  let τ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let pj : ℕ → M → EReal := fun j => perturbedRooftop θ u h (τ j)
  have hτpos : ∀ j, 0 < τ j := fun j => by dsimp [τ]; positivity
  have hτanti : Antitone τ := by
    intro j k hjk
    apply one_div_le_one_div_of_le (by positivity)
    have hjkR : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    linarith
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨L, hL0, hL⟩ := exists_abs_bound hh
  have hdata : ∀ j : ℕ, ∃ _hp : IsThetaPshPotential θ.val (pj j),
      ∀ x, pj j x ≤ u x + ((τ j * h x : ℝ) : EReal) ∧
        u x + ((τ j * h x : ℝ) : EReal) ≤ u x := by
    intro j
    obtain ⟨_Lj, _hLj0, _hLj, hp, _hlo, hb, hhg⟩ :=
      exists_genuine_rooftop_sandwich hn hbig hu hu0 (continuous_const.mul hh)
        (fun x => mul_nonpos_of_nonneg_of_nonpos (hτpos j).le (hh0 x))
    exact ⟨hp, fun x => ⟨hb x, hhg x⟩⟩
  choose hpj hbounds using hdata
  have hlo : ∀ j x, u x + ((-(τ j * L) : ℝ) : EReal) ≤ pj j x := by
    intro j
    apply le_rooftopEnvelope (hu.add_const (-(τ j * L)))
    apply quasiEverywhere_of_forall
    intro x
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    have hneg : -L ≤ h x := (abs_le.mp (hL x)).1
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left hneg (hτpos j).le
  have hm : ∀ x, Monotone fun j => pj j x := by
    intro x j k hjk
    exact rooftopEnvelope_mono (θ := θ.val)
      (fun y => add_le_add le_rfl (EReal.coe_le_coe_iff.mpr
        (mul_le_mul_of_nonpos_right (hτanti hjk) (hh0 y)))) x
  have hsup : ∀ x, (⨆ j, pj j x) = u x := by
    intro x
    refine le_antisymm (iSup_le fun j => (hbounds j x).1.trans (hbounds j x).2) ?_
    by_cases hubot : u x = ⊥
    · rw [hubot]
      exact bot_le
    let a : ℝ := (u x).toReal
    have hux : u x = (a : EReal) :=
      (EReal.coe_toReal (hu.1.quasiPlurisubharmonic.ne_top x) hubot).symm
    have hlimR : Tendsto (fun j => a - τ j * L) atTop (𝓝 a) := by
      have hc : Tendsto (fun _j : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
      simpa only [zero_mul, sub_zero] using hc.sub (hτlim.mul_const L)
    have hlimE : Tendsto (fun j => u x + ((-(τ j * L) : ℝ) : EReal)) atTop (𝓝 (u x)) := by
      rw [hux]
      have he : Tendsto (fun j => ((a - τ j * L : ℝ) : EReal)) atTop (𝓝 (a : EReal)) :=
        EReal.tendsto_coe.mpr hlimR
      simpa only [← EReal.coe_add, sub_eq_add_neg] using he
    exact le_of_tendsto hlimE (Eventually.of_forall fun j =>
      (hlo j x).trans (le_iSup (fun j => pj j x) j))
  have hsupFun : (⨆ j, pj j) = u := by
    funext x
    simpa only [iSup_apply] using hsup x
  have hreg : uscRegularization (⨆ j, pj j) = u := by
    rw [hsupFun]
    exact uscRegularization_eq hu.1.quasiPlurisubharmonic.upperSemicontinuous
  have hv : ∀ _a : Fin n, IsThetaPshPotential θ.val (uscRegularization (⨆ j, pj j)) := by
    intro a
    rw [hreg]
    exact hu
  have hread := IncreasingMixedDirectedNets.tendsto_integral_mixed_of_directed_monotone_regularized
    omega (theta := fun _ : Fin n => θ) (u := fun j _ => pj j)
    (fun j _ => hpj j) (fun _a j k hjk x => hm x hjk) hv q
  refine ⟨hpj, hm, hsup, ?_⟩
  simpa only [hreg, diagonalPotentialMeasure] using hread

/-- Actual original singular rooftops have an internally produced discrete
one-sided finite-energy variation at the canonical positive scales. -/
theorem energy_quotient_tendsto (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    Tendsto (fun j : ℕ =>
      ((energy θ φ hφ (perturbedRooftop θ u h (1 / ((j : ℝ) + 1)))).toReal -
        (energy θ φ hφ u).toReal) / (1 / ((j : ℝ) + 1))) atTop
      (𝓝 (∫ x, h x ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic)) := by
  let τ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let pj : ℕ → M → EReal := fun j => perturbedRooftop θ u h (τ j)
  have hτpos : ∀ j, 0 < τ j := fun j => by dsimp [τ]; positivity
  obtain ⟨hpj, _hm, _hsup, hread⟩ := exists_genuine_roofs_and_tendsto_integral
    omega hn hbig hu.1.plurisubharmonic hu0 hh hh0 (⟨h, hh⟩ : C(M, ℝ))
  have hslopes : ∀ j,
      τ j * (∫ x, h x ∂diagonalPotentialMeasure θ (pj j) (hpj j)) ≤
        (energy θ φ hφ (pj j)).toReal - (energy θ φ hφ u).toReal ∧
      (energy θ φ hφ (pj j)).toReal - (energy θ φ hφ u).toReal ≤
        τ j * (∫ x, h x ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) :=
    fun j => energy_slope_bounds omega hn hbig hu hu0 hh hh0 (t := τ j) (hτpos j).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hread tendsto_const_nhds
    (fun j => (le_div_iff₀ (hτpos j)).mpr (by
      change (∫ x, h x ∂diagonalPotentialMeasure θ (pj j) (hpj j)) * τ j ≤
        (energy θ φ hφ (pj j)).toReal - (energy θ φ hφ u).toReal
      simpa only [mul_comm] using (hslopes j).1))
    (fun j => (div_le_iff₀ (hτpos j)).mpr (by
      change (energy θ φ hφ (pj j)).toReal - (energy θ φ hφ u).toReal ≤
        (∫ x, h x ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) * τ j
      simpa only [mul_comm] using (hslopes j).2))

end

end SGPT.Foundations.Analysis.Pending.ActualContinuousObstacleDiscreteEnergyVariation
