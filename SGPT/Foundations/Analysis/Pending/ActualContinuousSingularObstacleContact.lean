import SGPT.Foundations.Analysis.Pending.RooftopTruncationConcentration
import SGPT.Foundations.Analysis.Pending.RooftopTruncatedObstacleConcentration
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationContinuous

set_option autoImplicit false

/-! # Actual continuous perturbations of original singular obstacles

DDL survey arXiv2303.11584v2 Proposition 5.12: genuine obstacle contact
prerequisites, not energy variation or prescribed-type MA existence.
Complete mathematical blueprint was captured before this SOURCE.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualContinuousSingularObstacleContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass ThetaCapacity PatchLocalBoundedMeasure
  ThetaCapacityLocalQuasiContinuity RooftopTruncationConcentration
  RooftopTruncatedObstacleConcentration RooftopUscObstacleApproximation

noncomputable section

private theorem exists_abs_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {h : X → ℝ} (hh : Continuous h) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, |h x| ≤ L := by
  obtain ⟨B, hB⟩ := (isCompact_range hh.abs).bddAbove
  exact ⟨max B 0, le_max_right _ _, fun x =>
    (hB ⟨x, rfl⟩).trans (le_max_left _ _)⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- All reference truncations of an actual continuous perturbation of the
original genuine singular potential are internally quasi-continuous. -/
theorem refTruncationsQuasiContinuous_add_continuous
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {h : M → ℝ}
    (hu : IsThetaPshPotential θ.val u) (hu0 : ∀ x, u x ≤ 0)
    (hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val)) (hh : Continuous h) :
    RefTruncationsQuasiContinuous θ (fun x => u x + (h x : EReal)) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_bound hh
  intro C hC Ω hΩ hVb K hK hKΩ η hη
  let V : M → EReal := thetaPshSupremum θ.val
  let D : ℝ := C + L
  let U : M → EReal := fun x => max (u x) (V x + ((-D : ℝ) : EReal))
  have hD0 : 0 ≤ D := add_nonneg hC hL0
  have hU : IsThetaPshPotential θ.val U :=
    IsThetaPshPotential.max hu (hV.add_const (-D))
  have hUb : IsBoundedPotentialOn U Ω :=
    isBoundedPotentialOn_max_reference hu0 hD0 hVb
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨G1, hG1o, hG1c, hG1cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn
      hU hΩ hUb hVb hK hKΩ hη3
  obtain ⟨G2, hG2o, hG2c, hG2cont⟩ :=
    exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn
      hV hΩ hVb hVb hK hKΩ hη3
  refine ⟨G1 ∪ G2, hG1o.union hG2o, ?_, ?_⟩
  · have hc : thetaCapacity θ V (G1 ∪ G2) ≤
        ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3) :=
      (thetaCapacity_union_le θ V G1 G2).trans (add_le_add hG1c.le hG2c.le)
    refine hc.trans_lt ?_
    rw [← ENNReal.ofReal_add hη3.le hη3.le]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith)
  · have hc1 : ContinuousOn (fun y => (U y).toReal) (K \ (G1 ∪ G2)) :=
      hG1cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
    have hc2 : ContinuousOn (fun y => (V y).toReal) (K \ (G1 ∪ G2)) :=
      hG2cont.mono fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
    have hcont : ContinuousOn (fun y =>
        max ((U y).toReal + h y) ((V y).toReal - C)) (K \ (G1 ∪ G2)) :=
      ContinuousOn.sup (hc1.add hh.continuousOn) (hc2.sub continuousOn_const)
    refine hcont.congr fun y hy => ?_
    have hyΩ : y ∈ Ω := hKΩ hy.1
    obtain ⟨aV, bV, hVbd⟩ := hVb
    obtain ⟨aU, bU, hUbd⟩ := hUb
    have hVbot : V y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot aV) (hVbd y hyΩ).1
    have hVtop : V y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top bV) (hVbd y hyΩ).2
    have hUbot : U y ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot aU) (hUbd y hyΩ).1
    have hUtop : U y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top bU) (hUbd y hyΩ).2
    have hsmall : V y + ((-D : ℝ) : EReal) + (h y : EReal) ≤
        V y + ((-C : ℝ) : EReal) := by
      rw [add_assoc, ← EReal.coe_add]
      refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
      have hhL := (le_abs_self (h y)).trans (hL y)
      dsimp [D]
      linarith
    have hmap : U y + (h y : EReal) =
        max (u y + (h y : EReal))
          (V y + ((-D : ℝ) : EReal) + (h y : EReal)) :=
      (Monotone.map_max (f := fun z : EReal => z + (h y : EReal))
        (fun _ _ hz => add_le_add hz le_rfl))
    have hid : refTrunc θ (fun x => u x + (h x : EReal)) C y =
        max (U y + (h y : EReal)) (V y + ((-C : ℝ) : EReal)) := by
      rw [hmap, max_assoc, max_eq_right hsmall]
      rfl
    have hVs : V y + ((-C : ℝ) : EReal) = (((V y).toReal - C : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hVtop hVbot, ← EReal.coe_add,
        EReal.toReal_coe, sub_eq_add_neg]
    have hcm : ∀ a b : ℝ, max (a : EReal) (b : EReal) = ((max a b : ℝ) : EReal) :=
      fun a b => (EReal.coe_strictMono.monotone.map_max).symm
    rw [hid, ← EReal.coe_toReal hUtop hUbot, hVs, ← EReal.coe_add, hcm,
      EReal.toReal_coe]

variable [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual normalized continuously perturbed singular obstacle has its
genuine roof and complete original pointwise singularity sandwich produced. -/
theorem exists_genuine_rooftop_sandwich (hn : 0 < n)
    {θ : ClosedRealOneOneForm n M}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} {h : M → ℝ}
    (hu : IsThetaPshPotential θ.val u) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ x, |h x| ≤ L) ∧
      ∃ _hp : IsThetaPshPotential θ.val
        (rooftopEnvelope θ.val (fun x => u x + (h x : EReal))),
      (∀ x, u x + ((-L : ℝ) : EReal) ≤
        rooftopEnvelope θ.val (fun y => u y + (h y : EReal)) x) ∧
      (∀ x, rooftopEnvelope θ.val (fun y => u y + (h y : EReal)) x ≤
        u x + (h x : EReal)) ∧
      (∀ x, u x + (h x : EReal) ≤ u x) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_bound hh
  have hlow : ∀ x, u x + ((-L : ℝ) : EReal) ≤ u x + (h x : EReal) := by
    intro x
    refine add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_)
    exact (abs_le.mp (hL x)).1
  have hhigh : ∀ x, u x + (h x : EReal) ≤ u x := by
    intro x
    simpa only [add_zero] using add_le_add (le_refl (u x))
      (EReal.coe_nonpos.mpr (hh0 x))
  have hf : UpperSemicontinuous (fun x => u x + (h x : EReal)) :=
    upperSemicontinuous_add_coe_continuous
      hu.1.quasiPlurisubharmonic.upperSemicontinuous hh
  have htop : ∀ x, u x + (h x : EReal) ≠ ⊤ :=
    fun x => ne_top_of_le_ne_top (by simp) ((hhigh x).trans (hu0 x))
  have hcomp := mem_rooftopCompetitors_of_le (hu.add_const (-L)) hlow
  have hp := isThetaPshPotential_rooftopEnvelope_of_upperSemicontinuous
    hn θ hbig hf htop ⟨_, hcomp⟩
  exact ⟨L, hL0, hL, hp,
    le_rooftopEnvelope (hu.add_const (-L)) hcomp.2,
    rooftopEnvelope_le_of_upperSemicontinuous hn θ hbig hf htop, hhigh⟩

/-- Whole actual NP Monge--Ampere contact for the original singular obstacle
`u+h`, with all genuine-envelope and reference-QC inputs internally produced. -/
theorem exists_genuine_rooftop_and_contact (hn : 0 < n)
    {θ : ClosedRealOneOneForm n M}
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} {h : M → ℝ}
    (hu : IsThetaPshPotential θ.val u) (hu0 : ∀ x, u x ≤ 0)
    (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    ∃ hp : IsThetaPshPotential θ.val
        (rooftopEnvelope θ.val (fun x => u x + (h x : EReal))),
      diagonalPotentialMeasure θ
        (rooftopEnvelope θ.val (fun x => u x + (h x : EReal))) hp
        {x | rooftopEnvelope θ.val (fun y => u y + (h y : EReal)) x <
          u x + (h x : EReal)} = 0 := by
  obtain ⟨L, hL0, hL, hp, hlo, hbelow, hhigh⟩ :=
    exists_genuine_rooftop_sandwich hn hbig hu hu0 hh hh0
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential θ.val
      θ.2.1 θ.2.2 hu.1.hasSmoothLocalPotentials ⟨_, hu⟩
  refine ⟨hp, diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_nonpos
    hn hbig hV ?_ (fun x => (hhigh x).trans (hu0 x))
    (refTruncationsQuasiContinuous_add_continuous hu hu0 hV hh) hp⟩
  exact upperSemicontinuous_add_coe_continuous
    hu.1.quasiPlurisubharmonic.upperSemicontinuous hh

end

end SGPT.Foundations.Analysis.Pending.ActualContinuousSingularObstacleContact
