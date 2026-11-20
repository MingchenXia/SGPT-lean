import SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityDomination
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.CapacityWeightedConvergence

set_option autoImplicit false

/-! # Actual capacity comparison on a locally lower-bounded reference locus

Independent truncation input for Xia's bounded-obstacle argument, PDF 0082.
Actual semipositive enlargement, strict max locality, and bounded mixed
capacity domination retain an unbounded reference outside the given locus.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualLocallyBoundedReferenceCapacity

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalMaxLocality
  ThetaCapacity CapacityWeightedConvergence DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- A reference bounded below only on the given locus produces an actual
finite domination constant, uniformly over all genuine capacity competitors. -/
theorem exists_capacity_bound (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {V : M → EReal} (hV0 : ∀ x, V x ≤ 0)
    {Ω : Set M} {c : ℝ} (hc : ∀ x ∈ Ω, (c : EReal) ≤ V x) :
    ∃ K : ℝ, 0 < K ∧ ∀ E : Set M, E ⊆ Ω →
      thetaCapacity θ V E ≤ ENNReal.ofReal K *
        thetaCapacity omega.form (fun _ => 0) E := by
  classical
  obtain ⟨A, hA, hα⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega θ
  let σ : ClosedRealOneOneForm n M := A • omega.form
  let α : ClosedRealOneOneForm n M := θ + σ
  have hσ : σ.val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omega.isSemipositive hA.le
  let B : ℝ := |c| + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨K, hK, hdom⟩ :=
    ActualBoundedMixedCapacityDomination.exists_uniform_capacity_bound omega
      (fun _ : Fin n => α) B hB
  refine ⟨K, hK, fun E hE => thetaCapacity_le_of_forall fun u hu huV hVu => ?_⟩
  have hu0 : ∀ x, u x ≤ 0 := fun x => (huV x).trans (hV0 x)
  have huα : IsThetaPshPotential α.val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu hσ
  let w : M → EReal := fun _ => ((-B : ℝ) : EReal)
  have hw : IsThetaPshPotential α.val w := by
    simpa only [w, zero_sub, EReal.coe_neg] using
      ((LocalPotentials.isThetaPshPotential_zero_iff α).mpr hα).sub_const B
  let q : M → EReal := fun x => max (u x) (w x)
  have hq : IsThetaPshPotential α.val q := IsThetaPshPotential.max huα hw
  have hqB : ∀ (i : Fin n) x, ((-B : ℝ) : EReal) ≤ q x ∧ q x ≤ (B : EReal) := by
    intro _ x
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · exact (hu0 x).trans (EReal.coe_nonneg.mpr hB)
    · exact EReal.coe_le_coe_iff.mpr (by linarith)
  let S : Set M := {x | ∀ _i : Fin n, w x < u x}
  have hS : MeasurableSet S := measurableSet_forall_lt
    (fun _ : Fin n => huα.1) (fun _ => hw.1)
  have hES : E ⊆ S := by
    intro x hx _i
    have hl : (c : EReal) ≤ u x + 1 := (hc x (hE hx)).trans (hVu x)
    have hb : -B + 1 < c := by dsimp [B]; linarith [neg_abs_le c]
    by_contra hn
    have hn' : u x ≤ ((-B : ℝ) : EReal) := not_lt.mp hn
    have hh : (c : EReal) ≤ ((-B + 1 : ℝ) : EReal) := by
      calc (c : EReal) ≤ u x + 1 := hl
        _ ≤ ((-B : ℝ) : EReal) + 1 := add_le_add hn' le_rfl
        _ = ((-B + 1 : ℝ) : EReal) := by rw [EReal.coe_add, EReal.coe_one]
    exact (not_le.mpr hb) (EReal.coe_le_coe_iff.mp hh)
  have hloc := congrArg (fun μ : Measure M => μ E)
    (globalMixedMeasure_restrict_max_eq
      (fun _ : Fin n => huα.1) (fun _ => hw.1) (fun _ => hq.1))
  rw [Measure.restrict_apply' hS, Measure.restrict_apply' hS,
    inter_eq_self_of_subset_left hES] at hloc
  have hmono := TraceFreeLimit.globalMixedMeasure_le_of_add_semipositive
    (fun _ : Fin n => hσ) (fun _ => hu) (fun _ => huα.1)
  calc diagonalPotentialMeasure θ u hu E
      ≤ globalMixedMeasure (fun _ : Fin n => α) (fun _ => u) (fun _ => huα.1) E :=
        hmono E
    _ = globalMixedMeasure (fun _ : Fin n => α) (fun _ => q) (fun _ => hq.1) E :=
        hloc.symm
    _ ≤ ENNReal.ofReal K * thetaCapacity omega.form (fun _ => 0) E :=
        hdom (fun _ => q) (fun _ => hq) hqB E

/-- Original Kähler-capacity quasicontinuity transfers internally to every
open locus on which the nonpositive reference has a finite lower bound. -/
theorem exists_isOpen_capacity_lt_continuousOn (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {V : M → EReal} (hV0 : ∀ x, V x ≤ 0)
    {Ω : Set M} (hΩ : IsOpen Ω) {c : ℝ} (hc : ∀ x ∈ Ω, (c : EReal) ≤ V x)
    {F : M → ℝ}
    (hF : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Set M, IsOpen G ∧ G ⊆ Ω ∧ thetaCapacity θ V G < ENNReal.ofReal ε ∧
      ContinuousOn F (Ω \ G) := by
  obtain ⟨K, hK, hdom⟩ := exists_capacity_bound omega θ hV0 hc
  have he : 0 < ε / K := div_pos hε hK
  obtain ⟨H, hHo, hHc, hFc⟩ := hF (ENNReal.ofReal (ε / K)) (ENNReal.ofReal_pos.mpr he)
  refine ⟨H ∩ Ω, hHo.inter hΩ, inter_subset_right, ?_, ?_⟩
  · calc thetaCapacity θ V (H ∩ Ω)
        ≤ ENNReal.ofReal K * thetaCapacity omega.form (fun _ => 0) (H ∩ Ω) :=
          hdom _ inter_subset_right
      _ ≤ ENNReal.ofReal K * thetaCapacity omega.form (fun _ => 0) H :=
          mul_le_mul_of_nonneg_left (thetaCapacity_mono inter_subset_left) zero_le
      _ < ENNReal.ofReal K * ENNReal.ofReal (ε / K) :=
          by simpa only [mul_comm] using
            ENNReal.mul_lt_mul_left (ne_of_gt (ENNReal.ofReal_pos.mpr hK))
              ENNReal.ofReal_ne_top hHc
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul hK.le, mul_div_cancel₀ _ hK.ne']
  · exact hFc.mono fun x hx hxH => hx.2 ⟨hxH, hx.1⟩

end
end SGPT.Foundations.Analysis.Pending.ActualLocallyBoundedReferenceCapacity
