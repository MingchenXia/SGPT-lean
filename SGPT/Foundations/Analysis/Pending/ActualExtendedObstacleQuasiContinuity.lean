import SGPT.Foundations.Analysis.Pending.ActualLocallyBoundedReferenceCapacity
import SGPT.Foundations.Analysis.Pending.ThetaCapacityMinQuasiContinuity
import SGPT.Foundations.Analysis.Pending.RooftopTruncationReference
import SGPT.Foundations.Analysis.Pending.MinimalSingularityLelongVanishing

set_option autoImplicit false

/-! # Original extended-real quasi-continuity and actual finite truncations

Xia, PDF 0079--0081. Finite clamping precedes realification at infinite
values. The original Kähler-capacity obstacle internally supplies the
reference-truncation quasi-continuity on locally bounded reference loci.
Contact concentration of unbounded obstacles is a subsequent consumer.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleQuasiContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  CapacityWeightedConvergence ThetaCapacity PatchLocalBoundedMeasure
  ThetaCapacityLocalQuasiContinuity ThetaCapacityMinQuasiContinuity
  RooftopTruncationConcentration

noncomputable section

/-- Original extended-real quasi-continuity, using the order topology and
without a measurability assumption on the original obstacle. -/
def QuasiContinuousERealFor {X : Type*} [TopologicalSpace X]
    (cap : Set X → ℝ≥0∞) (f : X → EReal) : Prop :=
  ∀ η : ℝ≥0∞, 0 < η → ∃ G : Set X, IsOpen G ∧ cap G < η ∧
    ContinuousOn f Gᶜ

private theorem continuous_clamp {a b : ℝ} (hab : a ≤ b) :
    Continuous (fun z : EReal => (max (min z (b : EReal)) (a : EReal)).toReal) := by
  have hκ : Continuous (fun z : EReal => max (min z (b : EReal)) (a : EReal)) :=
    (continuous_id.inf continuous_const).sup continuous_const
  refine continuous_iff_continuousAt.mpr fun z => ?_
  have hl : (a : EReal) ≤ max (min z (b : EReal)) (a : EReal) := le_max_right _ _
  have hu : max (min z (b : EReal)) (a : EReal) ≤ (b : EReal) :=
    max_le (min_le_right _ _) (EReal.coe_le_coe_iff.mpr hab)
  exact (EReal.tendsto_toReal (ne_of_lt (hu.trans_lt (EReal.coe_lt_top b)))
    (ne_of_gt ((EReal.bot_lt_coe a).trans_le hl))).comp hκ.continuousAt

/-- Every finite clamp of an original extended-real quasicontinuous obstacle
is genuinely real quasicontinuous, including at its infinite values. -/
theorem quasiContinuousFor_clamp {X : Type*} [TopologicalSpace X]
    {cap : Set X → ℝ≥0∞} {f : X → EReal} {a b : ℝ} (hab : a ≤ b)
    (hf : QuasiContinuousERealFor cap f) :
    QuasiContinuousFor cap (fun x => (max (min (f x) (b : EReal)) (a : EReal)).toReal) := by
  intro η hη
  obtain ⟨G, hGo, hGc, hfc⟩ := hf η hη
  exact ⟨G, hGo, hGc, (continuous_clamp hab).comp_continuousOn hfc⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The original nonpositive extended-real obstacle internally gives every
local reference-truncation quasi-continuity assertion, without a global
bound on the reference or measurability of the obstacle. -/
theorem refTruncationsQuasiContinuous_of_original (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {f : M → EReal} (hf0 : ∀ x, f x ≤ 0)
    (hf : QuasiContinuousERealFor (thetaCapacity omega.form (fun _ => 0)) f) :
    RefTruncationsQuasiContinuous θ f := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hM =>
    intro C hC Ω hΩ hVb K hK hKO ε hε
    refine ⟨∅, isOpen_empty, ?_, ?_⟩
    · simpa only [thetaCapacity_empty] using ENNReal.ofReal_pos.mpr hε
    · exact fun x _ => isEmptyElim x
  | inr hM =>
    have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
    intro C _hC Ω hΩ hVb K hK hKO ε hε
    obtain ⟨c, d, hVbd⟩ := hVb
    let a : ℝ := min (c - C) 0
    let w : M → EReal := fun x => max (f x) (a : EReal)
    let q : M → EReal := fun x => thetaPshSupremum θ.val x + ((-C : ℝ) : EReal)
    have ha0 : a ≤ 0 := min_le_right _ _
    have hwQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0))
        (fun x => (w x).toReal) := by
      have ht := quasiContinuousFor_clamp ha0 hf
      simpa only [EReal.coe_zero, min_eq_left (hf0 _)] using ht
    have hq : IsThetaPshPotential θ.val q := hV.add_const (-C)
    have hqb : IsBoundedPotentialOn q Ω := by
      refine ⟨c - C, d - C, fun x hx => ?_⟩
      constructor
      · simpa only [q, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using
          add_le_add (hVbd x hx).1 (le_refl (((-C : ℝ) : EReal)))
      · simpa only [q, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using
          add_le_add (hVbd x hx).2 (le_refl (((-C : ℝ) : EReal)))
    have hwa : ∀ x ∈ Ω, (a : EReal) ≤ q x := fun x hx =>
      (EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans
        (by simpa only [q, sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using
          add_le_add (hVbd x hx).1 (le_refl (((-C : ℝ) : EReal))))
    have hwfin : ∀ x, w x ≠ ⊥ ∧ w x ≠ ⊤ := by
      intro x
      exact ⟨ne_of_gt ((EReal.bot_lt_coe a).trans_le (le_max_right _ _)),
        ne_of_lt ((max_le (hf0 x) (EReal.coe_nonpos.mpr ha0)).trans_lt
          (by norm_num : (0 : EReal) < ⊤))⟩
    have hpQC : ∀ δ : ℝ, 0 < δ → ∃ G : Set M, IsOpen G ∧
        thetaCapacity θ (thetaPshSupremum θ.val) G < ENNReal.ofReal δ ∧
        ContinuousOn (fun x => (w x).toReal) (K \ G) := by
      intro δ hδ
      obtain ⟨G, hGo, _hGΩ, hGc, hcont⟩ :=
        ActualLocallyBoundedReferenceCapacity.exists_isOpen_capacity_lt_continuousOn
          omega θ (thetaPshSupremum_le_zero θ.val) hΩ
          (fun x hx => (hVbd x hx).1) hwQC hδ
      exact ⟨G, hGo, hGc, hcont.mono fun x hx => ⟨hKO hx.1, hx.2⟩⟩
    have hqQC : ∀ δ : ℝ, 0 < δ → ∃ G : Set M, IsOpen G ∧
        thetaCapacity θ (thetaPshSupremum θ.val) G < ENNReal.ofReal δ ∧
        ContinuousOn (fun x => (q x).toReal) (K \ G) := by
      intro δ hδ
      exact exists_isOpen_thetaCapacity_lt_continuousOn_of_boundedOn hq hΩ hqb
        ⟨c, d, hVbd⟩ hK hKO hδ
    obtain ⟨G, hGo, hGc, hwc, hqc⟩ :=
      exists_isOpen_thetaCapacity_lt_continuousOn_pair hpQC hqQC hε
    refine ⟨G, hGo, hGc, ?_⟩
    have heq : ∀ x ∈ K \ G, (refTrunc θ f C x).toReal =
        max ((w x).toReal) ((q x).toReal) := by
      intro x hx
      have hΩx := hKO hx.1
      have hlattice : refTrunc θ f C x = max (w x) (q x) := by
        change max (f x) (q x) = max (max (f x) (a : EReal)) (q x)
        rw [max_assoc, max_eq_right (hwa x hΩx)]
      rw [hlattice]
      obtain ⟨hwb, hwt⟩ := hwfin x
      have hqb' := hqb.ne_bot hΩx
      have hqt' := hqb.ne_top hΩx
      rcases le_total (w x) (q x) with h | h
      · rw [max_eq_right h, max_eq_right (EReal.toReal_le_toReal h hwb hqt')]
      · rw [max_eq_left h, max_eq_left (EReal.toReal_le_toReal h hqb' hwt)]
    exact ((hwc.sup hqc).congr heq)

end
end SGPT.Foundations.Analysis.Pending.ActualExtendedObstacleQuasiContinuity
