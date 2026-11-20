import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingTopology
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum

set_option autoImplicit false

/-! # A genuine supported maximum principle for actual boundary maximum pasting -/

open Metric Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingMaximum

noncomputable section

/-- A positive pasted maximum is forced onto the actual PSH branch, and its genuine strong maximum principle rules it out. -/
theorem gluedMax_le_const_on_closedBall
    {D : Set ℂ} {v u : ℂ → EReal} (hD : IsOpen D)
    (hv : PlurisubharmonicOn v D)
    {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hGusc : UpperSemicontinuousOn (gluedMax D v u) (closedBall c R))
    (hGtop : ∀ z ∈ closedBall c R, gluedMax D v u z ≠ ⊤)
    (hu : ∀ z ∈ closedBall c R, u z ≤ (C : EReal))
    (hs : ∀ z ∈ sphere c R, gluedMax D v u z ≤ (C : EReal)) :
    ∀ z ∈ closedBall c R, gluedMax D v u z ≤ (C : EReal) := by
  let G : ℂ → EReal := gluedMax D v u
  intro q hq
  by_contra hqC
  have hCq : (C : EReal) < G q := lt_of_not_ge hqC
  obtain ⟨y, hyD, hmax⟩ := hGusc.exists_isMaxOn ⟨q, hq⟩ (isCompact_closedBall c R)
  have hy_top : G y ≠ ⊤ := hGtop y hyD
  have hy_bot : G y ≠ ⊥ := by
    have hy_gt : (C : EReal) < G y := hCq.trans_le (hmax hq)
    intro hy
    rw [hy] at hy_gt
    exact (not_lt_of_ge bot_le) hy_gt
  let B : ℝ := (G y).toReal
  have hyB : G y = (B : EReal) := (EReal.coe_toReal hy_top hy_bot).symm
  have hCB : C < B := by
    rw [← EReal.coe_lt_coe_iff, ← hyB]
    exact hCq.trans_le (hmax hq)
  have hmaxmem : ∀ z ∈ closedBall c R, G z = (B : EReal) →
      z ∈ D ∧ z ∈ ball c R ∧ v z = (B : EReal) := by
    intro z hz hzB
    have hult : u z < (B : EReal) :=
      (hu z hz).trans_lt (EReal.coe_lt_coe_iff.mpr hCB)
    have hzD : z ∈ D := by
      by_contra hzD
      have hGu : G z = u z := by simp [G, gluedMax, hzD]
      have hGlt : G z < (B : EReal) := by rw [hGu]; exact hult
      rw [hzB] at hGlt
      exact (lt_irrefl (B : EReal)) hGlt
    have hzball : z ∈ ball c R := by
      have hzr : dist z c ≤ R := mem_closedBall.mp hz
      apply mem_ball.mpr
      apply lt_of_le_of_ne hzr
      intro hzr_eq
      have hzs : z ∈ sphere c R := mem_sphere.mpr hzr_eq
      have hzC := hs z hzs
      change G z ≤ (C : EReal) at hzC
      rw [hzB, EReal.coe_le_coe_iff] at hzC
      exact (not_lt_of_ge hzC) hCB
    have hzmax : max (v z) (u z) = (B : EReal) := by
      simpa only [G, gluedMax_eq_max hzD] using hzB
    have hvB : v z = (B : EReal) := by
      apply le_antisymm ((le_max_left _ _).trans_eq hzmax)
      apply le_of_not_gt
      intro hvlt
      have hm : max (v z) (u z) < (B : EReal) := max_lt hvlt hult
      rw [hzmax] at hm
      exact (lt_irrefl _) hm
    exact ⟨hzD, hzball, hvB⟩
  let O : Set ℂ := {z | z ∈ ball c R ∧ G z = (B : EReal)}
  have hO : IsOpen O := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨hzD, _, hvz⟩ := hmaxmem z (ball_subset_closedBall hz.1) hz.2
    obtain ⟨W, hW, hzW, hdisc⟩ := hv z hzD
    have hopen : IsOpen (W ∩ D ∩ ball c R) := (hW.inter hD).inter isOpen_ball
    have hzopen : z ∈ W ∩ D ∩ ball c R := ⟨⟨hzW, hzD⟩, hz.1⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen z hzopen
    have hBW : ball z δ ⊆ W := fun w hw => (hball hw).1.1
    have hBbound : ∀ w ∈ ball z δ, v w ≤ (B : EReal) := by
      intro w hw
      have hwD := (hball hw).1.2
      have hwK := ball_subset_closedBall (hball hw).2
      calc
        v w ≤ max (v w) (u w) := le_max_left _ _
        _ = G w := (gluedMax_eq_max hwD).symm
        _ ≤ (B : EReal) := (hmax hwK).trans_eq hyB
    have heq := hdisc.eqOn_ball_of_le_of_eq z hBW hBbound hvz
    refine ⟨δ, hδ, ?_⟩
    intro w hw
    have hwD := (hball hw).1.2
    have hwK := ball_subset_closedBall (hball hw).2
    refine ⟨(hball hw).2, ?_⟩
    apply le_antisymm ((hmax hwK).trans_eq hyB)
    calc
      (B : EReal) = v w := (heq hw).symm
      _ ≤ max (v w) (u w) := le_max_left _ _
      _ = G w := (gluedMax_eq_max hwD).symm
  have hK : IsCompact (closedBall c R ∩ G ⁻¹' Ici (B : EReal)) :=
    hGusc.isCompact_inter_preimage_Ici (isCompact_closedBall c R) (B : EReal)
  have hOK : O ⊆ closedBall c R ∩ G ⁻¹' Ici (B : EReal) := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, by simp [hz.2]⟩
  have hclosure : closure O ∩ closedBall c R ⊆ O := by
    intro z hz
    have hzK := closure_minimal hOK hK.isClosed hz.1
    have hzeq : G z = (B : EReal) :=
      le_antisymm ((hmax hz.2).trans_eq hyB) hzK.2
    exact ⟨(hmaxmem z hz.2 hzeq).2.1, hzeq⟩
  have hnonempty : (closedBall c R ∩ O).Nonempty :=
    ⟨y, hyD, (hmaxmem y hyD hyB).2.1, hyB⟩
  have hall : closedBall c R ⊆ O :=
    isPreconnected_closedBall.subset_of_closure_inter_subset hO hnonempty hclosure
  let z : ℂ := c + (R : ℂ)
  have hzs : z ∈ sphere c R := by simp [z, abs_of_pos hR]
  have hzO := hall (sphere_subset_closedBall hzs)
  exact (not_lt_of_ge (by
    have hzC := hs z hzs
    change G z ≤ (C : EReal) at hzC
    rw [hzO.2, EReal.coe_le_coe_iff] at hzC
    exact hzC)) hCB

end

end SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingMaximum
