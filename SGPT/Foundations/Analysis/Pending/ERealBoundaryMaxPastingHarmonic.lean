import SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingMaximum
import SGPT.Foundations.Analysis.FirstPass.HarmonicDiscPsh

set_option autoImplicit false

/-! # Genuine harmonic comparison for actual extended-real boundary maximum pasting -/

open Metric Set Filter InnerProductSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingHarmonic

open ERealBoundaryMaxPastingTopology ERealBoundaryMaxPastingMaximum

noncomputable section

/-- Subtracting the same actual finite real function commutes with the actual maximum pasting. -/
theorem gluedMax_sub_coe (D : Set ℂ) (v u : ℂ → EReal) (h : ℂ → ℝ) :
    (fun z => gluedMax D v u z - (h z : EReal)) =
      gluedMax D (fun z => v z - (h z : EReal)) (fun z => u z - (h z : EReal)) := by
  funext z
  by_cases hzD : z ∈ D
  · rw [gluedMax_eq_max hzD, gluedMax_eq_max hzD]
    rcases le_total (v z) (u z) with hvu | huv
    · rw [max_eq_right hvu, max_eq_right (EReal.sub_le_sub hvu le_rfl)]
    · rw [max_eq_left huv, max_eq_left (EReal.sub_le_sub huv le_rfl)]
  · simp [gluedMax, hzD]

/-- Actual boundary upper limits and genuine PSH branches produce harmonic comparison of the actual pasted maximum. -/
theorem gluedMax_le_harmonic_on_closedBall
    {Ω D : Set ℂ} {v u : ℂ → EReal} (hD : IsOpen D)
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v D)
    (hboundary : BoundaryDominatedOn Ω D v u)
    {h : ℂ → ℝ} (hh : HarmonicOnNhd h univ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hKΩ : closedBall c R ⊆ Ω)
    (hs : ∀ z ∈ sphere c R, gluedMax D v u z ≤ (h z : EReal)) :
    ∀ z ∈ closedBall c R, gluedMax D v u z ≤ (h z : EReal) := by
  let G : ℂ → EReal := gluedMax D v u
  have hGusc : UpperSemicontinuousOn G Ω :=
    upperSemicontinuousOn_gluedMax hD hu.upperSemicontinuousOn hv.upperSemicontinuousOn hboundary
  have hGtop : ∀ z ∈ Ω, G z ≠ ⊤ :=
    gluedMax_ne_top (fun z hz => (hu z hz).ne_top) (fun z hz => (hv z hz).ne_top)
  have hneg : Continuous (fun z => ((-h z : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (continuousOn_univ.mp hh.continuousOn).neg
  have hGsubusc : UpperSemicontinuousOn (fun z => G z - (h z : EReal)) (closedBall c R) := by
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
      (hGusc.mono hKΩ).add' (hneg.continuousOn.upperSemicontinuousOn)
        (fun z _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-h z)))
          (Or.inr (EReal.coe_ne_top (-h z))))
  have hGsubtop : ∀ z ∈ closedBall c R, G z - (h z : EReal) ≠ ⊤ := by
    intro z hz
    simpa only [sub_eq_add_neg, ← EReal.coe_neg] using
      EReal.add_ne_top (hGtop z (hKΩ hz)) (EReal.coe_ne_top (-h z))
  have hsubu : PlurisubharmonicOn (fun z => u z - (h z : EReal)) Ω :=
    hu.sub_harmonic (hh.mono (subset_univ Ω))
  have hsubv : PlurisubharmonicOn (fun z => v z - (h z : EReal)) D :=
    hv.sub_harmonic (hh.mono (subset_univ D))
  have hsbase : ∀ z ∈ sphere c R, u z - (h z : EReal) ≤ (0 : EReal) := by
    intro z hz
    apply EReal.sub_nonpos.mpr
    have huG : u z ≤ G z := by
      by_cases hzD : z ∈ D
      · exact (le_max_right _ _).trans_eq (gluedMax_eq_max hzD).symm
      · simp [G, gluedMax, hzD]
    exact huG.trans (hs z hz)
  have hbase : ∀ z ∈ closedBall c R, u z - (h z : EReal) ≤ (0 : EReal) :=
    hsubu.le_const_on_closedBall_of_le_on_sphere hR hKΩ (by simpa only [EReal.coe_zero] using hsbase)
  have hsub : (fun z => G z - (h z : EReal)) =
      gluedMax D (fun z => v z - (h z : EReal)) (fun z => u z - (h z : EReal)) :=
    gluedMax_sub_coe D v u h
  have hsub_apply (z : ℂ) : G z - (h z : EReal) =
      gluedMax D (fun z => v z - (h z : EReal)) (fun z => u z - (h z : EReal)) z :=
    congrFun hsub z
  have hcorrect : ∀ z ∈ closedBall c R, G z - (h z : EReal) ≤ (0 : EReal) := by
    rw [hsub] at hGsubusc
    simp_rw [hsub_apply] at hGsubtop ⊢
    apply gluedMax_le_const_on_closedBall hD hsubv hR hGsubusc hGsubtop
    · simpa only [EReal.coe_zero] using hbase
    · intro z hz
      rw [← hsub_apply z]
      simpa only [EReal.coe_zero] using EReal.sub_nonpos.mpr (hs z hz)
  intro z hz
  exact EReal.sub_nonpos.mp (hcorrect z hz)

end

end SGPT.Foundations.Analysis.Pending.ERealBoundaryMaxPastingHarmonic
