import SGPT.Okounkov.TranscendentalLiftingExtension
import SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact
import SGPT.Envelopes.DNTRegQuasiPsh

/-!
# Envelopes of continuous obstacles commute with pullback along a modification

Lane DN2, `thm:DNT23_C11bar` (modification package of FPT `thm:big-metric-laplacian-rooftop`,
`chapters/inputs/q10-big-envelope-regularity.tex`, "passage to a modification"): for an analytic
modification `π : Y → X` from a compact complex manifold and a continuous real obstacle `F`,

  `P_θ(F) ∘ π = P_{π^*θ}(F ∘ π)`

as soon as `P_θ(F)` is a `θ`-psh potential with nonempty competitor family (e.g. `{θ}` big,
`isThetaPshPotential_rooftopEnvelope_of_continuous`).  Proof: pullback and descent of `θ`-psh
potentials (`thetaPsh_pullback_bijOn`, DRWNXZ Lemma 2.1), competitors of a continuous obstacle lie
below it everywhere, surjectivity of `π`, and the upper semicontinuity of `P_θ(F) ∘ π`.

`envelope_pullback_data` packages the three hypotheses on the envelope consumed by
`hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing` on the modification, and
`neg_comp_isThetaPshPotential_of_hasBoundedComplexHessian` its obstacle hypothesis (`-f` quasi-psh
for `f = g ∘ π`, `g` with bounded complex Hessian; FPT's "bounded Hessian of `f ∘ π`" is not needed
in this form).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.ContinuousObstacleEnvelopeContact

universe u

section Competitors

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A competitor of a continuous real obstacle lies below the obstacle everywhere. -/
theorem competitor_le_of_continuous {θ : SmoothRealForm n M 2} {F : M → ℝ} (hF : Continuous F)
    {g : M → EReal} (hg : IsThetaPshPotential θ g)
    (hgF : QuasiEverywhere (n := n) (fun x => g x ≤ (F x : EReal))) (x : M) :
    g x ≤ (F x : EReal) :=
  le_coe_of_ae_in_charts_le hg.1 hF (fun e => by
    filter_upwards [hgF.ae_in_chart e volume] with z hz
    exact hz) x

end Competitors

section Pullback

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Envelope pullback** (FPT `thm:big-metric-laplacian-rooftop`, passage to a modification;
SGPT `prop:PSHpullbij` applied to the competitors): for an analytic modification `π : Y → X`
from a compact manifold and a continuous obstacle `F` whose envelope is a `θ`-psh potential lying
below `F`, `P_θ(F) ∘ π = P_{π^*θ}(F ∘ π)`. -/
theorem rooftopEnvelope_comp_of_isAnalyticModification [CompactSpace Y] {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (θ : ClosedRealOneOneForm n X) {F : X → ℝ}
    (hF : Continuous F)
    (hP : IsThetaPshPotential θ.val (rooftopEnvelope θ.val (fun x => (F x : EReal))))
    (hPF : ∀ x, rooftopEnvelope θ.val (fun x => (F x : EReal)) x ≤ (F x : EReal)) :
    (fun y => rooftopEnvelope θ.val (fun x => (F x : EReal)) (π y)) =
      rooftopEnvelope (ClosedRealOneOneForm.pullback hπ.1 θ).val (fun y => (F (π y) : EReal)) := by
  set P := rooftopEnvelope θ.val (fun x => (F x : EReal)) with hPdef
  have hs := AnalyticModificationStrongPullback.surjective_of_isAnalyticModification hπ
  have hFπ : Continuous (fun y => F (π y)) := hF.comp hπ.1.continuous
  apply le_antisymm
  · -- `P ∘ π` is a competitor upstairs
    exact le_rooftopEnvelope
      (AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ θ hP)
      (quasiEverywhere_of_forall (n := n) fun y => hPF (π y))
  · -- every competitor upstairs descends to a competitor downstairs
    have husc : UpperSemicontinuous (fun y => P (π y)) :=
      (upperSemicontinuous_rooftopEnvelope θ.val _).comp hπ.1.continuous
    refine (rooftopEnvelope_le_iff husc).mpr fun w hw hwF => ?_
    obtain ⟨φ, hφ, hφw⟩ := SGPT.Okounkov.TranscendentalLifting.exists_descent hπ θ hw
    have hφF : ∀ x, φ x ≤ (F x : EReal) := by
      intro x
      obtain ⟨y, rfl⟩ := hs x
      rw [hφw y]
      exact competitor_le_of_continuous hFπ hw hwF y
    have hφP : φ ≤ P := le_rooftopEnvelope hφ (quasiEverywhere_of_forall (n := n) hφF)
    intro y
    rw [← hφw y]
    exact hφP (π y)

/-- **The envelope data on the modification** (big class): with `X` compact, nonempty, of positive
dimension, `{θ}` big and `F` continuous, `u_Y := P_θ(F) ∘ π` is a `π^*θ`-psh potential, equals
`P_{π^*θ}(F ∘ π)`, and lies below `F ∘ π`: the hypotheses `hu`, `hudef`, `hule` of
`hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing` for `θ_Y = π^*θ`, `f = F ∘ π`. -/
theorem envelope_pullback_data [CompactSpace Y] [CompactSpace X] [Nonempty X] (hn : 0 < n)
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {F : X → ℝ} (hF : Continuous F) :
    IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val
        (fun y => rooftopEnvelope θ.val (fun x => (F x : EReal)) (π y)) ∧
      (fun y => rooftopEnvelope θ.val (fun x => (F x : EReal)) (π y)) =
        rooftopEnvelope (ClosedRealOneOneForm.pullback hπ.1 θ).val
          (fun y => (F (π y) : EReal)) ∧
      ∀ y, rooftopEnvelope θ.val (fun x => (F x : EReal)) (π y) ≤ (F (π y) : EReal) := by
  have hP := isThetaPshPotential_rooftopEnvelope_of_continuous hn θ hbig hF
  have hne := rooftopCompetitors_nonempty_of_isBigClass hn θ hbig hF
  have hPF : ∀ x, rooftopEnvelope θ.val (fun x => (F x : EReal)) x ≤ (F x : EReal) :=
    rooftopEnvelope_le_of_continuous hF hne hP.1
  exact ⟨AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
      hπ θ hP, rooftopEnvelope_comp_of_isAnalyticModification hπ θ hF hP hPF, fun y => hPF (π y)⟩

/-- **The pulled-back obstacle is quasi-psh from above**: if `g` has bounded complex Hessian on the
compact Kähler manifold `(X, ω)`, then `-(g ∘ π)` is a `π^*(S ω)`-psh potential for some `S > 0`
(the obstacle hypothesis of `hasBoundedMetricLaplacianOn_envelope_of_jointSmoothing`). -/
theorem neg_comp_isThetaPshPotential_of_hasBoundedComplexHessian [CompactSpace X] {π : Y → X}
    (hπ : IsAnalyticModification (n := n) π) (A : KahlerBackground n X) {g : X → ℝ}
    (hg : SGPT.Envelopes.DNTC11.HasBoundedComplexHessian (n := n) g) :
    ∃ S : ℝ, 0 < S ∧ IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 (S • A.form)).val
      (fun y => ((-g (π y) : ℝ) : EReal)) := by
  obtain ⟨S, hS, hpsh⟩ := SGPT.Envelopes.DNTReg.HasBoundedComplexHessian.exists_neg_psh A hg
  exact ⟨S, hS,
    AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification hπ
      (S • A.form) hpsh⟩

end Pullback

end SGPT.NPP.DN2
