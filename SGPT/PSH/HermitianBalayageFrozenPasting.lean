import SGPT.PSH.HermitianBalayageFrozenChart
import SGPT.PSH.HermitianBalayageEnvelope
import SGPT.PSH.HermitianChartPasting
import SGPT.PSH.HermitianExtremalEnvelopeValues

/-!
# The actual pasted frozen competitor and its extremal upper bound

The canonical ordinary replacement is corrected by the dominated frozen
potential and pasted into the original global competitor. Its actual
boundary values give boundary upper limits. Global Hermitian pasting and
the literal original extremal competitor family then prove the upper
bound; no incoming replacement-gap or competitor-membership certificate
is used.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Filter MeasureTheory TopologicalSpace Classical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open Hermitian HermitianExtremal SGPT.PSH.SourceDomainBalayageDraft
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A genuine original competitor produces a genuine pasted frozen
competitor. Consequently its canonical ordinary replacement lies below
the actual regularized global extremal plus the lower frozen correction. -/
theorem canonical_frozen_replacement_le_extremal
    (omega : Background (m + 1) M) (K : Set M) (e : ComplexChart (m + 1) M)
    {Ω : Opens (ComplexModel (m + 1))} (hΩ : Ω ≤ chartTarget e)
    (a : ComplexModel (m + 1)) {r : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ Ω)
    (hdisj : Disjoint K (chartDomain e (ball a r)))
    {u : M → EReal} (hu : u ∈ competitors omega K)
    {S : ℝ} (hu0 : ∀ x, 0 ≤ u x) (huS : ∀ x, u x ≤ (S : EReal))
    {qPlus qMinus : ComplexModel (m + 1) → ℝ}
    (hqPlus : ContDiffOn ℝ ∞ qPlus Ω) (hqMinus : ContDiff ℝ ∞ qMinus)
    (hdomPlus : ∀ z ∈ Ω, ∀ v : ComplexModel (m + 1),
      omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC qPlus z ![v, Complex.I • v])
    (hdomMinus : ∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
      smoothDDC qMinus z ![v, Complex.I • v] ≤ omega.form.coeff e z ![v, Complex.I • v])
    (hqBoundary : ∀ z ∈ sphere a r, qMinus z = qPlus z) :
    ∀ z ∈ ball a r,
      domainPerronEnvelope Ω ⟨ball a r, isOpen_ball⟩
        (correctedChartReader e Ω u qPlus) z ≤
        chartFunction (regularizedExtremal omega K) e z + (qMinus z : EReal) := by
  let D : Opens (ComplexModel (m + 1)) := ⟨ball a r, isOpen_ball⟩
  let F := correctedChartReader e Ω u qPlus
  have hF := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne hu.1 e hΩ
    hqPlus hdomPlus hu0 huS
  have hDc : IsCompact (closure (D : Set (ComplexModel (m + 1)))) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hDΩ : closure (D : Set (ComplexModel (m + 1))) ⊆ Ω :=
    closure_ball_subset_closedBall.trans hball
  have hDt : closure (D : Set (ComplexModel (m + 1))) ⊆ e.val.target := hDΩ.trans hΩ
  let V := domainPerronEnvelope Ω D F
  let Z : ComplexModel (m + 1) → EReal := fun z => V z + ((-qMinus z : ℝ) : EReal)
  have hVp := domainPerronEnvelope_plurisubharmonic (Nat.succ_pos m) hF.2.1 hDc hDΩ
  have hZp : PlurisubharmonicOn (fun z => Z z + (qMinus z : EReal)) D := by
    intro z hz
    apply (hVp z (hDΩ (subset_closure hz))).congr
    apply Eventually.of_forall
    intro y
    dsimp only [Z]
    rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
  have hboundary : ∀ z ∈ frontier (D : Set (ComplexModel (m + 1))),
      limsup Z (𝓝[(D : Set (ComplexModel (m + 1)))] z) ≤ chartFunction u e z := by
    intro z hz
    have hzΩ : z ∈ Ω := hDΩ hz.1
    have hznot : z ∉ D := by simpa only [D.isOpen.interior_eq, SetLike.mem_coe] using hz.2
    have hnegc : ContinuousAt (fun y => ((-qMinus y : ℝ) : EReal)) z :=
      continuous_coe_real_ereal.continuousAt.comp hqMinus.continuous.continuousAt.neg
    have hVusc : UpperSemicontinuousAt V z := upperSemicontinuous_uscRegularization _ z
    have hZusc : UpperSemicontinuousAt Z z :=
      hVusc.add' hnegc.upperSemicontinuousAt
        (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot (-qMinus z)))
          (Or.inr (EReal.coe_ne_top (-qMinus z))))
    have heq : Z z = chartFunction u e z := by
      dsimp only [Z, V]
      rw [domainPerronEnvelope_eq_off_domain (Nat.succ_pos m) hF.2.1 hDc hDΩ
        (ball_hasC1Boundary a hr) z hzΩ hznot]
      rw [hF.2.2 z hzΩ, hqBoundary z (frontier_ball_subset_sphere hz)]
      rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
    have hlim := (hZusc.upperSemicontinuousWithinAt (D : Set (ComplexModel (m + 1)))).limsup_le
    rwa [heq] at hlim
  let ψ := gluedMax (chartDomain e (D : Set (ComplexModel (m + 1)))) (fun x => Z (e.val x)) u
  have hψ : IsHermitianPSH omega ψ := isHermitianPSH_chart_gluedMax_of_boundary_limsup
    omega e D.isOpen hDc hDt hqMinus.contDiffOn hZp hdomMinus hu.1 hboundary
  have hψK : ∀ x ∈ K, ψ x ≤ 0 := by
    intro x hx
    have hxout : x ∉ chartDomain e (D : Set (ComplexModel (m + 1))) :=
      fun h => Set.disjoint_left.mp hdisj hx h
    simpa only [ψ, gluedMax, if_neg hxout] using hu.2 x hx
  have hψle := competitor_le_regularizedExtremal omega (A := K) (u := ψ) ⟨hψ, hψK⟩
  intro z hz
  have hzΩ : z ∈ Ω := hball (ball_subset_closedBall hz)
  have hzt : z ∈ e.val.target := hΩ hzΩ
  have hxD : e.val.symm z ∈ chartDomain e (D : Set (ComplexModel (m + 1))) :=
    ⟨e.val.map_target hzt, by
      change e.val (e.val.symm z) ∈ ball a r
      rw [e.val.right_inv hzt]
      exact hz⟩
  have hZψ : Z z ≤ ψ (e.val.symm z) := by
    dsimp only [ψ]
    rw [gluedMax_eq_max hxD, e.val.right_inv hzt]
    exact le_max_left _ _
  have hZle : Z z ≤ chartFunction (regularizedExtremal omega K) e z :=
    hZψ.trans (hψle (e.val.symm z))
  calc
    V z = Z z + (qMinus z : EReal) := by
      dsimp only [Z]
      rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]
    _ ≤ chartFunction (regularizedExtremal omega K) e z + (qMinus z : EReal) := add_le_add hZle le_rfl

end SGPT.PSH.HermitianBalayage
