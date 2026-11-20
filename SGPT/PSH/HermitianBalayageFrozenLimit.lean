import SGPT.PSH.HermitianBalayageFrozenPasting
import SGPT.PSH.HermitianBalayageIncreasingZeroMass
import SGPT.PSH.HermitianExtremalChoquet
import SGPT.Foundations.Analysis.FirstPass.UscRegularizationLocality
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight

/-!
# The actual frozen homogeneous replacement of the bounded extremal

The sequence is selected from the literal original extremal competitors.
Each ordinary replacement is pasted into its genuine global competitor,
so the extremal gives its upper bound. Their increasing regularized limit
has zero Monge--Ampère measure and the stated error. Neither a replacement
gap nor zero mass of the limiting replacement is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric Filter MeasureTheory TopologicalSpace Classical
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open Hermitian HermitianExtremal SGPT.PSH.SourceDomainBalayageDraft
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The genuine frozen replacement of the actual bounded regularized
extremal, constructed from actual increasing competitors and their
canonical ordinary balayages. -/
theorem exists_frozen_extremal_homogeneous_replacement
    (omega : Background (m + 1) M) (K : Set M) (e : ComplexChart (m + 1) M)
    (hE : IsHermitianPSH omega (regularizedExtremal omega K))
    {S : ℝ} (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal))
    {Ω : Opens (ComplexModel (m + 1))} (hΩ : Ω ≤ chartTarget e)
    (a : ComplexModel (m + 1)) {r : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ Ω)
    (hdisj : Disjoint K (chartDomain e (ball a r)))
    {qPlus qMinus : ComplexModel (m + 1) → ℝ}
    (hqPlus : ContDiff ℝ ∞ qPlus) (hqMinus : ContDiff ℝ ∞ qMinus)
    (hdomPlus : ∀ z ∈ Ω, ∀ v : ComplexModel (m + 1),
      omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC qPlus z ![v, Complex.I • v])
    (hdomMinus : ∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
      smoothDDC qMinus z ![v, Complex.I • v] ≤ omega.form.coeff e z ![v, Complex.I • v])
    (hqBoundary : ∀ z ∈ sphere a r, qMinus z = qPlus z)
    {η : ℝ} (hgap : ∀ z ∈ ball a r, qMinus z - qPlus z ≤ η) :
    ∃ v : ComplexModel (m + 1) → ℝ, Measurable v ∧
      ∃ hv : IsLocallyBoundedPshOn (⟨ball a r, isOpen_ball⟩ : Opens (ComplexModel (m + 1))) v,
        SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure
          ⟨ball a r, isOpen_ball⟩ v hv = 0 ∧
        ∀ z ∈ ball a r,
          0 ≤ v z - correctedChartReader e Ω (regularizedExtremal omega K) qPlus z ∧
          v z - correctedChartReader e Ω (regularizedExtremal omega K) qPlus z ≤ η := by
  classical
  let D : Opens (ComplexModel (m + 1)) := ⟨ball a r, isOpen_ball⟩
  let U := correctedChartReader e Ω (regularizedExtremal omega K) qPlus
  obtain ⟨u, hu, hub, humono, hueq⟩ :=
    exists_bounded_increasing_nonnegative_competitors omega K S hES
  let F := fun j => correctedChartReader e Ω (u j) qPlus
  have hF (j : ℕ) := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne
    (hu j).1 e hΩ hqPlus.contDiffOn hdomPlus (fun x => (hub j x).1) (fun x => (hub j x).2)
  have hU := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne hE e hΩ
    hqPlus.contDiffOn hdomPlus (regularizedExtremal_nonneg omega K) hES
  have hDc : IsCompact (closure (D : Set (ComplexModel (m + 1)))) :=
    (isCompact_closedBall a r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hDΩ : closure (D : Set (ComplexModel (m + 1))) ⊆ Ω :=
    closure_ball_subset_closedBall.trans hball
  have hDsub : D ≤ Ω := fun _ hz => hDΩ (subset_closure hz)
  let V := fun j => domainPerronEnvelope Ω D (F j)
  let w := fun j z => (V j z).toReal
  have hreader (j : ℕ) := domainPerronEnvelope_reader (Nat.succ_pos m) (hF j).2.1 hDc hDΩ
  have hw (j : ℕ) : IsLocallyBoundedPshOn D (w j) := SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsLocallyBoundedPshOn.mono_opens (hreader j).1 hDsub
  have hwmono : ∀ z ∈ D, Monotone fun j => w j z := by
    intro z hz i j hij
    apply domainPerronEnvelope_toReal_mono (Nat.succ_pos m) (hF i).2.1 (hF j).2.1 hDc hDΩ
      (fun y hy _ => ?_) (hDsub hz)
    apply EReal.coe_le_coe_iff.mp
    rw [(hF i).2.2 y hy, (hF j).2.2 y hy]
    exact add_le_add (humono _ hij) le_rfl
  have hwlower (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ D) : F j z ≤ w j z := by
    apply EReal.coe_le_coe_iff.mp
    rw [(hreader j).2 z (hDsub hz)]
    exact le_domainPerronEnvelope (hF j).2.1 z
  have hwupper (j : ℕ) (z : ComplexModel (m + 1)) (hz : z ∈ D) :
      w j z ≤ U z + η := by
    have h := canonical_frozen_replacement_le_extremal omega K e hΩ a hr hball hdisj
      (hu j) (fun x => (hub j x).1) (fun x => (hub j x).2)
      hqPlus.contDiffOn hqMinus hdomPlus hdomMinus hqBoundary z hz
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_add, (hreader j).2 z (hDsub hz), hU.2.2 z (hDsub hz), add_assoc, ← EReal.coe_add]
    exact h.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by linarith [hgap z hz])))
  obtain ⟨BPlus, hBPlus⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hqPlus.continuous.continuousOn
  obtain ⟨BMinus, hBMinus⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hqMinus.continuous.continuousOn
  let B := |S| + |BPlus| + |BMinus|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hwbound : ∀ j z, z ∈ D → |w j z| ≤ B := by
    intro j z hz
    have hzK : z ∈ closedBall a r := ball_subset_closedBall hz
    have hdata : (F j z : EReal) = chartFunction (u j) e z + (qPlus z : EReal) :=
      (hF j).2.2 z (hDsub hz)
    have hFlower : qPlus z ≤ F j z := by
      apply EReal.coe_le_coe_iff.mp
      rw [hdata]
      simpa only [zero_add, chartFunction] using add_le_add (hub j (e.val.symm z)).1 (le_rfl : (qPlus z : EReal) ≤ _)
    have hlower : -BPlus ≤ w j z :=
      (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hBPlus z hzK)).trans
        (hFlower.trans (hwlower j z hz))
    have htop := canonical_frozen_replacement_le_extremal omega K e hΩ a hr hball hdisj
      (hu j) (fun x => (hub j x).1) (fun x => (hub j x).2)
      hqPlus.contDiffOn hqMinus hdomPlus hdomMinus hqBoundary z hz
    have hupper : w j z ≤ S + BMinus := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_add, (hreader j).2 z (hDsub hz)]
      exact htop.trans (add_le_add (hES _) (EReal.coe_le_coe_iff.mpr
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hBMinus z hzK))))
    apply abs_le.mpr
    constructor
    · dsimp [B]
      linarith [le_abs_self S, le_abs_self BPlus, le_abs_self BMinus, abs_nonneg S,
        abs_nonneg BPlus, abs_nonneg BMinus]
    · dsimp [B]
      linarith [le_abs_self S, le_abs_self BPlus, le_abs_self BMinus, abs_nonneg BPlus]
  have hwzero (j : ℕ) :
      SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure D (w j) (hw j) D = 0 := by
    obtain ⟨τ, hτ, hτzero⟩ := exists_domainPerronEnvelope_ball_measure_zero
      (Nat.succ_pos m) (hF j).2.1 a hr hball
    have heq := (hτ.restrict_opens hDsub).unique (isBTLimit_canonicalBedfordTaylorMeasure (hw j))
    rw [← heq, Measure.restrict_apply_self]
    exact hτzero
  have hUlimit : EqOn (fun z => (U z : EReal))
      (uscRegularization (⨆ j, fun y => (F j y : EReal))) D := by
    intro z hz
    have hzΩ := hDsub hz
    have hraw : (⨆ j, fun y => (F j y : EReal)) =ᶠ[𝓝 z]
        (fun y => chartFunction (fun x => ⨆ j, u j x) e y + (qPlus y : EReal)) := by
      filter_upwards [Ω.isOpen.mem_nhds hzΩ] with y hy
      rw [iSup_apply]
      change (⨆ j, (F j y : EReal)) = (⨆ j, u j (e.val.symm y)) + (qPlus y : EReal)
      rw [← iSup_add_coe]
      apply iSup_congr
      intro j
      exact (hF j).2.2 y hy
    rw [uscRegularization_congr_of_eventuallyEq hraw,
      uscRegularization_add_coe_continuousAt_apply _ hqPlus.continuous.continuousAt,
      uscRegularization_chartFunction_apply _ e (hΩ hzΩ), hueq]
    exact hU.2.2 z hzΩ
  obtain ⟨hv, hvm, _, hvzero⟩ := increasing_usc_reader_zero_mass w hw hwmono hB hwbound hwzero
  let v := fun z => (uscRegularization (⨆ j, fun y => (w j y : EReal)) z).toReal
  refine ⟨v, hvm, hv, hvzero, ?_⟩
  exact increasing_usc_reader_gap F w (SGPT.Foundations.Analysis.Pending.BedfordTaylor.IsLocallyBoundedPshOn.mono_opens hU.2.1 hDsub) hUlimit hwlower hwupper

end SGPT.PSH.HermitianBalayage
