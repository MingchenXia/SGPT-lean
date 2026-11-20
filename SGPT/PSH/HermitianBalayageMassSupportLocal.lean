import SGPT.PSH.HermitianBalayageBackgroundMassEstimate
import SGPT.PSH.HermitianBalayageCommonCorrection
import SGPT.PSH.HermitianBalayageMassSupportGeometry

/-!
# Actual local zero mass off the compact extremal set

Uniform coefficient freezing supplies the actual two smooth corrections.
One common quadratic supplies one fixed finite comparison measure. The
actual background mass estimate is `O(r)` at every center in a smaller
compact ball. Finite packing and bounded overlap force zero mass there.
The result is transported back to the original correction by the proved
same-chart current identities.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorCollar
open Hermitian HermitianExtremal HermitianGlobalProducts
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual bounded extremal's original background patch measure is
locally zero at every coordinate point outside the prescribed closed set.
All frozen corrections, local replacements, comparison measures, finite
coverings and radius limits are produced internally. -/
theorem background_extremal_measure_locally_zero_off
    (omega : Background (m + 1) M) (K : Set M) (hK : IsClosed K)
    (P : BackgroundPatch omega) (hE : IsHermitianPSH omega (regularizedExtremal omega K))
    {S : ℝ} (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal))
    {z₀ : ComplexModel (m + 1)} (hz₀ : z₀ ∈ P.geometry.domain)
    (hzK : P.geometry.chart.val.symm z₀ ∉ K) :
    ∃ ε : ℝ, 0 < ε ∧ ball z₀ ε ⊆ P.geometry.domain ∧
      backgroundDiagonalMeasure P (regularizedExtremal omega K) hE
        ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩ (ball z₀ ε) = 0 := by
  let E := regularizedExtremal omega K
  let hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ E x ∧ E x ≤ (b : EReal) :=
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
  let e := P.geometry.chart
  let G : Set (ComplexModel (m + 1)) :=
    (P.geometry.domain : Set (ComplexModel (m + 1))) ∩
      (e.val.target ∩ e.val.symm ⁻¹' Kᶜ)
  have hG : IsOpen G := P.geometry.domain.isOpen.inter (e.val.symm.isOpen_inter_preimage hK.isOpen_compl)
  have hzG : z₀ ∈ G := ⟨hz₀, P.geometry.domain_le_target hz₀, hzK⟩
  have hGt : G ⊆ e.val.target := fun _ hz => hz.2.1
  let b := omega.form.coeff e
  obtain ⟨R, c, hR, hc, hbuffer, hfreeze⟩ := exists_uniform_frozen_corrections hG b
    ((omega.form.smooth e).mono hGt) (fun z hz => omega.isTypeOneOne e z (hGt hz)) hzG
  let L₄ := closedBall z₀ (4 * R)
  have hL₄t : L₄ ⊆ e.val.target := hbuffer.trans hGt
  obtain ⟨A, hA, hdomCommon, hdomFrozen⟩ := exists_compact_common_frozen_correction b
    (isCompact_closedBall z₀ (4 * R)) ((omega.form.smooth e).continuousOn.mono hL₄t)
    (mul_nonneg hc.le hR.le) z₀
  let q₀ := ballPot A z₀ 0
  have hq₀ : ContDiff ℝ ∞ q₀ := contDiff_ballPot A z₀ 0
  let Ω₀ : Opens (ComplexModel (m + 1)) := ⟨ball z₀ (4 * R), isOpen_ball⟩
  have hΩ₀G : (Ω₀ : Set (ComplexModel (m + 1))) ⊆ G := ball_subset_closedBall.trans hbuffer
  have hΩ₀P : Ω₀ ≤ P.geometry.domain := fun _ hz => (hΩ₀G hz).1
  have hdom₀ : ∀ z ∈ Ω₀, ∀ v : ComplexModel (m + 1),
      omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC q₀ z ![v, Complex.I • v] :=
    fun z hz v => hdomCommon z (ball_subset_closedBall hz) v
  let P₀ := changeBackgroundCorrection (restrictBackgroundPatch P Ω₀ hΩ₀P) q₀ hq₀.contDiffOn hdom₀
  let W := correctedChartReader e Ω₀ E q₀
  have hWr := correctedChartReader_measurable_locallyBoundedPsh omega.isTypeOneOne hE e
    (fun _ hz => hGt (hΩ₀G hz)) hq₀.contDiffOn hdom₀ (regularizedExtremal_nonneg omega K) hES
  have hW : IsLocallyBoundedPshOn Ω₀ W := hWr.2.1
  let μ := backgroundDiagonalMeasure P₀ E hE hb
  let ν := oldTraceSumMeasure Ω₀ W hW
  have hμfin : ∀ L : Set (ComplexModel (m + 1)), IsCompact L → L ⊆ Ω₀ → μ L ≠ ⊤ :=
    fun L hL hLΩ => (P₀.current_isPositive (fun _ => E) (fun _ => hE) (fun _ => hb)).traceMeasure_lt_top hL hLΩ |>.ne
  have hνfin : ∀ L : Set (ComplexModel (m + 1)), IsCompact L → L ⊆ Ω₀ → ν L ≠ ⊤ :=
    fun L hL hLΩ => (oldTraceSumMeasure_finiteOnCompacts hW hL hLΩ).ne
  obtain ⟨C, hC, hmass⟩ := exists_background_extremal_common_mass_estimate (m := m) (M := M)
  let d := 2 * Real.pi * c
  have hd : 0 < d := by dsimp [d]; positivity
  let ρ := min R (1 / d)
  have hρ : 0 < ρ := lt_min hR (div_pos zero_lt_one hd)
  let L := closedBall z₀ (R / 2)
  have hLΩ : L ⊆ Ω₀ := closedBall_subset_ball (by linarith)
  have hlocal : ∀ a ∈ L, ∀ r : ℝ, 0 < r → r < ρ →
      (μ (ball a (r / 4))).toReal ≤ (C * d) * r * (ν (ball a r)).toReal := by
    intro a ha r hr hrρ
    have haR : a ∈ closedBall z₀ R := closedBall_subset_closedBall (by linarith) ha
    have ha₄ : a ∈ L₄ := closedBall_subset_closedBall (by linarith) haR
    have hrR : r ≤ R := hrρ.le.trans (min_le_left _ _)
    have hκ : 0 ≤ d * r := mul_nonneg hd.le hr.le
    have hκ1 : d * r ≤ 1 := by
      have ht : r ≤ 1 / d := hrρ.le.trans (min_le_right _ _)
      have ht' := (le_div_iff₀ hd).mp ht
      nlinarith
    let Ω : Opens (ComplexModel (m + 1)) := ⟨ball a (2 * r), isOpen_ball⟩
    have hΩΩ₀ : Ω ≤ Ω₀ := by
      intro z hz
      have hza : dist z a < 2 * r := hz
      have haz : dist a z₀ ≤ R := haR
      have ht := dist_triangle z a z₀
      change dist z z₀ < 4 * R
      linarith
    have hball : closedBall a r ⊆ Ω := closedBall_subset_ball (by linarith)
    have hdisj : Disjoint K (chartDomain e (ball a r)) := by
      apply Set.disjoint_left.mpr
      intro x hxK hxD
      have hxΩ : e.val x ∈ Ω := ball_subset_ball (by linarith : r ≤ 2 * r) hxD.2
      have hxG := hΩ₀G (hΩΩ₀ hxΩ)
      have hn := hxG.2.2
      change e.val.symm (e.val x) ∉ K at hn
      rw [e.val.left_inv hxD.1] at hn
      exact hn hxK
    obtain ⟨h, hh, hddc, hbnds, hgap, hboundary⟩ := hfreeze a haR r hr hrR
    let qPlus := frozenUpperCorrection h a (c * r)
    let qMinus := frozenLowerCorrection h a (c * r) r
    have hqPlus := contDiff_frozenUpperCorrection hh a (c * r)
    have hqMinus := contDiff_frozenLowerCorrection hh a (c * r) r
    have hdomPlus : ∀ z ∈ Ω, ∀ v : ComplexModel (m + 1),
        omega.form.coeff e z ![v, Complex.I • v] ≤ smoothDDC qPlus z ![v, Complex.I • v] :=
      fun z hz v => (hbnds z (ball_subset_closedBall hz) v).2
    have hdomMinus : ∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
        smoothDDC qMinus z ![v, Complex.I • v] ≤ omega.form.coeff e z ![v, Complex.I • v] :=
      fun z hz v => (hbnds z (closedBall_subset_closedBall (by linarith : r ≤ 2 * r)
        (ball_subset_closedBall hz)) v).1
    have hgapκ : ∀ z ∈ ball a r, qMinus z - qPlus z ≤ (d * r) * r ^ 2 := by
      intro z hz
      have ht := (hgap z (ball_subset_closedBall hz)).2
      dsimp only [d]
      convert ht using 1; ring
    have hcommon : ∀ z ∈ ball a r, ∀ v : ComplexModel (m + 1),
        smoothDDC qPlus z ![v, Complex.I • v] ≤ smoothDDC q₀ z ![v, Complex.I • v] :=
      fun z _ v => hdomFrozen a ha₄ (c * r) (mul_le_mul_of_nonneg_left hrR hc.le) h hh hddc z v
    obtain ⟨hW', ht⟩ := hmass omega K P₀ hE S hES hq₀ Ω hΩΩ₀ a r (d * r) hr hκ hκ1
      hball hdisj qPlus qMinus hqPlus hqMinus hdomPlus hdomMinus hboundary hgapκ hcommon
    have hclosedΩ₀ : closedBall a r ⊆ Ω₀ := hball.trans hΩΩ₀
    have hinnerΩ₀ : closedBall a (r / 4) ⊆ Ω₀ :=
      (closedBall_subset_closedBall (by linarith : r / 4 ≤ r)).trans hclosedΩ₀
    have houter : closedBall a ((3 / 4 : ℝ) * r) ⊆ ball a r := closedBall_subset_ball (by linarith)
    have hνball : ν (ball a r) ≠ ⊤ := ne_top_of_le_ne_top
      (hνfin _ (isCompact_closedBall a r) hclosedΩ₀) (measure_mono ball_subset_closedBall)
    calc
      (μ (ball a (r / 4))).toReal ≤ (μ (closedBall a (r / 4))).toReal :=
        ENNReal.toReal_mono (hμfin _ (isCompact_closedBall _ _) hinnerΩ₀) (measure_mono ball_subset_closedBall)
      _ ≤ C * (d * r) * (ν (closedBall a ((3 / 4 : ℝ) * r))).toReal := ht
      _ ≤ C * (d * r) * (ν (ball a r)).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hνball (measure_mono houter)) (mul_nonneg hC hκ)
      _ = (C * d) * r * (ν (ball a r)).toReal := by ring
  have hμzero : μ L = 0 := measure_compact_eq_zero_of_local_radius_bound μ ν Ω₀.isOpen
    (isCompact_closedBall _ _) hLΩ hμfin hνfin hρ (mul_nonneg hC hd.le) hlocal
  have hμeq : μ = (backgroundDiagonalMeasure P E hE hb).restrict (Ω₀ : Set (ComplexModel (m + 1))) := by
    exact (backgroundDiagonalMeasure_changeCorrection (restrictBackgroundPatch P Ω₀ hΩ₀P)
      q₀ hq₀.contDiffOn hdom₀ E hE hb).trans
      (backgroundDiagonalMeasure_restrict P E hE hb Ω₀ hΩ₀P).symm
  have hzeroL : backgroundDiagonalMeasure P E hE hb L = 0 := by
    have ht := congrArg (fun η : Measure (ComplexModel (m + 1)) => η L) hμeq
    rw [Measure.restrict_apply isClosed_closedBall.measurableSet, inter_eq_left.mpr hLΩ] at ht
    exact ht.symm.trans hμzero
  refine ⟨R / 2, by positivity, ?_, measure_mono_null ball_subset_closedBall hzeroL⟩
  exact (ball_subset_closedBall.trans hLΩ).trans hΩ₀P

/-- The actual original background patch measure vanishes on the entire
coordinate part of the complement of the prescribed closed set. -/
theorem background_extremal_measure_off_eq_zero
    (omega : Background (m + 1) M) (K : Set M) (hK : IsClosed K)
    (P : BackgroundPatch omega) (hE : IsHermitianPSH omega (regularizedExtremal omega K))
    {S : ℝ} (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal)) :
    backgroundDiagonalMeasure P (regularizedExtremal omega K) hE
      ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
      ((P.geometry.domain : Set (ComplexModel (m + 1))) ∩ P.geometry.chart.val.symm ⁻¹' Kᶜ) = 0 := by
  let μ := backgroundDiagonalMeasure P (regularizedExtremal omega K) hE
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩
  let G := (P.geometry.domain : Set (ComplexModel (m + 1))) ∩ P.geometry.chart.val.symm ⁻¹' Kᶜ
  have hloc : ∀ z : G, ∃ ε : ℝ, 0 < ε ∧ ball (z : ComplexModel (m + 1)) ε ⊆ P.geometry.domain ∧
      μ (ball (z : ComplexModel (m + 1)) ε) = 0 := fun z =>
    background_extremal_measure_locally_zero_off omega K hK P hE hES z.property.1 z.property.2
  choose ε hε _hsub hzero using hloc
  obtain ⟨T, hTc, hcover⟩ := isOpen_iUnion_countable
    (fun z : G => ball (z : ComplexModel (m + 1)) (ε z)) (fun _ => isOpen_ball)
  have hsubset : G ⊆ ⋃ z ∈ T, ball (z : ComplexModel (m + 1)) (ε z) := by
    intro z hz
    rw [hcover]
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hε _)⟩
  apply measure_mono_null hsubset
  exact (measure_biUnion_null_iff hTc).mpr (fun z _ => hzero z)

variable [MeasurableSpace M] [BorelSpace M]

/-- The actual transported background patch measure is carried by the
prescribed closed set. No overlap compatibility is assumed. -/
theorem background_extremal_pushMeasure_compl_eq_zero
    (omega : Background (m + 1) M) (K : Set M) (hK : IsClosed K)
    (P : BackgroundPatch omega) (hE : IsHermitianPSH omega (regularizedExtremal omega K))
    {S : ℝ} (hES : ∀ x, regularizedExtremal omega K x ≤ (S : EReal)) :
    P.geometry.pushTraceMeasure (P.current (fun _ => regularizedExtremal omega K))
      (P.current_isPositive (fun _ => regularizedExtremal omega K) (fun _ => hE)
        (fun _ => ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩)) Kᶜ = 0 := by
  change P.geometry.pushMeasure (backgroundDiagonalMeasure P (regularizedExtremal omega K) hE
    ⟨0, S, fun x => ⟨regularizedExtremal_nonneg omega K x, hES x⟩⟩) Kᶜ = 0
  rw [P.geometry.pushMeasure_apply]
  exact background_extremal_measure_off_eq_zero omega K hK P hE hES

end SGPT.PSH.HermitianBalayage
