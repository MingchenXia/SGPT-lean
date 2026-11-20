import SGPT.Foundations.Analysis.Pending.ActualUnboundedScalarCurrentPullback
import SGPT.Foundations.Analysis.Pending.ActualDistributionTwoFormDdc
import SGPT.Foundations.Analysis.Pending.ActualSingleLogarithmicCurrentSingularity

set_option autoImplicit false

/-! # The full native logarithmic divisor is singular on every open domain

The complete mathematical statement and ENTIRE proof precede this import baseline.
Native ddC log-norm-squared normalization is retained; global Siu assembly is separate.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualOpenLogarithmicDivisorSingularity
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorLocality LocalBedfordTaylorCollar
  LocalCurrentLebesgue LocalCurrentPullbackDdc LocalSmoothScalarCurrents
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing PluriharmonicLogNorm
  ActualDistributionTwoFormDdc DivisorIntegrationCurrent

variable {m : ℕ} {Ω : Opens (ComplexModel (m + 1))}

private theorem zero_set_null {d : ComplexModel (m + 1) → ℂ}
    (hd : DifferentiableOn ℂ d Ω)
    (hd0 : ∀ x ∈ Ω, ∃ᶠ y in 𝓝 x, d y ≠ 0) :
    volume ((Ω : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}) = 0 := by
  apply measure_null_of_locally_null
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx.1
  obtain ⟨y, hy, hdny⟩ := ((hd0 x hx.1).and_eventually (ball_mem_nhds x hr)).exists
  have hb0 : volume (ball x r ∩ d ⁻¹' {0}) = 0 :=
    HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume
      (hd.mono hball) hdny hy
  refine ⟨((Ω : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}) ∩ ball x r,
    inter_mem_nhdsWithin _ (ball_mem_nhds x hr), ?_⟩
  have hsub : (((Ω : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}) ∩ ball x r) ⊆
      ball x r ∩ d ⁻¹' {0} := fun y hy => ⟨hy.2, hy.1.2⟩
  exact measure_mono_null hsub hb0

/-- Natural holomorphic data internally give the full native divisor reading,
its positivity and its actual singular/zero-AC parts on an arbitrary open domain. -/
theorem exists_positive_singular_divisor_reading
    {d : ComplexModel (m + 1) → ℂ} (hd : DifferentiableOn ℂ d Ω)
    (hd0 : ∀ x ∈ Ω, ∃ᶠ y in 𝓝 x, d y ≠ 0) :
    let T := regularDistribution volume (fun x => Real.log (‖d x‖ ^ 2))
      (locallyIntegrableOn_log_normSq Ω.isOpen hd hd0)
    let C := ActualDistributionTwoFormReading.complementaryRead (divisorCurrent hd hd0)
    C = ddc (scalarTopCurrent T) ∧
      ∃ hC : IsPositive C, hC.traceMeasure ⟂ₘ volume ∧ sgPart hC = C ∧ acPart hC = 0 := by
  classical
  let p := generatorLog (fun _ : Fin 1 => d)
  have hp : PlurisubharmonicOn p Ω := by
    intro x hx
    simpa only [EReal.coe_one, one_mul] using
      (plurisubharmonicAt_scaled_generatorLog ⟨Ω, Ω.isOpen, hx, fun _ => hd⟩
        (by norm_num : 0 < (1 : ℝ)))
  have hnd : ∀ x ∈ Ω, ∀ W : Set (ComplexModel (m + 1)), IsOpen W → x ∈ W →
      ∃ y ∈ (Ω : Set (ComplexModel (m + 1))) ∩ W, p y ≠ ⊥ := by
    intro x hx W hWo hxW
    have hΩ : ∀ᶠ y in 𝓝 x, y ∈ Ω := Ω.isOpen.mem_nhds hx
    have hW : ∀ᶠ y in 𝓝 x, y ∈ W := hWo.mem_nhds hxW
    obtain ⟨y, hy, hyΩ, hyW⟩ := ((hd0 x hx).and_eventually (hΩ.and hW)).exists
    refine ⟨y, ⟨hyΩ, hyW⟩, ?_⟩
    dsimp only [p]
    rw [generatorLog_of_nonzero (f := fun _ : Fin 1 => d) ⟨0, hy⟩]
    exact EReal.coe_ne_bot _
  obtain ⟨hLp, hfin, _hweak⟩ :=
    ActualUnboundedScalarCurrentPullback.exists_integrable_psh_truncation_currents hp hnd
  let hL := locallyIntegrableOn_log_normSq Ω.isOpen hd hd0
  let T := regularDistribution volume (fun x => Real.log (‖d x‖ ^ 2)) hL
  let C := ActualDistributionTwoFormReading.complementaryRead (divisorCurrent hd hd0)
  have hreal : (fun x => (p x).toReal) =ᵐ[volume.restrict Ω]
      fun x => Real.log (‖d x‖ ^ 2) := by
    filter_upwards [hfin] with x hx
    have hdnx : d x ≠ 0 := by
      intro hz
      apply hx.2
      exact (generatorLog_eq_bot_iff (fun _ : Fin 1 => d) x).mpr (fun _ => hz)
    have he := generatorLog_of_nonzero (f := fun _ : Fin 1 => d) (x := x) ⟨0, hdnx⟩
    simp only [p, he, EReal.toReal_coe, generatorNormSq, Fintype.sum_unique]
  have hdist : regularDistribution volume (fun x => (p x).toReal) hLp = T :=
    regularDistribution_congr_ae_on hLp hL hreal
  have hT : HasNonnegativeDistributionalLevi T := by
    rw [← hdist]
    exact hp.hasNonnegativeDistributionalLevi_of_locallyIntegrable hLp hfin
  have hTC : ddc (scalarTopCurrent T) = C := by
    rw [← complementaryRead_ddC]
    exact congrArg ActualDistributionTwoFormReading.complementaryRead
      (ddC_log_normSq_eq_divisorCurrent hd hd0)
  have hC : IsPositive C := hTC ▸ isPositive_ddc_scalarTopCurrent hT
  let Wset : Set (ComplexModel (m + 1)) := (Ω : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}ᶜ
  have hWo : IsOpen Wset :=
    hd.continuousOn.isOpen_inter_preimage Ω.isOpen isOpen_compl_singleton
  let W : Opens (ComplexModel (m + 1)) := ⟨Wset, hWo⟩
  have hWΩ : W ≤ Ω := fun _ hx => hx.1
  have hdn (x : ComplexModel (m + 1)) (hx : x ∈ W) : d x ≠ 0 := by
    simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hx.2
  let g : ComplexModel (m + 1) → ℝ := fun x => Real.log (Complex.normSq (d x))
  have hs : ContDiffOn ℝ ∞ (fun x => Complex.normSq (d x)) Ω := by
    have hdr : ContDiffOn ℝ ∞ d Ω :=
      (contDiffOn_of_differentiableOn_complex hd Ω.isOpen).restrict_scalars ℝ
    simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      (contDiff_norm_sq ℝ).comp_contDiffOn hdr
  have hg : ContDiffOn ℝ ∞ g W := by
    intro x hx
    exact ((hs.contDiffAt (Ω.isOpen.mem_nhds hx.1)).log
      (Complex.normSq_pos.mpr (hdn x hx)).ne').contDiffWithinAt
  have hdistW : restrictDistribution T hWΩ = regularDistribution volume g
      (hg.continuousOn.locallyIntegrableOn W.isOpen.measurableSet) := by
    dsimp only [T]
    rw [restrictDistribution_regularDistribution]
    apply regularDistribution_congr_ae_on
    exact Eventually.of_forall fun x => by simp only [g, Complex.normSq_eq_norm_sq]
  have hcur : restrict hWΩ C = ddcMul (oneCurrent W) g := by
    rw [← hTC, ddc_scalarTopCurrent_restrict, hdistW,
      scalarTopCurrent_regularDistribution_eq_mulBorel_of_contDiffOn hg]
    rfl
  have hhess (x : ComplexModel (m + 1)) (hx : x ∈ W) : smoothDDC g x = 0 := by
    have hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ d y := by
      filter_upwards [Ω.isOpen.mem_nhds hx.1] with y hy
      exact (hd y hy).differentiableAt (Ω.isOpen.mem_nhds hy)
    exact smoothDDC_log_normSq_eq_zero hhol (hdn x hx)
  have hzero : restrict hWΩ C = 0 := by
    ext γ φ
    rw [hcur, ddcMul_oneCurrent_apply hg]
    change (∫ x, φ x * formDensity (smoothDDC g x) γ) = 0
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      change φ x * formDensity (smoothDDC g x) γ = 0
      by_cases hx : x ∈ W
      · rw [hhess x hx, formDensity_apply]
        have hz : coordinateWedge (γ : RealForm (m + 1) (2 * m)) (0 : RealForm (m + 1) 2) = 0 := by
          simpa only [zero_smul] using
            (coordinateWedge_smul_right 0 (γ : RealForm (m + 1) (2 * m))
              (0 : RealForm (m + 1) 2))
        rw [hz, TopDegreeDensity.topDensity_zero, mul_zero]
      · rw [testFunction_eq_zero_of_notMem φ hx, zero_mul]
  let hCW := isPositive_restrict hC hWΩ
  have htrW : hCW.traceMeasure = 0 := by
    apply eq_of_forall_testFunction_integral_eq hCW.traceMeasure_compl (by simp)
      (fun K hK hKW => hCW.traceMeasure_lt_top hK hKW) (by intros; simp)
    intro φ
    rw [hCW.integral_traceMeasure, hzero]
    simp
  have hW0 : hC.traceMeasure W = 0 := by
    have h := congrArg (fun μ : Measure (ComplexModel (m + 1)) => μ univ) htrW
    rw [traceMeasure_restrict hC hWΩ, Measure.restrict_apply' W.isOpen.measurableSet,
      univ_inter] at h
    simpa using h
  let A : Set (ComplexModel (m + 1)) := (Ω : Set (ComplexModel (m + 1))) \ W
  have hAmeas : MeasurableSet A := Ω.isOpen.measurableSet.diff W.isOpen.measurableSet
  have hAeq : A = (Ω : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0} := by
    ext x
    change (x ∈ Ω ∧ ¬(x ∈ Ω ∧ d x ≠ 0)) ↔ (x ∈ Ω ∧ d x = 0)
    tauto
  have hA0 : volume A = 0 := by rw [hAeq]; exact zero_set_null hd hd0
  have hAc0 : hC.traceMeasure Aᶜ = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ hC.traceMeasure ((W : Set (ComplexModel (m + 1))) ∪ (Ω : Set (ComplexModel (m + 1)))ᶜ) :=
        measure_mono (by
          intro x hx
          by_cases hv : x ∈ Ω
          · exact Or.inl (by by_contra hw; exact hx ⟨hv, hw⟩)
          · exact Or.inr hv)
      _ ≤ hC.traceMeasure W + hC.traceMeasure (Ω : Set (ComplexModel (m + 1)))ᶜ :=
        measure_union_le _ _
      _ = 0 := by rw [hW0, hC.traceMeasure_compl, add_zero]
  have hsing : hC.traceMeasure ⟂ₘ volume :=
    ⟨Aᶜ, hAmeas.compl, hAc0, by simpa only [compl_compl] using hA0⟩
  have hsg : sgPart hC = C :=
    (ofMeasure_congr hC (sgMeasure_le hC) le_rfl
      (Measure.singularPart_eq_self.mpr hsing)).trans (ofMeasure_traceMeasure hC)
  have hac : acPart hC = 0 := by
    ext γ φ
    rw [acPart, ofMeasure_apply, acMeasure,
      (Measure.withDensity_rnDeriv_eq_zero _ _).mpr hsing, integral_zero_measure]
    rfl
  exact ⟨hTC.symm, hC, hsing, hsg, hac⟩

end SGPT.Foundations.Analysis.Pending.ActualOpenLogarithmicDivisorSingularity
