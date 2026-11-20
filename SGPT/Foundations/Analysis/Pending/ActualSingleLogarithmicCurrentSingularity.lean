import SGPT.Foundations.Analysis.Pending.ActualPrimitiveLogarithmicCurrentAbsoluteContinuity
import SGPT.Foundations.Analysis.Pending.PluriharmonicLogNorm
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

/-! # The actual single logarithmic current has a singular trace

Actual logarithmic PSH, holomorphic zero-set nullity and smooth curvature
off the zero set produce the singularity and both Lebesgue parts.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualSingleLogarithmicCurrentSingularity
open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorLocality LocalBedfordTaylorCollar
  LocalCurrentLebesgue LocalCurrentPullbackDdc LocalSmoothScalarCurrents
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing PluriharmonicLogNorm

variable {m : ℕ}

/-- A genuine nonzero holomorphic germ internally produces the full
singularity of its actual logarithmic current, including both Lebesgue
parts. No divisor or measure singularity witness is supplied. -/
theorem single_logarithmic_current_mutuallySingular
    (d : ComplexModel (m + 1) → ℂ) {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ d (ball (0 : ComplexModel (m + 1)) r))
    (hdne : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), d x = 0)
    {c : ℝ} (hc : 0 < c) :
    let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
    let p := fun x => (c : EReal) * generatorLog (fun _ : Fin 1 => d) x
    ∃ (hp : PlurisubharmonicOn p V) (hne : ∃ a ∈ V, p a ≠ ⊥),
      let hV := (convex_ball (0 : ComplexModel (m + 1)) r).isPreconnected
      let T := pshRegularDistribution hp volume hV hne
      let hT : HasNonnegativeDistributionalLevi T :=
        hp.pshRegularDistribution_hasNonnegativeDistributionalLevi hV hne
      let hC := isPositive_ddc_scalarTopCurrent hT
      hC.traceMeasure ⟂ₘ volume ∧ sgPart hC = ddc (scalarTopCurrent T) ∧ acPart hC = 0 := by
  classical
  let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
  let p := fun x => (c : EReal) * generatorLog (fun _ : Fin 1 => d) x
  have hV : IsPreconnected (V : Set (ComplexModel (m + 1))) := (convex_ball _ _).isPreconnected
  have hp : PlurisubharmonicOn p V := by
    intro x hx
    exact plurisubharmonicAt_scaled_generatorLog ⟨V, V.isOpen, hx, fun _ => hd⟩ hc
  have hneD : ∃ a ∈ V, d a ≠ 0 := by
    by_contra h
    apply hdne
    have hz : ∀ x ∈ V, d x = 0 := by simpa only [not_exists, not_and, not_not] using h
    filter_upwards [V.isOpen.mem_nhds (mem_ball_self hr)] with x hx
    exact hz x hx
  obtain ⟨a, ha, hda⟩ := hneD
  have hne : ∃ a ∈ V, p a ≠ ⊥ := by
    refine ⟨a, ha, ?_⟩
    intro h
    have hz := (scaled_generatorLog_add_eq_bot_iff (fun _ : Fin 1 => d) a hc 0).mp (by
      simpa only [EReal.coe_zero, add_zero] using h)
    exact hda (hz 0)
  let T := pshRegularDistribution hp volume hV hne
  let hT : HasNonnegativeDistributionalLevi T :=
    hp.pshRegularDistribution_hasNonnegativeDistributionalLevi hV hne
  let hC := isPositive_ddc_scalarTopCurrent hT
  let Wset : Set (ComplexModel (m + 1)) := (V : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}ᶜ
  have hWo : IsOpen Wset :=
    hd.continuousOn.isOpen_inter_preimage V.isOpen isOpen_compl_singleton
  let W : Opens (ComplexModel (m + 1)) := ⟨Wset, hWo⟩
  have hWV : W ≤ V := fun _ hx => hx.1
  have hdn (x : ComplexModel (m + 1)) (hx : x ∈ W) : d x ≠ 0 := by
    simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hx.2
  let g0 : ComplexModel (m + 1) → ℝ := fun x => Real.log (Complex.normSq (d x))
  let g : ComplexModel (m + 1) → ℝ := fun x => c * g0 x
  have hs : ContDiffOn ℝ ∞ (fun x => Complex.normSq (d x)) V := by
    have hdr : ContDiffOn ℝ ∞ d V :=
      (contDiffOn_of_differentiableOn_complex hd V.isOpen).restrict_scalars ℝ
    simpa only [Complex.normSq_eq_norm_sq, Function.comp_def] using
      (contDiff_norm_sq ℝ).comp_contDiffOn hdr
  have hg0 : ContDiffOn ℝ ∞ g0 W := by
    intro x hx
    exact ((hs.contDiffAt (V.isOpen.mem_nhds hx.1)).log
      (Complex.normSq_pos.mpr (hdn x hx)).ne').contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ g W := contDiffOn_const.mul hg0
  have heq : ∀ x ∈ W, p x = (g x : EReal) := by
    intro x hx
    have hlog := generatorLog_of_nonzero (f := fun _ : Fin 1 => d) (x := x) ⟨0, hdn x hx⟩
    simp only [p, hlog, generatorNormSq, Fintype.sum_unique,
      g, g0, Complex.normSq_eq_norm_sq, EReal.coe_mul]
  have hdist : restrictDistribution T hWV = regularDistribution volume g
      (hg.continuousOn.locallyIntegrableOn W.isOpen.measurableSet) := by
    change restrictDistribution (regularDistribution volume (fun x => (p x).toReal) _) _ = _
    rw [restrictDistribution_regularDistribution]
    apply regularDistribution_congr_ae_on
    exact (ae_restrict_mem W.isOpen.measurableSet).mono fun x hx => by
      change (p x).toReal = g x
      rw [heq x hx, EReal.toReal_coe]
  have hcur : restrict hWV (ddc (scalarTopCurrent T)) = ddcMul (oneCurrent W) g := by
    rw [ddc_scalarTopCurrent_restrict, hdist,
      scalarTopCurrent_regularDistribution_eq_mulBorel_of_contDiffOn hg]
    rfl
  have hhess (x : ComplexModel (m + 1)) (hx : x ∈ W) : smoothDDC g x = 0 := by
    change smoothDDC (fun y => c • g0 y) x = 0
    rw [smoothDDC_smul W.isOpen hg0 c hx]
    have hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ d y := by
      filter_upwards [V.isOpen.mem_nhds hx.1] with y hy
      exact (hd y hy).differentiableAt (V.isOpen.mem_nhds hy)
    rw [smoothDDC_log_normSq_eq_zero hhol (hdn x hx), smul_zero]
  have hzero : restrict hWV (ddc (scalarTopCurrent T)) = 0 := by
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
  let hCW := isPositive_restrict hC hWV
  have htrW : hCW.traceMeasure = 0 := by
    apply eq_of_forall_testFunction_integral_eq hCW.traceMeasure_compl (by simp)
      (fun K hK hKW => hCW.traceMeasure_lt_top hK hKW) (by intros; simp)
    intro φ
    rw [hCW.integral_traceMeasure]
    rw [hzero]
    simp
  have hW0 : hC.traceMeasure W = 0 := by
    have h := congrArg (fun μ : Measure (ComplexModel (m + 1)) => μ univ) htrW
    rw [traceMeasure_restrict hC hWV, Measure.restrict_apply' W.isOpen.measurableSet,
      univ_inter] at h
    simpa using h
  let A : Set (ComplexModel (m + 1)) := (V : Set (ComplexModel (m + 1))) \ W
  have hAmeas : MeasurableSet A := V.isOpen.measurableSet.diff W.isOpen.measurableSet
  have hAeq : A = (V : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0} := by
    ext x
    change (x ∈ V ∧ ¬(x ∈ V ∧ d x ≠ 0)) ↔ (x ∈ V ∧ d x = 0)
    tauto
  have hA0 : volume A = 0 := by
    rw [hAeq]
    exact HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume hd ha hda
  have hAc0 : hC.traceMeasure Aᶜ = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ hC.traceMeasure ((W : Set (ComplexModel (m + 1))) ∪ (V : Set (ComplexModel (m + 1)))ᶜ) :=
        measure_mono (by
          intro x hx
          by_cases hv : x ∈ V
          · exact Or.inl (by by_contra hw; exact hx ⟨hv, hw⟩)
          · exact Or.inr hv)
      _ ≤ hC.traceMeasure W + hC.traceMeasure (V : Set (ComplexModel (m + 1)))ᶜ :=
        measure_union_le _ _
      _ = 0 := by rw [hW0, hC.traceMeasure_compl, add_zero]
  have hsing : hC.traceMeasure ⟂ₘ volume :=
    ⟨Aᶜ, hAmeas.compl, hAc0, by simpa only [compl_compl] using hA0⟩
  have hsg : sgPart hC = ddc (scalarTopCurrent T) := by
    exact (ofMeasure_congr hC (sgMeasure_le hC) le_rfl
      (Measure.singularPart_eq_self.mpr hsing)).trans (ofMeasure_traceMeasure hC)
  have hac : acPart hC = 0 := by
    ext γ φ
    rw [acPart, ofMeasure_apply, acMeasure,
      (Measure.withDensity_rnDeriv_eq_zero _ _).mpr hsing, integral_zero_measure]
    rfl
  exact ⟨hp, hne, hsing, hsg, hac⟩

end SGPT.Foundations.Analysis.Pending.ActualSingleLogarithmicCurrentSingularity
