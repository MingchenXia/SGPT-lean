import SGPT.Foundations.Analysis.Pending.ActualOriginPrimitiveTraceNullity
import SGPT.Foundations.Analysis.Pending.LocalSmoothScalarCurrents
import SGPT.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
import SGPT.Foundations.Analysis.Pending.AnalyticSingularities
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

set_option autoImplicit false

/-! # Actual primitive logarithmic currents are locally absolutely continuous

This local residual-current producer uses origin-only primitive germs.
Global divisors, the Siu decomposition and the non-pluripolar product
identity remain separate obligations.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveLogarithmicCurrentAbsoluteContinuity
open FirstPass FirstPass.MongeAmpere DivisorRegularLocus
  ActualPrimitiveHolomorphicGraphProjection ActualOriginPrimitiveTraceNullity
  StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalCurrentLebesgue
  LocalCurrentPullbackDdc LocalCurrentDensityMatrix LocalSmoothScalarCurrents
  ScalarLeviPositiveCurrent LocalPositiveCurrentGluing

variable {m N : ℕ}

/-- The actual logarithmic current of an origin-primitive holomorphic family
internally has a locally absolutely continuous trace and equals its actual
Lebesgue absolutely continuous part. -/
theorem exists_local_absolutelyContinuous_primitive_logarithmic_current
    (f : Fin N → ComplexModel (m + 1) → ℂ) (hprimitive : IsPrimitiveAt f 0)
    (k : Fin N) (hk : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), f k x = 0)
    (Ω : Opens (ComplexModel (m + 1)))
    (hΩ : IsPreconnected (Ω : Set (ComplexModel (m + 1))))
    (h0 : (0 : ComplexModel (m + 1)) ∈ Ω)
    (hf : ∀ i, DifferentiableOn ℂ (f i) Ω) {c : ℝ} (hc : 0 < c) :
    let p := fun x => (c : EReal) * generatorLog f x
    ∃ (hp : PlurisubharmonicOn p Ω) (_hne : ∃ a ∈ Ω, p a ≠ ⊥),
      ∃ r : ℝ, 0 < r ∧
        let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
        ∃ (hsub : V ≤ Ω) (hV : IsPreconnected (V : Set (ComplexModel (m + 1))))
          (hneV : ∃ a ∈ V, p a ≠ ⊥),
          let T := pshRegularDistribution (hp.mono hsub) volume hV hneV
          let hT : HasNonnegativeDistributionalLevi T :=
            (hp.mono hsub).pshRegularDistribution_hasNonnegativeDistributionalLevi hV hneV
          let hC := isPositive_ddc_scalarTopCurrent hT
          hC.traceMeasure ≪ volume ∧ acPart hC = ddc (scalarTopCurrent T) := by
  classical
  let p := fun x => (c : EReal) * generatorLog f x
  have hp : PlurisubharmonicOn p Ω := by
    intro x hx
    exact plurisubharmonicAt_scaled_generatorLog ⟨Ω, Ω.isOpen, hx, hf⟩ hc
  have hne : ∃ a ∈ Ω, p a ≠ ⊥ := by
    by_contra h
    apply hk
    have hbot : ∀ x ∈ Ω, p x = ⊥ := by simpa only [not_exists, not_and, not_not] using h
    filter_upwards [Ω.isOpen.mem_nhds h0] with x hx
    have hz := (scaled_generatorLog_add_eq_bot_iff f x hc 0).mp (by
      simpa only [EReal.coe_zero, add_zero] using hbot x hx)
    exact hz k
  obtain ⟨r, hr, hsub, hV, hneV, hnull⟩ :=
    exists_local_trace_null_origin_primitive_common_zeros f hprimitive k hk Ω hΩ h0 p hp hne
  let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
  let T := pshRegularDistribution (hp.mono hsub) volume hV hneV
  let hT : HasNonnegativeDistributionalLevi T :=
    (hp.mono hsub).pshRegularDistribution_hasNonnegativeDistributionalLevi hV hneV
  let hC := isPositive_ddc_scalarTopCurrent hT
  have hs : ContDiffOn ℝ ∞ (generatorNormSq f) Ω := by
    unfold generatorNormSq
    refine ContDiffOn.sum fun i _ => ?_
    exact (contDiff_norm_sq ℝ).comp_contDiffOn
      (contDiffOn_real_of_differentiableOn_complex (hf i) Ω.isOpen)
  let Wset : Set (ComplexModel (m + 1)) := {x | x ∈ V ∧ 0 < generatorNormSq f x}
  have hWo : IsOpen Wset := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact inter_mem (V.isOpen.mem_nhds hx.1)
      ((hs.continuousOn.continuousAt (Ω.isOpen.mem_nhds (hsub hx.1))).eventually
        (lt_mem_nhds hx.2))
  let W : Opens (ComplexModel (m + 1)) := ⟨Wset, hWo⟩
  have hWV : W ≤ V := fun _ hx => hx.1
  let g : ComplexModel (m + 1) → ℝ := fun x => c * Real.log (generatorNormSq f x)
  have hg : ContDiffOn ℝ ∞ g W := by
    intro x hx
    exact (contDiffAt_const.mul
      ((hs.contDiffAt (Ω.isOpen.mem_nhds (hsub hx.1))).log hx.2.ne')).contDiffWithinAt
  have heq : ∀ x ∈ W, p x = (g x : EReal) := by
    intro x hx
    have hn : ∃ i, f i x ≠ 0 := by
      by_contra h
      have hz : ∀ i, f i x = 0 := by simpa only [not_exists, not_not] using h
      have hs0 : generatorNormSq f x = 0 := by simp [generatorNormSq, hz]
      exact hx.2.ne' hs0
    simp only [p, g, generatorLog_of_nonzero hn, EReal.coe_mul]
  have hgp : PlurisubharmonicOn (fun x => (g x : EReal)) W := by
    intro x hx
    apply (hp x (hsub hx.1)).congr
    filter_upwards [W.isOpen.mem_nhds hx] with y hy
    exact heq y hy
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
  let hCW := isPositive_restrict hC hWV
  let α : ComplexModel (m + 1) → RealForm (m + 1) 2 := smoothDDC g
  have hαc : ContinuousOn α W := (contDiffOn_ddcForm hg).continuousOn
  have hα : ∀ x ∈ W, IsSemipositiveOneOne (α x) :=
    fun _ hx => isSemipositiveOneOne_smoothDDC hg hgp hx
  have hpair (γ : formSpan (m + 1) m) (φ : 𝓓(W, ℝ)) :
      restrict hWV (ddc (scalarTopCurrent T)) γ φ =
        ∫ x, φ x * formDensity (α x) γ := by
    rw [hcur, ddcMul_oneCurrent_apply hg]
  have hω : kahlerPower (m + 1) m ∈ posCone (m + 1) m :=
    formPower_mem_spCone isSemipositiveOneOne_kahlerForm m
  have htr : hCW.traceMeasure =
      volume.withDensity (formWeight W α (kahlerPower (m + 1) m)) :=
    eq_of_forall_testFunction_integral_eq hCW.traceMeasure_compl (formWeight_compl α _)
      (fun K hK hKW => hCW.traceMeasure_lt_top hK hKW) (formWeight_lt_top hαc _)
      fun φ => by rw [hCW.integral_traceMeasure, hpair, integral_formWeight hαc hα hω]
  have hacW : hC.traceMeasure.restrict W ≪ volume := by
    rw [← traceMeasure_restrict hC hWV, htr]
    exact withDensity_absolutelyContinuous _ _
  have hac : hC.traceMeasure ≪ volume := by
    intro E hE
    have hEW : hC.traceMeasure (E ∩ W) = 0 := by
      rw [← Measure.restrict_apply' W.isOpen.measurableSet]
      exact hacW hE
    have hremain : (V : Set (ComplexModel (m + 1))) \ W ⊆
        {x | x ∈ V ∧ ∀ i, f i x = 0} := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hs0 : generatorNormSq f x = 0 :=
        le_antisymm (not_lt.mp (fun h => hx.2 ⟨hx.1, h⟩)) (generatorNormSq_nonneg f x)
      have hv0 : generatorVector f x = 0 := by
        apply norm_eq_zero.mp
        have hsq := (generatorVector_norm_sq f x).trans hs0
        nlinarith [norm_nonneg (generatorVector f x)]
      exact (generatorVector_eq_zero_iff f x).mp hv0
    have hVD : hC.traceMeasure ((V : Set (ComplexModel (m + 1))) \ W) = 0 :=
      measure_mono_null hremain hnull
    have hEV : hC.traceMeasure (E ∩ V) = 0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ hC.traceMeasure ((E ∩ W) ∪ ((V : Set (ComplexModel (m + 1))) \ W)) :=
          measure_mono (by
            intro x hx
            by_cases hw : x ∈ W
            · exact Or.inl ⟨hx.1, hw⟩
            · exact Or.inr ⟨hx.2, hw⟩)
        _ ≤ hC.traceMeasure (E ∩ W) + hC.traceMeasure ((V : Set (ComplexModel (m + 1))) \ W) :=
          measure_union_le _ _
        _ = 0 := by rw [hEW, hVD, add_zero]
    apply le_antisymm _ zero_le
    calc
      _ ≤ hC.traceMeasure ((E ∩ V) ∪ (V : Set (ComplexModel (m + 1)))ᶜ) :=
        measure_mono (by
          intro x hx
          by_cases hv : x ∈ V
          · exact Or.inl ⟨hx, hv⟩
          · exact Or.inr hv)
      _ ≤ hC.traceMeasure (E ∩ V) + hC.traceMeasure (V : Set (ComplexModel (m + 1)))ᶜ :=
        measure_union_le _ _
      _ = 0 := by rw [hEV, hC.traceMeasure_compl, add_zero]
  exact ⟨hp, hne, r, hr, hsub, hV, hneV, hac, acPart_eq_self_of_absolutelyContinuous hC hac⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveLogarithmicCurrentAbsoluteContinuity
