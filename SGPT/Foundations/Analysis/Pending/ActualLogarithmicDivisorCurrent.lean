import SGPT.Foundations.Analysis.Pending.ActualSingleLogarithmicCurrentSingularity
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

/-! # The actual geometric divisor identity from a nonzero holomorphic germ

The genuine scalar distribution and all-point germ hypothesis are produced
internally, retaining the literal two-form differential and coefficient c.
-/

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualLogarithmicDivisorCurrent
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  DivisorIntegrationCurrent LelongPoincareDivisor
  ActualSingleLogarithmicCurrentSingularity

variable {m : ℕ}

/-- Natural single-generator data produce all local nonzero germs and
the literal full distribution-valued geometric divisor identity. -/
theorem single_logarithmic_ddC_eq_divisorCurrent
    (d : ComplexModel (m + 1) → ℂ) {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ d (ball (0 : ComplexModel (m + 1)) r))
    (hdne : ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), d x = 0)
    {c : ℝ} (hc : 0 < c) :
    let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
    let p := fun x => (c : EReal) * generatorLog (fun _ : Fin 1 => d) x
    ∃ (hp : PlurisubharmonicOn p V) (hne : ∃ a ∈ V, p a ≠ ⊥)
      (hd0 : ∀ y ∈ V, ∃ᶠ z in 𝓝 y, d z ≠ 0),
      let hV := (convex_ball (0 : ComplexModel (m + 1)) r).isPreconnected
      let T := pshRegularDistribution hp volume hV hne
      ddC T = c • divisorCurrent hd hd0 := by
  obtain ⟨hp, hne, _, _, _⟩ := single_logarithmic_current_mutuallySingular d hr hd hdne hc
  let V : Opens (ComplexModel (m + 1)) := ⟨ball 0 r, isOpen_ball⟩
  let p := fun x => (c : EReal) * generatorLog (fun _ : Fin 1 => d) x
  have hV : IsPreconnected (V : Set (ComplexModel (m + 1))) := (convex_ball _ _).isPreconnected
  obtain ⟨a, ha, hpa⟩ := hne
  have hda : d a ≠ 0 := by
    intro hz
    apply hpa
    have hb := (scaled_generatorLog_add_eq_bot_iff (fun _ : Fin 1 => d) a hc 0).mpr
      (fun _ => hz)
    simpa only [EReal.coe_zero, add_zero] using hb
  have hZ0 : volume ((V : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0}) = 0 :=
    HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero volume hd ha hda
  have hd0 : ∀ y ∈ V, ∃ᶠ z in 𝓝 y, d z ≠ 0 := by
    intro y hy
    by_contra h
    have hev : ∀ᶠ z in 𝓝 y, d z = 0 := by simpa only [not_not] using not_frequently.mp h
    have hevV : ∀ᶠ z in 𝓝 y, z ∈ V := V.isOpen.mem_nhds hy
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
      (hevV.and hev)
    have hsub : ball y δ ⊆ (V : Set (ComplexModel (m + 1))) ∩ d ⁻¹' {0} :=
      fun z hz => ⟨(hball z hz).1, (hball z hz).2⟩
    have hb0 : volume (ball y δ) = 0 := measure_mono_null hsub hZ0
    exact (measure_ball_pos volume y hδ).ne' hb0
  have hL : LocallyIntegrableOn (fun x => Real.log (‖d x‖ ^ 2)) V volume :=
    locallyIntegrableOn_log_normSq V.isOpen hd hd0
  have hLC : LocallyIntegrableOn (fun x => c * Real.log (‖d x‖ ^ 2)) V volume :=
    by simpa only [Pi.smul_def, smul_eq_mul] using hL.smul c
  have hreal : (fun x => (p x).toReal) =ᵐ[volume.restrict V]
      fun x => c * Real.log (‖d x‖ ^ 2) := by
    filter_upwards [hp.ae_finite volume hV ⟨a, ha, hpa⟩] with x hx
    have hdx : d x ≠ 0 := by
      intro hz
      apply hx.2
      have hb := (scaled_generatorLog_add_eq_bot_iff (fun _ : Fin 1 => d) x hc 0).mpr
        (fun _ => hz)
      simpa only [EReal.coe_zero, add_zero] using hb
    have he := generatorLog_of_nonzero (f := fun _ : Fin 1 => d) (x := x) ⟨0, hdx⟩
    simp only [p, EReal.toReal_mul, EReal.toReal_coe, he, generatorNormSq,
      Fintype.sum_unique]
  refine ⟨hp, ⟨a, ha, hpa⟩, hd0, ?_⟩
  change ddC (regularDistribution volume (fun x => (p x).toReal) _) = _
  rw [regularDistribution_congr_ae_on _ hLC hreal,
    regularDistribution_const_mul c hL hLC, ← ddCLM_apply, map_smul,
    ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]

end SGPT.Foundations.Analysis.Pending.ActualLogarithmicDivisorCurrent
