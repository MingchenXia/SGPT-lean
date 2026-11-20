import SGPT.Foundations.Analysis.Pending.ActualDirectionalLeviMarginal
import SGPT.Foundations.Analysis.Pending.SmoothTestMeasureSeparation

set_option autoImplicit false

/-! # Actual compactly localized transverse Levi marginals

The original unbounded psh potential produces the directional measure.
Compact tensor cutoffs produce finite transverse measures; actual signed
Fubini densities dominate them through smooth-test measure separation.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian

namespace SGPT.Foundations.Analysis.Pending.ActualLocalizedLeviMarginal

open FirstPass

variable {m : ℕ}

private theorem ambient_le_of_smooth_tests (μ ν : Measure (ComplexModel m))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hle : ∀ φ : 𝓓((⊤ : Opens (ComplexModel m)), ℝ), (∀ x, 0 ≤ φ x) →
      (∫ x, φ x ∂μ) ≤ ∫ x, φ x ∂ν) : μ ≤ ν := by
  let O : Opens (ComplexModel m) := ⊤
  have hemb : MeasurableEmbedding (Subtype.val : O → ComplexModel m) :=
    MeasurableEmbedding.subtype_coe O.isOpen.measurableSet
  have hmap (ρ : Measure (ComplexModel m)) :
      (ρ.comap (Subtype.val : O → ComplexModel m)).map Subtype.val = ρ := by
    rw [hemb.map_comap, Subtype.range_coe]
    simp [O]
  have hfin (ρ : Measure (ComplexModel m)) [IsFiniteMeasure ρ] :
      IsFiniteMeasure (ρ.comap (Subtype.val : O → ComplexModel m)) := by
    constructor
    rw [hemb.comap_apply]
    exact (measure_mono (subset_univ _)).trans_lt (measure_lt_top ρ univ)
  let _ := hfin μ
  let _ := hfin ν
  have h : μ.comap (Subtype.val : O → ComplexModel m) ≤ ν.comap Subtype.val := by
    apply SmoothTestMeasureSeparation.Measure.le_of_testFunction_integral_le
    intro φ hφ
    have hμ := hemb.integral_map (μ := μ.comap Subtype.val) (fun x => φ x)
    have hν := hemb.integral_map (μ := ν.comap Subtype.val) (fun x => φ x)
    rw [hmap μ] at hμ
    rw [hmap ν] at hν
    rw [← hμ, ← hν]
    exact hle φ hφ
  rw [← hmap μ, ← hmap ν]
  exact Measure.map_mono h hemb.measurable

variable {U : Opens ℂ} {V : Opens (ComplexModel m)}

private def rectangle (U : Opens ℂ) (V : Opens (ComplexModel m)) :
    Opens (ℂ × ComplexModel m) := ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩

private def tensorTest (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)) : 𝓓(rectangle U V, ℝ) where
  toFun x := β x.1 * χ x.2
  contDiff' := (β.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd)
  hasCompactSupport' := (β.hasCompactSupport.prod χ.hasCompactSupport).of_isClosed_subset
    (isClosed_tsupport _) (by
      apply closure_minimal _ ((isClosed_tsupport β).prod (isClosed_tsupport χ))
      intro x hx
      exact ⟨subset_tsupport β (mul_ne_zero_iff.mp hx).1,
        subset_tsupport χ (mul_ne_zero_iff.mp hx).2⟩)
  tsupport_subset' := by
    apply (closure_minimal _ ((isClosed_tsupport β).prod (isClosed_tsupport χ))).trans
      (Set.prod_mono β.tsupport_subset χ.tsupport_subset)
    intro x hx
    exact ⟨subset_tsupport β (mul_ne_zero_iff.mp hx).1,
      subset_tsupport χ (mul_ne_zero_iff.mp hx).2⟩

private def multiplyTest (χ : 𝓓(V, ℝ)) (γ : 𝓓((⊤ : Opens (ComplexModel m)), ℝ)) :
    𝓓(V, ℝ) where
  toFun y := χ y * γ y
  contDiff' := χ.contDiff.mul γ.contDiff
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := tsupport_mul_subset_left.trans χ.tsupport_subset

private def leviTest (β : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  (1 / 4 : ℝ) •
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℂ) β) +
      TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I β))

private theorem leviTest_apply (β : 𝓓(U, ℝ)) (s : ℂ) :
    leviTest β s = leviForm β s (1 : ℂ) := by
  have h2 : ContDiff ℝ 2 (β : ℂ → ℝ) := β.contDiff.of_le ENat.LEInfty.out
  have hdd (v : ℂ) : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v β) s = realHessian β s v v := by
    rw [testFunction_lineDerivCLM_apply_eq_fderiv]
    have hfun : (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v β : ℂ → ℝ) =
        fun x => fderiv ℝ β x v :=
      funext fun x => testFunction_lineDerivCLM_apply_eq_fderiv β v x
    rw [hfun, fderiv_fderiv_apply_eq_realHessian h2]
  simp only [leviTest, _root_.smul_apply, _root_.add_apply, smul_eq_mul,
    hdd, leviForm, smul_eq_mul, mul_one]
  ring

private theorem integrable_fibre_density
    {f : ℂ × ComplexModel m → ℝ}
    (hf : LocallyIntegrableOn f (rectangle U V) volume)
    (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)) :
    Integrable (fun y => χ y * (∫ s, leviForm β s (1 : ℂ) * f (s, y))) volume := by
  have h := (tensorTest (leviTest β) χ).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℝ) hf
  change Integrable (fun x : ℂ × ComplexModel m =>
    leviTest β x.1 * χ x.2 * f x) volume at h
  rw [Measure.volume_eq_prod] at h
  have hi := h.integral_prod_right
  convert hi using 1
  funext y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [leviTest_apply]
  ring

private def localizedProjection (ν : Measure (rectangle U V))
    (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)) : Measure (ComplexModel m) :=
  (ν.withDensity (fun x => ENNReal.ofReal (β x.val.1 * χ x.val.2))).map
    (fun x => x.val.2)

private theorem localizedProjection_finite (ν : Measure (rectangle U V))
    [IsLocallyFiniteMeasure ν] (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)) :
    IsFiniteMeasure (localizedProjection ν β χ) := by
  let g := testFunctionToCompactlySupportedLM (rectangle U V) (tensorTest β χ)
  have hint : Integrable (fun x : rectangle U V => β x.val.1 * χ x.val.2) ν :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  let _ : IsFiniteMeasure (ν.withDensity
      (fun x : rectangle U V => ENNReal.ofReal (β x.val.1 * χ x.val.2))) :=
    isFiniteMeasure_withDensity_ofReal hint.2
  exact Measure.isFiniteMeasure_map _ _

private theorem localizedProjection_test_integral
    (ν : Measure (rectangle U V)) (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ))
    (hβ : ∀ s, 0 ≤ β s) (hχ : ∀ y, 0 ≤ χ y)
    (γ : 𝓓((⊤ : Opens (ComplexModel m)), ℝ)) :
    (∫ y, γ y ∂localizedProjection ν β χ) =
      ∫ x : rectangle U V, β x.val.1 * χ x.val.2 * γ x.val.2 ∂ν := by
  have hw : Measurable (fun x : rectangle U V => ENNReal.ofReal
      (β x.val.1 * χ x.val.2)) :=
    ((β.continuous.comp (continuous_fst.comp continuous_subtype_val)).mul
      (χ.continuous.comp (continuous_snd.comp continuous_subtype_val))).measurable.ennreal_ofReal
  have hpr : Measurable (fun x : rectangle U V => x.val.2) :=
    (continuous_snd.comp continuous_subtype_val).measurable
  rw [localizedProjection, integral_map hpr.aemeasurable
    γ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ hw.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (mul_nonneg (hβ _) (hχ _)), smul_eq_mul]

private theorem localizedProjection_ac
    {f : ℂ × ComplexModel m → ℝ}
    (hf : LocallyIntegrableOn f (rectangle U V) volume)
    (ν : Measure (rectangle U V)) [IsLocallyFiniteMeasure ν]
    (hrep : ∀ (β : 𝓓(U, ℝ)) (γ : 𝓓(V, ℝ)),
      (∫ x : rectangle U V, β x.val.1 * γ x.val.2 ∂ν) =
        ∫ y, γ y * (∫ s, leviForm β s (1 : ℂ) * f (s, y)))
    (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ))
    (hβ : ∀ s, 0 ≤ β s) (hχ : ∀ y, 0 ≤ χ y) :
    localizedProjection ν β χ ≪ volume := by
  let F : ComplexModel m → ℝ :=
    fun y => χ y * (∫ s, leviForm β s (1 : ℂ) * f (s, y))
  have hF : Integrable F volume := integrable_fibre_density hf β χ
  let ρ : Measure (ComplexModel m) :=
    volume.withDensity (fun y => ENNReal.ofReal ‖F y‖)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hF.norm.2
  let _ := localizedProjection_finite ν β χ
  have hle : localizedProjection ν β χ ≤ ρ := by
    apply ambient_le_of_smooth_tests
    intro γ hγ
    have hid : (∫ y, γ y ∂localizedProjection ν β χ) = ∫ y, γ y * F y := by
      rw [localizedProjection_test_integral ν β χ hβ hχ γ]
      have ht := hrep β (multiplyTest χ γ)
      calc
        _ = ∫ x : rectangle U V, β x.val.1 * multiplyTest χ γ x.val.2 ∂ν := by
          congr 1
          funext x
          change β x.val.1 * χ x.val.2 * γ x.val.2 = β x.val.1 * (χ x.val.2 * γ x.val.2)
          ring
        _ = _ := ht
        _ = _ := by
          congr 1
          funext y
          change (χ y * γ y) * (∫ s, leviForm β s (1 : ℂ) * f (s, y)) =
            γ y * (χ y * (∫ s, leviForm β s (1 : ℂ) * f (s, y)))
          ring
    have hρid : (∫ y, γ y ∂ρ) = ∫ y, γ y * ‖F y‖ := by
      change (∫ y, γ y ∂volume.withDensity (fun y => ENNReal.ofReal ‖F y‖)) = _
      rw [integral_withDensity_eq_integral_toReal_smul₀
        hF.norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul, mul_comm]
    rw [hid, hρid]
    apply integral_mono (hF.mul_of_top_right γ.memLp_top)
      (hF.norm.mul_of_top_right γ.memLp_top)
    intro y
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using le_abs_self (F y)) (hγ y)
  exact hle.absolutelyContinuous.trans (withDensity_absolutelyContinuous volume _)

/-- Genuine unbounded psh produces one directional measure whose every
nonnegative compact tensor localization has a finite, absolutely continuous
transverse pushforward. -/
theorem exists_directional_measure_with_localized_transverse_ac
    (U : Opens ℂ) (V : Opens (ComplexModel m)) (f : ℂ × ComplexModel m → EReal)
    (hf : PlurisubharmonicOn f ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hΩ : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hne : ∃ a ∈ ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))), f a ≠ ⊥) :
    let Ω : Opens (ℂ × ComplexModel m) :=
      ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩
    ∃ ν : Measure Ω, ν.Regular ∧ IsLocallyFiniteMeasure ν ∧
      (∀ φ : 𝓓(Ω, ℝ), (∫ x : Ω, φ x ∂ν) =
        distributionalLeviCLM (1, (0 : ComplexModel m))
          (pshRegularDistribution hf volume hΩ hne) φ) ∧
      ∀ (β : 𝓓(U, ℝ)) (χ : 𝓓(V, ℝ)), (∀ s, 0 ≤ β s) → (∀ y, 0 ≤ χ y) →
        let ρ : Measure (ComplexModel m) :=
          (ν.withDensity (fun x => ENNReal.ofReal (β x.val.1 * χ x.val.2))).map
            (fun x => x.val.2)
        IsFiniteMeasure ρ ∧ ρ ≪ volume := by
  obtain ⟨ν, hreg, hloc, hrep, hsigned⟩ :=
    ActualDirectionalLeviMarginal.exists_directional_measure_and_fibre_integrals U V f hf hΩ hne
  let ν' : Measure (rectangle U V) := ν
  let _ : IsLocallyFiniteMeasure ν' := hloc
  refine ⟨ν', hreg, hloc, hrep, ?_⟩
  intro β χ hβ hχ
  change IsFiniteMeasure (localizedProjection ν' β χ) ∧ localizedProjection ν' β χ ≪ volume
  exact ⟨localizedProjection_finite ν' β χ,
    localizedProjection_ac (hf.locallyIntegrableOn_toReal volume hΩ hne) ν' hsigned β χ hβ hχ⟩

end SGPT.Foundations.Analysis.Pending.ActualLocalizedLeviMarginal
