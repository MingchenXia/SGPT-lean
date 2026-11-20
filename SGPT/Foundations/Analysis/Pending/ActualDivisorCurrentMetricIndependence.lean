import SGPT.Foundations.Analysis.Pending.ActualDivisorMetricLocalReading
import SGPT.Foundations.Analysis.Pending.ActualOneOneComplementaryReadingInjectivity
import SGPT.Foundations.Analysis.Pending.ActualNativeDivisorCurrentUnitFactor

set_option autoImplicit false

/-! # Metric independence of the complete native divisor current

Actual local generators and units are constructed from the two natural
divisor metrics. Full local complementary identities recover actual
type-(1,1) coefficients before the global current is identified.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
namespace SGPT.Foundations.Analysis.Pending.ActualDivisorCurrentMetricIndependence
open FirstPass FirstPass.HolomorphicIdealSheaves GlobalCurrents
  StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorLocality
  ActualDistributionTwoFormReading ActualDistributionTwoFormDdc DivisorIntegrationCurrent
  _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {U V : Opens (ComplexModel (m + 1))}

private theorem reader_restrict (hVU : V ≤ U) (A : DistributionForm U 2) :
    restrict hVU (complementaryRead A) =
      complementaryRead (LelongPoincareDivisor.restrictForm A hVU) := by
  ext γ φ
  simp only [complementaryRead, LocalBedfordTaylorLocality.restrict_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, LinearMap.sum_apply, _root_.sum_apply, _root_.smul_apply,
    LelongPoincareDivisor.restrictForm_apply, extTest]

private theorem restrict_twice {W : Opens (ComplexModel (m + 1))}
    (hVU : V ≤ U) (hWV : W ≤ V) (T : LocalProductCurrent (m + 1) U m) :
    restrict hWV (restrict hVU T) = restrict (hWV.trans hVU) T := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply]
  congr 1
  ext y
  simp only [extTest_apply]

private theorem divisor_reading_restrict {g : ComplexModel (m + 1) → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (hVU : V ≤ U) :
    restrict hVU (complementaryRead (divisorCurrent hg hg0)) =
      complementaryRead (divisorCurrent (hg.mono hVU) (fun y hy => hg0 y (hVU hy))) := by
  rw [← ddC_log_normSq_eq_divisorCurrent, complementaryRead_ddC,
    LocalPositiveCurrentGluing.ddc_scalarTopCurrent_restrict,
    restrictDistribution_regularDistribution, ← complementaryRead_ddC,
    ddC_log_normSq_eq_divisorCurrent]

private theorem divisorCurrent_congr_on {g h : ComplexModel (m + 1) → ℂ}
    (hg : DifferentiableOn ℂ g U) (hh : DifferentiableOn ℂ h U)
    (hg0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, g z ≠ 0)
    (hh0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, h z ≠ 0) (heq : EqOn g h U) :
    divisorCurrent hg hg0 = divisorCurrent hh hh0 := by
  have hLg := locallyIntegrableOn_log_normSq U.isOpen hg hg0
  have hLh := locallyIntegrableOn_log_normSq U.isOpen hh hh0
  have hae : (fun y => Real.log (‖g y‖ ^ 2)) =ᵐ[volume.restrict U]
      (fun y => Real.log (‖h y‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with y hy
    rw [heq hy]
  have hdist := regularDistribution_congr_ae_on hLg hLh hae
  calc
    divisorCurrent hg hg0 = LelongPoincareDivisor.ddCLM (regularDistribution volume
        (fun y => Real.log (‖g y‖ ^ 2)) hLg) := by
      rw [LelongPoincareDivisor.ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]
    _ = LelongPoincareDivisor.ddCLM
        (regularDistribution volume (fun y => Real.log (‖h y‖ ^ 2)) hLh) :=
      congrArg LelongPoincareDivisor.ddCLM hdist
    _ = divisorCurrent hh hh0 := by
      rw [LelongPoincareDivisor.ddCLM_apply, ddC_log_normSq_eq_divisorCurrent]

private theorem restrictForm_isOneOne {A : DistributionForm U 2}
    (hA : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne A) (hVU : V ≤ U) :
    _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne
      (LelongPoincareDivisor.restrictForm A hVU) := by
  intro v w
  exact congrArg (fun T : 𝓓'(U, ℝ) => restrictDistribution T hVU) (hA v w)

private theorem localReading_mono {O : Opens (ComplexModel (m + 1))}
    (hUO : U ≤ O) (hVU : V ≤ U) (T : LocalProductCurrent (m + 1) O m)
    {g : ComplexModel (m + 1) → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, g z ≠ 0) (c : ℝ)
    (heq : restrict hUO T = c • complementaryRead (divisorCurrent hg hg0)) :
    restrict (hVU.trans hUO) T = c • complementaryRead
      (divisorCurrent (hg.mono hVU) (fun y hy => hg0 y (hVU hy))) := by
  rw [← restrict_twice hUO hVU T, heq]
  have hsmul : restrict hVU (c • complementaryRead (divisorCurrent hg hg0)) =
      c • restrict hVU (complementaryRead (divisorCurrent hg hg0)) := by
    ext γ φ
    rfl
  rw [hsmul, divisor_reading_restrict]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem mdifferentiableOn_of_chart {g : M → ℂ} (e : ComplexChart (m + 1) M)
    (hUe : U ≤ chartTarget e) (hG : DifferentiableOn ℂ (fun y => g (e.val.symm y)) U) :
    MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) g (e.val.symm '' (U : Set _)) := by
  have hsrc : e.val.symm '' (U : Set _) ⊆ e.val.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.val.map_target (hUe hy)
  have hmap : MapsTo e.val (e.val.symm '' (U : Set _)) U := by
    rintro _ ⟨y, hy, rfl⟩
    simpa only [e.val.right_inv (hUe hy)] using hy
  have hchart : MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1))
      𝓘(ℂ, ComplexModel (m + 1)) e.val (e.val.symm '' (U : Set _)) :=
    fun x hx => (mdifferentiableAt_atlas e.property (hsrc hx)).mdifferentiableWithinAt
  have hcomp := (mdifferentiableOn_iff_differentiableOn.mpr hG).comp hchart hmap
  exact hcomp.congr (fun x hx => by
    change g x = g (e.val.symm (e.val x))
    rw [e.val.left_inv (hsrc hx)])

omit [IsComplexManifold (m + 1) M] in
private theorem noncollapse_of_chart {g : M → ℂ} (e : ComplexChart (m + 1) M)
    (hUe : U ≤ chartTarget e)
    (hG0 : ∀ y ∈ U, ∃ᶠ z in 𝓝 y, g (e.val.symm z) ≠ 0) :
    ∀ S : Set M, IsOpen S → S ⊆ e.val.symm '' (U : Set _) → S.Nonempty →
      ∃ x ∈ S, g x ≠ 0 := by
  intro S hS hSU ⟨x, hx⟩
  have hsrc : S ⊆ e.val.source := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hSU hy
    exact e.val.map_target (hUe hz)
  have hxU : e.val x ∈ U := by
    obtain ⟨z, hz, heq⟩ := hSU hx
    rw [← heq, e.val.right_inv (hUe hz)]
    exact hz
  have hO : IsOpen (e.val '' S) := e.val.isOpen_image_of_subset_source hS hsrc
  obtain ⟨y, hy, hg⟩ := Filter.frequently_iff.mp (hG0 (e.val x) hxU)
    (hO.mem_nhds (mem_image_of_mem e.val hx))
  obtain ⟨x', hx', heq⟩ := hy
  refine ⟨x', hx', ?_⟩
  rw [← heq, e.val.left_inv (hsrc hx')] at hg
  exact hg

private theorem exists_local_coefficient_eq
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (D : EffectiveDivisor (m + 1) M)
    (E₁ E₂ : MeteredEffectiveQDivisor (m + 1) M)
    (hm₁ : DivisorMetric.IsDivisorMetric D E₁) (hm₂ : DivisorMetric.IsDivisorMetric D E₂)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ chartTarget e) :
    ∃ (W : Opens (ComplexModel (m + 1))) (hWe : W ≤ chartTarget e), z ∈ W ∧
      LelongPoincareDivisor.restrictForm
        ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₁).coefficients b e) hWe =
      LelongPoincareDivisor.restrictForm
        ((LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₂).coefficients b e) hWe := by
  obtain ⟨W₁, hW₁e, hz₁, g₁, hG₁, hG₁0, hgen₁, hread₁⟩ :=
    ActualDivisorMetricLocalReading.exists_normalized_local_divisor_reading b D E₁ hm₁ e hz
  obtain ⟨W₂, hW₂e, hz₂, g₂, hG₂, hG₂0, hgen₂, hread₂⟩ :=
    ActualDivisorMetricLocalReading.exists_normalized_local_divisor_reading b D E₂ hm₂ e hz
  let V₁ := e.val.symm '' (W₁ : Set _)
  let V₂ := e.val.symm '' (W₂ : Set _)
  have hV₁ : IsOpen V₁ := e.val.isOpen_image_symm_of_subset_target W₁.isOpen hW₁e
  have hV₂ : IsOpen V₂ := e.val.isOpen_image_symm_of_subset_target W₂.isOpen hW₂e
  have hx₁ : e.val.symm z ∈ V₁ := mem_image_of_mem e.val.symm hz₁
  have hx₂ : e.val.symm z ∈ V₂ := mem_image_of_mem e.val.symm hz₂
  have hgen₁' : ∀ x ∈ V₁, ∀ f, D.ideal.mem x f ↔ IsInSpanAt (n := m + 1) (· = g₁) x f := by
    rintro _ ⟨y, hy, rfl⟩ f
    exact hgen₁ y hy f
  have hgen₂' : ∀ x ∈ V₂, ∀ f, D.ideal.mem x f ↔ IsInSpanAt (n := m + 1) (· = g₂) x f := by
    rintro _ ⟨y, hy, rfl⟩ f
    exact hgen₂ y hy f
  obtain ⟨V₀, u, hV₀, hx₀, hVsub, hu, hu0, heq⟩ := DivisorMetric.exists_unit_of_generators
    hV₁ hV₂ (mdifferentiableOn_of_chart e hW₁e hG₁)
    (mdifferentiableOn_of_chart e hW₂e hG₂) (noncollapse_of_chart e hW₁e hG₁0)
    hgen₁' hgen₂' hx₁ hx₂
  let O : Opens (ComplexModel (m + 1)) :=
    ⟨e.val.target ∩ e.val.symm ⁻¹' V₀, e.val.isOpen_inter_preimage_symm hV₀⟩
  let W := (W₁ ⊓ W₂) ⊓ O
  have hWW₁ : W ≤ W₁ := inf_le_left.trans inf_le_left
  have hWW₂ : W ≤ W₂ := inf_le_left.trans inf_le_right
  have hWO : W ≤ O := inf_le_right
  have hWe : W ≤ chartTarget e := hWW₁.trans hW₁e
  have hzW : z ∈ W := ⟨⟨hz₁, hz₂⟩, hz, hx₀⟩
  have huOn : MDifferentiableOn 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) u V₀ :=
    fun x hx => (hu x hx).mdifferentiableWithinAt
  have hUc : DifferentiableOn ℂ (fun y => u (e.val.symm y)) W :=
    (MeteredDivisorPositivity.differentiableOn_comp_chartSymm e huOn).mono hWO
  have hU0 : ∀ y ∈ W, u (e.val.symm y) ≠ 0 := fun y hy => hu0 _ (hWO hy).2
  have hG₁W : DifferentiableOn ℂ (fun y => g₁ (e.val.symm y)) W := hG₁.mono hWW₁
  have hG₂W : DifferentiableOn ℂ (fun y => g₂ (e.val.symm y)) W := hG₂.mono hWW₂
  have hG₁W0 : ∀ y ∈ W, ∃ᶠ w in 𝓝 y, g₁ (e.val.symm w) ≠ 0 :=
    fun y hy => hG₁0 y (hWW₁ hy)
  have hG₂W0 : ∀ y ∈ W, ∃ᶠ w in 𝓝 y, g₂ (e.val.symm w) ≠ 0 :=
    fun y hy => hG₂0 y (hWW₂ hy)
  obtain ⟨hprod, hprod0, hprod_eq⟩ :=
    ActualNativeDivisorCurrentUnitFactor.exists_divisorCurrent_pow_mul_unit
      hG₁W hUc hG₁W0 hU0 1
  have hdiv : divisorCurrent hG₂W hG₂W0 = divisorCurrent hG₁W hG₁W0 := by
    refine (divisorCurrent_congr_on hG₂W hprod hG₂W0 hprod0 ?_).trans ?_
    · intro y hy
      simpa only [pow_one, mul_comm] using heq (e.val.symm y) (hWO hy).2
    · simpa only [Nat.cast_one, one_smul] using hprod_eq
  let A₁ := (LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₁).coefficients b e
  let A₂ := (LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₂).coefficients b e
  have hreading : complementaryRead (LelongPoincareDivisor.restrictForm A₁ hWe) =
      complementaryRead (LelongPoincareDivisor.restrictForm A₂ hWe) := by
    rw [← reader_restrict, ← reader_restrict]
    calc
      restrict hWe (complementaryRead A₁) = (LelongPoincareDivisor.haarFactor b : ℝ) •
          complementaryRead (divisorCurrent hG₁W hG₁W0) :=
        localReading_mono hW₁e hWW₁ _ hG₁ hG₁0 _ hread₁
      _ = (LelongPoincareDivisor.haarFactor b : ℝ) •
          complementaryRead (divisorCurrent hG₂W hG₂W0) := by rw [hdiv]
      _ = restrict hWe (complementaryRead A₂) :=
        (localReading_mono hW₂e hWW₂ _ hG₂ hG₂0 _ hread₂).symm
  refine ⟨W, hWe, hzW, ?_⟩
  exact ActualOneOneComplementaryReadingInjectivity.eq_of_complementaryRead_eq
    (restrictForm_isOneOne (LelongPoincareDivisor.isTypeOneOne_integrationCurrent b
      (Nat.succ_pos m) E₁ e) hWe)
    (restrictForm_isOneOne (LelongPoincareDivisor.isTypeOneOne_integrationCurrent b
      (Nat.succ_pos m) E₂ e) hWe) hreading

/-- The complete native global current of a genuine effective divisor is
independent of the choice of its actual smooth divisor metric. -/
theorem integrationCurrent_eq_of_isDivisorMetric
    (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel (m + 1)))) ℝ
      (ComplexModel (m + 1))) (D : EffectiveDivisor (m + 1) M)
    (E₁ E₂ : MeteredEffectiveQDivisor (m + 1) M)
    (hm₁ : DivisorMetric.IsDivisorMetric D E₁) (hm₂ : DivisorMetric.IsDivisorMetric D E₂) :
    LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₁ =
      LelongPoincareDivisor.integrationCurrent b (Nat.succ_pos m) E₂ := by
  classical
  apply LelongPoincareDivisor.globalCurrent_ext b
  intro e
  have hlocal (z : chartTarget e) := exists_local_coefficient_eq b D E₁ E₂ hm₁ hm₂ e z.property
  choose W hWe hzW heq using hlocal
  exact LelongPoincareDivisor.form_eq_of_forall_restrictForm_eq W hWe
    (fun z hz => ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩) heq

end SGPT.Foundations.Analysis.Pending.ActualDivisorCurrentMetricIndependence
