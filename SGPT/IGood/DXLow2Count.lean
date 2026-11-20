import SGPT.IGood.DXLow2Mul
import SGPT.PSH.MultiplierIdealInfSkoda

/-!
# Counting sections by multiplication

Blueprint `claude-dx-low2`, node `claude-dx-low2:count`. The section-counting step of the book's
Step 1 of the proof of `thm:DXmain1` (chapter *`𝓘`-good singularities*):

if `s ∈ H⁰(X, L^b ⊗ 𝓘(bη))` is non-zero, every `t ∈ H⁰(X, L^m ⊗ T ⊗ 𝓘(m w))` satisfies a
pointwise bound `|t|² ≤ C e^{m v}` (`t ∈ 𝓘_∞(m v)`, from `lma:IandIinf` when `w = c v`, `c > 1`),
and `m v + b η ≤ (m + b) Φ + D` pointwise, then multiplication by `s` maps
`H⁰(X, L^m ⊗ T ⊗ 𝓘(m w))` injectively into `H⁰(X, L^{m+b} ⊗ T ⊗ 𝓘((m+b)Φ))`, so

`h⁰(X, L^m ⊗ T ⊗ 𝓘(m w)) ≤ h⁰(X, L^{m+b} ⊗ T ⊗ 𝓘((m+b)Φ))`

(`finrank_le_of_mul`). The membership `s t ∈ 𝓘((m+b)Φ)` is checked through the global `L²`
criterion `∫_X |s t|² e^{-(m+b)Φ} dμ < ∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.IGood.DXLow2

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### Elementary inequalities for the weights -/

theorem ereal_coe_mul_ne_top {c : ℝ} (hc : 0 ≤ c) {a : EReal} (ha : a ≠ ⊤) :
    (c : EReal) * a ≠ ⊤ := by
  induction a using EReal.rec with
  | bot =>
    rcases hc.lt_or_eq with hc | rfl
    · rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
    · simp
  | coe a => exact EReal.coe_ne_top _
  | top => exact absurd rfl ha

/-- `e^{-kΦ} ≤ e^D e^{-m v} e^{-b η}` when `m v + b η ≤ k Φ + D`. -/
theorem multiplierWeight_le_mul {m b k D : ℝ} (hm : 0 ≤ m) (hb : 0 ≤ b) {a c Φ : EReal}
    (ha : a ≠ ⊤) (hc : c ≠ ⊤)
    (h : (m : EReal) * a + (b : EReal) * c ≤ (k : EReal) * Φ + (D : EReal)) :
    multiplierWeight k Φ ≤
      ENNReal.ofReal (Real.exp D) * (multiplierWeight m a * multiplierWeight b c) := by
  have hexp : EReal.exp ((m : EReal) * a) * EReal.exp ((b : EReal) * c) ≤
      EReal.exp ((k : EReal) * Φ) * ENNReal.ofReal (Real.exp D) := by
    rw [← EReal.exp_add, ← EReal.exp_coe, ← EReal.exp_add]
    exact EReal.exp_monotone h
  have hA : EReal.exp ((m : EReal) * a) ≠ ⊤ := by
    rw [Ne, EReal.exp_eq_top_iff]; exact ereal_coe_mul_ne_top hm ha
  have hB : EReal.exp ((b : EReal) * c) ≠ ⊤ := by
    rw [Ne, EReal.exp_eq_top_iff]; exact ereal_coe_mul_ne_top hb hc
  have hD0 : ENNReal.ofReal (Real.exp D) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos D
  have hDt : ENNReal.ofReal (Real.exp D) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [multiplierWeight, EReal.exp_neg]
  have hinv := ENNReal.inv_le_inv.mpr hexp
  rw [ENNReal.mul_inv (Or.inr hDt) (Or.inr hD0), ENNReal.mul_inv (Or.inr hB) (Or.inl hA)] at hinv
  calc (EReal.exp ((k : EReal) * Φ))⁻¹
      = ENNReal.ofReal (Real.exp D) *
          ((EReal.exp ((k : EReal) * Φ))⁻¹ * (ENNReal.ofReal (Real.exp D))⁻¹) := by
        rw [mul_comm (EReal.exp _)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel hD0 hDt, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp D) *
          ((EReal.exp ((m : EReal) * a))⁻¹ * (EReal.exp ((b : EReal) * c))⁻¹) := by
        gcongr

/-! ### The `𝓘_∞` bound -/

section InftyBound

variable (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]

/-- **The `𝓘_∞` bound** (consequence of `lma:IandIinf`): if `𝓘(m c v) ⊆ 𝓘_∞(m v)` and
`t ∈ H⁰(X, V ⊗ 𝓘(m · c v))`, then `|t|² e^{-m v} ≤ C` on the compact manifold `X`. -/
theorem exists_bound_of_mem_of_le_inftyIdeal [CompactSpace X] {v : X → EReal} {c : ℝ} {m : ℕ}
    (hw : IsGlobalQuasiPshPotential (n := n) (fun x => (c : EReal) * v x))
    (hle : (multiplierIdeal (n := n) 1 (fun x => (((m : ℝ) * c : ℝ) : EReal) * v x)).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun x => ((m : ℝ) : EReal) * v x)))
    (t : HolomorphicSections (n := n) V)
    (ht : t ∈ fullHolomorphicIdealSections (n := n) V
      (sourceDegreeMultiplierIdeal (n := n) m (fun x => (c : EReal) * v x))) :
    ∃ C : ℝ, ∀ y, ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight m (v y) ≤ ENNReal.ofReal C := by
  classical
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) V _
    (sourceDegreeMultiplierIdeal_isCoherent m hw) t] at ht
  have hfun : (fun x => ((m : ℝ) : EReal) * ((c : EReal) * v x)) =
      fun x => (((m : ℝ) * c : ℝ) : EReal) * v x := by
    funext x; rw [← mul_assoc, ← EReal.coe_mul]
  -- the local bound near every point
  have hloc : ∀ x : X, ∃ U ∈ 𝓝 x, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U,
      ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight m (v y) ≤ ENNReal.ofReal C := by
    intro x
    let e := (preferredOriginalFrame V x).val
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
    have hmem := ht x
    change (multiplierIdeal (n := n) 1 (fun x => ((m : ℝ) : EReal) * ((c : EReal) * v x))).mem x
      _ at hmem
    rw [hfun] at hmem
    obtain ⟨-, K, hK, hKev⟩ := hle x _ hmem
    have hcont := (frameNorm_continuousOn V e).continuousAt (e.open_baseSet.mem_nhds hx)
    have hFev : ∀ᶠ y in 𝓝 x, frameNorm V e y < frameNorm V e x + 1 :=
      hcont.eventually (gt_mem_nhds (lt_add_one _))
    refine ⟨e.baseSet ∩ {y | frameNorm V e y < frameNorm V e x + 1 ∧
        multiplierDensity (fun y => ((m : ℝ) : EReal) * v y) 1
          (sectionCoefficient V e t) y ≤ ENNReal.ofReal K},
      Filter.inter_mem (e.open_baseSet.mem_nhds hx) (hFev.and hKev),
      K * (frameNorm V e x + 1) ^ 2, by positivity, ?_⟩
    rintro y ⟨hyb, hyF, hyK⟩
    have hnorm := norm_eq_coefficient_mul_frameNorm V e t hyb
    have hF0 : 0 ≤ frameNorm V e y := norm_nonneg _
    rw [hnorm, mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal _),
      mul_assoc]
    have hw1 : multiplierWeight m (v y) = multiplierWeight 1 (((m : ℝ) : EReal) * v y) := by
      simp [multiplierWeight]
    rw [hw1]
    change ENNReal.ofReal (frameNorm V e y ^ 2) *
      multiplierDensity (fun y => ((m : ℝ) : EReal) * v y) 1 (sectionCoefficient V e t) y ≤ _
    calc _ ≤ ENNReal.ofReal ((frameNorm V e x + 1) ^ 2) * ENNReal.ofReal K := by
          gcongr
      _ = ENNReal.ofReal (K * (frameNorm V e x + 1) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_comm]
  choose U hU C hC hb using hloc
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  refine ⟨∑ x ∈ s, C x, fun y => ?_⟩
  have hy : y ∈ ⋃ x ∈ s, U x := hs ▸ Set.mem_univ y
  obtain ⟨x, hxs, hyx⟩ := Set.mem_iUnion₂.mp hy
  calc _ ≤ ENNReal.ofReal (C x) := hb x y hyx
    _ ≤ ENNReal.ofReal (∑ x ∈ s, C x) :=
        ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun x _ => hC x) hxs)

end InftyBound

/-! ### The product lies in the multiplier ideal -/

section Product

variable [MeasurableSpace X] [BorelSpace X]
variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- **Integrability of the product**: if `|t|² e^{-m v} ≤ C`, `∫ |s|² e^{-bη} < ∞` and
`m v + b η ≤ (m+b) Φ + D`, then `∫ |s t|² e^{-(m+b)Φ} < ∞`. -/
theorem lintegral_mulSection_lt_top {μ : Measure X} {p m : ℕ}
    {s : twistedSections L unit (p + 1)} {t : twistedSections L T m}
    {v η Φ : X → EReal} (hv : ∀ x, v x ≠ ⊤) (hη : ∀ x, η x ≠ ⊤) {D C : ℝ}
    (hineq : ∀ x, ((m : ℝ) : EReal) * v x + (((p + 1 : ℕ) : ℝ) : EReal) * η x ≤
      (((m + p + 1 : ℕ) : ℝ) : EReal) * Φ x + (D : EReal))
    (hC : ∀ y, ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight m (v y) ≤ ENNReal.ofReal C)
    (hs : (∫⁻ x, originalSectionDensity (n := n) (twistedPower L unit (p + 1)).Fiber η
      (p + 1 : ℕ) s x ∂μ) < ⊤) :
    (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T (m + p + 1)).Fiber Φ
      (m + p + 1 : ℕ) (mulSection s t) x ∂μ) < ⊤ := by
  have hpt : ∀ x, originalSectionDensity (n := n) (twistedPower L T (m + p + 1)).Fiber Φ
      (m + p + 1 : ℕ) (mulSection s t) x ≤
      (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        originalSectionDensity (n := n) (twistedPower L unit (p + 1)).Fiber η (p + 1 : ℕ) s x := by
    intro x
    have hw := multiplierWeight_le_mul (Nat.cast_nonneg m) (Nat.cast_nonneg (p + 1)) (hv x) (hη x)
      (hineq x)
    simp only [originalSectionDensity]
    rw [norm_mulSection, mul_pow, ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (‖s x‖ ^ 2) * ENNReal.ofReal (‖t x‖ ^ 2) *
          multiplierWeight (↑(m + p + 1)) (Φ x)
        ≤ ENNReal.ofReal (‖s x‖ ^ 2) * ENNReal.ofReal (‖t x‖ ^ 2) *
          (ENNReal.ofReal (Real.exp D) *
            (multiplierWeight (m : ℝ) (v x) * multiplierWeight ((p + 1 : ℕ) : ℝ) (η x))) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp D) *
            (ENNReal.ofReal (‖t x‖ ^ 2) * multiplierWeight (m : ℝ) (v x)) *
            (ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight ((p + 1 : ℕ) : ℝ) (η x)) := by ring
      _ ≤ ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C *
            (ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight ((p + 1 : ℕ) : ℝ) (η x)) := by
          gcongr
          exact hC x
  calc _ ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        originalSectionDensity (n := n) (twistedPower L unit (p + 1)).Fiber η (p + 1 : ℕ) s x ∂μ :=
        lintegral_mono hpt
    _ = (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        ∫⁻ x, originalSectionDensity (n := n) (twistedPower L unit (p + 1)).Fiber η
          (p + 1 : ℕ) s x ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hs

/-- **Counting sections by multiplication** (book's Step 1 of `thm:DXmain1`): with
`s ∈ H⁰(X, L^{p+1} ⊗ 𝓘((p+1)η))` non-zero, `𝓘(m c v) ⊆ 𝓘_∞(m v)` and
`m v + (p+1) η ≤ (m+p+1) Φ + D`,
`h⁰(X, L^m ⊗ T ⊗ 𝓘(m · c v)) ≤ h⁰(X, L^{m+p+1} ⊗ T ⊗ 𝓘((m+p+1)Φ))`. -/
theorem finrank_le_of_mul [CompactSpace X] [ConnectedSpace X] {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {p m : ℕ}
    {v η Φ : X → EReal} {c D : ℝ}
    (hw : IsGlobalQuasiPshPotential (n := n) (fun x => (c : EReal) * v x))
    (hv : ∀ x, v x ≠ ⊤) (hηq : IsGlobalQuasiPshPotential (n := n) η)
    (hΦ : IsGlobalQuasiPshPotential (n := n) Φ)
    (hle : (multiplierIdeal (n := n) 1 (fun x => (((m : ℝ) * c : ℝ) : EReal) * v x)).Le
      (SGPT.PSH.inftyIdeal (n := n) (fun x => ((m : ℝ) : EReal) * v x)))
    (hineq : ∀ x, ((m : ℝ) : EReal) * v x + (((p + 1 : ℕ) : ℝ) : EReal) * η x ≤
      (((m + p + 1 : ℕ) : ℝ) : EReal) * Φ x + (D : EReal))
    {s : twistedSections L unit (p + 1)} (hs0 : s ≠ 0)
    (hs : s ∈ fullHolomorphicIdealSections (n := n) (twistedPower L unit (p + 1)).Fiber
      (sourceDegreeMultiplierIdeal (n := n) (p + 1) η)) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T m (fun x => (c : EReal) * v x)) ≤
      Module.finrank ℂ (LiteralTwistedMultiplierSections L T (m + p + 1) Φ) := by
  have hsint := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ (p + 1) hηq s
    hμ).mp hs
  have hηt : ∀ x, η x ≠ ⊤ := fun x => hηq.1.ne_top x
  have hmaps : ∀ t ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T m).Fiber
      (sourceDegreeMultiplierIdeal (n := n) m (fun x => (c : EReal) * v x)),
      mulSectionLinear s m t ∈ fullHolomorphicIdealSections (n := n)
        (twistedPower L T (m + p + 1)).Fiber (sourceDegreeMultiplierIdeal (n := n) (m + p + 1) Φ) := by
    intro t ht
    obtain ⟨C, hC⟩ := exists_bound_of_mem_of_le_inftyIdeal _ hw hle t ht
    exact (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ (m + p + 1) hΦ _
      hμ).mpr (lintegral_mulSection_lt_top hv hηt hineq hC hsint)
  let F := (mulSectionLinear (T := T) s m).restrict hmaps
  have hF : Function.Injective F := by
    intro t₁ t₂ h
    apply Subtype.ext
    exact mulSectionLinear_injective hs0 m (congrArg Subtype.val h)
  let := fullTwistedMultiplierSections_finiteDimensional L T (m + p + 1) Φ
  rw [(literalTwistedMultiplierSectionEquiv L T m _).finrank_eq,
    (literalTwistedMultiplierSectionEquiv L T (m + p + 1) Φ).finrank_eq]
  exact LinearMap.finrank_le_finrank_of_injective hF

end Product

end SGPT.IGood.DXLow2
