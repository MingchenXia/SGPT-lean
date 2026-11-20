import SGPT.IGood.DXLow2Count

/-!
# Moving powers of `L` into the twist, and comparisons of multiplier sections

Blueprint `claude-dx-low2`, node `claude-dx-low2:shift`. Ingredients of the upper bound of
`thm:DXmain1` (the book's Step 2 of its proof):

* `shiftFiber`, `shiftSection`: the isomorphism `L^{⊗(r+p+1)} ⊗ T ≅ L^{⊗(p+1)} ⊗ (L^{⊗r} ⊗ T)`
  (inverse of the multiplication `mulFiber`), on fibers and on holomorphic sections; it preserves
  the pointwise norms (`norm_shiftSection`), hence the multiplier conditions;
* `finrank_full_le_shift`: `h⁰(X, L^{r+p+1} ⊗ T ⊗ 𝓘) ≤ h⁰(X, L^{p+1} ⊗ (L^r ⊗ T) ⊗ 𝓘)` for the
  multiplier ideal `𝓘 = 𝓘(mΦ)` of any degree;
* `mem_full_of_le_degree`: `𝓘(kφ) ⊆ 𝓘(aφ)` for `a ≤ k` (`φ` bounded above);
* `lintegral_mulSection_lt_top'`: integrability of `s t` when `|s|² e^{-bψ} ≤ C` and
  `∫ |t|² e^{-aφ} < ∞`, `b ψ + a φ ≤ m Φ + D`.
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

/-! ### The fiberwise isomorphism -/

section Fiber

variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

theorem frameCoord_symm_one {V : HermitianHolomorphicLineBundle.{0, 0} n X} (g : AtlasFrame V)
    {x : X} (hx : x ∈ g.val.baseSet) (c : ℂ) : frameCoord g x (g.val.symm x c) = c := by
  rw [frameCoord_apply g hx]
  have := g.val.apply_mk_symm hx c
  exact congrArg Prod.snd this

/-- The multiplication `L^{⊗(p+1)} ⊗ (L^{⊗r} ⊗ T) → L^{⊗(r+p+1)} ⊗ T` on the tensor product. -/
def shiftMulFiber (r p : ℕ) (x : X) :
    (twistedPower L (twistedPower L T r) (p + 1)).Fiber x →ₗ[ℂ]
      (twistedPower L T (r + p + 1)).Fiber x :=
  TensorProduct.lift (mulFiber L T x r p)

/-- In product frames the multiplication preserves coordinates. -/
theorem frameCoord_shiftMulFiber (e : AtlasFrame L) (f : AtlasFrame T) {x : X}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) (r p : ℕ)
    (v : (twistedPower L (twistedPower L T r) (p + 1)).Fiber x) :
    frameCoord (twistedPowerAtlasFrame e f (r + p + 1)) x (shiftMulFiber r p x v) =
      frameCoord (twistedPowerAtlasFrame e (twistedPowerAtlasFrame e f r) (p + 1)) x v := by
  have hp := positivePowerAtlasFrame_mem e hx p
  have hr := twistedPowerAtlasFrame_mem e f hx hy r
  have key : (frameCoord (twistedPowerAtlasFrame e f (r + p + 1)) x).comp
      (shiftMulFiber (L := L) (T := T) r p x) =
      frameCoord (twistedPowerAtlasFrame e (twistedPowerAtlasFrame e f r) (p + 1)) x := by
    apply TensorProduct.ext'
    intro a w
    have h1 := frameCoord_mulFiber e f hx hy r p a w
    have h2 := frameCoord_tensor_tmul (positivePowerAtlasFrame e p) (twistedPowerAtlasFrame e f r)
      hp hr a w
    change frameCoord (twistedPowerAtlasFrame e f (r + p + 1)) x (mulFiber L T x r p a w) =
      frameCoord (tensorAtlasFrame (positivePowerAtlasFrame e p) (twistedPowerAtlasFrame e f r)) x
        (a ⊗ₜ[ℂ] w)
    rw [h1, h2]
  exact LinearMap.congr_fun key v

/-- The frames at a point. -/
abbrev frameL (L : HermitianHolomorphicLineBundle.{0, 0} n X) (x : X) : AtlasFrame L :=
  ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩

theorem mem_frameL (L : HermitianHolomorphicLineBundle.{0, 0} n X) (x : X) :
    x ∈ (frameL L x).val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x

theorem shiftMulFiber_bijective (r p : ℕ) (x : X) :
    Function.Bijective (shiftMulFiber (L := L) (T := T) r p x) := by
  set e := frameL L x
  set f := frameL T x
  have hx := mem_frameL L x
  have hy := mem_frameL T x
  set G := twistedPowerAtlasFrame e f (r + p + 1)
  set S := twistedPowerAtlasFrame e (twistedPowerAtlasFrame e f r) (p + 1)
  have hG : x ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e f hx hy _
  have hS : x ∈ S.val.baseSet := twistedPowerAtlasFrame_mem e _ hx
    (twistedPowerAtlasFrame_mem e f hx hy r) _
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := frameCoord_shiftMulFiber e f hx hy r p v
    rw [hv, map_zero] at h
    exact (frameCoord_eq_zero_iff S hS v).mp h.symm
  · intro w
    refine ⟨frameCoord G x w • S.val.symm x 1, ?_⟩
    have hinj : ∀ a b, frameCoord G x a = frameCoord G x b → a = b := by
      intro a b hab
      have := (frameCoord_eq_zero_iff G hG (a - b)).mp (by rw [map_sub, hab, sub_self])
      exact sub_eq_zero.mp this
    apply hinj
    rw [frameCoord_shiftMulFiber e f hx hy r p, map_smul, frameCoord_symm_one S hS, smul_eq_mul,
      mul_one]

/-- The isomorphism `L^{⊗(r+p+1)} ⊗ T ≅ L^{⊗(p+1)} ⊗ (L^{⊗r} ⊗ T)` on fibers. -/
def shiftFiber (r p : ℕ) (x : X) :
    (twistedPower L T (r + p + 1)).Fiber x ≃ₗ[ℂ]
      (twistedPower L (twistedPower L T r) (p + 1)).Fiber x :=
  (LinearEquiv.ofBijective (shiftMulFiber (L := L) (T := T) r p x)
    (shiftMulFiber_bijective r p x)).symm

theorem shiftMulFiber_shiftFiber (r p : ℕ) (x : X) (w : (twistedPower L T (r + p + 1)).Fiber x) :
    shiftMulFiber r p x (shiftFiber r p x w) = w :=
  (LinearEquiv.ofBijective (shiftMulFiber (L := L) (T := T) r p x)
    (shiftMulFiber_bijective r p x)).apply_symm_apply w

theorem frameCoord_shiftFiber (e : AtlasFrame L) (f : AtlasFrame T) {x : X}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) (r p : ℕ)
    (w : (twistedPower L T (r + p + 1)).Fiber x) :
    frameCoord (twistedPowerAtlasFrame e (twistedPowerAtlasFrame e f r) (p + 1)) x
        (shiftFiber r p x w) =
      frameCoord (twistedPowerAtlasFrame e f (r + p + 1)) x w := by
  rw [← frameCoord_shiftMulFiber e f hx hy r p, shiftMulFiber_shiftFiber]

end Fiber

/-! ### Sections -/

section Sections

variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The isomorphism `H⁰(X, L^{r+p+1} ⊗ T) → H⁰(X, L^{p+1} ⊗ (L^r ⊗ T))`. -/
def shiftSection {r p : ℕ} (σ : twistedSections L T (r + p + 1)) :
    twistedSections L (twistedPower L T r) (p + 1) where
  toFun x := shiftFiber r p x (σ x)
  contMDiff_toFun := by
    intro x₀
    let e := frameL L x₀
    let f := frameL T x₀
    have he := mem_frameL L x₀
    have hf := mem_frameL T x₀
    let G := twistedPowerAtlasFrame e f (r + p + 1)
    let S := twistedPowerAtlasFrame e (twistedPowerAtlasFrame e f r) (p + 1)
    let := G.property
    let := S.property
    have hG : ∀ y ∈ e.val.baseSet ∩ f.val.baseSet, y ∈ G.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e f hy.1 hy.2 _
    have hS : ∀ y ∈ e.val.baseSet ∩ f.val.baseSet, y ∈ S.val.baseSet := fun y hy =>
      twistedPowerAtlasFrame_mem e _ hy.1 (twistedPowerAtlasFrame_mem e f hy.1 hy.2 r) _
    apply (S.val.contMDiffAt_section_iff (hS x₀ ⟨he, hf⟩)).mpr
    have hσ := (G.val.contMDiffAt_section_iff (hG x₀ ⟨he, hf⟩)).mp (σ.contMDiff x₀)
    apply hσ.congr_of_eventuallyEq
    filter_upwards [(e.val.open_baseSet.inter f.val.open_baseSet).mem_nhds ⟨he, hf⟩] with y hy
    rw [← frameCoord_apply S (hS y hy), ← frameCoord_apply G (hG y hy),
      frameCoord_shiftFiber e f hy.1 hy.2]

theorem shiftSection_apply {r p : ℕ} (σ : twistedSections L T (r + p + 1)) (x : X) :
    shiftSection σ x = shiftFiber r p x (σ x) := rfl

/-- `shiftSection` as a `ℂ`-linear map. -/
def shiftSectionLinear (r p : ℕ) :
    twistedSections L T (r + p + 1) →ₗ[ℂ] twistedSections L (twistedPower L T r) (p + 1) where
  toFun := shiftSection
  map_add' σ₁ σ₂ := by
    ext x
    exact map_add (shiftFiber r p x) (σ₁ x) (σ₂ x)
  map_smul' c σ := by
    ext x
    exact map_smul (shiftFiber r p x) c (σ x)

theorem shiftSectionLinear_injective (r p : ℕ) :
    Function.Injective (shiftSectionLinear (L := L) (T := T) r p) := by
  intro σ₁ σ₂ h
  ext x
  have := congrArg (fun τ => (τ : twistedSections L (twistedPower L T r) (p + 1)) x) h
  exact (shiftFiber r p x).injective this

/-- The isomorphism preserves the tensor metrics. -/
theorem norm_shiftSection {r p : ℕ} (σ : twistedSections L T (r + p + 1)) (y : X) :
    ‖shiftSection σ y‖ = ‖σ y‖ := by
  let e := frameL L y
  let f := frameL T y
  have he := mem_frameL L y
  have hf := mem_frameL T y
  let G := twistedPowerAtlasFrame e f (r + p + 1)
  let F := twistedPowerAtlasFrame e f r
  let S := twistedPowerAtlasFrame e F (p + 1)
  let := G.property
  let := S.property
  have hF : y ∈ F.val.baseSet := twistedPowerAtlasFrame_mem e f he hf r
  have hG : y ∈ G.val.baseSet := twistedPowerAtlasFrame_mem e f he hf _
  have hS : y ∈ S.val.baseSet := twistedPowerAtlasFrame_mem e F he hF _
  have nG := norm_eq_coefficient_mul_frameNorm (twistedPower L T (r + p + 1)).Fiber G.val σ hG
  have nS := norm_eq_coefficient_mul_frameNorm (twistedPower L (twistedPower L T r) (p + 1)).Fiber
    S.val (shiftSection σ) hS
  have fG := twistedPower_frame_norm e f he hf (r + p + 1)
  have fS := twistedPower_frame_norm e F he hF (p + 1)
  have fF := twistedPower_frame_norm e f he hf r
  have hc : sectionCoefficient (twistedPower L (twistedPower L T r) (p + 1)).Fiber S.val
      (shiftSection σ) y = sectionCoefficient (twistedPower L T (r + p + 1)).Fiber G.val σ y := by
    change (S.val ⟨y, shiftSection σ y⟩).2 = (G.val ⟨y, σ y⟩).2
    rw [← frameCoord_apply S hS, ← frameCoord_apply G hG, shiftSection_apply,
      frameCoord_shiftFiber e f he hf]
  rw [nS, nG, hc]
  simp only [frameNorm]
  rw [fS, fG, fF]
  ring

end Sections

/-! ### Multiplier sections -/

section Multiplier

variable [MeasurableSpace X] [BorelSpace X]
variable {L T : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- **Moving `L^r` into the twist**: for every degree `m` and every quasi-psh `Φ`,
`h⁰(X, L^{r+p+1} ⊗ T ⊗ 𝓘(mΦ)) ≤ h⁰(X, L^{p+1} ⊗ (L^r ⊗ T) ⊗ 𝓘(mΦ))`. -/
theorem finrank_full_le_shift [CompactSpace X] {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (r p m : ℕ) {Φ : X → EReal}
    (hΦ : IsGlobalQuasiPshPotential (n := n) Φ) :
    Module.finrank ℂ (fullHolomorphicIdealSections (n := n) (twistedPower L T (r + p + 1)).Fiber
        (sourceDegreeMultiplierIdeal (n := n) m Φ)) ≤
      Module.finrank ℂ (fullHolomorphicIdealSections (n := n)
        (twistedPower L (twistedPower L T r) (p + 1)).Fiber
        (sourceDegreeMultiplierIdeal (n := n) m Φ)) := by
  have hmaps : ∀ σ ∈ fullHolomorphicIdealSections (n := n) (twistedPower L T (r + p + 1)).Fiber
      (sourceDegreeMultiplierIdeal (n := n) m Φ),
      shiftSectionLinear r p σ ∈ fullHolomorphicIdealSections (n := n)
        (twistedPower L (twistedPower L T r) (p + 1)).Fiber
        (sourceDegreeMultiplierIdeal (n := n) m Φ) := by
    intro σ hσ
    rw [fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ m hΦ _ hμ] at hσ ⊢
    have heq : ∀ y, originalSectionDensity (n := n)
        (twistedPower L (twistedPower L T r) (p + 1)).Fiber Φ m (shiftSectionLinear r p σ) y =
        originalSectionDensity (n := n) (twistedPower L T (r + p + 1)).Fiber Φ m σ y := by
      intro y
      simp only [originalSectionDensity]
      rw [show shiftSectionLinear r p σ = shiftSection σ from rfl, norm_shiftSection]
    simp_rw [heq]
    exact hσ
  let F := (shiftSectionLinear (L := L) (T := T) r p).restrict hmaps
  have hF : Function.Injective F := by
    intro a b h
    exact Subtype.ext (shiftSectionLinear_injective r p (congrArg Subtype.val h))
  let := fullTwistedMultiplierSections_finiteDimensional L (twistedPower L T r) (p + 1)
  have : FiniteDimensional ℂ (fullHolomorphicIdealSections (n := n)
      (twistedPower L (twistedPower L T r) (p + 1)).Fiber
      (sourceDegreeMultiplierIdeal (n := n) m Φ)) := by
    let := twistedSections_finiteDimensional L (twistedPower L T r) (p + 1)
    infer_instance
  exact LinearMap.finrank_le_finrank_of_injective hF

/-- `𝓘(kφ) ⊆ 𝓘(aφ)` for `a ≤ k` (with `φ ≤ M`), on sections of any `V`. -/
theorem mem_full_of_le_degree [CompactSpace X] {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ)
    (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
    [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
    [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] [ContinuousFiberNorm V]
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ) {M : ℝ}
    (hφM : ∀ x, φ x ≤ (M : EReal)) {a k : ℕ} (hak : a ≤ k) {t : HolomorphicSections (n := n) V}
    (ht : t ∈ fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) k φ)) :
    t ∈ fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) a φ) := by
  rw [fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) _ _ hφ _ hμ] at ht ⊢
  have hka : (0 : ℝ) ≤ (k : ℝ) - a := by
    have : (a : ℝ) ≤ k := by exact_mod_cast hak
    linarith
  have hpt : ∀ y, originalSectionDensity (n := n) V φ a t y ≤
      ENNReal.ofReal (Real.exp (((k : ℝ) - a) * M)) * originalSectionDensity (n := n) V φ k t y := by
    intro y
    have hineq : ((k : ℝ) : EReal) * φ y + ((0 : ℝ) : EReal) * (0 : EReal) ≤
        ((a : ℝ) : EReal) * φ y + ((((k : ℝ) - a) * M : ℝ) : EReal) := by
      rw [EReal.coe_zero, zero_mul, add_zero,
        show ((k : ℝ) : EReal) = ((a : ℝ) : EReal) + (((k : ℝ) - a : ℝ) : EReal) by
          rw [← EReal.coe_add]; congr 1; ring,
        EReal.right_distrib_of_nonneg (by exact_mod_cast (Nat.cast_nonneg a))
          (by exact_mod_cast hka)]
      gcongr
      calc (((k : ℝ) - a : ℝ) : EReal) * φ y ≤ (((k : ℝ) - a : ℝ) : EReal) * (M : EReal) :=
            mul_le_mul_of_nonneg_left (hφM y) (by exact_mod_cast hka)
        _ = _ := by rw [← EReal.coe_mul]
    have hw := multiplierWeight_le_mul (Nat.cast_nonneg k) le_rfl (hφ.1.ne_top y)
      (EReal.zero_ne_top) hineq
    simp only [originalSectionDensity]
    calc ENNReal.ofReal (‖t y‖ ^ 2) * multiplierWeight (a : ℝ) (φ y)
        ≤ ENNReal.ofReal (‖t y‖ ^ 2) * (ENNReal.ofReal (Real.exp (((k : ℝ) - a) * M)) *
            (multiplierWeight (k : ℝ) (φ y) * multiplierWeight 0 0)) := by gcongr
      _ = _ := by
          simp only [multiplierWeight, EReal.coe_zero, zero_mul, neg_zero, EReal.exp_zero,
            mul_one]
          ring
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (((k : ℝ) - a) * M)) *
        originalSectionDensity (n := n) V φ k t y ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (((k : ℝ) - a) * M)) *
        ∫⁻ y, originalSectionDensity (n := n) V φ k t y ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ht

/-- **Integrability of the product, bounded factor `s`**: if `|s|² e^{-bψ} ≤ C`,
`∫ |t|² e^{-aφ} < ∞` and `b ψ + a φ ≤ m Φ + D`, then `∫ |s t|² e^{-mΦ} < ∞`. -/
theorem lintegral_mulSection_lt_top' {μ : Measure X} {p k : ℕ}
    {s : twistedSections L unit (p + 1)} {t : twistedSections L T k}
    {ψ φ Φ : X → EReal} (hψ : ∀ x, ψ x ≠ ⊤) (hφ : ∀ x, φ x ≠ ⊤) {a m : ℕ} {D C : ℝ}
    (hineq : ∀ x, (((p + 1 : ℕ) : ℝ) : EReal) * ψ x + ((a : ℝ) : EReal) * φ x ≤
      ((m : ℝ) : EReal) * Φ x + (D : EReal))
    (hC : ∀ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight ((p + 1 : ℕ) : ℝ) (ψ y) ≤
      ENNReal.ofReal C)
    (ht : (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ a t x ∂μ) < ⊤) :
    (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T (k + p + 1)).Fiber Φ m
      (mulSection s t) x ∂μ) < ⊤ := by
  have hpt : ∀ x, originalSectionDensity (n := n) (twistedPower L T (k + p + 1)).Fiber Φ m
      (mulSection s t) x ≤ (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        originalSectionDensity (n := n) (twistedPower L T k).Fiber φ a t x := by
    intro x
    have hw := multiplierWeight_le_mul (Nat.cast_nonneg (p + 1)) (Nat.cast_nonneg a) (hψ x) (hφ x)
      (hineq x)
    simp only [originalSectionDensity]
    rw [norm_mulSection, mul_pow, ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (‖s x‖ ^ 2) * ENNReal.ofReal (‖t x‖ ^ 2) * multiplierWeight (m : ℝ) (Φ x)
        ≤ ENNReal.ofReal (‖s x‖ ^ 2) * ENNReal.ofReal (‖t x‖ ^ 2) *
          (ENNReal.ofReal (Real.exp D) *
            (multiplierWeight ((p + 1 : ℕ) : ℝ) (ψ x) * multiplierWeight (a : ℝ) (φ x))) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp D) *
            (ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight ((p + 1 : ℕ) : ℝ) (ψ x)) *
            (ENNReal.ofReal (‖t x‖ ^ 2) * multiplierWeight (a : ℝ) (φ x)) := by ring
      _ ≤ ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C *
            (ENNReal.ofReal (‖t x‖ ^ 2) * multiplierWeight (a : ℝ) (φ x)) := by
          gcongr
          exact hC x
  calc _ ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        originalSectionDensity (n := n) (twistedPower L T k).Fiber φ a t x ∂μ := lintegral_mono hpt
    _ = (ENNReal.ofReal (Real.exp D) * ENNReal.ofReal C) *
        ∫⁻ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ a t x ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) ht

end Multiplier

end SGPT.IGood.DXLow2
