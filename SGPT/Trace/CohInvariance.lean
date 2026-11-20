import SGPT.GAGA.CohCircle
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicMultiplierGermCovariance
import SGPT.Foundations.Analysis.Pending.SNCCoordinateUnitCorrection
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentials
import SGPT.PSH.BookPSHMetrics

/-!
# Multiplier ideals of invariant weights are invariant under a circle action

Infrastructure of lane COHERENT (source `lma:fibIeq`, `chapter_trace.tex` lines 1166--1193:
"`h` and `h'` are invariant under this action"; blueprint `claude-coherent.tex`).

* `actChartEquiv σ θ y`: the action `σ_{-θ}` read in the preferred charts at `σ_θ y` and `y`, a
  local biholomorphism of `ℂⁿ` (inverse `σ_θ`).
* `CircleActionLift`, `IsInvariantMetric`: lifts of the `σ_θ` to holomorphic bundle maps of
  `L` (fibrewise linear and injective) and metrics invariant under them.
* `exists_shift_of_isInvariantMetric`: for an invariant psh metric `h = h₀ e^{-φ}`,
  `φ ∘ σ_θ = φ + u` near every point with `u` continuous (in local frames `s`, `s'`,
  `σ̃_θ s = a s' ∘ σ_θ` with `a` continuous and nonvanishing, and
  `u = log(|a|² |s' ∘ σ_θ|²_{h₀} / |s|²_{h₀})`).
* `isInvariantIdeal_multiplierIdeal`: the multiplier ideals `𝓘(cφ)` of an invariant metric are
  invariant ideals.
* `multiplierIdeal_act_iff`: if `φ` is quasi-psh and `φ ∘ σ_θ - φ` is locally a continuous real
  function, then `g ∈ 𝓘(cφ)_{σ_θ y}` iff `g ∘ σ_θ ∈ 𝓘(cφ)_y` (change of variables
  `multiplierIntegrableAt_comp_inv_iff` and invariance under continuous perturbations of the
  weight).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Trace.CohFib

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
  SGPT.GAGA.Coherent

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

theorem CircleAction.continuous_act (σ : CircleAction n X) (θ : ℝ) : Continuous (σ.act θ) :=
  σ.continuous.comp (continuous_const.prodMk continuous_id)

/-- A holomorphic self-map read between two preferred charts is holomorphic. -/
theorem differentiableAt_chart_comp {x₁ x₂ : X} {F : X → X}
    (hF : MDifferentiable 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) F) {w : ComplexModel n}
    (hw : w ∈ (chartAt (ComplexModel n) x₁).target)
    (hFw : F ((chartAt (ComplexModel n) x₁).symm w) ∈ (chartAt (ComplexModel n) x₂).source) :
    DifferentiableAt ℂ
      (fun w => chartAt (ComplexModel n) x₂ (F ((chartAt (ComplexModel n) x₁).symm w))) w := by
  have h1 := HolomorphicBoundedQuotient.mdifferentiableAt_chartAt_symm hw
  have h2 := (hF ((chartAt (ComplexModel n) x₁).symm w)).comp w h1
  have h3 := (HolomorphicBoundedQuotient.mdifferentiableAt_chartAt hFw).comp w h2
  rw [mdifferentiableAt_iff_differentiableAt] at h3
  exact h3

/-- `σ_{-θ}` read in the preferred charts at `σ_θ y` (source) and `y` (target), as a local
biholomorphism with inverse `σ_θ`. -/
def actChartEquiv (σ : CircleAction n X) (θ : ℝ) (y : X) :
    LocalHolomorphicEquivAt (n := n)
      (chartAt (ComplexModel n) (σ.act θ y) (σ.act θ y)) where
  source := (chartAt (ComplexModel n) (σ.act θ y)).target ∩
    (chartAt (ComplexModel n) (σ.act θ y)).symm ⁻¹'
      (σ.act (-θ) ⁻¹' (chartAt (ComplexModel n) y).source)
  target := (chartAt (ComplexModel n) y).target ∩ (chartAt (ComplexModel n) y).symm ⁻¹'
      (σ.act θ ⁻¹' (chartAt (ComplexModel n) (σ.act θ y)).source)
  isOpen_source := (chartAt (ComplexModel n) (σ.act θ y)).continuousOn_symm.isOpen_inter_preimage
    (chartAt (ComplexModel n) (σ.act θ y)).open_target
    ((chartAt (ComplexModel n) y).open_source.preimage (CircleAction.continuous_act σ (-θ)))
  isOpen_target := (chartAt (ComplexModel n) y).continuousOn_symm.isOpen_inter_preimage
    (chartAt (ComplexModel n) y).open_target
    ((chartAt (ComplexModel n) (σ.act θ y)).open_source.preimage
      (CircleAction.continuous_act σ θ))
  center_mem_source := by
    refine ⟨(chartAt (ComplexModel n) (σ.act θ y)).map_source
      (mem_chart_source (ComplexModel n) _), ?_⟩
    simp only [mem_preimage]
    rw [(chartAt (ComplexModel n) (σ.act θ y)).left_inv (mem_chart_source (ComplexModel n) _),
      σ.act_neg_act]
    exact mem_chart_source (ComplexModel n) y
  toFun w := chartAt (ComplexModel n) y
    (σ.act (-θ) ((chartAt (ComplexModel n) (σ.act θ y)).symm w))
  invFun v := chartAt (ComplexModel n) (σ.act θ y)
    (σ.act θ ((chartAt (ComplexModel n) y).symm v))
  toFun_holomorphic := fun w hw =>
    (differentiableAt_chart_comp (σ.mdifferentiable (-θ)) hw.1 hw.2).differentiableWithinAt
  invFun_holomorphic := fun v hv =>
    (differentiableAt_chart_comp (σ.mdifferentiable θ) hv.1 hv.2).differentiableWithinAt
  mapsTo_toFun := by
    intro w hw
    refine ⟨(chartAt (ComplexModel n) y).map_source hw.2, ?_⟩
    simp only [mem_preimage]
    rw [(chartAt (ComplexModel n) y).left_inv hw.2, σ.act_act_neg]
    exact (chartAt (ComplexModel n) (σ.act θ y)).map_target hw.1
  mapsTo_invFun := by
    intro v hv
    refine ⟨(chartAt (ComplexModel n) (σ.act θ y)).map_source hv.2, ?_⟩
    simp only [mem_preimage]
    rw [(chartAt (ComplexModel n) (σ.act θ y)).left_inv hv.2, σ.act_neg_act]
    exact (chartAt (ComplexModel n) y).map_target hv.1
  left_inv := by
    intro w hw
    rw [(chartAt (ComplexModel n) y).left_inv hw.2, σ.act_act_neg,
      (chartAt (ComplexModel n) (σ.act θ y)).right_inv hw.1]
  right_inv := by
    intro v hv
    rw [(chartAt (ComplexModel n) (σ.act θ y)).left_inv hv.2, σ.act_neg_act,
      (chartAt (ComplexModel n) y).right_inv hv.1]

theorem holomorphicAt_comp_act (σ : CircleAction n X) (θ : ℝ) {y : X} {g : X → ℂ}
    (hg : HolomorphicAt n g (σ.act θ y)) : HolomorphicAt n (fun p => g (σ.act θ p)) y := by
  have hT : Tendsto (σ.act θ) (𝓝 y) (𝓝 (σ.act θ y)) := (CircleAction.continuous_act σ θ).tendsto y
  filter_upwards [hT.eventually hg] with p hp
  exact hp.comp p (σ.mdifferentiable θ p)

/-- **Invariance of multiplier ideals.** Let `φ` be quasi-psh with `φ ∘ σ_θ = φ + u` near every
point, `u` continuous real. Then `g ∈ 𝓘(cφ)_{σ_θ y}` iff `g ∘ σ_θ ∈ 𝓘(cφ)_y`. -/
theorem multiplierIdeal_act_iff (σ : CircleAction n X) (θ : ℝ) {φ : X → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (hshift : ∀ y : X, ∃ u : X → ℝ, (∀ᶠ p in 𝓝 y, ContinuousAt u p) ∧
      ∀ᶠ p in 𝓝 y, φ (σ.act θ p) = φ p + (u p : EReal))
    (c : ℝ) (y : X) (g : X → ℂ) :
    (multiplierIdeal (n := n) c φ).mem (σ.act θ y) g ↔
      (multiplierIdeal (n := n) c φ).mem y (fun p => g (σ.act θ p)) := by
  set x' := σ.act θ y with hx'
  set e' := chartAt (ComplexModel n) x' with he'
  set e := chartAt (ComplexModel n) y with he
  have hy : y ∈ e.source := mem_chart_source (ComplexModel n) y
  have hx's : x' ∈ e'.source := mem_chart_source (ComplexModel n) x'
  set Φ := actChartEquiv σ θ y with hΦ
  have hw := hφ (complexChartAt (n := n) x') (e' x') (e'.map_source hx's)
  have h1 := LocalHolomorphicMultiplierGermCovariance.multiplierIntegrableAt_comp_inv_iff Φ
    (f := fun z => g (e'.symm z)) (c := c) hw
  have hΦ0 : Φ.toFun (e' x') = e y := by
    show e (σ.act (-θ) (e'.symm (e' x'))) = e y
    rw [e'.left_inv hx's, hx', σ.act_neg_act]
  rw [hΦ0] at h1
  obtain ⟨u, hucont, hueq⟩ := hshift y
  have hsymm : Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have := e.continuousAt_symm (e.map_source hy)
    rwa [ContinuousAt, e.left_inv hy] at this
  have hΦt : Φ.target ∈ 𝓝 (e y) := by
    rw [← hΦ0]
    exact Φ.isOpen_target.mem_nhds (Φ.mapsTo_toFun Φ.center_mem_source)
  -- the transported weight and function
  have hweq : (fun z => chartFunction φ (complexChartAt (n := n) x') (Φ.invFun z)) =ᶠ[𝓝 (e y)]
      fun v => φ (e.symm v) + (u (e.symm v) : EReal) := by
    filter_upwards [hΦt, hsymm.eventually hueq] with v hv hvu
    show φ (e'.symm (e' (σ.act θ (e.symm v)))) = _
    rw [e'.left_inv hv.2]
    exact hvu
  have hfeq : (fun z => g (e'.symm (Φ.invFun z))) =ᶠ[𝓝 (e y)]
      fun v => g (σ.act θ (e.symm v)) := by
    filter_upwards [hΦt] with v hv
    show g (e'.symm (e' (σ.act θ (e.symm v)))) = _
    rw [e'.left_inv hv.2]
  have hucont' : ∀ᶠ v in 𝓝 (e y), ContinuousAt (fun v => u (e.symm v)) v := by
    filter_upwards [hsymm.eventually hucont, e.open_target.mem_nhds (e.map_source hy)] with
      v hv hvt
    exact hv.comp (e.continuousAt_symm hvt)
  have hiff := SNCCoordinateUnitCorrection.multiplierIntegrableAt_add_continuous_iff
    (μ := MeasureTheory.volume) (φ := fun v => φ (e.symm v)) (c := c)
    (f := fun v => g (σ.act θ (e.symm v))) hucont'
  have hhol : HolomorphicAt n g x' ↔ HolomorphicAt n (fun p => g (σ.act θ p)) y := by
    constructor
    · exact holomorphicAt_comp_act σ θ
    · intro h
      have h2 := holomorphicAt_comp_act σ (-θ) (y := x') (g := fun p => g (σ.act θ p))
        (by rw [hx', σ.act_neg_act]; exact h)
      refine h2.congr (Eventually.of_forall fun p => ?_)
      show g (σ.act θ (σ.act (-θ) p)) = g p
      rw [σ.act_act_neg]
  change (HolomorphicAt n g x' ∧ MultiplierIntegrableAt (chartFunction φ
      (complexChartAt (n := n) x')) c (fun z => g (e'.symm z)) (e' x') MeasureTheory.volume) ↔
    (HolomorphicAt n (fun p => g (σ.act θ p)) y ∧ MultiplierIntegrableAt (fun v => φ (e.symm v)) c
      (fun v => g (σ.act θ (e.symm v))) (e y) MeasureTheory.volume)
  rw [hhol, ← h1, ← hiff]
  exact and_congr_right fun _ => ⟨fun h => h.congr hweq hfeq, fun h => h.congr hweq.symm hfeq.symm⟩

/-! ### Lifts to the line bundle and invariant metrics -/

section Bundle

open Bundle SGPT.PSH.LineBundleMetric
open scoped ENNReal

variable (σ : CircleAction n X) (L : X → Type*) [∀ x, AddCommGroup (L x)] [∀ x, Module ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [TopologicalSpace (TotalSpace ℂ L)] [FiberBundle ℂ L]
  [VectorBundle ℂ ℂ L] [ContMDiffVectorBundle ∞ ℂ L 𝓘(ℂ, ComplexModel n)]

/-- **A lift of the circle action to the holomorphic line bundle `L`**: for every `θ` a holomorphic
bundle map of `L` covering `σ_θ` which is linear and injective on the fibres (a bundle
isomorphism; the group law of the lifts is not needed and not required). -/
structure CircleActionLift where
  /-- The lift `L_x → L_{σ_θ x}`. -/
  lift : (θ : ℝ) → (x : X) → L x →ₗ[ℂ] L (σ.act θ x)
  injective : ∀ θ x, Function.Injective (lift θ x)
  /-- The lift is holomorphic on the total space. -/
  holomorphic : ∀ θ, MDifferentiable (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ))
    (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ))
    (fun v : TotalSpace ℂ L => TotalSpace.mk' ℂ (σ.act θ v.proj) (lift θ v.proj v.2))

variable {σ L}

/-- The (singular) metric `q` on `L` is invariant under the lifted action. -/
def IsInvariantMetric (τ : CircleActionLift σ L) (q : (x : X) → L x → ℝ≥0∞) : Prop :=
  ∀ (θ : ℝ) (x : X) (v : L x), q (σ.act θ x) (τ.lift θ x v) = q x v

theorem vec_eq_coeff_smul_frame (p : X) {x : X} (hx : x ∈ frameDomain L p) (w : L x) :
    w = ((trivializationAt ℂ L p) (TotalSpace.mk' ℂ x w)).2 • frame L p x := by
  set t := trivializationAt ℂ L p
  have h1 : t.symm x ((t (TotalSpace.mk' ℂ x w)).2) = w := t.symm_apply_apply_mk hx w
  have h2 : ∀ c : ℂ, t.symm x c = c • t.symm x 1 := by
    intro c
    rw [← t.symmL_apply (R := ℂ) hx c, ← t.symmL_apply (R := ℂ) hx 1, ← map_smul, smul_eq_mul,
      mul_one]
  conv_lhs => rw [← h1]
  rw [h2]
  rfl

theorem continuousAt_of_chartSmoothOn {g : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hg : ChartSmoothOn (n := n) g U) {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  set e := complexChartAt (n := n) p
  have hpe : p ∈ e.val.source := mem_complexChartAt_source p
  have hD : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
    e.val.isOpen_inter_preimage_symm hU
  have hpD : e.val p ∈ e.val.target ∩ e.val.symm ⁻¹' U :=
    ⟨e.val.map_source hpe, by rw [mem_preimage, e.val.left_inv hpe]; exact hp⟩
  have hc : ContinuousAt (fun z => g (e.val.symm z)) (e.val p) :=
    (hg e).continuousOn.continuousAt (hD.mem_nhds hpD)
  have h2 : ContinuousAt (fun x => g (e.val.symm (e.val x))) p :=
    hc.comp (e.val.continuousAt hpe)
  refine h2.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hpe] with x hx
  rw [e.val.left_inv hx]

/-- **An invariant metric has potentials invariant up to a continuous function.** If
`h = h₀ e^{-φ}` is invariant under the lifted action, then near every point `y`,
`φ ∘ σ_θ = φ + u` with `u` real and continuous. -/
theorem exists_shift_of_isInvariantMetric (τ : CircleActionLift σ L)
    {q : (x : X) → L x → ℝ≥0∞} {h₀ : HermitianMetric (n := n) L} {φ : X → EReal}
    (hq : IsPSHMetricWith q h₀ φ) (hinv : IsInvariantMetric τ q) (θ : ℝ) (y : X) :
    ∃ u : X → ℝ, (∀ᶠ p in 𝓝 y, ContinuousAt u p) ∧
      ∀ᶠ p in 𝓝 y, φ (σ.act θ p) = φ p + (u p : EReal) := by
  set y' := σ.act θ y with hy'
  set U := frameDomain L y ∩ σ.act θ ⁻¹' frameDomain L y' with hU
  have hUo : IsOpen U :=
    (isOpen_frameDomain y).inter ((isOpen_frameDomain y').preimage (CircleAction.continuous_act σ θ))
  have hyU : y ∈ U := ⟨mem_frameDomain y, mem_frameDomain y'⟩
  set a : X → ℂ := fun p => ((trivializationAt ℂ L y')
    (TotalSpace.mk' ℂ (σ.act θ p) (τ.lift θ p (frame L y p)))).2 with ha
  have hav : ∀ p ∈ U, τ.lift θ p (frame L y p) = a p • frame L y' (σ.act θ p) := fun p hp =>
    vec_eq_coeff_smul_frame y' hp.2 _
  have ha0 : ∀ p ∈ U, a p ≠ 0 := by
    intro p hp h0
    have h1 := hav p hp
    rw [h0, zero_smul] at h1
    exact frame_ne_zero hp.1 ((τ.injective θ p).eq_iff.1 (h1.trans (map_zero _).symm))
  -- continuity of `a` on `U`
  have hacont : ∀ p ∈ U, ContinuousAt a p := by
    intro p hp
    have hsec : ContinuousAt (fun x => TotalSpace.mk' ℂ x (frame L y x)) p :=
      ((frame_holomorphic (n := n) y).continuousOn).continuousAt
        ((isOpen_frameDomain y).mem_nhds hp.1)
    have hlift : Continuous (fun v : TotalSpace ℂ L =>
        TotalSpace.mk' ℂ (σ.act θ v.proj) (τ.lift θ v.proj v.2)) := (τ.holomorphic θ).continuous
    have htriv : ContinuousAt (trivializationAt ℂ L y')
        (TotalSpace.mk' ℂ (σ.act θ p) (τ.lift θ p (frame L y p))) :=
      (trivializationAt ℂ L y').continuousOn.continuousAt
        ((trivializationAt ℂ L y').open_source.mem_nhds
          ((trivializationAt ℂ L y').mem_source.2 hp.2))
    have hcomp : ContinuousAt (fun x => TotalSpace.mk' ℂ (σ.act θ x) (τ.lift θ x (frame L y x)))
        p := hlift.continuousAt.comp hsec
    exact continuous_snd.continuousAt.comp (ContinuousAt.comp (g := trivializationAt ℂ L y')
      (f := fun x => TotalSpace.mk' ℂ (σ.act θ x) (τ.lift θ x (frame L y x))) htriv hcomp)
  set N₀ : X → ℝ := fun p => (h₀.form p).normSq (frame L y p) with hN₀
  set N₁ : X → ℝ := fun p => ‖a p‖ ^ 2 * (h₀.form (σ.act θ p)).normSq (frame L y' (σ.act θ p))
    with hN₁
  have hN₀c : ∀ p ∈ U, ContinuousAt N₀ p := fun p hp =>
    continuousAt_of_chartSmoothOn (isOpen_frameDomain y)
      (h₀.smooth _ _ (isOpen_frameDomain y) (frame_holomorphic y)) hp.1
  have hN₁c : ∀ p ∈ U, ContinuousAt N₁ p := by
    intro p hp
    have h1 : ContinuousAt (fun x => (h₀.form x).normSq (frame L y' x)) (σ.act θ p) :=
      continuousAt_of_chartSmoothOn (isOpen_frameDomain y')
        (h₀.smooth _ _ (isOpen_frameDomain y') (frame_holomorphic y')) hp.2
    exact ((hacont p hp).norm.pow 2).mul (h1.comp (CircleAction.continuous_act σ θ).continuousAt)
  have hN₀p : ∀ p ∈ U, 0 < N₀ p := fun p hp => (h₀.form p).normSq_pos (frame_ne_zero hp.1)
  have hN₁p : ∀ p ∈ U, 0 < N₁ p := fun p hp =>
    mul_pos (pow_pos (norm_pos_iff.2 (ha0 p hp)) 2)
      ((h₀.form _).normSq_pos (frame_ne_zero hp.2))
  refine ⟨fun p => Real.log (N₁ p / N₀ p), ?_, ?_⟩
  · filter_upwards [hUo.mem_nhds hyU] with p hp
    exact ((hN₁c p hp).div (hN₀c p hp) (hN₀p p hp).ne').log
      (div_pos (hN₁p p hp) (hN₀p p hp)).ne'
  · filter_upwards [hUo.mem_nhds hyU] with p hp
    have hinvp := hinv θ p (frame L y p)
    rw [hq.eq_twisted, hq.eq_twisted, hav p hp] at hinvp
    have hne1 : a p • frame L y' (σ.act θ p) ≠ 0 :=
      smul_ne_zero (ha0 p hp) (frame_ne_zero hp.2)
    simp only [twistedForm, hne1, frame_ne_zero hp.1, if_false] at hinvp
    rw [(h₀.form _).normSq_smul] at hinvp
    -- `N₁ e^{-φ(σ p)} = N₀ e^{-φ(p)}`
    set r : ℝ := Real.log (N₁ p / N₀ p) with hr
    have hN1ne : ENNReal.ofReal (N₁ p) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; exact hN₁p p hp
    have hrhs : ENNReal.ofReal (N₁ p) * EReal.exp (-(φ p + (r : EReal))) =
        ENNReal.ofReal (N₀ p) * EReal.exp (-φ p) := by
      have hN0ne : ENNReal.ofReal (N₀ p) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]; exact hN₀p p hp
      induction hφp : φ p using EReal.rec with
      | bot =>
        simp only [EReal.bot_add, EReal.neg_bot, EReal.exp_top]
        rw [ENNReal.mul_top hN1ne, ENNReal.mul_top hN0ne]
      | top =>
        simp
      | coe t =>
        rw [← EReal.coe_add, ← EReal.coe_neg, ← EReal.coe_neg, EReal.exp_coe, EReal.exp_coe,
          ← ENNReal.ofReal_mul (hN₁p p hp).le, ← ENNReal.ofReal_mul (hN₀p p hp).le]
        congr 1
        have h1 := (hN₁p p hp).ne'
        have h0 := (hN₀p p hp).ne'
        simp only [neg_add, Real.exp_add, Real.exp_neg, hr,
          Real.exp_log (div_pos (hN₁p p hp) (hN₀p p hp))]
        field_simp
    have hkey : EReal.exp (-φ (σ.act θ p)) = EReal.exp (-(φ p + (r : EReal))) := by
      apply (ENNReal.mul_right_inj hN1ne ENNReal.ofReal_ne_top).1
      rw [hrhs]
      exact hinvp
    have h2 := EReal.exp_strictMono.injective hkey
    exact neg_injective h2

/-- **The multiplier ideals of an invariant psh metric are invariant ideals.** -/
theorem isInvariantIdeal_multiplierIdeal (τ : CircleActionLift σ L)
    {q : (x : X) → L x → ℝ≥0∞} {h₀ : HermitianMetric (n := n) L} {φ : X → EReal}
    (hq : IsPSHMetricWith q h₀ φ) (hinv : IsInvariantMetric τ q) (c : ℝ) :
    σ.IsInvariantIdeal (multiplierIdeal (n := n) c φ) := fun θ y g =>
  multiplierIdeal_act_iff σ θ hq.thetaPsh.1.quasiPlurisubharmonic
    (exists_shift_of_isInvariantMetric τ hq hinv θ) c y g

end Bundle

end SGPT.Trace.CohFib
