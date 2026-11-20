import SGPT.Trace.OTResFlat
import SGPT.Trace.OTMarginAssembly
import SGPT.Trace.OTExt4Lip

/-!
# Pieces of the normal pole and the critical integral of a glued section

Blueprint `claude-ot-residue.tex`, nodes `claude-ot-residue:piece`, `claude-ot-residue:crit`.

* `exists_piece`: near every point `p` of a submanifold `W`, in the flattening coordinates of
  `p`, a closed product `{|z'| ≤ r, |w| ≤ r}` inside the flattening target on which the normal
  pole satisfies `R ≥ c_R |w|²` (from `log R = log |w|² + O(1)`, `IsSubmanifoldPole.localForm`).
* `exists_pos_imp_mem`: an open neighbourhood of `{R = 0}` contains `{R < ε₀}` for some `ε₀ > 0`.
* `limsup_finset_sum_le`: `limsup ∑ ≤ ∑ limsup` in `[0, ∞]`.
* `lintegral_glued_crit_ne_top`: for `G` glued as in `IsCriticalGainGluing`,
  `∫_X |G|² (R^q log² R)⁻¹ e^{-(1+κ)Φ} < ∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTRes

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.TwistedL2 HermitianHolomorphicLineBundle
open SGPT.Trace.OTMargin (fcoord finv finv_mem continuousOn_finv fcoord_finv finv_fcoord
  mem_iff_fcoord normalWeight normalWeight_nonneg normalWeight_eq_zero_iff
  normalWeight_pos_of_notMem le_exp_of_log localForm_normalized)
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)
open SGPT.Trace.OTExt4 (closedLocalDom)

/-- `limsup (u + v) ≤ limsup u + limsup v` in `[0, ∞]`, for any filter. -/
theorem limsup_add_le_ennreal {α : Type*} {f : Filter α} (u v : α → ℝ≥0∞) :
    limsup (fun a => u a + v a) f ≤ limsup u f + limsup v f := by
  by_cases hu : limsup u f = ⊤
  · rw [hu, top_add]; exact le_top
  by_cases hv : limsup v f = ⊤
  · rw [hv, add_top]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := ENNReal.half_pos (by exact_mod_cast hε.ne')
  have h1 : limsup u f < limsup u f + (ε : ℝ≥0∞) / 2 := ENNReal.lt_add_right hu hε2.ne'
  have h2 : limsup v f < limsup v f + (ε : ℝ≥0∞) / 2 := ENNReal.lt_add_right hv hε2.ne'
  have hev : ∀ᶠ a in f, u a + v a ≤ limsup u f + limsup v f + (ε : ℝ≥0∞) := by
    filter_upwards [eventually_lt_of_limsup_lt h1, eventually_lt_of_limsup_lt h2] with a ha hb
    calc u a + v a ≤ (limsup u f + (ε : ℝ≥0∞) / 2) + (limsup v f + (ε : ℝ≥0∞) / 2) :=
          add_le_add ha.le hb.le
      _ = limsup u f + limsup v f + (ε : ℝ≥0∞) := by
          rw [add_add_add_comm, ENNReal.add_halves]
  exact limsup_le_of_le (by isBoundedDefault) hev

/-- `limsup ∑_{i ∈ s} u_i ≤ ∑_{i ∈ s} limsup u_i` in `[0, ∞]`. -/
theorem limsup_finset_sum_le {α ι : Type*} {f : Filter α} (s : Finset ι) (u : ι → α → ℝ≥0∞) :
    limsup (fun a => ∑ i ∈ s, u i a) f ≤ ∑ i ∈ s, limsup (u i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun _ => le_rfl)
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (limsup_add_le_ennreal (u j) (fun a => ∑ i ∈ s, u i a)).trans (add_le_add le_rfl ih)

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- If `R ≥ 0` is continuous on the compact `X` and `O` is an open set containing `{R = 0}`,
then `{R < ε₀} ⊆ O` for some `ε₀ > 0`. -/
theorem exists_pos_imp_mem [CompactSpace X] {R : X → ℝ} (hR : Continuous R) {O : Set X}
    (hO : IsOpen O) (h0 : ∀ x, R x ≤ 0 → x ∈ O) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ x, R x < ε₀ → x ∈ O := by
  have hc : IsCompact Oᶜ := hO.isClosed_compl.isCompact
  rcases (Oᶜ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    by_contra hx
    exact (eq_empty_iff_forall_notMem.mp he x) hx
  obtain ⟨x₀, hx₀, hmin⟩ := hc.exists_isMinOn hne hR.continuousOn
  have hpos : 0 < R x₀ := by
    by_contra h
    exact hx₀ (h0 x₀ (not_lt.mp h))
  refine ⟨R x₀, hpos, fun x hx => ?_⟩
  by_contra hxO
  exact absurd (hmin hxO) (not_le.mpr hx)

/-- **A piece of the normal pole** near `p ∈ W`, in the flattening coordinates of `p`. -/
theorem exists_piece {W : Set X} {m : ℕ} (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {ωb : KahlerBackground n X} {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) (p : W) :
    ∃ r cR : ℝ, 0 < r ∧ 0 < cR ∧
      closedLocalDom n m r r ⊆ (FlatData.ofRegularAtDim (hW p.1 p.2)).flat.target ∧
      ∀ z ∈ closedLocalDom n m r r,
        cR * normalWeight n m z ≤ R (finv (FlatData.ofRegularAtDim (hW p.1 p.2)) z) := by
  set Fd : FlatData n m X W := FlatData.ofRegularAtDim (hW p.1 p.2) with hFd
  obtain ⟨U, hU, C, hC⟩ := localForm_normalized hW hR.pole 0 p
  have hreg := hW p.1 p.2
  have hz0 : Fd.flat (Fd.amb.val p.1) = 0 := hreg.2.2.choose_spec.2.1
  have hxsrc : p.1 ∈ Fd.ambSource := FlatData.mem_ambSource_ofRegularAtDim hreg
  have h0flat : (0 : ComplexModel n) ∈ Fd.flat.target := by
    rw [← hz0]; exact Fd.flat.map_source hxsrc.2
  have hfx : finv Fd 0 = p.1 := by
    have := finv_fcoord Fd hxsrc
    rwa [show fcoord Fd p.1 = 0 from hz0] at this
  have hfc : ContinuousAt (finv Fd) 0 :=
    (continuousOn_finv Fd).continuousAt (Fd.flat.open_target.mem_nhds h0flat)
  have hev : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Fd.flat.target ∧ finv Fd z ∈ U := by
    filter_upwards [Fd.flat.open_target.mem_nhds h0flat, hfc.eventually (by rw [hfx]; exact hU)]
      with z h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨r₁, hr₁, hr₁s⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hr : 0 < r₁ / 3 := by positivity
  have hsub : closedLocalDom n m (r₁ / 3) (r₁ / 3) ⊆ ball 0 r₁ := fun z hz => by
    rw [mem_ball_zero_iff]
    exact (SGPT.Trace.OTExt4.norm_le_of_mem_closedLocalDom hr.le hr.le hz).trans_lt (by linarith)
  refine ⟨r₁ / 3, Real.exp (-max C 0), hr, Real.exp_pos _, fun z hz => (hr₁s z (hsub hz)).1,
    fun z hz => ?_⟩
  have hzt := (hr₁s z (hsub hz)).1
  by_cases hpl : z ∈ complexCoordinatePlane n m
  · rw [(normalWeight_eq_zero_iff z).mpr hpl, mul_zero]
    exact hR.nonneg _
  · have hnw := normalWeight_pos_of_notMem (m := m) hpl
    have hW' : finv Fd z ∉ W := fun h => hpl (by
      have := (mem_iff_fcoord Fd (finv_mem Fd hzt)).mp h
      rwa [fcoord_finv Fd hzt] at this)
    have hRp := hR.pos_of_notMem hW'
    have hloc := hC (finv Fd z) (hr₁s z (hsub hz)).2 hW'
    rw [fcoord_finv Fd hzt, neg_zero, EReal.coe_zero, add_zero, logPole,
      ENNReal.log_pos_real' (by simpa [ENNReal.toReal_ofReal (hR.nonneg _)] using hRp),
      EReal.toReal_coe, ENNReal.toReal_ofReal (hR.nonneg _)] at hloc
    have h1 := le_exp_of_log hnw (hloc.trans (le_max_left C 0))
    rw [Real.exp_log hRp] at h1
    have h2 : Real.exp (-max C 0) * Real.exp (max C 0) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc Real.exp (-max C 0) * normalWeight n m z
        ≤ Real.exp (-max C 0) * (Real.exp (max C 0) * R (finv Fd z)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = R (finv Fd z) := by rw [← mul_assoc, h2, one_mul]

/-! ### The critical integral of a glued section -/

section Glued

variable [MeasurableSpace X] [BorelSpace X] (V : HermitianHolomorphicLineBundle.{0, 0} n X)

theorem continuous_of_chartSmooth {h : X → ℝ} (hh : ChartSmooth (n := n) h) : Continuous h :=
  continuous_iff_continuousAt.mpr fun _ =>
    MeteredDivisorWeightBounds.continuousAt_of_chartContDiffOn (n := n) (h := h)
      isOpen_univ (fun e => by simpa using hh e) (mem_univ _)

/-- **The critical integral of a glued section is finite**: for `G = ∑ η_i F_i` as in
`IsCriticalGainGluing` and the weight `w = e^{-(1+κ)Φ}` (measurable),
`∫_X |G|² (R^q log² R)⁻¹ w ≤ N B² ∑_i ∫_{U_i} |F_i|² w (R^q log² R)⁻¹ < ∞`. -/
theorem lintegral_glued_crit_ne_top {μ : Measure X} {W : Set X} {q : ℕ} {R : X → ℝ}
    {Φ : X → EReal} {κ : ℝ} {f : (y : W) → V.Fiber y} {G : (x : X) → V.Fiber x}
    (hG : SGPT.Trace.OTExt2.IsCriticalGainGluing (n := n) V.Fiber μ W q R Φ κ f G)
    (hw : Measurable fun x => multiplierWeight (1 + κ) (Φ x)) (hRc : Continuous R)
    (hR0 : ∀ x, 0 ≤ R x) :
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * (R x ^ q * Real.log (R x) ^ 2)⁻¹) *
      multiplierWeight (1 + κ) (Φ x) ∂μ ≠ ⊤ := by
  classical
  obtain ⟨ι, _, U, F, η, hUo, hFhol, -, hFcrit, hηs, hηc, -, -, hGeq⟩ := hG
  set k : X → ℝ := fun x => (R x ^ q * Real.log (R x) ^ 2)⁻¹ with hkdef
  have hk0 : ∀ x, 0 ≤ k x := fun x => by
    have := hR0 x
    simp only [hkdef]; positivity
  have hkm : Measurable fun x => ENNReal.ofReal (k x) :=
    ENNReal.measurable_ofReal.comp ((hRc.pow q).measurable.mul
      ((Real.measurable_log.comp hRc.measurable).pow_const 2)).inv
  have hB : ∀ i, ∃ B : ℝ, ∀ x, ‖η i x‖ ≤ B := fun i =>
    (continuous_of_chartSmooth (hηs i)).bounded_above_of_compact_support (hηc i)
  choose B hBi using hB
  set Bt : ℝ := ∑ i, |B i| with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hηB : ∀ i x, |η i x| ≤ Bt := fun i x => by
    have h1 := hBi i x
    rw [Real.norm_eq_abs] at h1
    exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |B i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  set Nc : ℝ := (Fintype.card ι : ℝ) * Bt ^ 2 with hNc
  have hNc0 : 0 ≤ Nc := by positivity
  set g : ι → X → ℝ≥0∞ := fun i => (U i).indicator fun x => ENNReal.ofReal (‖F i x‖ ^ 2)
    with hgdef
  have hgm : ∀ i, Measurable (g i) := fun i =>
    SGPT.Trace.OTMargin.measurable_indicator_of_continuousOn' (hUo i)
      (ENNReal.continuous_ofReal.comp_continuousOn
        ((ContinuousFiberNorm.continuous.comp_continuousOn (hFhol i).continuousOn).pow 2))
  have hpt : ∀ x, ENNReal.ofReal (‖G x‖ ^ 2 * k x) * multiplierWeight (1 + κ) (Φ x) ≤
      ∑ i, ENNReal.ofReal Nc * (g i x * multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x)) := by
    intro x
    have hnorm : ‖G x‖ ^ 2 ≤ Nc * ∑ i, (U i).indicator (fun x => ‖F i x‖ ^ 2) x := by
      rw [hGeq x]
      refine (SGPT.Trace.OTMargin.norm_sum_sq_le_card _).trans ?_
      rw [hNc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      have hη2 : η i x ^ 2 ≤ Bt ^ 2 := by
        have := hηB i x
        nlinarith [abs_nonneg (η i x), sq_abs (η i x)]
      by_cases hx : x ∈ U i
      · rw [if_pos hx, indicator_of_mem hx]
        exact mul_le_mul_of_nonneg_right hη2 (sq_nonneg _)
      · rw [if_neg hx, indicator_of_notMem hx, norm_zero]; simp
    have hind : ∀ i, 0 ≤ (U i).indicator (fun x => ‖F i x‖ ^ 2) x := fun i =>
      indicator_nonneg (fun _ _ => sq_nonneg _) x
    calc ENNReal.ofReal (‖G x‖ ^ 2 * k x) * multiplierWeight (1 + κ) (Φ x)
        ≤ ENNReal.ofReal ((Nc * ∑ i, (U i).indicator (fun x => ‖F i x‖ ^ 2) x) * k x) *
            multiplierWeight (1 + κ) (Φ x) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hnorm (hk0 x))) le_rfl
      _ = ∑ i, ENNReal.ofReal Nc * (g i x * multiplierWeight (1 + κ) (Φ x) *
            ENNReal.ofReal (k x)) := by
          have hre : (Nc * ∑ i, (U i).indicator (fun x => ‖F i x‖ ^ 2) x) * k x =
              ∑ i, Nc * (U i).indicator (fun x => ‖F i x‖ ^ 2) x * k x := by
            rw [Finset.mul_sum, Finset.sum_mul]
          rw [hre, ENNReal.ofReal_sum_of_nonneg (fun i _ => by
            have := hind i; have := hk0 x; positivity), Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (mul_nonneg hNc0 (hind i)), ENNReal.ofReal_mul hNc0]
          have h2 : ENNReal.ofReal ((U i).indicator (fun x => ‖F i x‖ ^ 2) x) = g i x := by
            simp only [hgdef]
            by_cases hx : x ∈ U i
            · rw [indicator_of_mem hx, indicator_of_mem hx]
            · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]
          rw [h2]
          ring
  have hterm : ∀ i, ∫⁻ x, ENNReal.ofReal Nc * (g i x * multiplierWeight (1 + κ) (Φ x) *
      ENNReal.ofReal (k x)) ∂μ ≠ ⊤ := by
    intro i
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    have heq : (fun x => g i x * multiplierWeight (1 + κ) (Φ x) * ENNReal.ofReal (k x)) =
        (U i).indicator fun x => ENNReal.ofReal (‖F i x‖ ^ 2) * multiplierWeight (1 + κ) (Φ x) *
          ENNReal.ofReal (k x) := by
      funext x
      simp only [hgdef]
      by_cases hx : x ∈ U i
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul, zero_mul]
    rw [heq, lintegral_indicator (hUo i).measurableSet]
    exact hFcrit i
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  have hsum := lintegral_finsetSum' (μ := μ) Finset.univ
    (f := fun i x => ENNReal.ofReal Nc * (g i x * multiplierWeight (1 + κ) (Φ x) *
      ENNReal.ofReal (k x)))
    (fun i _ => (measurable_const.mul (((hgm i).mul hw).mul hkm)).aemeasurable)
  rw [hsum]
  exact ENNReal.sum_ne_top.mpr fun i _ => hterm i

end Glued

end SGPT.Trace.OTRes
