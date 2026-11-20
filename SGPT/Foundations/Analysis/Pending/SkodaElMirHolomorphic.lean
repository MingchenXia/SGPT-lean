import SGPT.Foundations.Analysis.Pending.SkodaElMirSubmanifold

set_option autoImplicit false

/-!
# Skoda--El Mir for zero sets of holomorphic maps; the graph of a holomorphic map

`SkodaElMirSubmanifold` proves that `𝟙_Δ T` and `𝟙_{M \ Δ} T` are closed for a closed positive
current `T` and a closed set `Δ` which is, near each of its points, the zero set of a `ℂ`-LINEAR map
read in an atlas chart.  Here the linear map is replaced by a map `Y` that is only holomorphic on an
open subset `W` of the chart target (`IsHoloFlat`); no submersion condition is needed.

The log cut-offs `Vᵢ = ρ(log ‖Y‖² / (i + 1) + 1)` (`holoLogCutoff`) are smooth on `W`, vanish near
`{Y = 0}`, tend to `1` off it and are plurisubharmonic on `W ∩ {‖Y‖² < 1}`:
`log ‖Y‖²` is plurisubharmonic off `{Y = 0}` for holomorphic `Y` by the same Demailly--Păun
estimate (`ConcentrationPotentialLevi.le_leviForm_log_sum_of_pos`, which takes holomorphic
coordinates `Gⱼ = Yⱼ`).  The local vanishing argument and its assembly are those of
`SkodaElMirSubmanifold`, with the cut-offs localized to `W`.

The application: the graph `Γ_f = {(v, x) | f v = x}` of a holomorphic map `f : V → X` between
complex manifolds of the same dimension is holomorphically flat in the product charts of `V × X`,
with `Y(z, w) = w - F(z)`, `F` the coordinate representative of `f` (`isHoloFlat_graph`); hence
`𝟙_{Γ_f} T` and `𝟙_{V × X \ Γ_f} T` are closed (`isClosedCurrent_restrictCurrent_graph`).  This is
step 1 of the support theorem for graphs requested by TN-CLASSICAL (inbox I-0831 C-0032) for the
graph route of the `(P)` step of Boucksom 4.8 (`demailly-cadg:III.2.3`).
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.SkodaElMirHolomorphic

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents ClosedCurrentLocalTests
  CurrentTraceMeasure SmoothDDCForm ChartPartition SlotTestForms SkodaElMirEstimate
  CurrentRestriction LogCutoffLevi ConcentrationPotentialLevi SkodaElMirSubmanifold

/-! ### Log cut-offs along the zero set of a holomorphic map -/

section Cutoff

variable {n c : ℕ} (Y : ComplexModel n → ComplexModel c)

/-- **`log ‖Y‖²` is plurisubharmonic off `{Y = 0}`** for `Y` holomorphic near `z`. -/
theorem leviForm_log_normSq_nonneg_of_holo {z : ComplexModel n}
    (hYd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ Y y) (hz : Y z ≠ 0) (v : ComplexModel n) :
    0 ≤ leviForm (fun y => Real.log (‖Y y‖ ^ 2)) z v := by
  set G : Fin c → ComplexModel n → ℂ := fun j y => Y y j
  have hnorm : ∀ y, ∑ j, (fun _ : ComplexModel n => (1 : ℝ)) y ^ 2 * Complex.normSq (G j y) + 0 =
      ‖Y y‖ ^ 2 := fun y => by
    simp [G, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ∑ j, (fun _ : ComplexModel n => (1 : ℝ)) z ^ 2 * Complex.normSq (G j z) + 0 := by
    rw [hnorm]; positivity
  have hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y := fun j =>
    hYd.mono fun y hy => ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiableAt).comp y hy
  have h := le_leviForm_log_sum_of_pos (c := fun _ _ => (1 : ℝ)) (G := G) hpos
    (fun _ => contDiffAt_const) hG v
  have hfun : (fun y => Real.log (∑ j, (fun _ : ComplexModel n => (1 : ℝ)) y ^ 2 *
      Complex.normSq (G j y) + 0)) = fun y => Real.log (‖Y y‖ ^ 2) := funext fun y => by rw [hnorm]
  rw [hfun] at h
  refine le_trans (le_of_eq ?_) h
  have hdel : Complex.normSq (delC (fun _ : ComplexModel n => (1 : ℝ)) z v) = 0 := by
    rw [normSq_delC]; simp
  simp [hdel, leviForm_const]

/-- **The log cut-off** `Vᵢ(z) = ρ(log ‖Y z‖²/(i+1) + 1)`, `0` where `Y z = 0`. -/
def holoLogCutoff (i : ℕ) (z : ComplexModel n) : ℝ :=
  if Y z = 0 then 0 else cutoffProfile (Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1)

theorem holoLogCutoff_of_eq_zero (i : ℕ) {z : ComplexModel n} (hz : Y z = 0) :
    holoLogCutoff Y i z = 0 :=
  if_pos hz

theorem holoLogCutoff_eventuallyEq_zero (i : ℕ) {z : ComplexModel n} (hc : ContinuousAt Y z)
    (hz : Y z = 0) : holoLogCutoff Y i =ᶠ[𝓝 z] fun _ => 0 := by
  have hlt : ∀ᶠ y in 𝓝 z, ‖Y y‖ ^ 2 < Real.exp (-((i : ℝ) + 1)) :=
    (hc.norm.pow 2).eventually_lt continuousAt_const (by
      show ‖Y z‖ ^ 2 < _
      rw [hz, norm_zero, zero_pow two_ne_zero]
      exact Real.exp_pos _)
  filter_upwards [hlt] with y hy
  by_cases hy0 : Y y = 0
  · exact if_pos hy0
  · rw [holoLogCutoff, if_neg hy0]
    apply cutoffProfile_of_nonpos
    have hpos : 0 < ‖Y y‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y y‖ ^ 2) < -((i : ℝ) + 1) := by
      have := Real.log_lt_log hpos hy
      rwa [Real.log_exp] at this
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    rw [div_add_one hi.ne', div_nonpos_iff]
    right
    exact ⟨by linarith, hi.le⟩

theorem holoLogCutoff_eventuallyEq (i : ℕ) {z : ComplexModel n} (hc : ContinuousAt Y z)
    (hz : Y z ≠ 0) :
    holoLogCutoff Y i =ᶠ[𝓝 z]
      fun y => cutoffProfile (Real.log (‖Y y‖ ^ 2) / ((i : ℝ) + 1) + 1) := by
  filter_upwards [hc.eventually_ne hz] with y hy
  exact if_neg hy

theorem contDiffAt_log_normSq_of_contDiffAt {z : ComplexModel n} (hY : ContDiffAt ℝ ∞ Y z)
    (hz : Y z ≠ 0) : ContDiffAt ℝ ∞ (fun y => Real.log (‖Y y‖ ^ 2)) z :=
  ((contDiff_norm_sq ℝ).contDiffAt.comp z hY).log (pow_pos (norm_pos_iff.2 hz) 2).ne'

theorem contDiffAt_holoLogCutoff (i : ℕ) {z : ComplexModel n} (hY : ContDiffAt ℝ ∞ Y z) :
    ContDiffAt ℝ ∞ (holoLogCutoff Y i) z := by
  by_cases hz : Y z = 0
  · exact contDiffAt_const.congr_of_eventuallyEq
      (holoLogCutoff_eventuallyEq_zero Y i hY.continuousAt hz)
  · refine ContDiffAt.congr_of_eventuallyEq ?_
      (holoLogCutoff_eventuallyEq Y i hY.continuousAt hz)
    exact contDiff_cutoffProfile.contDiffAt.comp z
      (((contDiffAt_log_normSq_of_contDiffAt Y hY hz).div_const _).add contDiffAt_const)

theorem holoLogCutoff_nonneg (i : ℕ) (z : ComplexModel n) : 0 ≤ holoLogCutoff Y i z := by
  unfold holoLogCutoff
  split_ifs
  · exact le_rfl
  · exact cutoffProfile_nonneg _

theorem holoLogCutoff_le_one (i : ℕ) {z : ComplexModel n} (hz1 : ‖Y z‖ ^ 2 < 1) :
    holoLogCutoff Y i z ≤ 1 := by
  unfold holoLogCutoff
  split_ifs with hz
  · norm_num
  · apply cutoffProfile_le_one
    have hpos : 0 < ‖Y z‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y z‖ ^ 2) < 0 := Real.log_neg hpos hz1
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) < 0 := div_neg_of_neg_of_pos hlog hi
    linarith

/-- **`Vᵢ → 1` off `{Y = 0}`.** -/
theorem tendsto_holoLogCutoff {z : ComplexModel n} (hz : Y z ≠ 0) :
    Tendsto (fun i : ℕ => holoLogCutoff Y i z) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℕ => Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1) atTop (𝓝 1) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.log (‖Y z‖ ^ 2))
    rw [mul_zero] at this
    have h2 := this.add_const 1
    rw [zero_add] at h2
    refine h2.congr fun i => ?_
    ring
  have h3 := (continuous_cutoffProfile.tendsto 1).comp h1
  rw [cutoffProfile_one] at h3
  refine h3.congr fun i => ?_
  simp only [Function.comp_apply, holoLogCutoff, if_neg hz]

/-- **`Vᵢ` is plurisubharmonic on `{‖Y‖² < 1}` where `Y` is holomorphic.** -/
theorem smoothDDC_holoLogCutoff_nonneg (i : ℕ) {z : ComplexModel n}
    (hYd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ Y y) (hY : ContDiffAt ℝ ∞ Y z) (hz1 : ‖Y z‖ ^ 2 < 1)
    (u : ComplexModel n) : 0 ≤ smoothDDC (holoLogCutoff Y i) z ![u, Complex.I • u] := by
  by_cases hz : Y z = 0
  · rw [smoothDDC_congr (holoLogCutoff_eventuallyEq_zero Y i hY.continuousAt hz), smoothDDC_zero]
    simp
  · rw [smoothDDC_congr (holoLogCutoff_eventuallyEq Y i hY.continuousAt hz)]
    set L : ComplexModel n → ℝ := fun y => Real.log (‖Y y‖ ^ 2) / ((i : ℝ) + 1) + 1 with hL
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hlogC : ContDiffAt ℝ 2 (fun y => Real.log (‖Y y‖ ^ 2)) z :=
      (contDiffAt_log_normSq_of_contDiffAt Y hY hz).of_le h2
    have hLC : ContDiffAt ℝ 2 L z := (hlogC.div_const _).add contDiffAt_const
    have hcomp : ContDiffAt ℝ 2 (fun y => cutoffProfile (L y)) z :=
      (contDiff_cutoffProfile.contDiffAt.of_le h2).comp z hLC
    rw [smoothDDC_complexDiagonal_eq_leviForm hcomp, leviForm_comp contDiff_cutoffProfile hLC,
      hL, leviForm_affine hlogC]
    have hpos : 0 < ‖Y z‖ ^ 2 := by positivity
    have hlog : Real.log (‖Y z‖ ^ 2) < 0 := Real.log_neg hpos hz1
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hLz : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1 ≤ 1 := by
      have : Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) < 0 := div_neg_of_neg_of_pos hlog hi
      linarith
    have hd2 := deriv2_cutoffProfile_nonneg hLz
    have hd1 := deriv_cutoffProfile_nonneg (Real.log (‖Y z‖ ^ 2) / ((i : ℝ) + 1) + 1)
    have hlev := leviForm_log_normSq_nonneg_of_holo Y hYd hz u
    have hπ := Real.pi_pos
    have : 0 ≤ leviForm (fun y => Real.log (‖Y y‖ ^ 2)) z u / ((i : ℝ) + 1) := by positivity
    positivity

end Cutoff

/-! ### Holomorphically flat sets -/

section Flat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A set that is, near each of its points, the zero set of a map that is holomorphic on an open
subset of an atlas chart target. -/
def IsHoloFlat (Δ : Set M) : Prop :=
  ∀ x ∈ Δ, ∃ (e : ComplexChart n M) (W : Set (ComplexModel n)) (c : ℕ)
    (Y : ComplexModel n → ComplexModel c), x ∈ e.val.source ∧ IsOpen W ∧ W ⊆ e.val.target ∧
      e.val x ∈ W ∧ (∀ z ∈ W, ContDiffAt ℂ ∞ Y z) ∧
      ∀ p ∈ e.val.source, e.val p ∈ W → (p ∈ Δ ↔ Y (e.val p) = 0)

omit [IsComplexManifold n M] in
/-- Linearly flat sets are holomorphically flat. -/
theorem IsLinearlyFlat.isHoloFlat {Δ : Set M} (h : IsLinearlyFlat (n := n) Δ) :
    IsHoloFlat (n := n) Δ := fun x hx => by
  obtain ⟨e, hxe, c, Y, hY⟩ := h x hx
  exact ⟨e, e.val.target, c, Y, hxe, e.val.open_target, subset_rfl, e.val.map_source hxe,
    fun z _ => Y.contDiff.contDiffAt, fun p hp _ => hY p hp⟩

end Flat

section Assembly

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] {k : ℕ}
  {T : ProductCurrent n M (k + 1)}

/-- `W ∩ {‖Y‖² < 1}` is open when `Y` is continuous on the open set `W`. -/
theorem isOpen_inter_normSq_lt {W : Set (ComplexModel n)} (hW : IsOpen W) {c : ℕ}
    {Y : ComplexModel n → ComplexModel c} (hY : ∀ z ∈ W, ContDiffAt ℂ ∞ Y z) :
    IsOpen (W ∩ {z | ‖Y z‖ ^ 2 < 1}) := by
  have hc : ContinuousOn (fun z => ‖Y z‖ ^ 2) W := fun z hz =>
    ((hY z hz).continuousAt.norm.pow 2).continuousWithinAt
  exact hc.isOpen_inter_preimage hW isOpen_Iio

/-- **Near a point of `Δ`**, for the zero set of a map holomorphic on `W`. -/
theorem local_vanishing_of_mem (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (e : ComplexChart n M) {W : Set (ComplexModel n)}
    (hW : IsOpen W) (hWt : W ⊆ e.val.target) {c : ℕ} {Y : ComplexModel n → ComplexModel c}
    (hY : ∀ z ∈ W, ContDiffAt ℂ ∞ Y z)
    (hYΔ : ∀ p ∈ e.val.source, e.val p ∈ W → (p ∈ Δ ↔ Y (e.val p) = 0))
    (hΔm : MeasurableSet Δ) :
    ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
      tsupport f ⊆ e.val.symm '' (W ∩ {z | ‖Y z‖ ^ 2 < 1}) → IsCompact (tsupport f) →
        ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
          restrictCurrent w T hT Δᶜ (closedTestForm f g hf hg k β) = 0 := by
  intro f g hf hg hfO hfc β hβ
  set O : Set (ComplexModel n) := W ∩ {z | ‖Y z‖ ^ 2 < 1} with hO_def
  have hO : IsOpen O := isOpen_inter_normSq_lt hW hY
  have hOt : O ⊆ e.val.target := inter_subset_left.trans hWt
  have hYr : ∀ z ∈ W, ContDiffAt ℝ ∞ Y z := fun z hz => (hY z hz).restrict_scalars ℝ
  have hYd : ∀ z ∈ W, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ Y y := fun z hz =>
    Filter.eventually_of_mem (hW.mem_nhds hz) fun y hy => (hY y hy).differentiableAt (by simp)
  obtain ⟨χ, hχ, hχc, hχO, hχ0, hχ1, hχf⟩ := exists_chart_bump e hO hOt hfO hfc
  -- the second cut-off, equal to one near the support of `χ`
  obtain ⟨χ₂, hχ₂, hχ₂c, hχ₂O, hχ₂0, hχ₂1, hχ₂K⟩ := exists_cutoff hO hχc (hχO)
  set V : ℕ → ComplexModel n → ℝ := fun i z => χ₂ z * holoLogCutoff Y i z with hV_def
  have hVd : ∀ i, ContDiff ℝ ∞ (V i) := fun i => by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ W
    · exact hχ₂.contDiffAt.mul (contDiffAt_holoLogCutoff Y i (hYr z hz))
    · have hz' : z ∉ tsupport χ₂ := fun h => hz (hχ₂O h).1
      have h0 : V i =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz'] with y hy
        simp only [hV_def, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hVc : ∀ i, HasCompactSupport (V i) := fun i => hχ₂c.mul_right
  have hVt : ∀ i, tsupport (V i) ⊆ e.val.target := fun i =>
    tsupport_mul_subset_left.trans (hχ₂O.trans hOt)
  set v : ℕ → M → ℝ := fun i => chartExtend e (V i) with hv_def
  have hv : ∀ i, ChartSmooth (n := n) (v i) := fun i =>
    chartSmooth_chartExtend e (hVd i) (hVc i) (hVt i)
  have hV0 : ∀ i z, 0 ≤ V i z := fun i z => mul_nonneg (hχ₂0 z) (holoLogCutoff_nonneg Y i z)
  have hV1 : ∀ i z, V i z ≤ 1 := fun i z => by
    by_cases hz : χ₂ z = 0
    · simp [hV_def, hz]
    · have hzO : z ∈ O := hχ₂O (subset_tsupport _ hz)
      have h1 := holoLogCutoff_le_one Y i hzO.2
      have h0 := holoLogCutoff_nonneg Y i z
      calc V i z = χ₂ z * holoLogCutoff Y i z := rfl
        _ ≤ 1 * 1 := mul_le_mul (hχ₂1 z) h1 h0 zero_le_one
        _ = 1 := one_mul 1
  -- near the support of `χ`, `vᵢ` is the log cut-off
  have hloc : ∀ i {z : ComplexModel n}, z ∈ tsupport χ →
      (fun y => v i (e.val.symm y)) =ᶠ[𝓝 z] holoLogCutoff Y i := by
    intro i z hz
    have hev : ∀ᶠ y in 𝓝 z, χ₂ y = 1 := hχ₂K.filter_mono (nhds_le_nhdsSet hz)
    filter_upwards [chartExtend_eventuallyEq (β := V i) (hχO.trans hOt hz), hev] with y hy hy2
    change chartExtend e (V i) (e.val.symm y) = _
    rw [hy, hV_def]
    simp [hy2]
  have hval : ∀ i {y : M}, chartExtend e χ y ≠ 0 → v i y = holoLogCutoff Y i (e.val y) := by
    intro i y hy
    obtain ⟨hys, hyχ⟩ := chartExtend_ne_zero hy
    have := (hloc i hyχ).self_of_nhds
    simpa [e.val.left_inv hys] using this
  -- the limits at a point where `h₁ ≠ 0`
  have hlim : ∀ {y : M}, chartExtend e χ y ≠ 0 →
      (y ∈ Δ ∧ ∀ i, v i y = 0) ∨ (y ∉ Δ ∧ Tendsto (fun i => v i y) atTop (𝓝 1)) := by
    intro y hy
    obtain ⟨hys, hyχ⟩ := chartExtend_ne_zero hy
    have hyW : e.val y ∈ W := (hχO hyχ).1
    by_cases hyΔ : y ∈ Δ
    · left
      refine ⟨hyΔ, fun i => ?_⟩
      rw [hval i hy, holoLogCutoff_of_eq_zero Y i ((hYΔ y hys hyW).mp hyΔ)]
    · right
      refine ⟨hyΔ, ?_⟩
      have hYy : Y (e.val y) ≠ 0 := fun h0 => hyΔ ((hYΔ y hys hyW).mpr h0)
      exact (tendsto_holoLogCutoff Y hYy).congr fun i => (hval i hy).symm
  refine restrictCurrent_closedTestForm_eq_zero w hT hTc hβ hΔm.compl hf hg e
    hχ hχc (hχO.trans hOt) hχ0 hχ1 hχf (v := v) hv
    (fun i y => chartExtend_nonneg (hV0 i) y) (fun i y => chartExtend_le_one (hV1 i) y) ?_ ?_ ?_
  · -- plurisubharmonicity where `h₁ ≠ 0`
    intro i e' z hz hx u
    obtain ⟨hps, hpχ⟩ := chartExtend_ne_zero hx
    have hzs : z ∈ (chartTransition e' e).source := ⟨hz, hps⟩
    rw [KahlerDomination.lineValue_compatible _ e' e hzs u]
    set ze := chartTransition e' e z
    have hze : ze = e.val (e'.val.symm z) := rfl
    rw [ddcForm_coeff, smoothDDC_congr (hloc i (hze ▸ hpχ))]
    have hzO : ze ∈ O := hχO (hze ▸ hpχ)
    exact smoothDDC_holoLogCutoff_nonneg Y i (hYd ze hzO.1) (hYr ze hzO.1) hzO.2 _
  · -- `θ(vᵢ) → 𝟙_{M \ Δ}`
    intro y hy
    rcases hlim hy with ⟨hyΔ, h0⟩ | ⟨hyΔ, h1⟩
    · rw [indicator_of_notMem (not_not.mpr hyΔ)]
      simp only [h0, elMirCutoff_zero]
      exact tendsto_const_nhds
    · rw [indicator_of_mem hyΔ, ← elMirCutoff_one]
      exact (contDiff_elMirCutoff.continuous.tendsto 1).comp h1
  · -- `θ'(vᵢ) → 0` on the support of `f`
    intro y hfy
    have hy : chartExtend e χ y ≠ 0 := by
      rw [(hχf y (subset_tsupport _ hfy)).self_of_nhds]
      exact one_ne_zero
    rcases hlim hy with ⟨-, h0⟩ | ⟨-, h1⟩
    · simp only [h0, deriv_elMirCutoff_zero]
      exact tendsto_const_nhds
    · rw [← deriv_elMirCutoff_one]
      exact (continuous_deriv_elMirCutoff.tendsto 1).comp h1

/-- **Skoda--El Mir for a holomorphically flat closed set**: `𝟙_{M \ Δ} T` is closed. -/
theorem isClosedCurrent_restrictCurrent_compl (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (hΔ : IsClosed Δ) (hflat : IsHoloFlat (n := n) Δ) :
    IsClosedCurrent (restrictCurrent w T hT Δᶜ) := by
  classical
  have hloc : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∀ (f g : M → ℝ) (hf : ChartSmooth (n := n) f) (hg : ChartSmooth (n := n) g),
        tsupport f ⊆ U → IsCompact (tsupport f) →
          ∀ β : Fin k → ClosedRealOneOneForm n M, (∀ j, (β j).val.IsSemipositive) →
            restrictCurrent w T hT Δᶜ (closedTestForm f g hf hg k β) = 0 := by
    intro x
    by_cases hx : x ∈ Δ
    · obtain ⟨e, W, c, Y, hxe, hW, hWt, hxW, hY, hYΔ⟩ := hflat x hx
      set O : Set (ComplexModel n) := W ∩ {z | ‖Y z‖ ^ 2 < 1}
      have hO : IsOpen O := isOpen_inter_normSq_lt hW hY
      have hOt : O ⊆ e.val.target := inter_subset_left.trans hWt
      refine ⟨e.val.symm '' O, ?_, ⟨e.val x, ⟨hxW, ?_⟩, e.val.left_inv hxe⟩,
        local_vanishing_of_mem w hT hTc e hW hWt hY hYΔ hΔ.measurableSet⟩
      · rw [e.val.symm_image_eq_source_inter_preimage hOt]
        exact e.val.isOpen_inter_preimage hO
      · show ‖Y (e.val x)‖ ^ 2 < 1
        rw [(hYΔ x hxe hxW).mp hx, norm_zero]
        norm_num
    · obtain ⟨e, O, hO, hOt, hxO, hvan⟩ := local_vanishing_of_notMem w hT hTc hΔ x
      refine ⟨e.val.symm '' O, ?_, hxO hx, hvan⟩
      rw [e.val.symm_image_eq_source_inter_preimage hOt]
      exact e.val.isOpen_inter_preimage hO
  choose U hUo hxU hU using hloc
  exact isClosedCurrent_of_local w (isPositive_restrictCurrent w T hT Δᶜ) U hUo hxU hU

/-- **Skoda--El Mir for a holomorphically flat closed set**: `𝟙_Δ T` is closed. -/
theorem isClosedCurrent_restrictCurrent (w : KahlerBackground n M) (hT : IsPositive T)
    (hTc : IsClosedCurrent T) {Δ : Set M} (hΔ : IsClosed Δ) (hflat : IsHoloFlat (n := n) Δ) :
    IsClosedCurrent (restrictCurrent w T hT Δ) := by
  have h := restrictCurrent_add_compl w T hT hΔ.measurableSet
  have : restrictCurrent w T hT Δ = T - restrictCurrent w T hT Δᶜ := eq_sub_of_add_eq h
  rw [this]
  exact hTc.sub (isClosedCurrent_restrictCurrent_compl w hT hTc hΔ hflat)

end Assembly

/-! ### The graph of a holomorphic map -/

section Graph

open scoped ProductComplexManifold
open ProductComplexManifold HolomorphicMaps

variable {n : ℕ} {V X : Type*} [TopologicalSpace V] [ChartedSpace (ComplexModel n) V]
  [IsComplexManifold n V] [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {f : V → X}

/-- The defining map `(z, w) ↦ w - F(z)` of the graph in a product chart, `F` the coordinate
representative of `f`. -/
def graphDefining (f : V → X) (a : ComplexChart n V) (b : ComplexChart n X)
    (ζ : ComplexModel (n + n)) : ComplexModel n :=
  ((prodModelEquiv n n).symm ζ).2 - coordinateMap f a b ((prodModelEquiv n n).symm ζ).1

/-- **The graph of a holomorphic map is holomorphically flat** in the product charts. -/
theorem isHoloFlat_graph (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) :
    IsHoloFlat (n := n + n) (M := V × X) {p | f p.1 = p.2} := by
  rintro ⟨v, x⟩ (h : f v = x)
  subst h
  set E := complexChartAt (n := n + n) ((v, f v) : V × X)
  set a : ComplexChart n V := complexChartAt (n := n) v
  set b : ComplexChart n X := complexChartAt (n := n) (f v)
  have hE : E.val = prodChart a.val b.val := rfl
  set π₁ : ComplexModel (n + n) → ComplexModel n := fun ζ => ((prodModelEquiv n n).symm ζ).1
  have hπ₁ : Continuous π₁ :=
    continuous_fst.comp (prodModelEquiv n n).symm.continuous
  set W : Set (ComplexModel (n + n)) := E.val.target ∩ π₁ ⁻¹' coordinateDomain f a b with hW_def
  have hW : IsOpen W :=
    E.val.open_target.inter ((coordinateDomain_isOpen hf a b).preimage hπ₁)
  have hva : v ∈ a.val.source := mem_complexChartAt_source v
  have hvb : f v ∈ b.val.source := mem_complexChartAt_source (f v)
  refine ⟨E, W, n, graphDefining f a b, mem_complexChartAt_source _, hW, inter_subset_left,
    ⟨E.val.map_source (mem_complexChartAt_source _), ?_⟩, ?_, ?_⟩
  · show π₁ (E.val (v, f v)) ∈ coordinateDomain f a b
    rw [hE]
    simp only [π₁, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨a.val.map_source hva, ?_⟩
    show f (a.val.symm (a.val v)) ∈ b.val.source
    rw [a.val.left_inv hva]
    exact hvb
  · intro ζ hζ
    have h1 : ContDiffAt ℂ ∞ (fun ζ : ComplexModel (n + n) =>
        coordinateMap f a b (π₁ ζ)) ζ :=
      (coordinateMap_contDiffAt hf a b hζ.2).comp ζ
        ((ContinuousLinearMap.fst ℂ (ComplexModel n) (ComplexModel n)).comp
          (prodModelEquiv n n).symm.toContinuousLinearMap).contDiff.contDiffAt
    have h2 : ContDiffAt ℂ ∞ (fun ζ : ComplexModel (n + n) =>
        ((prodModelEquiv n n).symm ζ).2) ζ :=
      ((ContinuousLinearMap.snd ℂ (ComplexModel n) (ComplexModel n)).comp
          (prodModelEquiv n n).symm.toContinuousLinearMap).contDiff.contDiffAt
    exact h2.sub h1
  · rintro ⟨p₁, p₂⟩ hp hpW
    rw [hE, prodChart_source] at hp
    have hpW' : π₁ (E.val (p₁, p₂)) ∈ coordinateDomain f a b := hpW.2
    rw [hE] at hpW'
    simp only [π₁, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply] at hpW'
    have hfp : f p₁ ∈ b.val.source := by
      have := hpW'.2
      simpa [a.val.left_inv hp.1] using this
    rw [hE]
    simp only [graphDefining, prodChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      coordinateMap, Function.comp_apply, a.val.left_inv hp.1, sub_eq_zero]
    exact ⟨fun h => by rw [h], fun h => (b.val.injOn hfp hp.2 h.symm)⟩

variable [CompactSpace V] [CompactSpace X] [MeasurableSpace (V × X)] [BorelSpace (V × X)] {k : ℕ}
  {T : ProductCurrent (n + n) (V × X) (k + 1)}

/-- **Skoda--El Mir on the graph of a holomorphic map** (`demailly-cadg:III.2.3` for `Γ_f`): for a
closed positive current `T` on `V × X`, `𝟙_{Γ_f} T` and `𝟙_{V × X \ Γ_f} T` are closed. -/
theorem isClosedCurrent_restrictCurrent_graph
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (w : KahlerBackground (n + n) (V × X)) (hT : IsPositive T) (hTc : IsClosedCurrent T) :
    IsClosedCurrent (restrictCurrent w T hT {p | f p.1 = p.2}) ∧
      IsClosedCurrent (restrictCurrent w T hT {p | f p.1 = p.2}ᶜ) := by
  have hcl : IsClosed {p : V × X | f p.1 = p.2} :=
    isClosed_eq (hf.continuous.comp continuous_fst) continuous_snd
  exact ⟨isClosedCurrent_restrictCurrent w hT hTc hcl (isHoloFlat_graph hf),
    isClosedCurrent_restrictCurrent_compl w hT hTc hcl (isHoloFlat_graph hf)⟩

end Graph

end SGPT.Foundations.Analysis.Pending.SkodaElMirHolomorphic
