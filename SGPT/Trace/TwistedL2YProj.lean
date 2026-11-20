import SGPT.Trace.TwistedL2YHilbert

/-!
# The data vector, the special families and the projected field on a manifold

Blueprint `claude-tl2-man2.tex` (lane TL2-MAN2, `claude-tl2-man2:projection`).  The manifold version
of `claude-tl2-dens:special` and `claude-tl2-dens:projection`:

* `yG`: the representative of the data functional `τ ↦ ⟨τ, ∂̄G⟩` in `H₂ = L²(X, μ; ℂⁿ)`
  (`memLp_yG` from the hypothesis on `Dσ`, `inner_repFamX_yG`);
* `ylamX c e u`: the representative of `T u = ∂̄u` for a test function `u` in the chart-frame
  `(c, e)` (`inner_ylamX`, `inner_repFamX_ylamX`);
* `specVX c e ψ j k`: the special families `S*(ψ dz̄_j ∧ dz̄_k)` in `(c, e)`
  (`inner_specVX`), orthogonal to the data vector (`∂̄∂̄G = 0`) and to all `ylamX` in all
  chart-frames (`T* S* = 0`; the computation is done in the chart of the special family, using the
  transport of `σ^{-T}∂̄u` and of `u` between charts);
* `exists_vX`: the projected field.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix
open scoped Topology ContDiff ComplexConjugate Manifold ComplexOrder InnerProductSpace ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-! ### `L²` pairings on a general measure space -/

theorem inner_toLp_left' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (x : α →₂[μ] ComplexModel n) {f : α → ComplexModel n} (hf : MemLp f 2 μ) :
    ⟪hf.toLp f, x⟫_ℂ = ∫ z, ⟪f z, x z⟫_ℂ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

theorem inner_toLp_right' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (x : α →₂[μ] ComplexModel n) {f : α → ComplexModel n} (hf : MemLp f 2 μ) :
    ⟪x, hf.toLp f⟫_ℂ = ∫ z, ⟪x z, f z⟫_ℂ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

theorem inner_toLp_toLp' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ComplexModel n} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ z, ⟪f z, g z⟫_ℂ ∂μ := by
  rw [inner_toLp_left']
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with z hz
  rw [hz]

theorem lowS_sigmaMatX (omega : KahlerBackground n X) (r : X → ℝ) (c : ComplexChart n X)
    (W : ComplexModel n → ComplexModel n) (z : ComplexModel n) (k : Fin n) :
    lowS (sigmaMatX omega r c) W z k = mv (gX omega r c z) (W z) k := by
  simp [lowS, mv_apply, gX, transpose_apply]

/-! ### Scalar transport of test functions between chart-frames -/

section Transf

variable {L : HermitianHolomorphicLineBundle.{0, 0} n X}

/-- The support `c⁻¹(tsupport u)` in `X` of a scalar function on a chart. -/
def sSupp (c : ComplexChart n X) (u : ComplexModel n → ℂ) : Set X :=
  c.val.source ∩ c.val ⁻¹' tsupport u

theorem isClosed_sSupp {c : ComplexChart n X} {u : ComplexModel n → ℂ} (hc : HasCompactSupport u)
    (ht : tsupport u ⊆ c.val.target) : IsClosed (sSupp c u) := by
  rw [sSupp, ← c.val.symm_image_eq_source_inter_preimage ht]
  exact (hc.isCompact.image_of_continuousOn (c.val.continuousOn_symm.mono ht)).isClosed

theorem mem_of_mem_sSupp {c : ComplexChart n X} {e : AtlasFrame L} {u : ComplexModel n → ℂ}
    (ht : tsupport u ⊆ chartFrameDomain L c e) {x : X} (hx : x ∈ sSupp c u) :
    x ∈ c.val.source ∩ e.val.baseSet := by
  have := (ht hx.2).2
  simp only [mem_preimage, c.val.left_inv hx.1] at this
  exact ⟨hx.1, this⟩

theorem transfX_eventuallyEq_zero' {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    {u : ComplexModel n → ℂ} (hc : HasCompactSupport u) (ht : tsupport u ⊆ c.val.target)
    {z : ComplexModel n} (hz : z ∈ c'.val.target) (hx : c'.val.symm z ∉ sSupp c u) :
    transfX L c e c' e' u =ᶠ[𝓝 z] 0 := by
  classical
  have hO : IsOpen (c'.val.target ∩ c'.val.symm ⁻¹' (sSupp c u)ᶜ) :=
    c'.val.continuousOn_symm.isOpen_inter_preimage c'.val.open_target
      (isClosed_sSupp hc ht).isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hz, hx⟩] with y hy
  by_cases hc' : y ∈ ovl c' c ∧ c'.val.symm y ∈ e.val.baseSet
  · rw [transfX, if_pos hc']
    have h0 : u (chg c' c y) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h' => hy.2 ⟨hc'.1.2, h'⟩
    rw [h0, mul_zero]
    rfl
  · rw [transfX, if_neg hc']
    rfl

theorem contDiffOn_transfX' {c c' : ComplexChart n X} {e e' : AtlasFrame L}
    {u : ComplexModel n → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (ht : tsupport u ⊆ chartFrameDomain L c e) :
    ContDiffOn ℝ ∞ (transfX L c e c' e' u) (chartFrameDomain L c' e') := by
  classical
  have ht' : tsupport u ⊆ c.val.target := ht.trans fun _ hz => hz.1
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  by_cases hx : c'.val.symm z ∈ sSupp c u
  · have hx' := mem_of_mem_sSupp ht hx
    have hzo : z ∈ ovl c' c := ⟨hz.1, hx'.1⟩
    set S : Set (ComplexModel n) :=
      ovl c' c ∩ c'.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet) with hS
    have hSo : IsOpen S :=
      (c'.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
        (isOpen_ovl c' c) (e.val.open_baseSet.inter e'.val.open_baseSet)
    have hzS : z ∈ S := ⟨hzo, hx'.2, hz.2⟩
    have htr : ContDiffOn ℝ ∞ (fun y => frameTrans L e e' (c'.val.symm y)) S :=
      contDiffOn_real_of_differentiableOn_complex
        ((differentiableOn_frameTrans c' e e').mono fun y hy => ⟨hy.1.1, hy.2⟩) hSo
    have hchg : ContDiffOn ℝ ∞ (chg c' c) S :=
      (contDiffOn_real_of_differentiableOn_complex (differentiableOn_chg c' c)
        (isOpen_ovl c' c)).mono fun y hy => hy.1
    refine ((htr.mul (hu.comp_contDiffOn hchg)).contDiffAt (hSo.mem_nhds hzS)).congr_of_eventuallyEq ?_
    filter_upwards [hSo.mem_nhds hzS] with y hy
    rw [transfX, if_pos ⟨hy.1, hy.2.1⟩]
    rfl
  · exact contDiffAt_const.congr_of_eventuallyEq
      (transfX_eventuallyEq_zero' (e := e) (e' := e') hc ht' hz.1 hx)

end Transf

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-! ### The data vector -/

/-- The unit-frame coefficient vector of `∂̄G` in the chart `c`, read through the frame `e`. -/
def gamF (c : ComplexChart n X) (e : AtlasFrame T.L) (x : X) : ComplexModel n :=
  (T.cfd c e).indicator (fun x => (T.ucX e x)⁻¹ • dbarV (chartCoeff T.L c e T.G) (c.val x)) x

/-- The unit-frame coefficient vector of `∂̄G` in the reference chart. -/
def gamR (x : X) : ComplexModel n := T.gamF (cR n x) (unitFrameTriv T.L x) x

/-- **The data vector** `e^{-φ/2} B*⁻¹ ∂̄G` in `H₂`. -/
def yG (x : X) : ComplexModel n :=
  T.U.indicator (fun x => mv (((T.hw x : ℝ) : ℂ) • T.BiR x) (T.gamR x)) x

variable {T}

theorem continuousOn_dbarV_G (c : ComplexChart n X) (e : AtlasFrame T.L) :
    ContinuousOn (dbarV (chartCoeff T.L c e T.G)) (T.pieceDomain c e) :=
  (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun _ =>
    (contDiffOn_dbarDir (T.isOpen_pieceDomain c e) (T.contDiffOn_chartCoeff c e) _).continuousOn)

theorem measurable_gamF (c : ComplexChart n X) (e : AtlasFrame T.L) : Measurable (T.gamF c e) := by
  have h1 : ContinuousOn (fun x => dbarV (chartCoeff T.L c e T.G) (c.val x)) (T.cfd c e) :=
    (continuousOn_dbarV_G c e).comp (c.val.continuousOn.mono fun x hx => hx.1.1)
      fun x hx => chart_mem_pieceDomain hx
  have h2 := ((measurable_ucX (T := T) e).inv).smul
    (measurable_indicator_of_continuousOn_ref (T.isOpen_cfd c e) h1)
  convert h2 using 1
  funext x
  by_cases hx : x ∈ T.cfd c e
  · simp [gamF, indicator_of_mem hx]
  · simp [gamF, indicator_of_notMem hx]

theorem gamF_frame {c : ComplexChart n X} {e e' : AtlasFrame T.L} {x : X} (hx : x ∈ T.cfd c e)
    (hx' : x ∈ e'.val.baseSet) : T.gamF c e' x = T.gamF c e x := by
  have hx'' : x ∈ T.cfd c e' := ⟨⟨hx.1.1, hx'⟩, hx.2⟩
  have hz := chart_mem_pieceDomain hx
  have hb : x ∈ e.val.baseSet ∩ e'.val.baseSet := ⟨hx.1.2, hx'⟩
  rw [gamF, gamF, indicator_of_mem hx'', indicator_of_mem hx]
  have hzD : c.val x ∈ T.ovlD c c e e' :=
    mem_ovlD hz ⟨by rw [c.val.left_inv hx.1.1]; exact hx.1.1, by rw [c.val.left_inv hx.1.1]; exact hx'⟩
  have hev := T.chartCoeff_transport hzD
  have hev' : chartCoeff T.L c e' T.G =ᶠ[𝓝 (c.val x)]
      fun y => frameTrans T.L e e' (c.val.symm y) * chartCoeff T.L c e T.G y := by
    filter_upwards [hev, chg_self_eventuallyEq (c := c) (c.val.map_source hx.1.1)] with y hy hy'
    rw [← hy]
    simp only [id] at hy'
    rw [hy']
  have hO : IsOpen (c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet)) :=
    c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter e'.val.open_baseSet)
  have ht : DifferentiableAt ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) (c.val x) :=
    (differentiableOn_frameTrans c e e').differentiableAt (hO.mem_nhds
      ⟨c.val.map_source hx.1.1, by rw [mem_preimage, c.val.left_inv hx.1.1]; exact hb⟩)
  have hG : DifferentiableAt ℝ (chartCoeff T.L c e T.G) (c.val x) :=
    ((T.contDiffOn_chartCoeff c e).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)).differentiableAt
      (by simp)
  have hd : dbarV (chartCoeff T.L c e' T.G) (c.val x) =
      frameTrans T.L e e' x • dbarV (chartCoeff T.L c e T.G) (c.val x) := by
    ext l
    simp only [dbarV, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply]
    rw [dbarDir_congr_of_eventuallyEq hev', dbarDir_holo_mul ht hG, c.val.left_inv hx.1.1]
  rw [hd, smul_smul, ucX_trans hb]
  congr 1
  have h1 := frameTrans_ne_zero e e' hb
  have h2 := ucX_ne_zero (T := T) hx.1.2
  field_simp

theorem gamR_eq {x : X} (hx : x ∈ T.U) {e : AtlasFrame T.L} (he : x ∈ e.val.baseSet) :
    T.gamR x = T.gamF (cR n x) e x := by
  exact gamF_frame ⟨⟨mem_cR_source x, he⟩, hx⟩ (mem_unitFrameTriv_baseSet T.L x)

theorem measurable_gamR : Measurable T.gamR := by
  classical
  refine measurable_cR_comp (n := n) (f := fun c x => T.gamF c (unitFrameTriv T.L x) x) fun c => ?_
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Subsingleton.measurable
  set E : ℕ → AtlasFrame T.L := fun k => atlasFrameAt T.L (frameSeq T.L hX k) with hE
  have hm := Measurable.find (f := fun k => T.gamF c (E k))
    (p := fun k x => x ∈ (E k).val.baseSet) (fun k => measurable_gamF c (E k))
    (fun k => (E k).val.open_baseSet.measurableSet) (frameSeq_spec T.L hX)
  convert hm using 1
  funext x
  rfl

theorem measurable_yG : Measurable T.yG :=
  measurable_ref_mv (M := fun c x => ((T.hw x : ℝ) : ℂ) • BiX T.omega T.r c (c.val x))
    T.isOpen_U (fun c i j => by
      have h1 : ContinuousOn (fun x => BiX T.omega T.r c (c.val x)) (T.U ∩ c.val.source) :=
        (continuousOn_BiX T.isOpen_U T.kahler c).comp (c.val.continuousOn.mono inter_subset_right)
          fun x hx => ⟨c.val.map_source hx.2, by rw [mem_preimage, c.val.left_inv hx.2]; exact hx.1⟩
      have h2 : ContinuousOn (fun x => ((T.hw x : ℝ) : ℂ)) (T.U ∩ c.val.source) :=
        Complex.continuous_ofReal.comp_continuousOn (continuousOn_hw.mono inter_subset_left)
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact h2.mul (continuousOn_entry' h1 i j)) measurable_gamR

/-- **The pointwise pairing of a piece with the data vector.** -/
theorem inner_repX_yG_pt {c : ComplexChart n X} {e : AtlasFrame T.L}
    (h : ComplexModel n → ComplexModel n) {x : X} (hx : x ∈ T.cfd c e) :
    ⟪T.repX c e h x, T.yG x⟫_ℂ = ((T.wX c e (c.val x) : ℝ) : ℂ) *
      dbarPairing (chartCoeff T.L c e T.G) (c.val x) (h (c.val x)) := by
  have hu := ucX_ne_zero (T := T) hx.1.2
  have hxR : x ∈ T.cfd (cR n x) e := ⟨⟨mem_cR_source x, hx.1.2⟩, hx.2⟩
  have hzo : c.val x ∈ ovl c (cR n x) := chart_mem_ovl_cR hx.1.1
  have hψz : chg c (cR n x) (c.val x) = (cR n x).val x := chg_chart hx.1.1
  -- the transport of the pairing to the reference chart
  have htr : dbarPairing (chartCoeff T.L (cR n x) e T.G) ((cR n x).val x)
      (mv (JR c x) (h (c.val x))) = dbarPairing (chartCoeff T.L c e T.G) (c.val x) (h (c.val x)) := by
    have hG : DifferentiableAt ℝ (chartCoeff T.L c e T.G) (c.val x) :=
      ((T.contDiffOn_chartCoeff c e).contDiffAt
        ((T.isOpen_pieceDomain c e).mem_nhds (chart_mem_pieceDomain hx))).differentiableAt (by simp)
    have hG' : DifferentiableAt ℝ (chartCoeff T.L (cR n x) e T.G) (chg c (cR n x) (c.val x)) := by
      rw [hψz]
      exact ((T.contDiffOn_chartCoeff (cR n x) e).contDiffAt
        ((T.isOpen_pieceDomain (cR n x) e).mem_nhds (chart_mem_pieceDomain hxR))).differentiableAt
          (by simp)
    have hrel : (fun y => chartCoeff T.L (cR n x) e T.G (chg c (cR n x) y)) =ᶠ[𝓝 (c.val x)]
        fun y => (fun _ => (1 : ℂ)) y * chartCoeff T.L c e T.G y := by
      filter_upwards [(isOpen_ovl c (cR n x)).mem_nhds hzo] with y hy
      simp only [chartCoeff, symm_chg hy, one_mul]
    have h1 := dbarPairing_transport (isOpen_ovl c (cR n x)) (differentiableOn_chg c (cR n x))
      (differentiableOn_const 1) hzo hG hG' hrel (h (c.val x))
    rw [hψz, one_smul, map_one, mul_one, one_mul] at h1
    rw [JR, mv_Jm]
    exact h1
  have hI : ⟪mv (T.BR x * JR c x) (h (c.val x)), mv (T.BiR x)
      (dbarV (chartCoeff T.L (cR n x) e T.G) ((cR n x).val x))⟫_ℂ =
      dbarPairing (chartCoeff T.L c e T.G) (c.val x) (h (c.val x)) := by
    rw [mv_mul, inner_mv_left, ← mv_mul, BR_conjTranspose, BR_mul_BiR hx.2, mv_one, inner_dbarV,
      htr]
  rw [repX_of_mem hx, yG, indicator_of_mem hx.2, gamR_eq hx.2 hx.1.2, gamF,
    indicator_of_mem hxR]
  simp only [mv_smul_mat, mv_smul, inner_smul_left, inner_smul_right]
  rw [hI]
  have hw := wX_chart_eq (T := T) hx.1
  have hnorm : ((‖T.ucX e x‖ ^ 2 : ℝ) : ℂ) = conj (T.ucX e x) * T.ucX e x := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hwC : ((T.wX c e (c.val x) : ℝ) : ℂ) * (conj (T.ucX e x) * T.ucX e x) =
      ((T.hw x : ℝ) : ℂ) * ((T.hw x : ℝ) : ℂ) := by
    rw [← hnorm, ← Complex.ofReal_mul, hw, ← Complex.ofReal_mul, sq]
  have hc0 : conj (T.ucX e x) ≠ 0 := by simpa using hu
  have hW : ((T.wX c e (c.val x) : ℝ) : ℂ) = ((T.hw x : ℝ) : ℂ) * ((T.hw x : ℝ) : ℂ) /
      (conj (T.ucX e x) * T.ucX e x) := by
    rw [eq_div_iff (mul_ne_zero hc0 hu)]; exact hwC
  simp only [Complex.conj_ofReal, map_inv₀]
  rw [hW]
  field_simp

theorem norm_yG_sq_le (x : X) :
    ‖T.yG x‖ ^ 2 ≤ T.U.indicator (fun x => max (T.Dσ x) 0 * Real.exp (-T.φ x)) x := by
  by_cases hxU : x ∈ T.U
  · rw [yG, indicator_of_mem hxU, indicator_of_mem hxU]
    set e := atlasFrameAt T.L x
    have he : x ∈ e.val.baseSet := mem_atlasFrameAt_baseSet T.L x
    have hxR : x ∈ T.cfd (cR n x) e := ⟨⟨mem_cR_source x, he⟩, hxU⟩
    set c := cR n x
    set z := c.val x
    have hz : z ∈ c.val.target := c.val.map_source (mem_cR_source x)
    have hzx : c.val.symm z = x := c.val.left_inv (mem_cR_source x)
    have hzU : c.val.symm z ∈ T.U := by rw [hzx]; exact hxU
    have hu := ucX_ne_zero (T := T) he
    rw [gamR_eq hxU he, gamF, indicator_of_mem hxR, mv_smul_mat, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (hw_pos x).le, mul_pow, hw_sq, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    refine norm_mv_BiX_sq_le T.isOpen_U T.kahler hz hzU (le_max_right _ _) fun v => ?_
    have hb := T.Dσ_bound c e z ⟨hz, by rw [mem_preimage, hzx]; exact he⟩ hzU v
    rw [hzx] at hb
    rw [inner_smul_right, inner_dbarV, norm_mul, mul_pow, norm_inv]
    have h1 := norm_ucX_sq_mul (T := T) he
    have hq : 0 ≤ sigmaQX T.omega T.r c z v := by
      rw [sigmaQX_eq_norm_sq T.isOpen_U T.kahler hz hzU]; positivity
    have hpos : 0 < ‖T.ucX e x‖ := norm_pos_iff.mpr hu
    have hf : frameNormSq T.L e x = (‖T.ucX e x‖⁻¹) ^ 2 := by
      field_simp; linarith
    rw [← hf]
    calc frameNormSq T.L e x * ‖dbarPairing (chartCoeff T.L c e T.G) z v‖ ^ 2
        = ‖dbarPairing (chartCoeff T.L c e T.G) z v‖ ^ 2 * frameNormSq T.L e x := by ring
      _ ≤ T.Dσ x * sigmaQX T.omega T.r c z v := hb
      _ ≤ max (T.Dσ x) 0 * sigmaQX T.omega T.r c z v :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hq
  · simp [yG, indicator_of_notMem hxU]

theorem memLp_yG : MemLp T.yG 2 T.μ := by
  refine ⟨measurable_yG.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hU := T.isOpen_U.measurableSet
  calc ∫⁻ x, ‖T.yG x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂T.μ
      ≤ ∫⁻ x, T.U.indicator (fun x => ENNReal.ofReal (T.Dσ x * Real.exp (-T.φ x))) x ∂T.μ := by
        refine lintegral_mono fun x => ?_
        have h := norm_yG_sq_le (T := T) x
        rw [← ofReal_norm, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
          (norm_nonneg _) (by norm_num)]
        by_cases hx : x ∈ T.U
        · rw [indicator_of_mem hx]; rw [indicator_of_mem hx] at h
          have h' : ‖T.yG x‖ ^ (2 : ℝ) ≤ max (T.Dσ x) 0 * Real.exp (-T.φ x) := by
            exact_mod_cast h
          rcases le_total 0 (T.Dσ x) with hD | hD
          · rw [max_eq_left hD] at h'
            exact ENNReal.ofReal_le_ofReal h'
          · rw [max_eq_right hD, zero_mul] at h'
            have h0 : ‖T.yG x‖ ^ (2 : ℝ) = 0 :=
              le_antisymm h' (Real.rpow_nonneg (norm_nonneg _) _)
            rw [h0, ENNReal.ofReal_zero]
            exact bot_le
        · rw [indicator_of_notMem hx]; rw [indicator_of_notMem hx] at h
          have : ‖T.yG x‖ ^ (2 : ℝ) = 0 := by
            have h0 : ‖T.yG x‖ = 0 := by nlinarith [norm_nonneg (T.yG x)]
            rw [h0]; norm_num
          rw [this, ENNReal.ofReal_zero]
    _ = ∫⁻ x in T.U, ENNReal.ofReal (T.Dσ x * Real.exp (-T.φ x)) ∂T.μ := lintegral_indicator hU _
    _ < ⊤ := T.Dσ_integrable

/-- **The data pairing of a piece is its `H₂`-pairing with the data vector.** -/
theorem integral_inner_repX_yG {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hhc : Continuous h) (hhs : HasCompactSupport h)
    (hKd : tsupport h ⊆ T.pieceDomain c e) :
    ∫ x, ⟪T.repX c e h x, T.yG x⟫_ℂ ∂T.μ = T.localDataPairing c e (T.ρX c) h := by
  have hK : IsCompact (tsupport h) := hhs
  have hKt : tsupport h ⊆ c.val.target := hKd.trans (T.pieceDomain_subset_target c e)
  have hmeas : Measurable fun x => ⟪T.repX c e h x, T.yG x⟫_ℂ :=
    (continuous_inner : Continuous fun p : ComplexModel n × ComplexModel n => ⟪p.1, p.2⟫_ℂ).measurable2
      (measurable_repX c e hhc.measurable) measurable_yG
  have h0 : ∀ z ∉ tsupport h, h z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [integral_eq_chart c (T.isChartDensity_ρX c) hK hKt hmeas fun x hx => ?_]
  · rw [localDataPairing]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport h)
      (f := fun z => dbarPairing (chartCoeff T.L c e T.G) z (h z) *
        cweight (localWeight T.L c e (T.ρX c) T.φ) z) fun z hz => by
          simp [h0 z hz, dbarPairing_zero]]
    refine setIntegral_congr_fun hK.measurableSet fun z hz => ?_
    have hzd := hKd hz
    have hx := symm_mem_cfd hzd
    rw [inner_repX_yG_pt h hx, c.val.right_inv hzd.1.1]
    change _ = _ * cweight (T.pX c e) z
    rw [cweight_pX hzd.1]
    ring
  · by_cases hxs : x ∈ c.val.source
    · rw [repX_eq_zero (h0 _ fun h' => hx ⟨hxs, h'⟩), inner_zero_left]
    · rw [repX_of_notMem fun h' => hxs h'.1.1, inner_zero_left]

/-! ### The `T*`-test vectors -/

variable (T) in
/-- `σ^{-T} ∂̄u = g_c⁻¹ ∂̄u` in the chart `c`. -/
def YuX (c : ComplexChart n X) (u : ComplexModel n → ℂ) (z : ComplexModel n) : ComplexModel n :=
  mv (gX T.omega T.r c z)⁻¹ (dbarV u z)

theorem YuX_eq_zero {c : ComplexChart n X} {u : ComplexModel n → ℂ} {z : ComplexModel n}
    (hz : z ∉ tsupport u) : T.YuX c u z = 0 := by
  have : dbarV u z = 0 := by
    ext l; simp [dbarV, dbarDir_eq_zero_of_notMem hz]
  simp [YuX, this]

theorem tsupport_YuX_subset (c : ComplexChart n X) (u : ComplexModel n → ℂ) :
    tsupport (T.YuX c u) ⊆ tsupport u :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (YuX_eq_zero h)) (isClosed_tsupport u)

theorem continuous_YuX {c : ComplexChart n X} {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.pieceDomain c e) u) : Continuous (T.YuX c u) := by
  have h2 : Continuous (dbarV u) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun l => continuous_dbarDir' (hu.1.of_le (by simp)))
  have hc : ContinuousOn (T.YuX c u) (T.pieceDomain c e) :=
    continuousOn_mv (fun i j => continuousOn_entry' (continuousOn_gXinv c e) i j) h2.continuousOn
  exact continuous_of_continuousOn_of_eq_zero' (T.isOpen_pieceDomain c e) hc (isClosed_tsupport u)
    hu.2.2 fun z hz => YuX_eq_zero hz

theorem memLp_YuX {c : ComplexChart n X} {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.pieceDomain c e) u) : MemLp (T.repX c e (T.YuX c u)) 2 T.μ :=
  memLp_repX hu.2.1 hu.2.2 ((continuous_YuX hu).memLp_of_hasCompactSupport
    (hu.2.1.mono' fun _ hz => subset_closure hz |> tsupport_YuX_subset c u))
    (continuous_YuX hu).measurable fun _ hz => YuX_eq_zero hz

/-- The `H₂`-representative of `T u = ∂̄u` for a test function `u` in the chart-frame `(c, e)`. -/
def ylamX (c : ComplexChart n X) (e : AtlasFrame T.L) {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.pieceDomain c e) u) : H2X T := (memLp_YuX hu).toLp _

/-- **The pairing with `T u` as a chart integral** (`⟨W, ∂̄u⟩` in the frame of `u`). -/
theorem integral_inner_repX_Yu {c : ComplexChart n X} {e : AtlasFrame T.L}
    {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn (T.pieceDomain c e) u)
    {f : X → ComplexModel n} (hf : Measurable f) :
    ∫ x, ⟪f x, T.repX c e (T.YuX c u) x⟫_ℂ ∂T.μ = ∫ z, (T.pieceDomain c e).indicator (fun z =>
      cweight (T.pX c e) z * ∑ l, dbarDir (coordVec l) u z * conj (T.WeX c e f z l)) z := by
  have h1 := integral_inner_repX (T := T) (c := c) (e := e) hu.2.1 hu.2.2
    (continuous_YuX hu).measurable (fun z hz => YuX_eq_zero hz) hf
  have h2 : ∫ x, ⟪f x, T.repX c e (T.YuX c u) x⟫_ℂ ∂T.μ =
      conj (∫ x, ⟪T.repX c e (T.YuX c u) x, f x⟫_ℂ ∂T.μ) := by
    rw [← integral_conj]
    exact integral_congr_ae (Eventually.of_forall fun x => (inner_conj_symm _ _).symm)
  rw [h2, h1, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.pieceDomain c e
  · have hcw : conj (cweight (T.pX c e) z) = cweight (T.pX c e) z := by
      rw [cweight, Complex.conj_ofReal]
    rw [indicator_of_mem hz, indicator_of_mem hz, map_mul, hcw, inner_conj_symm, YuX,
      inner_mv_left, gX_conjTranspose T.isOpen_U T.kahler hz.1.1 hz.2, ← mv_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
        (posDef_gX T.isOpen_U T.kahler hz.1.1 hz.2).det_pos.ne'), mv_one, sum_dbar_conj_eq_inner]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, map_zero]

theorem inner_ylamX (c : ComplexChart n X) (e : AtlasFrame T.L) {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.pieceDomain c e) u) (x : H2X T) :
    ⟪x, ylamX c e hu⟫_ℂ = ∫ z, (T.pieceDomain c e).indicator (fun z =>
      cweight (T.pX c e) z * ∑ l, dbarDir (coordVec l) u z * conj (T.WeX c e x z l)) z := by
  rw [ylamX, inner_toLp_right']
  exact integral_inner_repX_Yu hu (measurable_coe x)

/-! ### The special families -/

variable (T) in
/-- The special family `e^{p} (∂_k ψ ∂/∂z_j - ∂_j ψ ∂/∂z_k) = S*(ψ dz̄_j ∧ dz̄_k)` in `(c, e)`. -/
def specVX (c : ComplexChart n X) (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ) (j k : Fin n)
    (z : ComplexModel n) : ComplexModel n :=
  ((Real.exp (T.pX c e z) : ℝ) : ℂ) •
    (dDir (coordVec k) ψ z • (coordVec j : ComplexModel n) - dDir (coordVec j) ψ z • coordVec k)

theorem specVX_eq_zero {c : ComplexChart n X} {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    {j k : Fin n} {z : ComplexModel n} (hz : z ∉ tsupport ψ) : T.specVX c e ψ j k z = 0 := by
  simp [specVX, dDir_eq_zero_of_notMem hz]

theorem continuous_specVX {c : ComplexChart n X} {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.pieceDomain c e) ψ) (j k : Fin n) :
    Continuous (T.specVX c e ψ j k) := by
  have hO := T.isOpen_pieceDomain c e
  have h1 : ContinuousOn (fun z => ((Real.exp (T.pX c e z) : ℝ) : ℂ)) (T.pieceDomain c e) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (contDiffOn_pX c e).continuousOn)
  have hd : ∀ v, Continuous (dDir v ψ) := fun v =>
    (contDiff_dDir (k := 0) (hψ.1.of_le (by norm_num))).continuous
  refine continuous_of_continuousOn_of_eq_zero' hO ?_ (isClosed_tsupport ψ) hψ.2.2
    fun z hz => specVX_eq_zero hz
  exact h1.smul ((((hd _).smul continuous_const).sub
    ((hd _).smul continuous_const)).continuousOn)

theorem tsupport_specVX_subset (c : ComplexChart n X) (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ)
    (j k : Fin n) : tsupport (T.specVX c e ψ j k) ⊆ tsupport ψ :=
  closure_minimal (fun z hz => by
    by_contra h
    exact hz (specVX_eq_zero h)) (isClosed_tsupport ψ)

theorem memLp_specVX {c : ComplexChart n X} {e : AtlasFrame T.L} {ψ : ComplexModel n → ℂ}
    (hψ : IsTestFunctionOn (T.pieceDomain c e) ψ) (j k : Fin n) :
    MemLp (T.repX c e (T.specVX c e ψ j k)) 2 T.μ :=
  memLp_repX hψ.2.1 hψ.2.2 ((continuous_specVX hψ j k).memLp_of_hasCompactSupport
    (hψ.2.1.mono' fun _ hz => subset_closure hz |> tsupport_specVX_subset c e ψ j k))
    (continuous_specVX hψ j k).measurable fun _ hz => specVX_eq_zero hz

/-- **The `H₂`-pairing with a special family**: `σ` cancels. -/
theorem integral_inner_specVX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ψ : ComplexModel n → ℂ} (hψ : IsTestFunctionOn (T.pieceDomain c e) ψ) (j k : Fin n)
    {f : X → ComplexModel n} (hf : Measurable f) :
    ∫ x, ⟪T.repX c e (T.specVX c e ψ j k) x, f x⟫_ℂ ∂T.μ = ∫ z, (T.pieceDomain c e).indicator
      (fun z => conj (dDir (coordVec k) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e f) z j -
        conj (dDir (coordVec j) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e f) z k) z := by
  rw [integral_inner_repX hψ.2.1 hψ.2.2 (continuous_specVX hψ j k).measurable
    (fun z hz => specVX_eq_zero hz) hf]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ T.pieceDomain c e
  · rw [indicator_of_mem hz, indicator_of_mem hz, lowS_sigmaMatX, lowS_sigmaMatX]
    have hB : cweight (T.pX c e) z * ((Real.exp (T.pX c e z) : ℝ) : ℂ) = 1 := by
      rw [cweight, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    rw [specVX, inner_smul_left, inner_sub_left, inner_smul_left, inner_smul_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left, Complex.conj_ofReal]
    simp only [map_one, one_mul]
    linear_combination (conj (dDir (coordVec k) ψ z) * mv (gX T.omega T.r c z) (T.WeX c e f z) j -
      conj (dDir (coordVec j) ψ z) * mv (gX T.omega T.r c z) (T.WeX c e f z) k) * hB
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

theorem inner_specVX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ψ : ComplexModel n → ℂ} (hψ : IsTestFunctionOn (T.pieceDomain c e) ψ) (j k : Fin n)
    (x : H2X T) :
    ⟪(memLp_specVX hψ j k).toLp _, x⟫_ℂ = ∫ z, (T.pieceDomain c e).indicator
      (fun z => conj (dDir (coordVec k) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e x) z j -
        conj (dDir (coordVec j) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e x) z k) z := by
  rw [inner_toLp_left']
  exact integral_inner_specVX hψ j k (measurable_coe x)

/-- The special families have zero data pairing (`∂̄∂̄G = 0`). -/
theorem inner_specVX_yG {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ψ : ComplexModel n → ℂ} (hψ : IsTestFunctionOn (T.pieceDomain c e) ψ) (j k : Fin n) :
    ⟪(memLp_specVX hψ j k).toLp _, memLp_yG.toLp T.yG⟫_ℂ = 0 := by
  have hts : tsupport (T.specVX c e ψ j k) ⊆ T.pieceDomain c e :=
    (tsupport_specVX_subset c e ψ j k).trans hψ.2.2
  rw [inner_toLp_toLp', integral_inner_repX_yG (continuous_specVX hψ j k)
    (hψ.2.1.mono' fun _ hz => subset_closure hz |> tsupport_specVX_subset c e ψ j k) hts,
    localDataPairing,
    ← integral_antisym_eq_zero (T.isOpen_pieceDomain c e) (T.contDiffOn_chartCoeff c e) hψ j k]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.pieceDomain c e
  · have hB : cweight (T.pX c e) z * ((Real.exp (T.pX c e z) : ℝ) : ℂ) = 1 := by
      rw [cweight, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        Complex.ofReal_one]
    change _ * cweight (T.pX c e) z = _
    rw [← inner_dbarV, specVX, inner_smul_left, inner_sub_left,
      inner_smul_left, inner_smul_left, EuclideanSpace.inner_single_left,
      EuclideanSpace.inner_single_left, Complex.conj_ofReal]
    simp only [dbarV, map_one, one_mul, PiLp.toLp_apply]
    linear_combination (dbarDir (coordVec j) (chartCoeff T.L c e T.G) z *
        conj (dDir (coordVec k) ψ z) - dbarDir (coordVec k) (chartCoeff T.L c e T.G) z *
        conj (dDir (coordVec j) ψ z)) * hB
  · have hzψ : z ∉ tsupport ψ := fun h => hz (hψ.2.2 h)
    rw [specVX_eq_zero hzψ, dDir_eq_zero_of_notMem hzψ, dDir_eq_zero_of_notMem hzψ]
    simp [dbarPairing_zero]

/-! ### `T* S* = 0` across chart-frames -/

/-- **`g_{c'}` applied to the transport of `σ^{-T}∂̄u` is `∂̄` of the transported `u`.** -/
theorem mv_gX_transpX_YuX {c c' : ComplexChart n X} {e e' : AtlasFrame T.L}
    {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn (T.pieceDomain c e) u) {z' : ComplexModel n}
    (hz' : z' ∈ T.pieceDomain c' e') :
    mv (gX T.omega T.r c' z') (transpX T.L c e c' e' (T.YuX c u) z') =
      dbarV (transfX T.L c e c' e' u) z' := by
  have htu : tsupport u ⊆ chartFrameDomain T.L c e := fun z hz => (hu.2.2 hz).1
  have htt : tsupport u ⊆ c.val.target := htu.trans fun _ hz => hz.1
  by_cases hx : c'.val.symm z' ∈ sSupp c u
  · obtain ⟨hxs, hxb⟩ := mem_of_mem_sSupp htu hx
    have hzo' : z' ∈ ovl c' c := ⟨hz'.1.1, hxs⟩
    set z := chg c' c z'
    have hzo : z ∈ ovl c c' := chg_mem_ovl hzo'
    have hzz : chg c c' z = z' := chg_chg hzo'
    have hsz : c.val.symm z = c'.val.symm z' := symm_chg hzo'
    have hzd : z ∈ T.pieceDomain c e := by
      refine ⟨⟨hzo.1, ?_⟩, ?_⟩
      · rw [mem_preimage, hsz]; exact hxb
      · rw [mem_preimage, hsz]; exact hz'.2
    have hb : c.val.symm z ∈ e.val.baseSet ∩ e'.val.baseSet := by
      rw [hsz]; exact ⟨hxb, hz'.1.2⟩
    set t := frameTrans T.L e e' (c.val.symm z)
    have ht0 : t ≠ 0 := frameTrans_ne_zero e e' hb
    set M := Jm c c' z
    set d := dbarV u z
    set d' := dbarV (transfX T.L c e c' e' u) z'
    -- the transport of `∂̄u`: `Mᴴ d' = t d`
    have hA : mv Mᴴ d' = t • d := by
      set S : Set (ComplexModel n) :=
        ovl c c' ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ e'.val.baseSet) with hS
      have hSo : IsOpen S :=
        (c.val.continuousOn_symm.mono fun _ hy => hy.1).isOpen_inter_preimage
          (isOpen_ovl c c') (e.val.open_baseSet.inter e'.val.open_baseSet)
      have hzS : z ∈ S := ⟨hzo, hb⟩
      have hψ : DifferentiableOn ℂ (chg c c') S := (differentiableOn_chg c c').mono fun y hy => hy.1
      have ht' : DifferentiableOn ℂ (fun y => frameTrans T.L e e' (c.val.symm y)) S :=
        (differentiableOn_frameTrans c e e').mono fun y hy => ⟨hy.1.1, hy.2⟩
      have hud : DifferentiableAt ℝ u z := hu.1.differentiable (by simp) z
      have hu'd : DifferentiableAt ℝ (transfX T.L c e c' e' u) (chg c c' z) := by
        rw [hzz]
        exact ((contDiffOn_transfX' hu.1 hu.2.1 htu).contDiffAt
          ((isOpen_chartFrameDomain T.L c' e').mem_nhds hz'.1)).differentiableAt (by simp)
      have hrel := transfX_chg_eventually (L := T.L) (c := c) (c' := c') (e := e) (e' := e')
        (g := u) hzo hb.1
      refine ext_inner_left ℂ fun v => ?_
      have h1 := dbarPairing_transport hSo hψ ht' hzS hud hu'd hrel v
      rw [hzz] at h1
      rw [← inner_dbarV, ← inner_dbarV, inner_smul_left, ← mv_Jm, inner_mv_left] at h1
      rw [inner_smul_right]
      have hc : conj t ≠ 0 := by simpa using ht0
      have h2 : conj t * ⟪v, mv Mᴴ d'⟫_ℂ = conj t * (t * ⟪v, d⟫_ℂ) := by
        rw [h1]; ring
      exact mul_left_cancel₀ hc h2
    -- `Mᴴ g' (t M Y) = t d`
    have hzU : c.val.symm z ∈ T.U := hzd.2
    have hgchg := gX_chg' T.isOpen_U T.kahler hzo hzU
    rw [hzz] at hgchg
    have hg : IsUnit (gX T.omega T.r c z).det :=
      isUnit_iff_ne_zero.mpr (posDef_gX T.isOpen_U T.kahler hzo.1 hzU).det_pos.ne'
    have hB : mv Mᴴ (mv (gX T.omega T.r c' z') (t • mv M (T.YuX c u z))) = t • d := by
      rw [mv_smul, mv_smul, ← mv_mul, ← mv_mul,
        show Mᴴ * gX T.omega T.r c' z' * M = gX T.omega T.r c z from hgchg.symm, YuX, ← mv_mul,
        mul_nonsing_inv _ hg, mv_one]
    have htr : transpX T.L c e c' e' (T.YuX c u) z' = t • mv M (T.YuX c u z) := by
      rw [transpX_of_mem hzo' (by simpa using hxb), mv_Jm, ← hsz]
    have hMu : IsUnit Mᴴ.det := by
      rw [det_conjTranspose]
      exact ((isUnit_iff_isUnit_det _).mp (isUnit_linMat_fderiv_chg hzo)).star
    have hinj : ∀ a b : ComplexModel n, mv Mᴴ a = mv Mᴴ b → a = b := fun a b hab => by
      have := congrArg (mv (Mᴴ)⁻¹) hab
      rwa [← mv_mul, ← mv_mul, nonsing_inv_mul _ hMu, mv_one, mv_one] at this
    rw [htr]
    exact hinj _ _ (hB.trans hA.symm)
  · have hYs : tsupport (T.YuX c u) ⊆ tsupport u := tsupport_YuX_subset c u
    have hx' : c'.val.symm z' ∉ TwistedDatum.pieceSupport c (T.YuX c u) := fun h =>
      hx ⟨h.1, hYs h.2⟩
    have h1 : transpX T.L c e c' e' (T.YuX c u) =ᶠ[𝓝 z'] 0 :=
      transpX_eventuallyEq_zero (hu.2.1.mono' (subset_closure.trans hYs)) (hYs.trans htt)
        hz'.1.1 hx'
    have h2 : transfX T.L c e c' e' u =ᶠ[𝓝 z'] 0 :=
      transfX_eventuallyEq_zero' hu.2.1 htt hz'.1.1 hx
    rw [h1.self_of_nhds]
    ext l
    simp [dbarV, dbarDir_eq_zero_of_eventuallyEq_zero h2]

/-- **The special families are orthogonal to the `T*`-test vectors** in all chart-frames. -/
theorem inner_specVX_ylamX {c' : ComplexChart n X} {e' : AtlasFrame T.L}
    {ψ : ComplexModel n → ℂ} (hψ : IsTestFunctionOn (T.pieceDomain c' e') ψ) (j k : Fin n)
    {c : ComplexChart n X} {e : AtlasFrame T.L} {u : ComplexModel n → ℂ}
    (hu : IsTestFunctionOn (T.pieceDomain c e) u) :
    ⟪(memLp_specVX hψ j k).toLp _, ylamX c e hu⟫_ℂ = 0 := by
  have htu : tsupport u ⊆ chartFrameDomain T.L c e := fun z hz => (hu.2.2 hz).1
  have hg : ContDiffOn ℝ ∞ (transfX T.L c e c' e' u) (T.pieceDomain c' e') :=
    (contDiffOn_transfX' hu.1 hu.2.1 htu).mono fun z hz => hz.1
  rw [ylamX, inner_toLp_toLp', integral_inner_specVX hψ j k
    (measurable_repX c e (continuous_YuX hu).measurable),
    ← integral_antisym_eq_zero (T.isOpen_pieceDomain c' e') hg hψ j k]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.pieceDomain c' e'
  · rw [indicator_of_mem hz, lowS_sigmaMatX, lowS_sigmaMatX]
    have hW : T.WeX c' e' (T.repX c e (T.YuX c u)) z = transpX T.L c e c' e' (T.YuX c u) z := by
      have := WeX_repX (T := T) (c := c') (e := e') (c' := c) (e' := e) (h := T.YuX c u)
        (symm_mem_cfd hz)
      rwa [c'.val.right_inv hz.1.1] at this
    rw [hW, mv_gX_transpX_YuX hu hz]
    simp only [dbarV, PiLp.toLp_apply]
    ring
  · have hzψ : z ∉ tsupport ψ := fun h => hz (hψ.2.2 h)
    rw [indicator_of_notMem hz, dDir_eq_zero_of_notMem hzψ, dDir_eq_zero_of_notMem hzψ]
    simp

/-! ### Test families in `H₂` and the projection -/

theorem memLp_pieceX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hh : IsLocalTestField T.L T.U c e h) :
    MemLp (T.repX c e h) 2 T.μ :=
  memLp_repX hh.2.1 hh.2.2 (hh.1.continuous.memLp_of_hasCompactSupport hh.2.1)
    hh.1.continuous.measurable fun _ hz => image_eq_zero_of_notMem_tsupport hz

/-- The representative of a finite family in `H₂`. -/
def repFamX (F : T.XFam) : H2X T := ∑ i ∈ F.s, (memLp_pieceX (F.spec i)).toLp _

theorem coeFn_repFamX (F : T.XFam) :
    ⇑(repFamX F) =ᵐ[T.μ] fun x => ∑ i ∈ F.s, T.repX (F.c i) (F.e i) (F.h i) x := by
  have h1 := Lp.coeFn_fun_finsetSum F.s fun i => (memLp_pieceX (F.spec i)).toLp _
  have h2 : ∀ᵐ x ∂T.μ, ∀ i ∈ F.s, ((memLp_pieceX (F.spec i)).toLp _ : H2X T) x =
      T.repX (F.c i) (F.e i) (F.h i) x :=
    (F.s.eventually_all).mpr fun i _ => (memLp_pieceX (F.spec i)).coeFn_toLp
  filter_upwards [h1, h2] with x hx1 hx2
  rw [repFamX, hx1]
  exact Finset.sum_congr rfl hx2

/-- **The data pairing of a family is its `H₂`-pairing with the data vector.** -/
theorem inner_repFamX_yG (F : T.XFam) : ⟪repFamX F, memLp_yG.toLp T.yG⟫_ℂ = F.data := by
  rw [repFamX, sum_inner, XFam.data]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_toLp_toLp', integral_inner_repX_yG (F.spec i).1.continuous (F.spec i).2.1
    (F.spec i).2.2]

theorem WepsX_sum {ι : Type*} (s : Finset ι) (f : ι → X → ComplexModel n) (x : X) :
    T.WepsX (fun x => ∑ i ∈ s, f i x) x = ∑ i ∈ s, T.WepsX (f i) x := by
  by_cases hx : x ∈ T.U
  · simp only [WepsX, indicator_of_mem hx, mv_sum]
  · simp [WepsX, indicator_of_notMem hx]

theorem WeX_sum (c : ComplexChart n X) (e : AtlasFrame T.L) {ι : Type*} (s : Finset ι)
    (f : ι → X → ComplexModel n) (z : ComplexModel n) :
    T.WeX c e (fun x => ∑ i ∈ s, f i x) z = ∑ i ∈ s, T.WeX c e (f i) z := by
  by_cases hz : z ∈ T.pieceDomain c e
  · have hx := symm_mem_cfd hz
    have h := fun (g : X → ComplexModel n) => WeX_chart (T := T) g hx
    rw [c.val.right_inv hz.1.1] at h
    rw [h, WepsX_sum, mv_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (h (f i)).symm
  · simp [WeX_eq_zero hz]

/-- **The `T*`-pairing of a family** (integration by parts in the chart of the test function). -/
theorem inner_repFamX_ylamX (F : T.XFam) {c : ComplexChart n X} {e : AtlasFrame T.L}
    {u : ComplexModel n → ℂ} (hu : IsTestFunctionOn (T.pieceDomain c e) u) :
    ⟪repFamX F, ylamX c e hu⟫_ℂ =
      ∫ z, u z * conj (chartTheta (T.pX c e) (F.tot c e) z) * cweight (T.pX c e) z := by
  have hm : Measurable fun x => ∑ i ∈ F.s, T.repX (F.c i) (F.e i) (F.h i) x :=
    Finset.measurable_sum _ fun i _ => measurable_repX _ _ (F.spec i).1.continuous.measurable
  rw [ylamX, inner_toLp_right']
  rw [integral_congr_ae (g := fun x => ⟪∑ i ∈ F.s, T.repX (F.c i) (F.e i) (F.h i) x,
    T.repX c e (T.YuX c u) x⟫_ℂ) (by
      filter_upwards [coeFn_repFamX F] with x hx
      rw [hx])]
  rw [integral_inner_repX_Yu hu hm, ← integral_dbar_conj_eq (T.isOpen_pieceDomain c e)
    (contDiffOn_pX c e) (F.contDiffOn_tot c e) hu]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  by_cases hz : z ∈ T.pieceDomain c e
  · rw [indicator_of_mem hz, WeX_sum]
    have hx := symm_mem_cfd hz
    have htot : ∑ i ∈ F.s, T.WeX c e (T.repX (F.c i) (F.e i) (F.h i)) z = F.tot c e z := by
      rw [XFam.tot]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := WeX_repX (T := T) (c := c) (e := e) (c' := F.c i) (e' := F.e i) (h := F.h i) hx
      rwa [c.val.right_inv hz.1.1] at this
    rw [htot]
  · have hzu : z ∉ tsupport u := fun h => hz (hu.2.2 h)
    rw [indicator_of_notMem hz]
    simp [dbarDir_eq_zero_of_notMem hzu]

variable (T) in
/-- The index type of the special families. -/
def SpecIdxX : Type :=
  {q : ComplexChart n X × AtlasFrame T.L × (ComplexModel n → ℂ) × Fin n × Fin n //
    IsTestFunctionOn (T.pieceDomain q.1 q.2.1) q.2.2.1}

/-- The special families in `H₂`. -/
def genX (q : T.SpecIdxX) : H2X T := (memLp_specVX q.2 q.1.2.2.2.1 q.1.2.2.2.2).toLp _

/-- **The projected field on a manifold** (`claude-tl2-man2:projection`): for every finite family
`τ` there is `v ∈ H₂` with `∂̄(σ^♭ v) = 0` and `T* v = T* τ` weakly in every chart-frame, and
`⟨v, ∂̄G⟩ = ⟨τ, ∂̄G⟩`. -/
theorem exists_vX (F : T.XFam) : ∃ v : H2X T,
    (∀ (c : ComplexChart n X) (e : AtlasFrame T.L) (ψ : ComplexModel n → ℂ),
      IsTestFunctionOn (T.pieceDomain c e) ψ → ∀ j k : Fin n,
      ∫ z, (T.pieceDomain c e).indicator (fun z =>
        conj (dDir (coordVec k) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e v) z j -
        conj (dDir (coordVec j) ψ z) * lowS (sigmaMatX T.omega T.r c) (T.WeX c e v) z k) z = 0) ∧
    (∀ (c : ComplexChart n X) (e : AtlasFrame T.L) (u : ComplexModel n → ℂ),
      IsTestFunctionOn (T.pieceDomain c e) u →
      ∫ z, (T.pieceDomain c e).indicator (fun z => cweight (T.pX c e) z *
        ∑ l, dbarDir (coordVec l) u z * conj (T.WeX c e v z l)) z =
      ∫ z, u z * conj (chartTheta (T.pX c e) (F.tot c e) z) * cweight (T.pX c e) z) ∧
    ⟪v, memLp_yG.toLp T.yG⟫_ℂ = F.data := by
  obtain ⟨v, h1, h2⟩ := exists_proj_orth (genX (T := T)) (repFamX F)
  refine ⟨v, fun c e ψ hψ j k => ?_, fun c e u hu => ?_, ?_⟩
  · have := h1 ⟨(c, e, ψ, j, k), hψ⟩
    rw [show genX ⟨(c, e, ψ, j, k), hψ⟩ = (memLp_specVX hψ j k).toLp _ from rfl,
      inner_specVX hψ j k] at this
    exact this
  · have := h2 (ylamX c e hu) fun q => inner_specVX_ylamX q.2 _ _ hu
    rw [inner_ylamX, inner_repFamX_ylamX] at this
    exact this
  · rw [h2 _ fun q => inner_specVX_yG q.2 _ _, inner_repFamX_yG]

end TwistedDatum

end SGPT.Trace.TwistedL2
