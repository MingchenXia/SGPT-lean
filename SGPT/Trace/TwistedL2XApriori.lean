import SGPT.Trace.TwistedL2XFamily

/-!
# The twisted a priori estimate on a complex manifold

Blueprint `claude-tl2-man.tex` (lane TL2-MAN, `claude-tl2-man:apriori`,
`claude-tl2-man:reduction`).  For a twisted datum on a complex manifold `X` and a finite family of
local pieces in arbitrary charts and frames:

* `XFam.sum_mkh`: the globalized polarized Morrey--Kohn--Hörmander identity
  `∫_X |ϑ' W|² a|e|²e^{-φ} dμ = ∫_X tr(A_W Ā_W) a|e|²e^{-φ} dμ + ∫_X Levi(p')(W) a|e|²e^{-φ} dμ`;
* `XFam.apriori`: `|⟨τ, ∂̄G⟩|² ≤ (∫_U D e^{-φ} dμ) (‖T* τ‖² + Q(τ))`, with the defect
  `Q(τ) = -Re ∫_X tr(A_W Ā_W) a |e|² e^{-φ} dμ`;
* `XFam.norm_sq_data_le` and `twistedL2CorrectionStatement_of_graphDensityX`: if every datum on `X`
  satisfies graph density of test families (`GraphDensityX`), then
  `TwistedFunctionalBoundStatement n X` and `TwistedL2CorrectionStatement n X` hold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

/-- Cauchy--Schwarz in the form `(∫ k)² ≤ ∫ f ∫ g` for `k² ≤ f g`, on any measure space. -/
theorem sq_integral_le_of_sq_le_mul_gen {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g k : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hk : Integrable k μ)
    (hf0 : ∀ z, 0 ≤ f z) (hg0 : ∀ z, 0 ≤ g z) (hk0 : ∀ z, 0 ≤ k z)
    (hkfg : ∀ z, k z ^ 2 ≤ f z * g z) :
    (∫ z, k z ∂μ) ^ 2 ≤ (∫ z, f z ∂μ) * ∫ z, g z ∂μ := by
  refine sq_le_mul_of_forall_pos (integral_nonneg hk0) (integral_nonneg hf0)
    (integral_nonneg hg0) fun t ht => ?_
  have hpt : ∀ z, 2 * k z ≤ t * f z + g z / t := by
    intro z
    have hM : 0 ≤ g z / t := div_nonneg (hg0 z) ht.le
    have hL : 0 ≤ t * f z := mul_nonneg ht.le (hf0 z)
    have hLM : t * f z * (g z / t) = f z * g z := by field_simp
    have h4 : 4 * k z ^ 2 ≤ (t * f z + g z / t) ^ 2 := by
      nlinarith [sq_nonneg (t * f z - g z / t), hkfg z]
    nlinarith [hk0 z, sq_nonneg (t * f z + g z / t - 2 * k z)]
  have hint : Integrable (fun z => t * f z + g z / t) μ := (hf.const_mul t).add (hg.div_const t)
  calc 2 * ∫ z, k z ∂μ = ∫ z, 2 * k z ∂μ := (integral_const_mul 2 _).symm
    _ ≤ ∫ z, (t * f z + g z / t) ∂μ := integral_mono (hk.const_mul 2) hint hpt
    _ = t * (∫ z, f z ∂μ) + (∫ z, g z ∂μ) / t := by
      rw [integral_add (hf.const_mul t) (hg.div_const t), integral_const_mul, integral_div]

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable {T : TwistedDatum n X}

/-! ### Weights and diagonal values -/

theorem cweight_pTX {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) :
    cweight (T.pTX c e) z = ((T.ρX c z : ℝ) : ℂ) * ((T.aC c z * T.wX c e z : ℝ) : ℂ) := by
  have h : ((Real.exp (-T.pX c e z) : ℝ) : ℂ) = ((T.ρX c z : ℝ) : ℂ) * ((T.wX c e z : ℝ) : ℂ) :=
    cweight_pX (T := T) hz.1
  have e1 : Real.exp (-(T.pTX c e z)) = T.aC c z * Real.exp (-T.pX c e z) := by
    simp only [pTX]
    rw [show -(T.pX c e z - Real.log (T.aC c z)) = Real.log (T.aC c z) + -T.pX c e z by ring,
      Real.exp_add, Real.exp_log (aC_pos hz)]
  rw [cweight, e1, Complex.ofReal_mul, h]
  push_cast
  ring

theorem FθX_diag_re (c : ComplexChart n X) (e : AtlasFrame T.L)
    (u : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    (T.FθX c e u u z).re = ‖chartTheta (T.pTX c e) u z‖ ^ 2 * (T.aC c z * T.wX c e z) := by
  simp only [FθX, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem FAX_diag_re (c : ComplexChart n X) (e : AtlasFrame T.L)
    (u : ComplexModel n → ComplexModel n) (z : ComplexModel n) :
    (T.FAX c e u u z).re =
      (T.aC c z + T.bC c z) * ‖chartTheta (T.pX c e) u z‖ ^ 2 * T.wX c e z := by
  simp only [FAX, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem FLX_diag_re {c : ComplexChart n X} {e : AtlasFrame T.L}
    (u : ComplexModel n → ComplexModel n) {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) :
    (T.FLX c e u u z).re = leviForm (T.pTX c e) z (u z) * (T.aC c z * T.wX c e z) := by
  have h2 : ContDiffAt ℝ 2 (T.pTX c e) z :=
    ((contDiffOn_pTX c e).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  simp only [FLX, leviS_self h2]
  norm_cast

theorem HsX_diag {c : ComplexChart n X} {e : AtlasFrame T.L} {z : ComplexModel n}
    (hz : z ∈ T.pieceDomain c e) (v : ComplexModel n) :
    T.HsX c e z v v = (twistedCurvature (T.aC c) (T.bC c) (T.pX c e) z v : ℂ) := by
  have h2 := two_le_infty
  have ha : ContDiffAt ℝ ∞ (T.aC c) z :=
    (contDiffOn_aC (e := e) c).contDiffAt ((T.isOpen_pieceDomain c e).mem_nhds hz)
  have hp : ContDiffAt ℝ ∞ (T.pX c e) z := contDiffAt_pX hz
  have hdA : T.dAX c z v * conj (T.dAX c z v) = ((holDerivSq (T.aC c) z v : ℝ) : ℂ) := by
    have h := FunctionalTwistedAdjointYoungDraft.normSq_chartTwistDerivative (T.aC c)
      (fun _ => v) (ha.differentiableAt (by simp))
    rw [FunctionalTwistedAdjointYoungDraft.chartTwistDerivative_eq_dDir] at h
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← h]
    rfl
  simp only [HsX, leviS_self (hp.of_le h2), leviS_self (ha.of_le h2), hdA, twistedCurvature]
  push_cast
  ring

theorem FHX_diag_re {c : ComplexChart n X} {e : AtlasFrame T.L}
    (u : ComplexModel n → ComplexModel n) {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) :
    (T.FHX c e u u z).re =
      twistedCurvature (T.aC c) (T.bC c) (T.pX c e) z (u z) * T.wX c e z := by
  simp only [FHX, HsX_diag hz]
  norm_cast

theorem twistedCurvature_nonnegX {c : ComplexChart n X} {e : AtlasFrame T.L}
    {z : ComplexModel n} (hz : z ∈ T.pieceDomain c e) (v : ComplexModel n) :
    0 ≤ twistedCurvature (T.aC c) (T.bC c) (T.pX c e) z v := by
  by_cases hv : v = 0
  · subst hv
    simp [twistedCurvature, holDerivSq]
  · exact (T.curvature_pos c e (T.ρX c) (T.isChartDensity_ρX c) z hz.1 hz.2 v hv).le

/-! ### The reference chart-frame at a point -/

/-- The preferred chart at `x`. -/
def chartX (x : X) : ComplexChart n X := complexChartAt (n := n) x

theorem mem_ref {x : X} :
    x ∈ (chartX (n := n) x).val.source ∩ (atlasFrameAt T.L x).val.baseSet :=
  ⟨mem_complexChartAt_source x, mem_atlasFrameAt_baseSet T.L x⟩

namespace XFam

variable (F : T.XFam)

/-! ### The globalized identity and the pointwise inequality -/

/-- **The globalized twisted Morrey--Kohn--Hörmander identity on `X`.** -/
theorem sum_mkh :
    ∫ x, F.Φ T.FθX x ∂T.μ = (∫ x, F.Φ T.FTX x ∂T.μ) + ∫ x, F.Φ T.FLX x ∂T.μ := by
  rw [F.integral_Φ isGaugeFormX_theta, F.integral_Φ isGaugeFormX_tr,
    F.integral_Φ isGaugeFormX_levi, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD := T.isOpen_pieceDomain (F.c i) (F.e i)
  have hmkh := integral_chartTheta_mul_conj_local hD (contDiffOn_pTX (F.c i) (F.e i))
    (F.contDiffOn_tot (F.c i) (F.e i)) (F.spec i).1 (F.spec i).2.1 (F.tsupport_subset_pd i)
  have hout : ∀ z, z ∉ T.pieceDomain (F.c i) (F.e i) → F.h i =ᶠ[𝓝 z] 0 := fun z hz =>
    notMem_tsupport_iff_eventuallyEq.mp fun h' => hz (F.tsupport_subset_pd i h')
  have e1 : ∀ z, chartTheta (T.pTX (F.c i) (F.e i)) (F.tot (F.c i) (F.e i)) z *
      conj (chartTheta (T.pTX (F.c i) (F.e i)) (F.h i) z) * cweight (T.pTX (F.c i) (F.e i)) z =
      ((T.ρX (F.c i) z : ℝ) : ℂ) * F.pc T.FθX i z := by
    intro z
    by_cases hz : z ∈ T.pieceDomain (F.c i) (F.e i)
    · simp only [pc, FθX, cweight_pTX hz]; ring
    · simp [pc, FθX, chartTheta_eq_zero_of_eventuallyEq (hout z hz)]
  have e2 : ∀ z, trS (F.tot (F.c i) (F.e i)) (F.h i) z * cweight (T.pTX (F.c i) (F.e i)) z =
      ((T.ρX (F.c i) z : ℝ) : ℂ) * F.pc T.FTX i z := by
    intro z
    by_cases hz : z ∈ T.pieceDomain (F.c i) (F.e i)
    · simp only [pc, FTX, cweight_pTX hz]; ring
    · simp [pc, FTX, trS_eq_zero_of_right (hout z hz)]
  have e3 : ∀ z, leviS (T.pTX (F.c i) (F.e i)) z (F.tot (F.c i) (F.e i) z) (F.h i z) *
      cweight (T.pTX (F.c i) (F.e i)) z = ((T.ρX (F.c i) z : ℝ) : ℂ) * F.pc T.FLX i z := by
    intro z
    by_cases hz : z ∈ T.pieceDomain (F.c i) (F.e i)
    · simp only [pc, FLX, cweight_pTX hz]; ring
    · simp [pc, FLX, (hout z hz).self_of_nhds, leviS_zero_right]
  simp only [e1, e2, e3] at hmkh
  exact hmkh

theorem Φ_ref {G : T.GForm} (hG : T.IsGaugeFormX G) {x : X} (hx : x ∈ T.U) :
    F.Φ G x = G (chartX x) (atlasFrameAt T.L x) (F.tot (chartX x) (atlasFrameAt T.L x))
      (F.tot (chartX x) (atlasFrameAt T.L x)) ((chartX (n := n) x).val x) :=
  F.Φ_eq_diag hG hx mem_ref

/-- **The pointwise twisted inequality** (logarithmic twist and Young). -/
theorem curv_le (x : X) :
    (F.Φ T.FHX x).re ≤ (F.Φ T.FLX x).re + (F.Φ T.FAX x).re - (F.Φ T.FθX x).re := by
  by_cases hx : x ∈ T.U
  · set c := chartX (n := n) x
    set e := atlasFrameAt T.L x
    have hz : c.val x ∈ T.pieceDomain c e := mem_pd_of_chart hx mem_ref
    rw [F.Φ_ref isGaugeFormX_curv hx, F.Φ_ref isGaugeFormX_levi hx,
      F.Φ_ref isGaugeFormX_tstar hx, F.Φ_ref isGaugeFormX_theta hx,
      FHX_diag_re _ hz, FLX_diag_re _ hz, FAX_diag_re, FθX_diag_re]
    have hY := FunctionalTwistedDatumLocalYoungDraft.TwistedDatum.datum_twistedCurvature_le_shiftedLevi_and_adjoint
      T c e (T.isChartDensity_ρX c) (F.tot c e) hz
    have hY' : twistedCurvature (T.aC c) (T.bC c) (T.pX c e) (c.val x) (F.tot c e (c.val x)) ≤
        T.aC c (c.val x) * leviForm (T.pTX c e) (c.val x) (F.tot c e (c.val x)) +
          (T.aC c (c.val x) + T.bC c (c.val x)) *
            ‖chartTheta (T.pX c e) (F.tot c e) (c.val x)‖ ^ 2 -
          T.aC c (c.val x) * ‖chartTheta (T.pTX c e) (F.tot c e) (c.val x)‖ ^ 2 := hY
    have hw := wX_pos (T := T) hz.1
    nlinarith
  · simp [F.Φ_eq_zero isGaugeFormX_curv hx, F.Φ_eq_zero isGaugeFormX_levi hx,
      F.Φ_eq_zero isGaugeFormX_tstar hx, F.Φ_eq_zero isGaugeFormX_theta hx]

theorem curv_nonneg (x : X) : 0 ≤ (F.Φ T.FHX x).re := by
  by_cases hx : x ∈ T.U
  · have hz := mem_pd_of_chart (c := chartX x) (e := atlasFrameAt T.L x) hx mem_ref
    rw [F.Φ_ref isGaugeFormX_curv hx, FHX_diag_re _ hz]
    exact mul_nonneg (twistedCurvature_nonnegX hz _) (wX_pos hz.1).le
  · simp [F.Φ_eq_zero isGaugeFormX_curv hx]

theorem FAX_re_nonneg (x : X) : 0 ≤ (F.Φ T.FAX x).re := by
  by_cases hx : x ∈ T.U
  · have hz := mem_pd_of_chart (c := chartX x) (e := atlasFrameAt T.L x) hx mem_ref
    rw [F.Φ_ref isGaugeFormX_tstar hx, FAX_diag_re]
    have ha := aC_pos hz
    have hb := bC_pos hz
    exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (wX_pos hz.1).le
  · simp [F.Φ_eq_zero isGaugeFormX_tstar hx]

/-- **The integrated twisted inequality**: `∫ H(W) ≤ ‖T* τ‖² + Q(τ)`. -/
theorem integral_curv_le :
    ∫ x, (F.Φ T.FHX x).re ∂T.μ ≤
      (∫ x, (F.Φ T.FAX x).re ∂T.μ) - (∫ x, F.Φ T.FTX x ∂T.μ).re := by
  have iH : Integrable (fun x => (F.Φ T.FHX x).re) T.μ :=
    (F.integrable_Φ (G := T.FHX) isGaugeFormX_curv).re
  have iL' := F.integrable_Φ (G := T.FLX) isGaugeFormX_levi
  have iA : Integrable (fun x => (F.Φ T.FAX x).re) T.μ :=
    (F.integrable_Φ (G := T.FAX) isGaugeFormX_tstar).re
  have iθ' := F.integrable_Φ (G := T.FθX) isGaugeFormX_theta
  have iLr : Integrable (fun x => (F.Φ T.FLX x).re) T.μ := iL'.re
  have iθr : Integrable (fun x => (F.Φ T.FθX x).re) T.μ := iθ'.re
  have hmono : ∫ x, (F.Φ T.FHX x).re ∂T.μ ≤ ∫ x, ((F.Φ T.FLX x).re +
      (F.Φ T.FAX x).re - (F.Φ T.FθX x).re) ∂T.μ :=
    integral_mono iH ((iLr.add iA).sub iθr) F.curv_le
  rw [integral_sub (f := fun x => (F.Φ T.FLX x).re + (F.Φ T.FAX x).re)
    (iLr.add iA) iθr, integral_add iLr iA] at hmono
  have hmkh := congrArg Complex.re F.sum_mkh
  rw [Complex.add_re] at hmkh
  have e1 : (∫ x, F.Φ T.FθX x ∂T.μ).re = ∫ x, (F.Φ T.FθX x).re ∂T.μ := (integral_re iθ').symm
  have e2 : (∫ x, F.Φ T.FLX x ∂T.μ).re = ∫ x, (F.Φ T.FLX x).re ∂T.μ := (integral_re iL').symm
  linarith

/-! ### The data pairing -/

theorem data_sq_le (x : X) :
    ‖F.Φ T.FDX x‖ ^ 2 ≤
      T.U.indicator (fun x => T.D x * Real.exp (-T.φ x)) x * (F.Φ T.FHX x).re := by
  by_cases hx : x ∈ T.U
  · set c := chartX (n := n) x
    set e := atlasFrameAt T.L x
    have hxs := (mem_ref (T := T) (x := x)).1
    have hz : c.val x ∈ T.pieceDomain c e := mem_pd_of_chart hx mem_ref
    rw [F.Φ_ref isGaugeFormX_data hx, F.Φ_ref isGaugeFormX_curv hx, FHX_diag_re _ hz,
      indicator_of_mem hx]
    simp only [FDX]
    have hB := T.D_bound c e (T.ρX c) (T.isChartDensity_ρX c) (c.val x) hz.1 hz.2
      (F.tot c e (c.val x))
    rw [c.val.left_inv hxs] at hB
    have hB' : ‖dbarPairing (chartCoeff T.L c e T.G) (c.val x) (F.tot c e (c.val x))‖ ^ 2 *
        frameNormSq T.L e x ≤ T.D x * twistedCurvature (T.aC c) (T.bC c) (T.pX c e) (c.val x)
          (F.tot c e (c.val x)) := hB
    have hwX : T.wX c e (c.val x) = frameNormSq T.L e x * Real.exp (-T.φ x) := by
      simp only [wX, c.val.left_inv hxs]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (wX_pos hz.1).le, mul_pow, hwX]
    have hN := frameNormSq_pos e (mem_ref (T := T) (x := x)).2
    have hφ := Real.exp_pos (-T.φ x)
    have hK : 0 ≤ frameNormSq T.L e x * Real.exp (-T.φ x) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hB' hK
    nlinarith [this]
  · simp [F.Φ_eq_zero isGaugeFormX_data hx, F.Φ_eq_zero isGaugeFormX_curv hx]

/-- The data pairing of a family, computed with the chosen chart densities. -/
def data : ℂ := ∑ i ∈ F.s, T.localDataPairing (F.c i) (F.e i) (T.ρX (F.c i)) (F.h i)

theorem data_eq_integral : F.data = ∫ x, F.Φ T.FDX x ∂T.μ := by
  rw [F.integral_Φ isGaugeFormX_data, data]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [localDataPairing]
  congr 1
  funext z
  by_cases hz : z ∈ chartFrameDomain T.L (F.c i) (F.e i)
  · simp only [pc, FDX] at *
    rw [show localWeight T.L (F.c i) (F.e i) (T.ρX (F.c i)) T.φ = T.pX (F.c i) (F.e i) from rfl,
      cweight_pX hz]
    ring
  · have h0 : F.h i z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (F.tsupport_subset i h')
    simp [pc, FDX, h0, dbarPairing_zero]

/-! ### The `T*`-energy -/

theorem localTStar_eq_ref (i : F.ι) {x : X} (hx : x ∈ T.U) :
    T.localTStar (F.c i) (F.e i) (T.ρX (F.c i)) (F.h i) x =
      (((T.a x + T.b x : ℝ) : ℂ) * chartTheta (T.pX (chartX x) (atlasFrameAt T.L x))
        (transpX T.L (F.c i) (F.e i) (chartX x) (atlasFrameAt T.L x) (F.h i))
          ((chartX (n := n) x).val x)) • (atlasFrameAt T.L x).val.symm x 1 := by
  set c := chartX (n := n) x
  set e := atlasFrameAt T.L x
  have hxs := (mem_ref (T := T) (x := x))
  have hz : c.val x ∈ T.pieceDomain c e := mem_pd_of_chart hx hxs
  have hsymm : c.val.symm (c.val x) = x := c.val.left_inv hxs.1
  by_cases hxi : x ∈ (F.c i).val.source ∩ (F.e i).val.baseSet
  · have hz' : c.val.symm (c.val x) ∈ (F.c i).val.source ∩ (F.e i).val.baseSet := by
      rw [hsymm]; exact hxi
    have hθ := T.chartTheta_transport (T.isOpen_pieceDomain c e)
      (T.isOpen_pieceDomain (F.c i) (F.e i)) subset_rfl subset_rfl (F.contDiffOn_transp i c e)
      (F.spec i).1.contDiffOn hz hz' (chg_mem_pieceDomain hz hz')
      (isTransp_piece (F.spec i).2.1 (F.tsupport_subset i) hz.1 hz')
    rw [chg_chart hxs.1, hsymm] at hθ
    rw [T.localTStar_of_mem hxi, pieceTheta, (F.c i).val.left_inv hxi.1]
    have hθ' : chartTheta (localWeight T.L (F.c i) (F.e i) (T.ρX (F.c i)) T.φ) (F.h i)
        ((F.c i).val x) = frameTrans T.L e (F.e i) x *
          chartTheta (T.pX c e) (transpX T.L (F.c i) (F.e i) c e (F.h i)) (c.val x) := hθ
    rw [hθ', frame_eq_frameTrans_smul (F.e i) e ⟨hxi.2, hxs.2⟩, smul_smul]
    congr 1
    have h1 := frameTrans_mul_symm e (F.e i) ⟨hxs.2, hxi.2⟩
    linear_combination (((T.a x + T.b x : ℝ) : ℂ) *
      chartTheta (T.pX c e) (transpX T.L (F.c i) (F.e i) c e (F.h i)) (c.val x)) * h1
  · have hns : x ∉ pieceSupport (F.c i) (F.h i) := fun h' =>
      hxi (mem_of_mem_pieceSupport (F.tsupport_subset i) h')
    have hzero : transpX T.L (F.c i) (F.e i) c e (F.h i) =ᶠ[𝓝 (c.val x)] 0 :=
      transpX_eventuallyEq_zero (F.spec i).2.1 ((F.tsupport_subset i).trans fun _ hz => hz.1)
        hz.1.1 (by rw [hsymm]; exact hns)
    rw [TwistedDatum.localTStar, if_neg hxi, chartTheta_eq_zero_of_eventuallyEq hzero, mul_zero,
      zero_smul]

theorem norm_sq_sum_localTStar {x : X} (hx : x ∈ T.U) :
    ‖∑ i ∈ F.s, T.localTStar (F.c i) (F.e i) (T.ρX (F.c i)) (F.h i) x‖ ^ 2 * T.H1weight x =
      (F.Φ T.FAX x).re := by
  set c := chartX (n := n) x
  set e := atlasFrameAt T.L x
  have hxs : x ∈ c.val.source ∩ e.val.baseSet := mem_ref
  have hz : c.val x ∈ T.pieceDomain c e := mem_pd_of_chart hx hxs
  have hsymm : c.val.symm (c.val x) = x := c.val.left_inv hxs.1
  rw [Finset.sum_congr rfl fun i _ => F.localTStar_eq_ref i hx, ← Finset.sum_smul,
    ← Finset.mul_sum, ← chartTheta_finset_sum F.s fun i _ =>
      (contDiffAt_of_pd (F.contDiffOn_transp i c e) hz).differentiableAt (by simp)]
  change ‖(((T.a x + T.b x : ℝ) : ℂ) * chartTheta (T.pX c e) (F.tot c e) (c.val x)) •
    e.val.symm x 1‖ ^ 2 * T.H1weight x = _
  rw [F.Φ_eq_diag isGaugeFormX_tstar hx hxs, FAX_diag_re, norm_smul, mul_pow, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (T.ab_pos hx).le]
  have hab := (T.ab_pos hx).ne'
  have hw : T.wX c e (c.val x) = frameNormSq T.L e x * Real.exp (-T.φ x) := by
    simp only [wX, hsymm]
  have ha' : T.aC c (c.val x) = T.a x := by simp only [aC, hsymm]
  have hb' : T.bC c (c.val x) = T.b x := by simp only [bC, hsymm]
  rw [hw, ha', hb']
  simp only [H1weight, frameNormSq]
  field_simp

/-- **`‖T* τ‖²` as an integral over `X`.** -/
theorem lintegral_tstar_eq :
    ∫⁻ x in T.U, ENNReal.ofReal (‖∑ i ∈ F.s, T.localTStar (F.c i) (F.e i) (T.ρX (F.c i))
      (F.h i) x‖ ^ 2 * T.H1weight x) ∂T.μ = ENNReal.ofReal (∫ x, (F.Φ T.FAX x).re ∂T.μ) := by
  have iA : Integrable (fun x => (F.Φ T.FAX x).re) T.μ :=
    (F.integrable_Φ (G := T.FAX) isGaugeFormX_tstar).re
  rw [ofReal_integral_eq_lintegral_ofReal iA (Eventually.of_forall F.FAX_re_nonneg),
    ← lintegral_indicator T.isOpen_U.measurableSet]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ T.U
  · rw [indicator_of_mem hx, F.norm_sq_sum_localTStar hx]
  · rw [indicator_of_notMem hx, F.Φ_eq_zero isGaugeFormX_tstar hx]
    simp

/-- The `T*`-energy of the family. -/
def energy : ℝ := ∫ x, (F.Φ T.FAX x).re ∂T.μ

/-- The `∂̄`-defect `Q(τ) = -Re ∫ tr(A_W Ā_W) a |e|² e^{-φ} dμ` of the family. -/
def defect : ℝ := -(∫ x, F.Φ T.FTX x ∂T.μ).re

theorem energy_nonneg : 0 ≤ F.energy := integral_nonneg F.FAX_re_nonneg

/-- **The twisted a priori estimate on a manifold** (`claude-tl2-man:apriori`). -/
theorem apriori
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ‖F.data‖ ^ 2 ≤ (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
      (F.energy + F.defect) := by
  set M := (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal with hM
  set k : X → ℝ := fun x => ‖F.Φ T.FDX x‖ with hk
  set g : X → ℝ := fun x => (F.Φ T.FHX x).re with hg
  set f : X → ℝ := fun x => k x ^ 2 / g x with hf
  have ik : Integrable k T.μ := (F.integrable_Φ (G := T.FDX) isGaugeFormX_data).norm
  have ig : Integrable g T.μ := (F.integrable_Φ (G := T.FHX) isGaugeFormX_curv).re
  have hg0 : ∀ x, 0 ≤ g x := F.curv_nonneg
  have hk0 : ∀ x, 0 ≤ k x := fun x => norm_nonneg _
  have hf0 : ∀ x, 0 ≤ f x := fun x => div_nonneg (sq_nonneg _) (hg0 x)
  have hkfg : ∀ x, k x ^ 2 ≤ f x * g x := by
    intro x
    by_cases hgx : g x = 0
    · have := F.data_sq_le x
      change k x ^ 2 ≤ _ * g x at this
      rw [hgx, mul_zero] at this
      rw [hgx, mul_zero]
      exact this
    · rw [hf, div_mul_cancel₀ _ hgx]
  have hfm : Measurable f := by
    have hkc : Continuous k := (F.continuous_Φ isGaugeFormX_data).norm
    have hgc : Continuous g := Complex.continuous_re.comp (F.continuous_Φ isGaugeFormX_curv)
    exact (hkc.measurable.pow_const 2).div hgc.measurable
  have hpt : ∀ x, ENNReal.ofReal (f x) ≤
      T.U.indicator (fun x => ENNReal.ofReal (T.D x * Real.exp (-T.φ x))) x := by
    intro x
    rcases (hf0 x).eq_or_lt with h0 | hpos
    · rw [← h0, ENNReal.ofReal_zero]; exact bot_le
    · have hgx : 0 < g x := by
        rcases (hg0 x).eq_or_lt with h' | h'
        · exfalso; simp [hf, ← h'] at hpos
        · exact h'
      have hle : f x ≤ T.U.indicator (fun x => T.D x * Real.exp (-T.φ x)) x := by
        rw [hf, div_le_iff₀ hgx]
        exact F.data_sq_le x
      by_cases hx : x ∈ T.U
      · rw [indicator_of_mem hx] at hle ⊢
        exact ENNReal.ofReal_le_ofReal hle
      · rw [indicator_of_notMem hx] at hle
        linarith
  have hlint : ∫⁻ x, ENNReal.ofReal (f x) ∂T.μ ≤
      ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ := by
    rw [← lintegral_indicator T.isOpen_U.measurableSet]
    exact lintegral_mono hpt
  have ifn : Integrable f T.μ :=
    ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).mpr
      (hlint.trans_lt hfin)⟩
  have hfM : ∫ x, f x ∂T.μ ≤ M := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_mono hfin.ne hlint
  have hCS := sq_integral_le_of_sq_le_mul_gen ifn ig ik hf0 hg0 hk0 hkfg
  have hcurv := F.integral_curv_le
  have hgI : 0 ≤ ∫ x, g x ∂T.μ := integral_nonneg hg0
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hnorm : ‖F.data‖ ≤ ∫ x, k x ∂T.μ := by
    rw [F.data_eq_integral]
    exact norm_integral_le_integral_norm _
  calc ‖F.data‖ ^ 2 ≤ (∫ x, k x ∂T.μ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ x, f x ∂T.μ) * ∫ x, g x ∂T.μ := hCS
    _ ≤ M * ∫ x, g x ∂T.μ := mul_le_mul_of_nonneg_right hfM hgI
    _ ≤ M * (F.energy + F.defect) := by
      refine mul_le_mul_of_nonneg_left ?_ hM0
      simp only [energy, defect]
      linarith

end XFam

/-! ### Graph density and the reduction -/

/-- **Graph density of test families on `X`** (FPT `lem:cutoff-mollifier-density`, read on finite
families of local pieces): every family can be approximated, in the data pairing and in the
`T*`-energy, by families with arbitrarily small `∂̄`-defect. -/
def GraphDensityX (T : TwistedDatum n X) : Prop :=
  ∀ F : T.XFam, ∀ ε : ℝ, 0 < ε → ∃ F' : T.XFam,
    ‖F'.data - F.data‖ ≤ ε ∧ F'.energy ≤ F.energy + ε ∧ F'.defect ≤ ε

/-- The functional bound for a family, from graph density. -/
theorem XFam.norm_sq_data_le (hdens : T.GraphDensityX) (F : T.XFam)
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤) :
    ‖F.data‖ ^ 2 ≤ (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
      F.energy := by
  set M := (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hE := F.energy_nonneg
  have key : ∀ ε : ℝ, 0 < ε → ‖F.data‖ ≤ Real.sqrt (M * (F.energy + 2 * ε)) + ε := by
    intro ε hε
    obtain ⟨F', h1, h2, h3⟩ := hdens F ε hε
    have ha := F'.apriori hfin
    have hb : ‖F'.data‖ ^ 2 ≤ M * (F.energy + 2 * ε) :=
      ha.trans (mul_le_mul_of_nonneg_left (by linarith) hM)
    have hc : ‖F'.data‖ ≤ Real.sqrt (M * (F.energy + 2 * ε)) := Real.le_sqrt_of_sq_le hb
    have hd : ‖F.data‖ ≤ ‖F'.data‖ + ε := by
      have := norm_sub_norm_le F.data F'.data
      rw [norm_sub_rev] at this
      linarith
    linarith
  have hlim : Tendsto (fun ε : ℝ => Real.sqrt (M * (F.energy + 2 * ε)) + ε) (𝓝[>] 0)
      (𝓝 (Real.sqrt (M * F.energy))) := by
    have hc : Continuous fun ε : ℝ => Real.sqrt (M * (F.energy + 2 * ε)) + ε := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖F.data‖ ≤ Real.sqrt (M * F.energy) :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  calc ‖F.data‖ ^ 2 ≤ Real.sqrt (M * F.energy) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = M * F.energy := Real.sq_sqrt (mul_nonneg hM hE)

theorem localWeight_eventuallyEq {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {z : ComplexModel n}
    (hz : z ∈ c.val.target) :
    (fun y => (localWeight T.L c e ρ T.φ y : ℂ)) =ᶠ[𝓝 z] fun y => (T.pX c e y : ℂ) := by
  filter_upwards [c.val.open_target.mem_nhds hz] with y hy
  simp only [pX, localWeight, isChartDensity_eqOn hρ (T.isChartDensity_ρX c) hy]

theorem localTStar_density_eq {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) (h : ComplexModel n → ComplexModel n)
    (x : X) : T.localTStar c e ρ h x = T.localTStar c e (T.ρX c) h x := by
  classical
  by_cases hx : x ∈ c.val.source ∩ e.val.baseSet
  · simp only [localTStar, if_pos hx]
    rw [chartTheta_congr_weight (localWeight_eventuallyEq hρ (c.val.map_source hx.1))
      (EventuallyEq.refl _ h)]
    rfl
  · simp only [localTStar, if_neg hx]

theorem localDataPairing_density_eq {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U c e h) :
    T.localDataPairing c e ρ h = T.localDataPairing c e (T.ρX c) h := by
  simp only [localDataPairing]
  congr 1
  funext z
  by_cases hz : z ∈ c.val.target
  · rw [cweight_congr (p' := T.pX c e) ?_]
    · rfl
    · simp only [pX, localWeight, isChartDensity_eqOn hρ (T.isChartDensity_ρX c) hz]
  · have h0 : h z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hh.2.2 h').1.1
    simp [h0, dbarPairing_zero]

/-- **The functional bound on `X` from graph density** (`claude-tl2-man:reduction`). -/
theorem functionalBound_of_graphDensityX (hdens : T.GraphDensityX)
    (hfin : ∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ < ⊤)
    (ι : Type) (s : Finset ι) (c : ι → ComplexChart n X)
    (e : ι → AtlasFrame T.L) (ρ : ι → ComplexModel n → ℝ) (h : ι → ComplexModel n → ComplexModel n)
    (hρ : ∀ i ∈ s, IsChartDensity T.μ (c i) (ρ i))
    (hh : ∀ i ∈ s, IsLocalTestField T.L T.U (c i) (e i) (h i)) :
    ENNReal.ofReal (‖∑ i ∈ s, T.localDataPairing (c i) (e i) (ρ i) (h i)‖ ^ 2) ≤
      (∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ) *
        ∫⁻ x in T.U, ENNReal.ofReal
          (‖∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x‖ ^ 2 * T.H1weight x) ∂T.μ := by
  classical
  let F : T.XFam :=
    { ι := s, s := Finset.univ, c := fun i => c i, e := fun i => e i, h := fun i => h i,
      spec := fun i => hh i i.2 }
  have hdata : ∑ i ∈ s, T.localDataPairing (c i) (e i) (ρ i) (h i) = F.data := by
    rw [XFam.data, ← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => localDataPairing_density_eq (hρ i i.2) (hh i i.2)
  have htstar : ∀ x, ∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x =
      ∑ i ∈ F.s, T.localTStar (F.c i) (F.e i) (T.ρX (F.c i)) (F.h i) x := by
    intro x
    rw [← Finset.sum_coe_sort s]
    exact Finset.sum_congr rfl fun i _ => localTStar_density_eq (hρ i i.2) (h i) x
  have hE : ∫⁻ x in T.U, ENNReal.ofReal
      (‖∑ i ∈ s, T.localTStar (c i) (e i) (ρ i) (h i) x‖ ^ 2 * T.H1weight x) ∂T.μ =
      ENNReal.ofReal F.energy := by
    simp_rw [htstar]
    exact F.lintegral_tstar_eq
  rw [hdata, hE]
  have hb := F.norm_sq_data_le hdens hfin
  calc ENNReal.ofReal (‖F.data‖ ^ 2)
      ≤ ENNReal.ofReal ((∫⁻ x in T.U, ENNReal.ofReal (T.D x * Real.exp (-T.φ x)) ∂T.μ).toReal *
          F.energy) := ENNReal.ofReal_le_ofReal hb
    _ = _ := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]

end TwistedDatum

variable (n X)

/-- `TwistedFunctionalBoundStatement n X` on a complex manifold, assuming graph density of test
families for every twisted datum on `X`. -/
theorem twistedFunctionalBoundStatement_of_graphDensityX
    (hdens : ∀ T : TwistedDatum n X, T.GraphDensityX) :
    TwistedFunctionalBoundStatement n X :=
  fun T hfin ι s c e ρ h hρ hh =>
    TwistedDatum.functionalBound_of_graphDensityX (hdens T) hfin ι s c e ρ h hρ hh

/-- **The main twisted estimate on a complex manifold from graph density**
(`claude-tl2-man:reduction`). -/
theorem twistedL2CorrectionStatement_of_graphDensityX
    (hdens : ∀ T : TwistedDatum n X, T.GraphDensityX) : TwistedL2CorrectionStatement n X :=
  twistedL2CorrectionStatement_of_functional
    (twistedFunctionalBoundStatement_of_graphDensityX n X hdens)

end SGPT.Trace.TwistedL2
