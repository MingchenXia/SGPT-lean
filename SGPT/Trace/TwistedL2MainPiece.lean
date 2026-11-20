import SGPT.Trace.TwistedL2MainChart
import SGPT.Foundations.Analysis.Pending.LeviWirtinger

/-!
# Local pieces of test forms and the space `H₁`

For a twisted datum `T` and a local piece `(c, e, ρ, h)`: the local weight is smooth on the piece
domain `c(U ∩ c.source ∩ e.baseSet)`, `ϑ h` is continuous with support in `tsupport h`, and the
section `T* = (a+b) ϑ (h ⊗ e)` has an `L²(μ|_U)` coordinate (`memLp_H1coord_localTStar`).
`H₁ = L²(U, L; e^{-φ}/(a+b) dμ)` is realized as `L²(μ|_U)` through
`H1coord s = (e^{-φ}/(a+b))^{1/2} ⟪ε, s⟫` (`ε` the measurable unit frame).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold ComplexConjugate InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1 SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

/-! ### `ϑ` in a chart -/

theorem chartTheta_eq_zero {p : ComplexModel n → ℝ} {h : ComplexModel n → ComplexModel n}
    {z : ComplexModel n} (hz : z ∉ tsupport h) : chartTheta p h z = 0 := by
  have h0 : h =ᶠ[𝓝 z] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  have hj : ∀ j : Fin n, (fun y => h y j) =ᶠ[𝓝 z] fun _ => 0 := fun j =>
    h0.mono fun y hy => by simp [hy]
  simp only [chartTheta, deltaDir]
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hz0 : h z = 0 := h0.self_of_nhds
  rw [dDir_eq_zero_of_eventuallyEq_zero (hj j), hz0]
  simp

theorem tsupport_chartTheta_subset (p : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n) :
    tsupport (chartTheta p h) ⊆ tsupport h :=
  closure_minimal (fun _ hz => by_contra fun hz' => hz (chartTheta_eq_zero hz'))
    (isClosed_tsupport h)

theorem contDiff_coord {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h) (j : Fin n) :
    ContDiff ℝ ∞ (fun y => h y j) :=
  ((EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hh

theorem tsupport_coord_subset (h : ComplexModel n → ComplexModel n) (j : Fin n) :
    tsupport (fun y => h y j) ⊆ tsupport h :=
  tsupport_comp_subset (g := fun v : ComplexModel n => v j) (by simp) h

theorem continuous_chartTheta {p : ComplexModel n → ℝ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    (hp : ContDiffOn ℝ ∞ p D) {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h)
    (hts : tsupport h ⊆ D) : Continuous (chartTheta p h) := by
  have hpc : ContDiffOn ℝ ∞ (fun y => (p y : ℂ)) D := Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  have hdp : ∀ v : ComplexModel n, ContinuousOn (dDir v fun y => (p y : ℂ)) D := by
    intro v
    have hc : ContinuousOn (fderiv ℝ fun y => (p y : ℂ)) D :=
      hpc.continuousOn_fderiv_of_isOpen hD (by simp)
    have h1 : ContinuousOn (fun x => fderiv ℝ (fun y => (p y : ℂ)) x v) D :=
      hc.clm_apply continuousOn_const
    have h2 : ContinuousOn (fun x => fderiv ℝ (fun y => (p y : ℂ)) x (Complex.I • v)) D :=
      hc.clm_apply continuousOn_const
    exact ((h1.sub (continuousOn_const.mul h2)).div_const 2)
  have hterm : ∀ j : Fin n, Continuous (deltaDir (coordVec j) p (fun y => h y j)) := by
    intro j
    have h1 : Continuous (dDir (coordVec j) (fun y => h y j)) :=
      (contDiff_dDir (k := 0) ((contDiff_coord hh j).of_le (by simp))).continuous
    have h2 : Continuous (fun y => dDir (coordVec j) (fun y => (p y : ℂ)) y * h y j) :=
      continuous_mul_of_tsupport_subset hD (hdp _) (contDiff_coord hh j).continuous
        ((tsupport_coord_subset h j).trans hts)
    exact h1.sub h2
  unfold chartTheta
  exact (continuous_finsetSum _ fun j _ => hterm j).neg

theorem dDir_const_mul_fun {f : ComplexModel n → ℂ} {v x : ComplexModel n}
    (hf : DifferentiableAt ℝ f x) (κ : ℂ) :
    dDir v (fun y => κ * f y) x = κ * dDir v f x := by
  have h : fderiv ℝ (fun y => κ * f y) x = κ • fderiv ℝ f x := fderiv_const_mul hf κ
  simp only [dDir, h, smul_apply, smul_eq_mul]
  ring

theorem chartTheta_smul (p : ComplexModel n → ℝ) {h : ComplexModel n → ComplexModel n}
    (hh : ContDiff ℝ ∞ h) (κ : ℂ) (z : ComplexModel n) :
    chartTheta p (κ • h) z = κ * chartTheta p h z := by
  simp only [chartTheta, deltaDir, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dDir_const_mul_fun (((contDiff_coord hh j).differentiable (by simp)) z)]
  ring

theorem dbarPairing_smul (f : ComplexModel n → ℂ) (z v : ComplexModel n) (κ : ℂ) :
    dbarPairing f z (κ • v) = conj κ * dbarPairing f z v := by
  simp only [dbarPairing, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

variable {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace TwistedDatum

variable (T : TwistedDatum n X)

/-! ### The piece domain and the local weight -/

/-- The domain `c(U ∩ c.source ∩ e.baseSet)` of the local pieces in `(c, e)`. -/
def pieceDomain (c : ComplexChart n X) (e : AtlasFrame T.L) : Set (ComplexModel n) :=
  chartFrameDomain T.L c e ∩ c.val.symm ⁻¹' T.U

theorem isOpen_pieceDomain (c : ComplexChart n X) (e : AtlasFrame T.L) :
    IsOpen (T.pieceDomain c e) :=
  isOpen_chartFrameDomain_inter T.L c e T.isOpen_U

theorem pieceDomain_subset_target (c : ComplexChart n X) (e : AtlasFrame T.L) :
    T.pieceDomain c e ⊆ c.val.target := fun _ hz => hz.1.1

theorem pieceDomain_subset_chartSmooth (c : ComplexChart n X) (e : AtlasFrame T.L) :
    T.pieceDomain c e ⊆ c.val.target ∩ c.val.symm ⁻¹' T.U := fun _ hz => ⟨hz.1.1, hz.2⟩

theorem contDiffOn_localWeight {c : ComplexChart n X} (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) :
    ContDiffOn ℝ ∞ (localWeight T.L c e ρ T.φ) (T.pieceDomain c e) := by
  have h1 : ContDiffOn ℝ ∞ (fun z => frameNormSq T.L e (c.val.symm z)) (T.pieceDomain c e) :=
    (T.metric_smooth c e).mono fun z hz => hz.1
  have h1' : ContDiffOn ℝ ∞ (fun z => Real.log (frameNormSq T.L e (c.val.symm z)))
      (T.pieceDomain c e) :=
    h1.log fun z hz => (frameNormSq_pos e hz.1.2).ne'
  have h2 : ContDiffOn ℝ ∞ (fun z => T.φ (c.val.symm z)) (T.pieceDomain c e) :=
    (T.φ_smooth c).mono (T.pieceDomain_subset_chartSmooth c e)
  have h3 : ContDiffOn ℝ ∞ (fun z => Real.log (ρ z)) (T.pieceDomain c e) :=
    (hρ.1.mono (T.pieceDomain_subset_target c e)).log fun z hz =>
      (hρ.2.1 z (T.pieceDomain_subset_target c e hz)).ne'
  exact (h1'.neg.add h2).sub h3

theorem exp_neg_localWeight {c : ComplexChart n X} (e : AtlasFrame T.L)
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain T.L c e) :
    Real.exp (-localWeight T.L c e ρ T.φ z) =
      frameNormSq T.L e (c.val.symm z) * Real.exp (-T.φ (c.val.symm z)) * ρ z := by
  have hA := frameNormSq_pos e hz.2
  have hρz := hρ.2.1 z hz.1
  simp only [localWeight]
  rw [show -(-Real.log (frameNormSq T.L e (c.val.symm z)) + T.φ (c.val.symm z) - Real.log (ρ z)) =
    Real.log (frameNormSq T.L e (c.val.symm z)) + -T.φ (c.val.symm z) + Real.log (ρ z) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log hA, Real.exp_log hρz]

/-- The continuity of `a + b` read in a chart. -/
theorem continuousOn_ab (c : ComplexChart n X) :
    ContinuousOn (fun z => T.a (c.val.symm z) + T.b (c.val.symm z))
      (c.val.target ∩ c.val.symm ⁻¹' T.U) :=
  (T.a_smooth c).continuousOn.add (T.b_smooth c).continuousOn

theorem ab_pos {x : X} (hx : x ∈ T.U) : 0 < T.a x + T.b x := by
  obtain ⟨m, M, hm, hb⟩ := T.bounds
  have := hb x hx
  linarith [this.1, this.2.2.1]

theorem H1weight_pos {x : X} (hx : x ∈ T.U) : 0 < T.H1weight x :=
  div_pos (Real.exp_pos _) (T.ab_pos hx)

theorem continuousOn_H1weight : ContinuousOn T.H1weight T.U := by
  have hφ := mainContinuousOn_of_chartSmoothOn T.isOpen_U T.φ_smooth
  have ha := mainContinuousOn_of_chartSmoothOn T.isOpen_U T.a_smooth
  have hb := mainContinuousOn_of_chartSmoothOn T.isOpen_U T.b_smooth
  exact (Real.continuous_exp.comp_continuousOn hφ.neg).div (ha.add hb)
    fun x hx => (T.ab_pos hx).ne'

/-! ### `T*` of a local piece -/

/-- `(a+b) ϑ h` in the chart: the coefficient of `T*` of the local piece. -/
def pieceTheta (c : ComplexChart n X) (e : AtlasFrame T.L) (ρ : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) (z : ComplexModel n) : ℂ :=
  ((T.a (c.val.symm z) + T.b (c.val.symm z) : ℝ) : ℂ) *
    chartTheta (localWeight T.L c e ρ T.φ) h z

theorem continuous_pieceTheta {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U c e h) : Continuous (T.pieceTheta c e ρ h) := by
  have hθ : Continuous (chartTheta (localWeight T.L c e ρ T.φ) h) :=
    continuous_chartTheta (T.isOpen_pieceDomain c e) (T.contDiffOn_localWeight e hρ) hh.1 hh.2.2
  have hab : ContinuousOn (fun z => ((T.a (c.val.symm z) + T.b (c.val.symm z) : ℝ) : ℂ))
      (T.pieceDomain c e) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((T.continuousOn_ab c).mono (T.pieceDomain_subset_chartSmooth c e))
  exact continuous_mul_of_tsupport_subset (T.isOpen_pieceDomain c e) hab hθ
    ((tsupport_chartTheta_subset _ h).trans hh.2.2)

theorem pieceTheta_eq_zero {c : ComplexChart n X} {e : AtlasFrame T.L} {ρ : ComplexModel n → ℝ}
    {h : ComplexModel n → ComplexModel n} {z : ComplexModel n} (hz : z ∉ tsupport h) :
    T.pieceTheta c e ρ h z = 0 := by
  rw [pieceTheta, chartTheta_eq_zero hz, mul_zero]

theorem localTStar_of_mem {c : ComplexChart n X} {e : AtlasFrame T.L} {ρ : ComplexModel n → ℝ}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∈ c.val.source ∩ e.val.baseSet) :
    T.localTStar c e ρ h x = T.pieceTheta c e ρ h (c.val x) • e.val.symm x 1 := by
  rw [localTStar, if_pos hx, pieceTheta, c.val.left_inv hx.1]

/-- The support set `c⁻¹(tsupport h)` of a local piece. -/
def pieceSupport (c : ComplexChart n X) (h : ComplexModel n → ComplexModel n) : Set X :=
  c.val.source ∩ c.val ⁻¹' tsupport h

theorem localTStar_eq_zero {c : ComplexChart n X} {e : AtlasFrame T.L} {ρ : ComplexModel n → ℝ}
    {h : ComplexModel n → ComplexModel n} {x : X} (hx : x ∉ pieceSupport c h) :
    T.localTStar c e ρ h x = 0 := by
  by_cases hxs : x ∈ c.val.source ∩ e.val.baseSet
  · rw [T.localTStar_of_mem hxs, T.pieceTheta_eq_zero (fun hz => hx ⟨hxs.1, hz⟩), zero_smul]
  · rw [localTStar, if_neg hxs]

theorem isCompact_pieceSupport {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hh : IsLocalTestField T.L T.U c e h) :
    IsCompact (pieceSupport c h) := by
  have ht : tsupport h ⊆ c.val.target := hh.2.2.trans fun z hz => hz.1.1
  rw [pieceSupport, ← c.val.symm_image_eq_source_inter_preimage ht]
  exact hh.2.1.isCompact.image_of_continuousOn (c.val.continuousOn_symm.mono ht)

theorem pieceSupport_subset {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hh : IsLocalTestField T.L T.U c e h) :
    pieceSupport c h ⊆ T.U ∩ (c.val.source ∩ e.val.baseSet) := by
  intro x hx
  obtain ⟨⟨-, hb⟩, hU⟩ := hh.2.2 hx.2
  simp only [mem_preimage, c.val.left_inv hx.1] at hb hU
  exact ⟨hU, hx.1, hb⟩

theorem localTStar_smul {c : ComplexChart n X} {e : AtlasFrame T.L} {ρ : ComplexModel n → ℝ}
    {h : ComplexModel n → ComplexModel n} (hh : ContDiff ℝ ∞ h) (κ : ℂ) (x : X) :
    T.localTStar c e ρ (κ • h) x = κ • T.localTStar c e ρ h x := by
  by_cases hx : x ∈ c.val.source ∩ e.val.baseSet
  · simp only [localTStar, if_pos hx, chartTheta_smul _ hh, smul_smul]
    ring_nf
  · simp only [localTStar, if_neg hx, smul_zero]

theorem localDataPairing_smul (c : ComplexChart n X) (e : AtlasFrame T.L)
    (ρ : ComplexModel n → ℝ) (h : ComplexModel n → ComplexModel n) (κ : ℂ) :
    T.localDataPairing c e ρ (κ • h) = conj κ * T.localDataPairing c e ρ h := by
  simp only [localDataPairing, Pi.smul_apply, dbarPairing_smul, mul_assoc]
  exact integral_const_mul _ _

theorem isLocalTestField_smul {c : ComplexChart n X} {e : AtlasFrame T.L}
    {h : ComplexModel n → ComplexModel n} (hh : IsLocalTestField T.L T.U c e h) (κ : ℂ) :
    IsLocalTestField T.L T.U c e (κ • h) :=
  have hs : Function.support (κ • h) ⊆ Function.support h := Function.support_const_smul_subset κ h
  ⟨hh.1.const_smul κ, hh.2.1.mono hs, (closure_mono hs).trans hh.2.2⟩

/-! ### The space `H₁` -/

/-- `(e^{-φ}/(a+b))^{1/2}` on `U`, zero off `U`. -/
def sqrtW (x : X) : ℝ := T.U.indicator (fun x => Real.sqrt (T.H1weight x)) x

/-- The coordinate of a section in `H₁ = L²(μ|_U)`: `(e^{-φ}/(a+b))^{1/2} ⟪ε, s⟫`. -/
def H1coord (s : (x : X) → T.L.Fiber x) (x : X) : ℂ :=
  (T.sqrtW x : ℂ) * ⟪unitFrame T.L x, s x⟫_ℂ

open Classical in
theorem measurable_sqrtW : Measurable T.sqrtW := by
  have hc : ContinuousOn (fun x => Real.sqrt (T.H1weight x)) T.U :=
    Real.continuous_sqrt.comp_continuousOn T.continuousOn_H1weight
  have := hc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
    T.isOpen_U.measurableSet
  convert this using 1
  ext x
  simp only [sqrtW, Set.indicator, Set.piecewise]

theorem sqrtW_sq {x : X} (hx : x ∈ T.U) : T.sqrtW x ^ 2 = T.H1weight x := by
  rw [sqrtW, Set.indicator_of_mem hx, Real.sq_sqrt (T.H1weight_pos hx).le]

theorem sqrtW_pos {x : X} (hx : x ∈ T.U) : 0 < T.sqrtW x := by
  rw [sqrtW, Set.indicator_of_mem hx]
  exact Real.sqrt_pos.2 (T.H1weight_pos hx)

theorem H1coord_add (s s' : (x : X) → T.L.Fiber x) (x : X) :
    T.H1coord (s + s') x = T.H1coord s x + T.H1coord s' x := by
  simp only [H1coord, Pi.add_apply, inner_add_right, mul_add]

theorem H1coord_sum {ι : Type} (u : Finset ι) (s : ι → (x : X) → T.L.Fiber x) (x : X) :
    T.H1coord (fun y => ∑ i ∈ u, s i y) x = ∑ i ∈ u, T.H1coord (s i) x := by
  simp only [H1coord, inner_sum, Finset.mul_sum]

theorem norm_H1coord_sq (s : (x : X) → T.L.Fiber x) {x : X} (hx : x ∈ T.U) :
    ‖T.H1coord s x‖ ^ 2 = ‖s x‖ ^ 2 * T.H1weight x := by
  rw [H1coord, norm_mul, mul_pow, norm_inner_unitFrame, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, T.sqrtW_sq hx, mul_comm]

theorem H1coord_localTStar (c : ComplexChart n X) (e : AtlasFrame T.L) (ρ : ComplexModel n → ℝ)
    (h : ComplexModel n → ComplexModel n) (x : X) :
    T.H1coord (T.localTStar c e ρ h) x = (T.sqrtW x : ℂ) *
      (c.val.source ∩ e.val.baseSet).indicator
        (fun x => T.pieceTheta c e ρ h (c.val x) * (frameNormSq T.L e x : ℂ)) x *
      conj (e.val.baseSet.indicator (unitCoeff e) x) := by
  by_cases hx : x ∈ c.val.source ∩ e.val.baseSet
  · rw [H1coord, T.localTStar_of_mem hx, inner_unitFrame_frame_smul e hx.2,
      Set.indicator_of_mem hx, Set.indicator_of_mem hx.2]
    ring
  · rw [H1coord, localTStar, if_neg hx, inner_zero_right, Set.indicator_of_notMem hx]
    ring

open Classical in
theorem measurable_H1coord_localTStar {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U c e h) :
    Measurable (T.H1coord (T.localTStar c e ρ h)) := by
  have hO : IsOpen (c.val.source ∩ e.val.baseSet) := c.val.open_source.inter e.val.open_baseSet
  have h1 : ContinuousOn (fun x => T.pieceTheta c e ρ h (c.val x) * (frameNormSq T.L e x : ℂ))
      (c.val.source ∩ e.val.baseSet) := by
    refine ((T.continuous_pieceTheta hρ hh).comp_continuousOn
      (c.val.continuousOn.mono inter_subset_left)).mul ?_
    have hn : ContinuousOn (fun x => ‖e.val.symm x 1‖) e.val.baseSet :=
      frameNorm_continuousOn T.L.Fiber e.val
    exact Complex.continuous_ofReal.comp_continuousOn ((hn.pow 2).mono inter_subset_right)
  have hm1 : Measurable ((c.val.source ∩ e.val.baseSet).indicator
      (fun x => T.pieceTheta c e ρ h (c.val x) * (frameNormSq T.L e x : ℂ))) := by
    have := h1.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const hO.measurableSet
    convert this using 1
    ext x
    simp only [Set.indicator, Set.piecewise]
  have hm := ((Complex.measurable_ofReal.comp T.measurable_sqrtW).mul hm1).mul
    (Complex.continuous_conj.measurable.comp (measurable_indicator_unitCoeff e))
  convert hm using 1
  ext x
  rw [T.H1coord_localTStar]
  rfl

theorem memLp_H1coord_localTStar {c : ComplexChart n X} {e : AtlasFrame T.L}
    {ρ : ComplexModel n → ℝ} (hρ : IsChartDensity T.μ c ρ) {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U c e h) :
    MemLp (T.H1coord (T.localTStar c e ρ h)) 2 (T.μ.restrict T.U) := by
  set F := T.H1coord (T.localTStar c e ρ h) with hFdef
  set K := pieceSupport c h with hKdef
  have hK : IsCompact K := T.isCompact_pieceSupport hh
  have hKU := T.pieceSupport_subset hh
  have hF0 : ∀ x ∉ K, F x = 0 := by
    intro x hx
    rw [hFdef, H1coord, T.localTStar_eq_zero hx, inner_zero_right, mul_zero]
  have hFK : F = K.indicator F := by
    ext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hF0 x hx]
  -- a bound on `K`
  have hcont : ContinuousOn (fun x => T.sqrtW x * (‖T.pieceTheta c e ρ h (c.val x)‖ *
      ‖e.val.symm x 1‖)) K := by
    have hs : ContinuousOn T.sqrtW T.U := by
      have hc : ContinuousOn (fun x => Real.sqrt (T.H1weight x)) T.U :=
        Real.continuous_sqrt.comp_continuousOn T.continuousOn_H1weight
      exact hc.congr fun x hx => by simp [sqrtW, Set.indicator_of_mem hx]
    have hθ : ContinuousOn (fun x => ‖T.pieceTheta c e ρ h (c.val x)‖) K :=
      ((T.continuous_pieceTheta hρ hh).norm.comp_continuousOn
        (c.val.continuousOn.mono fun x hx => (hKU hx).2.1))
    have hn : ContinuousOn (fun x => ‖e.val.symm x 1‖) K :=
      (frameNorm_continuousOn T.L.Fiber e.val).mono fun x hx => (hKU hx).2.2
    exact (hs.mono fun x hx => (hKU hx).1).mul (hθ.mul hn)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hbound : ∀ x ∈ K, ‖F x‖ ≤ C := by
    intro x hx
    have hxs := (hKU hx).2
    refine le_trans (le_of_eq ?_) ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC x hx))
    rw [hFdef, H1coord, T.localTStar_of_mem hxs, norm_mul, norm_inner_unitFrame, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (T.sqrtW_pos (hKU hx).1)]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  rw [hFK, memLp_indicator_iff_restrict hKm]
  have hfin : (T.μ.restrict T.U).restrict K univ < ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.restrict_apply hKm]
    obtain ⟨hρc, hρpos, hmap⟩ := hρ
    exact (measure_mono inter_subset_left).trans_lt
      (measure_source_inter_preimage_lt_top c hρc.continuousOn hmap hh.2.1.isCompact
        (hh.2.2.trans fun z hz => hz.1.1))
  have : IsFiniteMeasure ((T.μ.restrict T.U).restrict K) := ⟨hfin⟩
  refine MemLp.of_bound (T.measurable_H1coord_localTStar hρ hh).aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hKm]
  exact Eventually.of_forall hbound

/-- `T*` of a local piece as an element of `H₁ = L²(μ|_U)`. -/
def tstarL2 {c : ComplexChart n X} {e : AtlasFrame T.L} {ρ : ComplexModel n → ℝ}
    (hρ : IsChartDensity T.μ c ρ) {h : ComplexModel n → ComplexModel n}
    (hh : IsLocalTestField T.L T.U c e h) : Lp ℂ 2 (T.μ.restrict T.U) :=
  (T.memLp_H1coord_localTStar hρ hh).toLp _

end TwistedDatum

end SGPT.Trace.TwistedL2
