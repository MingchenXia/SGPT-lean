import SGPT.Trace.OTExt3Corollary
import SGPT.Trace.OTMarginLocal

/-!
# FPT `thm:compact-submanifold-extension` for submanifolds of full dimension

Blueprint `claude-ot-ext4.tex`, nodes `claude-ot-ext4:full-volume`, `claude-ot-ext4:full`.
Xia, *Foundations of pluripotential theory*, q07, `thm:compact-submanifold-extension`, in the
case `dim Y = dim X`.

A closed connected submanifold `W` of dimension `n = dim X` is open and closed (a connected
component of `X`).  A section `f` of `V|_W` with coefficients in `𝓘(φ|_W)` is holomorphic on `W`
(its local extensions `exists_gainPatch_intrinsic` agree with it on the open set `W`), so `f`
extended by `0` off `W` is a holomorphic section `s` of `V` on `X`, and

  `∫_X |s|² e^{-φ} dV_ω = ∫_W |f|² e^{-φ} dV_ω ≤ C ∫_W |f|² e^{-φ} dV_{ω|_W}`,

where `C` compares the two smooth positive volumes `dV_ω` (on the open set `W ⊆ X`) and
`dV_{ω|_W}` (on the manifold `W`) (`exists_setLIntegral_le_of_full`): in the flattening chart of a
point of `W`, both are a continuous positive density times Lebesgue measure
(`lintegral_finv_image_le`, `IsSmoothPositiveVolume` of `W`), and finitely many such charts cover
the compact `W`.

* `compactSubmanifoldExtensionAlong_of_eq`: `CompactSubmanifoldExtensionAlong ω W` for
  `dim W = dim X` (with `N = 1`).
* `otExtAlong_of_eq`: the book's `thm:OT_ext` (`OTExtAlong`) for `dim Y = dim X`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt4

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal NNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OTMargin SGPT.Bergman.CompactHolomorphicSectionsDraft

/-- The coordinate inclusion `ℂⁿ → ℂⁿ` is the identity. -/
theorem coordinateInclusion_self {n : ℕ} (z : ComplexModel n) : coordinateInclusion n n z = z := by
  ext i
  simp [coordinateInclusion_apply, i.2]

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- A submanifold of full dimension is open. -/
theorem isOpen_of_full {W : Set X} (hW : ∀ x ∈ W, RegularAtDim (n := n) W x n) : IsOpen W := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hreg := hW x hx
  filter_upwards [(FlatData.ofRegularAtDim hreg).isOpen_ambSource.mem_nhds
    (FlatData.mem_ambSource_ofRegularAtDim hreg)] with y hy
  exact (mem_iff_fcoord (FlatData.ofRegularAtDim hreg) hy).mpr fun i hi => absurd i.2 (by omega)

variable [MeasurableSpace X] [BorelSpace X]

/-- **One flattening chart of a full-dimensional submanifold.**  For a flattening datum `F` of
`W` (`dim W = n`), a smooth positive volume `μ` of `X`, a smooth positive volume `ν` of `W` and a
compact `K` in the flat target, `∫_{ζ⁻¹ K} g dμ ≤ C ∫_W g dν` for all measurable `g ≥ 0`. -/
theorem exists_lintegral_finv_image_le_of_full {W : Set X}
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x n) (F : FlatData n n X W)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    [MeasurableSpace W] [BorelSpace W] {ν : Measure W}
    (hν : letI := chartedSpace le_rfl hW; IsSmoothPositiveVolume (n := n) ν)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ F.flat.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : X → ℝ≥0∞, Measurable g →
      ∫⁻ x in finv F '' K, g x ∂μ ≤ ENNReal.ofReal C * ∫⁻ y : W, g y ∂ν := by
  let := chartedSpace le_rfl hW
  obtain ⟨C₁, hC₁0, hC₁⟩ := lintegral_finv_image_le F hμ hK hKt
  let e : ComplexChart n W := ⟨F.chart le_rfl, chart_mem_atlas le_rfl hW F⟩
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hν e
  have hKt' : K ⊆ e.val.target := fun z hz => by
    show coordinateInclusion n n z ∈ F.flat.target
    rw [coordinateInclusion_self]; exact hKt hz
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, fun g _ => ?_⟩
    simp [hKe]
  obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hKne (hρs.continuousOn.mono hKt')
  have hc : 0 < ρ z₀ := hρpos z₀ (hKt' hz₀K)
  refine ⟨C₁ * (ρ z₀)⁻¹, by positivity, fun g hg => ?_⟩
  have hgW : Measurable fun y : W => g y := hg.comp continuous_subtype_val.measurable
  have hread := setLIntegral_source_inter_preimage e hρs.continuousOn hmap hK hKt' hgW
  have hsymm : ∀ z ∈ K, ((e.val.symm z : W) : X) = finv F z := fun z hz => by
    show (F.invPoint z : X) = _
    rw [F.invPoint_val (hKt' hz)]
    show F.amb.val.symm (F.flat.symm (coordinateInclusion n n z)) = _
    rw [coordinateInclusion_self]; rfl
  calc ∫⁻ x in finv F '' K, g x ∂μ ≤ ENNReal.ofReal C₁ * ∫⁻ z in K, g (finv F z) := hC₁ g hg
    _ ≤ ENNReal.ofReal C₁ * ∫⁻ z in K, ENNReal.ofReal (ρ z₀)⁻¹ *
          (ENNReal.ofReal (ρ z) * g ((e.val.symm z : W) : X)) := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' hK.isClosed.measurableSet fun z hz => ?_)
        rw [hsymm z hz, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
        refine le_mul_of_one_le_left zero_le ?_
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]
        exact hmin hz
    _ = ENNReal.ofReal C₁ * (ENNReal.ofReal (ρ z₀)⁻¹ *
          ∫⁻ y in e.val.source ∩ e.val ⁻¹' K, g y ∂ν) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hread]
    _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ y : W, g y ∂ν) := by
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal (C₁ * (ρ z₀)⁻¹) * ∫⁻ y : W, g y ∂ν := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC₁0]

/-- **Comparison of volumes on a full-dimensional submanifold.**  For a compact submanifold `W`
of dimension `n = dim X`, a smooth positive volume `μ` of `X` and a smooth positive volume `ν`
of `W`, there is `C > 0` with `∫_W g dμ ≤ C ∫_W g dν` for all measurable `g ≥ 0` on `X`. -/
theorem exists_setLIntegral_le_of_full {W : Set X}
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x n) (hWc : IsCompact W)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    [MeasurableSpace W] [BorelSpace W] {ν : Measure W}
    (hν : letI := chartedSpace le_rfl hW; IsSmoothPositiveVolume (n := n) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : X → ℝ≥0∞, Measurable g →
      ∫⁻ x in W, g x ∂μ ≤ ENNReal.ofReal C * ∫⁻ y : W, g y ∂ν := by
  -- a radius at every point of `W`
  have hrad : ∀ p : W, ∃ r : ℝ, 0 < r ∧
      closedBall (0 : ComplexModel n) r ⊆ (FlatData.ofRegularAtDim (hW p.1 p.2)).flat.target := by
    intro p
    set Fd := FlatData.ofRegularAtDim (hW p.1 p.2)
    have hz0 : Fd.flat (Fd.amb.val p.1) = 0 := (hW p.1 p.2).2.2.choose_spec.2.1
    have h0 : (0 : ComplexModel n) ∈ Fd.flat.target := by
      rw [← hz0]; exact Fd.flat.map_source (FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)).2
    obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.mp Fd.flat.open_target 0 h0
    exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hrt⟩
  choose r hr hrt using hrad
  have hcomp := fun p : W => exists_lintegral_finv_image_le_of_full hW
    (FlatData.ofRegularAtDim (hW p.1 p.2)) hμ hν (isCompact_closedBall 0 (r p)) (hrt p)
  choose C hC0 hC using hcomp
  set A : W → Set X := fun p => finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' ball 0 (r p)
    with hA
  have hAo : ∀ p, IsOpen (A p) := fun p =>
    isOpen_finv_image _ (ball_subset_closedBall.trans (hrt p))
  have hpA : ∀ p : W, p.1 ∈ A p := by
    intro p
    set Fd := FlatData.ofRegularAtDim (hW p.1 p.2)
    have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW p.1 p.2)
    have hz0 : fcoord Fd p.1 = 0 := (hW p.1 p.2).2.2.choose_spec.2.1
    exact ⟨0, mem_ball_self (hr p), by rw [← hz0, finv_fcoord Fd hpF]⟩
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover A hAo
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hpA ⟨x, hx⟩⟩)
  refine ⟨∑ p ∈ t, C p + 1, by
    have := Finset.sum_nonneg (s := t) fun p _ => hC0 p
    linarith, fun g hg => ?_⟩
  set B : W → Set X := fun p => finv (FlatData.ofRegularAtDim (hW p.1 p.2)) '' closedBall 0 (r p)
    with hB
  have hBm : ∀ p, MeasurableSet (B p) := fun p =>
    ((isCompact_closedBall 0 (r p)).image_of_continuousOn
      ((continuousOn_finv _).mono (hrt p))).isClosed.measurableSet
  have hAB : ∀ p, A p ⊆ B p := fun p => image_mono ball_subset_closedBall
  have hpt : ∀ x, W.indicator g x ≤ ∑ p ∈ t, (B p).indicator g x := by
    intro x
    by_cases hx : x ∈ W
    · obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp (ht hx)
      rw [indicator_of_mem hx]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun p => (B p).indicator g x)
        (fun _ _ => zero_le) hpt)
      rw [indicator_of_mem (hAB p hxp)]
    · rw [indicator_of_notMem hx]; exact zero_le
  calc ∫⁻ x in W, g x ∂μ = ∫⁻ x, W.indicator g x ∂μ :=
        (lintegral_indicator hWc.isClosed.measurableSet g).symm
    _ ≤ ∫⁻ x, ∑ p ∈ t, (B p).indicator g x ∂μ := lintegral_mono hpt
    _ = ∑ p ∈ t, ∫⁻ x in B p, g x ∂μ := by
        rw [lintegral_finsetSum' _ fun p _ => (hg.indicator (hBm p)).aemeasurable]
        exact Finset.sum_congr rfl fun p _ => lintegral_indicator (hBm p) g
    _ ≤ ∑ p ∈ t, ENNReal.ofReal (C p) * ∫⁻ y : W, g y ∂ν :=
        Finset.sum_le_sum fun p _ => hC p g hg
    _ = ENNReal.ofReal (∑ p ∈ t, C p) * ∫⁻ y : W, g y ∂ν := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun p _ => hC0 p]
    _ ≤ ENNReal.ofReal (∑ p ∈ t, C p + 1) * ∫⁻ y : W, g y ∂ν := by
        gcongr; linarith

variable [CompactSpace X]

/-- **FPT `thm:compact-submanifold-extension` for `dim Y = dim X`.**  For a closed connected
submanifold `W` of dimension `n` (a connected component of `X`), `N = 1` and `C` the comparison
constant of the Kähler volumes of `ω` and `ω|_W` on `W`: every `f ∈ H⁰(W, V|_W)` in `𝓘(φ|_W)`
extends by `0` to `s ∈ H⁰(X, V)` with `∫_X |s|² e^{-φ} dV ≤ C ∫_W |f|² e^{-φ} dV_W`. -/
theorem compactSubmanifoldExtensionAlong_of_eq (ωb : KahlerBackground n X) {W : Set X}
    (hW : IsClosedConnectedSubmanifold n W n) : CompactSubmanifoldExtensionAlong ωb hW := by
  unfold CompactSubmanifoldExtensionAlong
  intro hk
  let : ChartedSpace (ComplexModel n) W := chartedSpace hk hW.2.2
  have : IsComplexManifold n W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
  have hWc : IsCompact W := hW.1.isCompact
  have hWo : IsOpen W := isOpen_of_full hW.2.2
  obtain ⟨C, hC0, hC⟩ := exists_setLIntegral_le_of_full hW.2.2 hWc hμ hμW
  refine ⟨1, C, one_pos, hC0, fun V hV θV hθV φ hφ _ f hf => ?_⟩
  have hφq : ManifoldQuasiPlurisubharmonic (n := n) φ := hφ.1.quasiPlurisubharmonic
  have hφm : Measurable φ := hφq.upperSemicontinuous.measurable
  choose B' K B S hB'o hBo hKc hmem hB'K hKB hsm hagree _ using
    fun p : W => exists_gainPatch_intrinsic V.Fiber hμ hk hW.2.2 hφq one_pos hf p
  classical
  set σf : (x : X) → V.Fiber x := fun x => if hx : x ∈ W then f ⟨x, hx⟩ else 0 with hσf
  have hσsm : ContMDiff 𝓘(ℂ, ComplexModel n) (𝓘(ℂ, ComplexModel n).prod 𝓘(ℂ, ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (σf x)) := by
    intro x
    by_cases hx : x ∈ W
    · set p : W := ⟨x, hx⟩
      have hxB : x ∈ B p := hKB p (hB'K p (hmem p))
      refine (hsm p x hxB).congr_of_eventuallyEq ?_
      filter_upwards [(hBo p).mem_nhds hxB, hWo.mem_nhds hx] with y hyB hyW
      simp only [hσf, dif_pos hyW]
      rw [hagree p ⟨y, hyW⟩ hyB]
    · refine ((Bundle.contMDiff_zeroSection ℂ V.Fiber (IB := 𝓘(ℂ, ComplexModel n))
        (n := ∞)) x).congr_of_eventuallyEq ?_
      filter_upwards [hW.1.isOpen_compl.mem_nhds hx] with y hy
      simp only [hσf, dif_neg (show y ∉ W from hy)]
      rfl
  set σ : HolomorphicSections (n := n) V.Fiber := ⟨σf, hσsm⟩ with hσ
  have hσW : ∀ y : W, σ y = f y := fun y => by
    show σf y.1 = f y; simp only [hσf, dif_pos y.2]
  refine ⟨σ, hσW, ?_⟩
  set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (‖σ x‖ ^ 2) * multiplierWeight 1 (φ x) with hg
  have hσc : Continuous fun x => ‖σ x‖ :=
    ContinuousFiberNorm.continuous.comp σ.contMDiff.continuous
  have hgm : Measurable g :=
    (ENNReal.continuous_ofReal.comp (hσc.pow 2)).measurable.mul
      ((multiplierWeight_antitone zero_le_one).measurable.comp hφm)
  have hgW : ∀ x, x ∉ W → g x = 0 := fun x hx => by
    have : σ x = 0 := by show σf x = 0; simp only [hσf, dif_neg hx]
    simp [hg, this]
  calc ∫⁻ x, g x ∂(IntegrationCurrent.kahlerVolume ωb)
      = ∫⁻ x in W, g x ∂(IntegrationCurrent.kahlerVolume ωb) := by
        rw [← lintegral_indicator hWc.isClosed.measurableSet]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ W
        · rw [indicator_of_mem hx]
        · rw [indicator_of_notMem hx, hgW x hx]
    _ ≤ ENNReal.ofReal C * ∫⁻ y : W, g y
          ∂(IntegrationCurrent.kahlerVolume (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)) :=
        hC g hgm
    _ = _ := by
        congr 1
        refine lintegral_congr fun y => ?_
        simp only [hg, hσW y]

/-- **`thm:OT_ext` for `dim Y = dim X`**: the book's `OTExtAlong` for a closed connected
submanifold of full dimension (FPT `cor:compact-positive-metric-extension` applied to
`compactSubmanifoldExtensionAlong_of_eq`). -/
theorem otExtAlong_of_eq (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} (hW : IsClosedConnectedSubmanifold n W n) {δ : ℝ}
    (hδ : 0 < δ) : OTExtAlong ωb L T θ hW δ :=
  SGPT.Trace.OTExt3.otExtAlong_of_compactSubmanifoldExtension ωb L T hL hT θ hθ hW hδ
    (compactSubmanifoldExtensionAlong_of_eq ωb hW)

end SGPT.Trace.OTExt4
