import SGPT.Trace.BertiniNativeSectionPole
import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-! ONE fixed-native-metric curvature bound BEFORE every actual section/member/epsilon. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniNativeSectionPole
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open ConcentrationPotentialLevi
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

private theorem actualLogSquareLevi {n : ℕ} {w : ComplexModel n → ℝ} {z : ComplexModel n}
    (hw : ContDiffAt ℝ 2 w z) (hw0 : 0 < w z) (v : ComplexModel n) :
    leviForm (fun y => Real.log (w y ^ 2)) z v =
      2 * (w z * leviForm w z v - Complex.normSq (delC w z v)) / w z ^ 2 := by
  have heq : (fun y => Real.log (w y ^ 2)) = (2 : ℝ) • (fun y => Real.log (w y)) := by
    funext y
    simp only [Real.log_pow,Nat.cast_ofNat,Pi.smul_apply,smul_eq_mul]
  rw [heq,leviForm_smul (hw.log hw0.ne') 2 v,leviForm_log_of_pos hw hw0 v,normSq_delC]
  field_simp [hw0.ne']

private theorem actualWeightedNormLogLevi {n : ℕ} {w : ComplexModel n → ℝ}
    {f : ComplexModel n → ℂ} {z : ComplexModel n} (hw : ContDiffAt ℝ 2 w z)
    (hw0 : 0 < w z) (hf : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ f y)
    {ε : ℝ} (hε : 0 ≤ ε) (hpos : 0 < w z ^ 2 * Complex.normSq (f z) + ε)
    (v : ComplexModel n) :
    (w z ^ 2 * Complex.normSq (f z)) / (w z ^ 2 * Complex.normSq (f z) + ε) *
      leviForm (fun y => Real.log (w y ^ 2)) z v ≤
    leviForm (fun y => Real.log (w y ^ 2 * Complex.normSq (f y) + ε)) z v := by
  have h := le_leviForm_log_sum_of_pos (ι := Fin 1) (c := fun _ => w) (G := fun _ => f)
    (s := ε) (z := z) (by simpa only [Fin.sum_univ_one] using hpos) (fun _ => hw) (fun _ => hf) v
  simp only [Fin.sum_univ_one] at h
  have hnonneg : 0 ≤ ε * Complex.normSq (gammaTerm w f z v) /
      (w z ^ 2 * Complex.normSq (f z) + ε) ^ 2 :=
    div_nonneg (mul_nonneg hε (Complex.normSq_nonneg _)) (sq_nonneg _)
  calc
    _ = 2 * (Complex.normSq (f z) *
        (w z * leviForm w z v - Complex.normSq (delC w z v))) /
          (w z ^ 2 * Complex.normSq (f z) + ε) := by
      rw [actualLogSquareLevi hw hw0]
      field_simp [hw0.ne',hpos.ne']
    _ ≤ ε * Complex.normSq (gammaTerm w f z v) /
        (w z ^ 2 * Complex.normSq (f z) + ε) ^ 2 +
        2 * (Complex.normSq (f z) *
          (w z * leviForm w z v - Complex.normSq (delC w z v))) /
            (w z ^ 2 * Complex.normSq (f z) + ε) := le_add_of_nonneg_left hnonneg
    _ ≤ _ := h

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

omit [CompactSpace X] in
private theorem actualNativeFrameLogLevi (P : HermitianHolomorphicLineBundle.{0,0} n X)
    (hP : IsSourceSmoothHermitianMetric P) (c : ComplexChart n X) (e : AtlasFrame P)
    {z : ComplexModel n} (hz : z ∈ c.val.target) (he : c.val.symm z ∈ e.val.baseSet)
    (v : ComplexModel n) :
    leviForm (fun y => Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z v =
      -(Real.pi * (sourceNativeFirstChernForm P hP).val.coeff c z ![v,Complex.I • v]) := by
  have hD : IsOpen (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hn := (hP c e).contDiffAt (hD.mem_nhds ⟨hz,he⟩)
  have hweight : ContDiffAt ℝ 2 (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z :=
    (hn.log (sq_pos_of_pos (norm_pos_iff.mpr (sourceAtlasFrame_ne_zero P e he))).ne').neg.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have h := smoothDDC_complexDiagonal_eq_leviForm hweight v
  rw [← sourceNativeFirstChernForm_isOwn P hP c e z hz he] at h
  have hneg : leviForm (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z v =
      Real.pi * (sourceNativeFirstChernForm P hP).val.coeff c z ![v,Complex.I • v] := by
    rw [h,mul_div_cancel₀ _ Real.pi_ne_zero]
  have hnegative : leviForm (fun y => -Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z v =
      -leviForm (fun y => Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z v :=
    leviForm_neg (fun y => Real.log (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) z v
  rw [hnegative] at hneg
  linarith

omit [CompactSpace X] in
private theorem actualNativeSectionWeightedLevi (P : HermitianHolomorphicLineBundle.{0,0} n X)
    (hP : IsSourceSmoothHermitianMetric P) (s : HolomorphicSections (n := n) P.Fiber)
    (c : ComplexChart n X) {z : ComplexModel n} (hz : z ∈ c.val.target)
    {ε : ℝ} (hε : 0 ≤ ε) (hpos : 0 < ‖s (c.val.symm z)‖ ^ 2 + ε) (v : ComplexModel n) :
    ‖s (c.val.symm z)‖ ^ 2 / (‖s (c.val.symm z)‖ ^ 2 + ε) *
      (-(Real.pi * (sourceNativeFirstChernForm P hP).val.coeff c z ![v,Complex.I • v])) ≤
    leviForm (fun y => Real.log (‖s (c.val.symm y)‖ ^ 2 + ε)) z v := by
  let e : AtlasFrame P := ⟨trivializationAt ℂ P.Fiber (c.val.symm z),inferInstance⟩
  let := e.property
  have he : c.val.symm z ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  let D := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
  have hD : IsOpen D := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hzD : z ∈ D := ⟨hz,he⟩
  let w : ComplexModel n → ℝ := fun y => ‖e.val.symm (c.val.symm y) 1‖
  let f : ComplexModel n → ℂ := fun y => sectionCoefficient P.Fiber e.val s (c.val.symm y)
  have hw0 : 0 < w z := norm_pos_iff.mpr (sourceAtlasFrame_ne_zero P e he)
  have hw : ContDiffAt ℝ 2 w z := by
    have hnorm := (hP c e).contDiffAt (hD.mem_nhds hzD)
    have hsqrt := hnorm.sqrt (sq_pos_of_pos hw0).ne'
    have heq : (fun y => Real.sqrt (‖e.val.symm (c.val.symm y) 1‖ ^ 2)) = w := by
      funext y
      exact Real.sqrt_sq (norm_nonneg _)
    rw [heq] at hsqrt
    exact hsqrt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfOn := sourceSectionCoefficient_chart_holomorphic P s c e
  have hf : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ f y := by
    filter_upwards [hD.mem_nhds hzD] with y hy
    exact (hfOn y hy).differentiableAt (hD.mem_nhds hy)
  have hR (y : ComplexModel n) (hy : y ∈ D) :
      ‖s (c.val.symm y)‖ ^ 2 = w y ^ 2 * Complex.normSq (f y) := by
    rw [norm_eq_coefficient_mul_frameNorm P.Fiber e.val s hy.2,mul_pow]
    simp only [w,f,frameNorm,Complex.normSq_eq_norm_sq]
    ring
  have hp : 0 < w z ^ 2 * Complex.normSq (f z) + ε := by rwa [← hR z hzD]
  have hlower := actualWeightedNormLogLevi hw hw0 hf hε hp v
  have hframe := actualNativeFrameLogLevi P hP c e hz he v
  change leviForm (fun y => Real.log (w y ^ 2)) z v = _ at hframe
  rw [hframe,← hR z hzD] at hlower
  have heq : (fun y => Real.log (‖s (c.val.symm y)‖ ^ 2 + ε)) =ᶠ[𝓝 z]
      (fun y => Real.log (w y ^ 2 * Complex.normSq (f y) + ε)) := by
    filter_upwards [hD.mem_nhds hzD] with y hy
    rw [hR y hy]
  rw [← GlobalTubeFunction.leviForm_congr_of_eventuallyEq heq v] at hlower
  exact hlower

theorem exists_uniform_poleWeight_levi_bound
    (omega : KahlerBackground n X) (P : HermitianHolomorphicLineBundle.{0,0} n X)
    (hP : IsSourceSmoothHermitianMetric P) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ s : HolomorphicSections (n := n) P.Fiber,
      (∀ ε : ℝ, 0 < ε → ∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, ∀ v : ComplexModel n,
        0 ≤ leviForm (fun y => Real.log (poleWeight P s (c.val.symm y) + ε)) z v / Real.pi +
          b * SGPT.Trace.TwistedL2.kahlerQuad omega c z v) ∧
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < poleWeight P s (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun y => Real.log (poleWeight P s (c.val.symm y))) z v / Real.pi +
            b * SGPT.Trace.TwistedL2.kahlerQuad omega c z v) := by
  obtain ⟨b,hb,hbound⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega
    (-sourceNativeFirstChernForm P hP)
  have hAll (s : HolomorphicSections (n := n) P.Fiber) (ε : ℝ) (hε : 0 ≤ ε)
      (c : ComplexChart n X) (z : ComplexModel n) (hz : z ∈ c.val.target)
      (hpos : 0 < ‖s (c.val.symm z)‖ ^ 2 + ε) (v : ComplexModel n) :
      0 ≤ leviForm (fun y => Real.log (‖s (c.val.symm y)‖ ^ 2 + ε)) z v / Real.pi +
        b * SGPT.Trace.TwistedL2.kahlerQuad omega c z v := by
    let Q := SGPT.Trace.TwistedL2.kahlerQuad omega c z v
    let T := (sourceNativeFirstChernForm P hP).val.coeff c z ![v,Complex.I • v]
    let N := ‖s (c.val.symm z)‖ ^ 2
    let lam := N / (N + ε)
    have hQ : 0 ≤ Q := omega.isSemipositive c z hz v
    have hN : 0 ≤ N := sq_nonneg _
    have hlam0 : 0 ≤ lam := div_nonneg hN hpos.le
    have hlam1 : lam ≤ 1 := (div_le_one hpos).mpr (by linarith)
    have hB := hbound c z hz v
    simp only [ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul,ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hB
    have hBT : T ≤ b * Q := by
      change 0 ≤ -T + b * Q at hB
      linarith
    have hbase : -(Real.pi * b * Q) ≤ -(Real.pi * T) := by nlinarith [Real.pi_pos]
    have hsmall : -(Real.pi * b * Q) ≤ lam * (-(Real.pi * b * Q)) := by
      have hn : -(Real.pi * b * Q) ≤ 0 := neg_nonpos.mpr
        (mul_nonneg (mul_nonneg Real.pi_pos.le hb.le) hQ)
      simpa only [one_mul] using mul_le_mul_of_nonpos_right hlam1 hn
    have hscaled : -(Real.pi * b * Q) ≤ lam * (-(Real.pi * T)) :=
      hsmall.trans (mul_le_mul_of_nonneg_left hbase hlam0)
    have hlower := actualNativeSectionWeightedLevi P hP s c hz hε hpos v
    have hL : -(Real.pi * b * Q) ≤
        leviForm (fun y => Real.log (‖s (c.val.symm y)‖ ^ 2 + ε)) z v := hscaled.trans hlower
    have hdivide : -(b * Q) ≤
        leviForm (fun y => Real.log (‖s (c.val.symm y)‖ ^ 2 + ε)) z v / Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hL])
    change 0 ≤ _ + b * Q
    nlinarith [hdivide]
  refine ⟨b,hb.le,fun s => ⟨?_,?_⟩⟩
  · intro ε hε c z hz v
    exact hAll (poleSection P s) ε hε.le c z hz (by
      exact lt_of_le_of_lt (poleWeight_nonneg P s (c.val.symm z))
        (lt_add_of_pos_right _ hε)) v
  · intro c z hz hpos v
    simpa only [poleWeight,add_zero] using
      hAll (poleSection P s) 0 (le_refl 0) c z hz (by simpa only [poleWeight,add_zero] using hpos) v

end SGPT.Trace.BertiniNativeSectionPole
