import SGPT.Trace.BertiniUniversalNativeLift
import SGPT.Bergman.SourceNativeTensorChern

/-! ONE actual auxiliary integer BEFORE ALL regular members and ALL
smooth semipositive twists; literal original native multiplier pullbacks. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeKodairaPullback SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.Bertini SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2
variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem exists_uniform_auxiliary_regular_native_multiplier_lift
    (G T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hT : IsSourceSmoothHermitianMetric T)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (b : ℝ) (hb : 0 ≤ b) (m : ℕ) (hmn : m < n) :
    let ωG : KahlerBackground n X := ⟨sourceNativeFirstChernForm G hG,hGpos⟩
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (U : HermitianHolomorphicLineBundle.{0,0} n X)
      (hU : IsSourceSmoothHermitianMetric U), (sourceNativeFirstChernForm U hU).val.IsSemipositive →
      ∀ k : ℕ, k₀ ≤ k →
      ∀ (W : Set X) (_hclosed : IsClosed W) (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m),
      ∀ (R : X → ℝ), IsGlobalNormalPole ωG W R →
      (∀ (c : ComplexChart n X), ∀ z ∈ c.val.target, 0 < R (c.val.symm z) →
        ∀ v : ComplexModel n,
          0 ≤ leviForm (fun w => Real.log (R (c.val.symm w))) z v / Real.pi + b * kahlerQuad ωG c z v) →
      let hk : m ≤ n := hmn.le
      letI := chartedSpace hk hreg
      letI := isComplexManifold_chartedSpace hk hreg
      let ι : ContMDiffMap 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) W X ∞ :=
        ⟨Subtype.val,contMDiff_val hk hreg⟩
      ∀ σ : nativeMultiplierSections (nativeHolomorphicPullbackBundle (twistedPower G (tensor T U) k) ι)
        (fun y : W => φ y.val),
        ∃ s : nativeMultiplierSections (twistedPower G (tensor T U) k) φ,
          sourceNativeHolomorphicSectionPullback (twistedPower G (tensor T U) k) ι s.val = σ.val := by
  intro ωG
  let θG := sourceNativeFirstChernForm G hG
  let θT := sourceNativeFirstChernForm T hT
  obtain ⟨C,bK,hC,_hbK,hLift⟩ := exists_regular_original_native_multiplier_lift_threshold ωG φ hφ
  obtain ⟨A,_hA,hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul θT.val ωG.form.val ωG.isKahler.1
  let N₀ := regularNormalPoleThreshold n m bK b
  let k₀ : ℕ := max 1 ⌈N₀ + C + A⌉₊
  have hk₀ : 0 < k₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨k₀,hk₀,?_⟩
  intro U hU hUpos k hkk₀ W hclosed hreg R hR hbR
  have hkbound : N₀ + C + A ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈N₀ + C + A⌉₊).trans hkk₀)
  let hTU := sourceNativeTensor_smooth T U hT hU
  let θTU := sourceNativeFirstChernForm (tensor T U) hTU
  let V := twistedPower G (tensor T U) k
  have hV : IsSourceSmoothHermitianMetric V := sourceNativeTwistedPower_smooth G (tensor T U) hG hTU k
  let θV := (k : ℝ) • θG + θTU
  have hθV : IsOwnFirstChernForm V θV := sourceNativeTwistedPower_isOwn G (tensor T U) hG hTU k
  have hmargin : (θV - (N₀ + C) • ωG.form).val.IsSemipositive := by
    intro e z hz v
    have hd := hdom e z hz v
    have hUsemi := hUpos e z hz v
    have hω := ωG.isSemipositive e z hz v
    have hTUcoeff := DFunLike.congr_fun (sourceNativeTensor_chern_coeff T U hT hU e hz) ![v,Complex.I • v]
    change θTU.val.coeff e z ![v,Complex.I • v] =
      θT.val.coeff e z ![v,Complex.I • v] + (sourceNativeFirstChernForm U hU).val.coeff e z ![v,Complex.I • v] at hTUcoeff
    have hscale : A * ωG.form.val.coeff e z ![v,Complex.I • v] ≤
        ((k : ℝ) - (N₀ + C)) * ωG.form.val.coeff e z ![v,Complex.I • v] :=
      mul_le_mul_of_nonneg_right (by linarith) hω
    dsimp only [θV]
    simp only [sub_eq_add_neg,ClosedRealOneOneForm.coeff_add,ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul,ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hd ⊢
    rw [hTUcoeff]
    change (k : ℝ) * ωG.form.val.coeff e z ![v,Complex.I • v] +
      (θT.val.coeff e z ![v,Complex.I • v] + (sourceNativeFirstChernForm U hU).val.coeff e z ![v,Complex.I • v]) +
      -((N₀ + C) * ωG.form.val.coeff e z ![v,Complex.I • v]) ≥ 0
    linarith
  exact hLift b hb W m hclosed hmn.le hreg hmn R hR hbR V hV θV hθV hmargin

end SGPT.Trace.BertiniUniversal
