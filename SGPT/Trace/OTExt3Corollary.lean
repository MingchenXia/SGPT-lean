import SGPT.Trace.OTExt3Finite
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Bergman.SourceNativeTensorSmoothMetric
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Foundations.Analysis.Pending.PotentialMassComparison
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# FPT `cor:compact-positive-metric-extension`: `thm:OT_ext` from the compact submanifold extension

Blueprint `claude-ot-ext3.tex`, node `claude-ot-ext3:corollary`.  Xia, *Foundations of
pluripotential theory*, q07, `cor:compact-positive-metric-extension`: for `θ = c₁(L, h)`,
`c₁(T, h_T) ≥ -b_T ω` and `φ ∈ PSH(X, θ - δω)`, the metric `h_T h^k e^{-kφ}` on `L^k ⊗ T` has
curvature `≥ (kδ - b_T) ω ≥ N ω` for `kδ - b_T ≥ N`, so `thm:compact-submanifold-extension`
applies to `V = L^k ⊗ T`, `φ_V = kφ`; the finiteness of the norm on `Y` follows from
`s ∈ H⁰(Y, (L^k ⊗ T)|_Y ⊗ 𝓘(kφ|_Y))` (`lintegral_lt_top_of_isAlongMultiplierSection`), and the
extension, of finite norm, lies in `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`.

`otExtAlong_of_compactSubmanifoldExtension`: `CompactSubmanifoldExtensionAlong ω Y` implies the
book's `OTExtAlong ω L T θ Y δ` for every `δ > 0` (with `k₀ = max 1 ⌈(N + b_T)/δ⌉` and the same
`C`).  The Chern form of `L^k ⊗ T` is `k θ_L + θ_T` for the native Chern forms
(`sourceNativeTwistedPower_isOwn`); `θ` and the native `θ_L` have the same coefficients on every
chart target (both are `ddᶜ(-log |e|²)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt3

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 (IsOwnFirstChernForm)
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- Two own first Chern forms of the same bundle have the same coefficients on chart targets. -/
theorem coeff_eq_of_isOwnFirstChernForm {L : HermitianHolomorphicLineBundle.{0, 0} n X}
    {θ θ' : ClosedRealOneOneForm n X} (hθ : IsOwnFirstChernForm L θ)
    (hθ' : IsOwnFirstChernForm L θ') (e : ComplexChart n X) {z : ComplexModel n}
    (hz : z ∈ e.val.target) : θ.val.coeff e z = θ'.val.coeff e z := by
  let E : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber (e.val.symm z), inferInstance⟩
  have hb : e.val.symm z ∈ E.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber _
  rw [hθ e E z hz hb, hθ' e E z hz hb]

theorem coe_mul_ne_bot {c : ℝ} (hc : 0 < c) {a : EReal} (ha : a ≠ ⊥) :
    (c : EReal) * a ≠ ⊥ := by
  induction a using EReal.rec with
  | bot => exact absurd rfl ha
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot
  | coe x => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

theorem multiplierWeight_one_coe_mul' (c : ℝ) (a : EReal) :
    multiplierWeight 1 ((c : EReal) * a) = multiplierWeight c a := by
  simp [multiplierWeight]

variable [CompactSpace X]

/-- **FPT `cor:compact-positive-metric-extension`**: FPT `thm:compact-submanifold-extension` for
`Y = W` implies the book's `thm:OT_ext` conclusion `OTExtAlong` for `W` and every `δ > 0`. -/
theorem otExtAlong_of_compactSubmanifoldExtension (ωb : KahlerBackground n X)
    (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (hL : IsSourceSmoothHermitianMetric L)
    (hT : IsSourceSmoothHermitianMetric T) (θ : ClosedRealOneOneForm n X)
    (hθ : IsOwnFirstChernForm L θ) {W : Set X} {m : ℕ}
    (hW : IsClosedConnectedSubmanifold n W m) {δ : ℝ} (hδ : 0 < δ)
    (hC : CompactSubmanifoldExtensionAlong ωb hW) : OTExtAlong ωb L T θ hW δ := by
  unfold CompactSubmanifoldExtensionAlong at hC
  unfold OTExtAlong
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  obtain ⟨N, C, hN, hC0, hext⟩ := hC
  set θL := SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm L hL
  set θT := SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm T hT
  have hθL := SGPT.Bergman.NativeHermitianMetric.sourceNativeFirstChernForm_isOwn L hL
  obtain ⟨A, hA, hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul θT.val ωb.form.val
    ωb.isKahler.1
  refine ⟨max 1 ⌈(N + A) / δ⌉₊, C, hC0, fun k hk' φ hφ hφW s hs => ?_⟩
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk'
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkδ : N + A ≤ k * δ := by
    have h1 : (N + A) / δ ≤ k :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hk')
    rwa [div_le_iff₀ hδ] at h1
  have hV := SGPT.Bergman.NativeHermitianMetric.sourceNativeTwistedPower_smooth L T hL hT k
  have hθV := SGPT.Bergman.NativeHermitianMetric.sourceNativeTwistedPower_isOwn L T hL hT k
  set ψ : X → EReal := fun x => ((k : ℝ) : EReal) * φ x with hψdef
  -- `kφ ∈ PSH(X, c₁(V) - N ω)`
  have hψ0 : IsThetaPshPotential ((k : ℝ) • (θ - δ • ωb.form)).val ψ :=
    PotentialMassComparison.isThetaPshPotential_smul hφ hk0
  have hψ : IsThetaPshPotential (((k : ℝ) • θL + θT) - N • ωb.form).val ψ := by
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hψ0 ?_
    intro e z hz v
    have hcoef := coeff_eq_of_isOwnFirstChernForm hθ hθL e hz
    have hd := hdom e z hz v
    have hω : 0 ≤ ωb.form.val.coeff e z ![v, Complex.I • v] := ωb.isSemipositive e z hz v
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
      ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      hcoef] at hd ⊢
    have h2 : A * ωb.form.val.coeff e z ![v, Complex.I • v] ≤
        ((k : ℝ) * δ - N) * ωb.form.val.coeff e z ![v, Complex.I • v] :=
      mul_le_mul_of_nonneg_right (by linarith) hω
    nlinarith
  have hψW : ∃ y ∈ W, ψ y ≠ ⊥ := by
    obtain ⟨y, hyW, hy⟩ := hφW
    exact ⟨y, hyW, coe_mul_ne_bot hk0 hy⟩
  have hs1 : IsAlongMultiplierSection (twistedPower L T k).Fiber (m := m) 1 (fun y : W => ψ y) s := by
    intro y
    have := hs y
    simp only [hψdef, EReal.coe_one, one_mul]
    exact this
  obtain ⟨s', hs'W, hs'int⟩ := hext (twistedPower L T k) hV ((k : ℝ) • θL + θT) hθV ψ hψ hψW s hs1
  have hweight : ∀ x, multiplierWeight 1 (ψ x) = multiplierWeight (k : ℝ) (φ x) := fun x =>
    multiplierWeight_one_coe_mul' _ _
  simp only [hweight] at hs'int
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hμW := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
    (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
  have hφm : Measurable φ := hφ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
  have hfinW := lintegral_lt_top_of_isAlongMultiplierSection (twistedPower L T k).Fiber hμW hk0
    (hφm.comp continuous_subtype_val.measurable) hs
  have hfin : ∫⁻ x, ENNReal.ofReal (‖s' x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)
      ∂(IntegrationCurrent.kahlerVolume ωb) < ⊤ :=
    lt_of_le_of_lt hs'int (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinW)
  refine ⟨s', (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) (twistedPower L T k).Fiber k
    hφ.quasiPshPotential s' hμ).mpr hfin, hs'W, hs'int⟩

end SGPT.Trace.OTExt3
