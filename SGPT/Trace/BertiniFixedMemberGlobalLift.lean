import SGPT.Trace.OTResMain
import SGPT.Trace.BertiniSectionMultiplication
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

/-! Genuine global native multiplier lifting for ONE FIXED closed connected
member. Literal I(phi|W) input, literal I(phi) output; threshold depends on W. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2

variable {n m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_fixed_member_eventual_original_multiplier_lift
    (G T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hT : IsSourceSmoothHermitianMetric T)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    {W : Set X} (hW : IsClosedConnectedSubmanifold n W m)
    (hφW : ∃ y ∈ W, φ y ≠ ⊥) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI := chartedSpace hk hW.2.2
    letI := isComplexManifold_chartedSpace hk hW.2.2
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ∀ f : (y : W) → (twistedPower G T k).Fiber y,
        IsAlongMultiplierSection (twistedPower G T k).Fiber (m := m) 1 (fun y : W => φ y.val) f →
        ∃ s : nativeMultiplierSections (twistedPower G T k) φ, ∀ y : W, s.val y.val = f y := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let := chartedSpace hk hW.2.2
  let := isComplexManifold_chartedSpace hk hW.2.2
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel _
  let : BorelSpace W := ⟨rfl⟩
  let θ := sourceNativeFirstChernForm G hG
  let omegaG : KahlerBackground n X := ⟨θ,hGpos⟩
  obtain ⟨C,hC,hφC⟩ := GlobalQuasiPshKahlerBackground.exists_pos_isThetaPshPotential_smul omegaG hφ
  obtain ⟨kOT,_COT,_hCOT,hOT⟩ := SGPT.Trace.OTRes.otExtAlong omegaG G T hG hT θ
    (sourceNativeFirstChernForm_isOwn G hG) hW (δ := (1 / 2 : ℝ)) (by norm_num)
  let k₀ : ℕ := max kOT (max 1 ⌈2 * C⌉₊)
  have hk₀pos : 0 < k₀ := lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 ⌈2 * C⌉₊).trans (le_max_right kOT (max 1 ⌈2 * C⌉₊)))
  refine ⟨k₀,hk₀pos,?_⟩
  intro k hkk₀ f hf
  have hkOT : kOT ≤ k := (le_max_left kOT (max 1 ⌈2 * C⌉₊)).trans hkk₀
  have hklarge : max 1 ⌈2 * C⌉₊ ≤ k := (le_max_right kOT (max 1 ⌈2 * C⌉₊)).trans hkk₀
  have hk1 : 1 ≤ k := (le_max_left 1 ⌈2 * C⌉₊).trans hklarge
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (zero_lt_one.trans_le hk1)
  have hkceil : ⌈2 * C⌉₊ ≤ k := (le_max_right 1 ⌈2 * C⌉₊).trans hklarge
  have h2C : 2 * C ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hkceil)
  let ψ : X → EReal := fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * φ x
  have hψ0 : IsThetaPshPotential ((k : ℝ)⁻¹ • (C • omegaG.form)).val ψ :=
    PotentialMassComparison.isThetaPshPotential_smul hφC (inv_pos.mpr hkreal)
  have hsmall : (k : ℝ)⁻¹ * C ≤ 1 / 2 := by
    rw [inv_mul_eq_div,div_le_iff₀ hkreal]
    linarith
  have hsemi : (((1 / 2 : ℝ) - (k : ℝ)⁻¹ * C) • omegaG.form).val.IsSemipositive :=
    KahlerDomination.isSemipositive_smul omegaG.isSemipositive (by linarith)
  have hform : (k : ℝ)⁻¹ • (C • omegaG.form) +
      ((1 / 2 : ℝ) - (k : ℝ)⁻¹ * C) • omegaG.form = θ - (1 / 2 : ℝ) • omegaG.form := by
    change (k : ℝ)⁻¹ • (C • omegaG.form) +
      ((1 / 2 : ℝ) - (k : ℝ)⁻¹ * C) • omegaG.form = omegaG.form - (1 / 2 : ℝ) • omegaG.form
    rw [smul_smul]
    module
  have hψ : IsThetaPshPotential (θ - (1 / 2 : ℝ) • omegaG.form).val ψ := by
    rw [← hform]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive hψ0 hsemi
  have hψW : ∃ y ∈ W, ψ y ≠ ⊥ := by
    obtain ⟨y,hyW,hy⟩ := hφW
    exact ⟨y,hyW,SGPT.Trace.OTExt3.coe_mul_ne_bot (inv_pos.mpr hkreal) hy⟩
  have hscale (x : X) : ((k : ℝ) : EReal) * ψ x = φ x := by
    change ((k : ℝ) : EReal) * ((((k : ℝ)⁻¹ : ℝ) : EReal) * φ x) = φ x
    rw [← mul_assoc,← EReal.coe_mul,mul_inv_cancel₀ hkreal.ne',EReal.coe_one,one_mul]
  have hfs : IsAlongMultiplierSection (twistedPower G T k).Fiber (m := m) (k : ℝ)
      (fun y : W => ψ y.val) f := by
    have heq : (fun y : W => ((k : ℝ) : EReal) * ψ y.val) =
        (fun y : W => ((1 : ℝ) : EReal) * φ y.val) := by
      funext y
      simpa only [EReal.coe_one,one_mul] using hscale y.val
    intro y
    change (multiplierIdeal (n := m) 1 (fun y : W => ((k : ℝ) : EReal) * ψ y.val)).mem y _
    rw [heq]
    exact hf y
  obtain ⟨s,hsmem,hseq,_hbound⟩ := hOT k hkOT ψ hψ hψW f hfs
  have hI : sourceDegreeMultiplierIdeal (n := n) k ψ = sourceDegreeMultiplierIdeal (n := n) 1 φ := by
    unfold sourceDegreeMultiplierIdeal
    congr 1
    funext x
    simpa only [Nat.cast_one,EReal.coe_one,one_mul] using hscale x
  have hsφ : s ∈ fullHolomorphicIdealSections (n := n) (twistedPower G T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) 1 φ) := by
    rw [← hI]
    exact hsmem
  exact ⟨⟨s,hsφ⟩,hseq⟩

end SGPT.Trace.Bertini
