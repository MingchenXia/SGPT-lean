import SGPT.Projective.OkounkovOriginalPerturbAbsorption
import SGPT.Okounkov.ValGen2Atlas
import SGPT.Okounkov.TranscendentalCoreAlgebra
import SGPT.Foundations.Analysis.Pending.IEnvelopeOrder

/-! Actual multiplier ideal exponent monotonicity from the produced compact original weight bound, no normalization premise.
Blueprint: okounkov-original-multiplier-exponent-order.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace SGPT.Okounkov.OriginalMultiplierExponentOrder
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov.TranscendentalCore

private theorem scaled_le_scaled_add {a b C : ℝ} (hb : 0<b) (hba : b≤a)
    {z : EReal} (hz : z≤(C:EReal)) :
    (a:EReal)*z≤(b:EReal)*z+(((a-b)*C:ℝ):EReal) := by
  have ha : 0<a := hb.trans_le hba
  induction z using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ha,EReal.coe_mul_bot_of_pos hb,EReal.bot_add]
  | top => exact False.elim ((not_le_of_gt (EReal.coe_lt_top C)) hz)
  | coe z =>
    rw [←EReal.coe_mul,←EReal.coe_mul,←EReal.coe_add,EReal.coe_le_coe_iff]
    have hzR : z≤C := EReal.coe_le_coe_iff.mp hz
    nlinarith only [mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hzR)]

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
    [IsSeparated f] [QuasiCompact f] [Nonempty (SchemeComplexPoint f)]
local instance exponentOrderTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance exponentOrderCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance exponentOrderManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- Actual original I(k phi)⊆I(m phi), k≥m>0, produced from genuine compact theta-psh geometry, no phi≤0 input. -/
theorem multiplierIdeal_le_of_nat_le {L : X.Modules} (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n E L) {φ : SchemeComplexPoint f → EReal}
    (hφ : IsThetaPshPotential (H.curvature a).val φ) (k m : ℕ) (hm : 0<m) (hmk : m≤k) :
    (multiplierIdeal (n:=n) (k:ℝ) φ).Le (multiplierIdeal (n:=n) (m:ℝ) φ) := by
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hk : 0<k := hm.trans_le hmk
  obtain ⟨C,hC⟩ := hφ.exists_global_upper_bound
  have hψ := isThetaPshPotential_nonneg_smul hφ (show (0:ℝ)≤m from Nat.cast_nonneg _)
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hpoint : ∀ x, (k:EReal)*φ x≤(m:EReal)*φ x+((((k:ℝ)-(m:ℝ))*C:ℝ):EReal) :=
    fun x => scaled_le_scaled_add hmR hmkR (hC x)
  have hψ' : ManifoldQuasiPlurisubharmonic (n:=n) (fun x => (m:EReal)*φ x) := hψ.1.quasiPlurisubharmonic
  have horder := iOrderOnManifold_of_le_add hψ' hpoint
  have hle := SGPT.Okounkov.multiplierIdeal_le_of_iOrderOnManifold horder (show (0:ℝ)<1 from zero_lt_one)
  have hkEq : multiplierIdeal (n:=n) (1:ℝ) (fun x => (k:EReal)*φ x)=multiplierIdeal (n:=n) (k:ℝ) φ := by
    simpa only [Nat.mul_one,Nat.cast_one] using ValGen2.multiplierIdeal_natCast_mul f n φ hk zero_lt_one
  have hmEq : multiplierIdeal (n:=n) (1:ℝ) (fun x => (m:EReal)*φ x)=multiplierIdeal (n:=n) (m:ℝ) φ := by
    simpa only [Nat.mul_one,Nat.cast_one] using ValGen2.multiplierIdeal_natCast_mul f n φ hm zero_lt_one
  rw [hkEq,hmEq] at hle
  exact hle
end SGPT.Okounkov.OriginalMultiplierExponentOrder
