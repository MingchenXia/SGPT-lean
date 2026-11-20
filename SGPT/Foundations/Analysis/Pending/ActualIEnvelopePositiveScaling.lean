import SGPT.Foundations.Analysis.Pending.IEnvelopeAnalytic
import SGPT.Foundations.Analysis.Pending.MultiplierSubadditivity
import SGPT.Foundations.Analysis.Pending.MultiplierIdealWeightLowerBound
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Actual positive real covariance of the all-level ideal order and I-envelope -/

namespace SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling

open MeasureTheory FirstPass FirstPass.IEnvelope FirstPass.PositiveClasses
  FirstPass.QuasiEquisingularApproximation MultiplierSubadditivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Reparameterizing every actual positive multiplier level transports
the genuine all-level ideal order, with both infinite values retained. -/
theorem iOrderOnManifold_smul {u v : M → EReal}
    (hI : IOrderOnManifold (n := n) u v) {a : ℝ} (ha : 0 < a) :
    IOrderOnManifold (n := n) (fun x => (a : EReal) * u x)
      (fun x => (a : EReal) * v x) := by
  intro c hc e z hz f hf hmem
  let : MeasurableSpace (ComplexModel n) := borel _
  have : BorelSpace (ComplexModel n) := ⟨rfl⟩
  have hweights (p : M → EReal) (y : ComplexModel n) :
      multiplierWeight c (chartFunction (fun x => (a : EReal) * p x) e y) =
        multiplierWeight (c * a) (chartFunction p e y) := by
    simp only [chartFunction, multiplierWeight,
      MultiplierIdealWeightLowerBound.coe_mul_coe_mul]
  have hm : MultiplierIntegrableAt (chartFunction u e) (c * a) f z volume :=
    multiplierIntegrableAt_of_weight_eq (mul_pos hc ha) (hweights u) hmem
  have hv := hI (c * a) (mul_pos hc ha) e z hz f hf hm
  exact multiplierIntegrableAt_of_weight_eq hc (fun y => (hweights v y).symm) hv

variable [CompactSpace M] [Nonempty M]

/-- Literal positive scaling covariance is produced by genuine normalized
competitors in both directions, without a native separation assumption. -/
theorem iSingularityEnvelope_smul (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    {a : ℝ} (ha : 0 < a) :
    iSingularityEnvelope (a • θ).val (fun x => (a : EReal) * u x) =
      fun x => (a : EReal) * iSingularityEnvelope θ.val u x := by
  let p : M → EReal := iSingularityEnvelope θ.val u
  let au : M → EReal := fun x => (a : EReal) * u x
  let q : M → EReal := iSingularityEnvelope (a • θ).val au
  have hp : IsThetaPshPotential θ.val p :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu
  have hIp : IEquivalentOnManifold (n := n) p u :=
    (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hu.1.hasSmoothLocalPotentials u hu).symm
  have hau : IsThetaPshPotential (a • θ).val au :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hu ha
  have hq : IsThetaPshPotential (a • θ).val q :=
    iSingularityEnvelope_isThetaPshPotential (a • θ).val (a • θ).property.1
      (a • θ).property.2 hau.1.hasSmoothLocalPotentials au hau
  have hIq : IEquivalentOnManifold (n := n) q au :=
    (iEquivalent_iSingularityEnvelope (a • θ).val (a • θ).property.1
      (a • θ).property.2 hau.1.hasSmoothLocalPotentials au hau).symm
  have hap : IsThetaPshPotential (a • θ).val (fun x => (a : EReal) * p x) :=
    RestrictedApproximantComparison.isThetaPshPotential_smul hp ha
  have hap0 : (fun x => (a : EReal) * p x) ≤ 0 := by
    intro x
    change (a : EReal) * p x ≤ (0 : EReal)
    have hp0 : p x ≤ (0 : EReal) := iSingularityEnvelope_le_zero θ.val u x
    simpa only [mul_zero] using
      mul_le_mul_of_nonneg_left hp0 (EReal.coe_nonneg.mpr ha.le)
  have hlow : (fun x => (a : EReal) * p x) ≤ q :=
    le_iSingularityEnvelope hap hap0
      ⟨iOrderOnManifold_smul hIp.1 ha, iOrderOnManifold_smul hIp.2 ha⟩
  have hai : 0 < a⁻¹ := inv_pos.mpr ha
  have hcancel (r : M → EReal) :
      (fun x => ((a⁻¹ : ℝ) : EReal) * ((a : EReal) * r x)) = r := by
    funext x
    rw [MultiplierIdealWeightLowerBound.coe_mul_coe_mul,
      inv_mul_cancel₀ ha.ne', EReal.coe_one, one_mul]
  have hqinv : IsThetaPshPotential θ.val
      (fun x => ((a⁻¹ : ℝ) : EReal) * q x) := by
    have h := RestrictedApproximantComparison.isThetaPshPotential_smul hq hai
    simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using h
  have hqinv0 : (fun x => ((a⁻¹ : ℝ) : EReal) * q x) ≤ 0 := by
    intro x
    change ((a⁻¹ : ℝ) : EReal) * q x ≤ (0 : EReal)
    have hq0 : q x ≤ (0 : EReal) := iSingularityEnvelope_le_zero (a • θ).val au x
    simpa only [mul_zero] using
      mul_le_mul_of_nonneg_left hq0 (EReal.coe_nonneg.mpr hai.le)
  have hIinv : IEquivalentOnManifold (n := n)
      (fun x => ((a⁻¹ : ℝ) : EReal) * q x) u := by
    have h : IEquivalentOnManifold (n := n)
        (fun x => ((a⁻¹ : ℝ) : EReal) * q x)
        (fun x => ((a⁻¹ : ℝ) : EReal) * au x) :=
      ⟨iOrderOnManifold_smul hIq.1 hai, iOrderOnManifold_smul hIq.2 hai⟩
    simpa only [au, hcancel u] using h
  have hinv : (fun x => ((a⁻¹ : ℝ) : EReal) * q x) ≤ p :=
    le_iSingularityEnvelope hqinv hqinv0 hIinv
  apply le_antisymm
  · intro x
    have h := mul_le_mul_of_nonneg_left (hinv x) (EReal.coe_nonneg.mpr ha.le)
    simpa only [MultiplierIdealWeightLowerBound.coe_mul_coe_mul,
      mul_inv_cancel₀ ha.ne', EReal.coe_one, one_mul] using h
  · exact hlow

end

end SGPT.Foundations.Analysis.Pending.ActualIEnvelopePositiveScaling
