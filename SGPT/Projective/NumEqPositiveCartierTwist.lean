import SGPT.Bergman.SiuNSCartierBundle
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-! Every actual original Cartier divisor can be twisted by one actual
positive native bundle to manufacture a positive bundle of exact own curvature. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.BDivisor.NSKodaira HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

/-- The same actual positive native A and the actual original divisor
metric manufacture A^M tensor O(D), with exact positive original curvature.
No positive twist bundle or Chern/intersection certificate is supplied. -/
theorem exists_positive_native_divisor_twist
    (A : HermitianHolomorphicLineBundle.{0,0} n X) (hA : IsSourceSmoothHermitianMetric A)
    (omega : ClosedRealOneOneForm n X) (hω : IsOwnFirstChernForm A omega) (hK : omega.val.IsKahler)
    (D : EffectiveDivisor n X) (E : MeteredEffectiveQDivisor n X)
    (hE : DivisorMetric.IsDivisorMetric D E) :
    ∃ M : ℕ, 0 < M ∧ ∃ B : HermitianHolomorphicLineBundle.{0,0} n X,
      IsSourceSmoothHermitianMetric B ∧ IsOwnFirstChernForm B (E.curvature + (M : ℝ) • omega) ∧
      (E.curvature + (M : ℝ) • omega).val.IsKahler := by
  let κ : KahlerBackground n X := ⟨omega, hK⟩
  obtain ⟨C, hC, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ E.curvature
  obtain ⟨M, hM⟩ := exists_nat_gt C
  have hM0 : 0 < M := by exact_mod_cast hC.trans hM
  let η := E.curvature + (M : ℝ) • omega
  have hη : η.val.IsKahler := by
    refine ⟨fun c z hz => ⟨η.property.2 c z hz, fun v hv => ?_⟩, η.property.1⟩
    have h1 := hsemi c z hz v
    have h2 := (hK.1 c z hz).2 v hv
    change 0 < η.val.coeff c z ![v, Complex.I • v]
    dsimp only [η]
    simp only [κ, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h1 ⊢
    nlinarith [mul_pos (sub_pos.mpr hM) h2]
  obtain ⟨LD, hLD, hD⟩ := exists_native_divisor_metric D E hE
  let AP := positivePower A (M - 1)
  let hAP := sourceNativePositivePower_smooth A hA (M - 1)
  let B := tensor AP LD
  let hB := sourceNativeTensor_smooth AP LD hAP hLD
  have hM' : M - 1 + 1 = M := Nat.sub_add_cancel hM0
  have hgeo : (sourceNativeFirstChernForm B hB).val.GeometricallyEq η.val := by
    intro c z hz
    rw [sourceNativeTensor_chern_coeff AP LD hAP hLD c hz,
      sourceNativePositivePower_chern_coeff A hA c hz (M - 1), hM',
      sourceNativeFirstChernForm_geometricallyEq A hA hω c hz,
      sourceNativeFirstChernForm_geometricallyEq LD hLD hD c hz]
    simp only [η, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
    exact add_comm _ _
  refine ⟨M, hM0, B, hB, ?_, hη⟩
  intro c e z hz he
  exact (hgeo c hz).symm.trans (sourceNativeFirstChernForm_isOwn B hB c e z hz he)

end SGPT.Projective.NumEq
