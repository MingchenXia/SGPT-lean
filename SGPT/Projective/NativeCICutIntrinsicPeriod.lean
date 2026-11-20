import SGPT.Projective.NativeMemberWholeInclusion
import SGPT.Projective.NativeCITowerPeriodBase

/-! The actual original whole regular cut's intrinsic mixed period,
deduced from genuine full native current geometry and genuine LP/Stokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle MeasureTheory
open scoped Topology Distributions Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open ProductTestForms MixedMassClassInvariance NefMixedMass
open LelongPoincareDivisor CanonicalCurrentFrame ActualCompactGlobalPairingCalibration
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.BDivisor.NSKodaira HermitianHolomorphicLineBundle

namespace NativeRegularCut
variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 2)) X] [IsComplexManifold (m + 2) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {L : NativePositiveLine (m + 2) X} (D : NativeRegularCut L)

/-- The actual intrinsic period on the SAME entire original regular
member is the chosen power times the SAME ambient original Chern period.
The full geometric current identity is a proved theorem, never a premise. -/
theorem slotIntegral_restrict_eq_power
    (κ : KahlerBackground (m + 2) X)
    (beta : Fin (m + 1) → ClosedRealOneOneForm (m + 2) X) :
    let : ChartedSpace (ComplexModel (m + 1)) D.carrier := D.carrierCharts
    let : IsComplexManifold (m + 1) D.carrier := D.carrierComplex
    let : MeasurableSpace D.carrier := borel D.carrier
    let : BorelSpace D.carrier := ⟨rfl⟩
    ∀ κW : KahlerBackground (m + 1) D.carrier,
    slotIntegral κW (fun i => ClosedRealOneOneForm.pullback D.inclusion.contMDiff (beta i)) =
      (D.power : ℝ) * slotIntegral κ (Fin.snoc beta L.curvature) := by
  let : ChartedSpace (ComplexModel (m + 1)) D.carrier := D.carrierCharts
  let : IsComplexManifold (m + 1) D.carrier := D.carrierComplex
  let : MeasurableSpace D.carrier := borel D.carrier
  let : BorelSpace D.carrier := ⟨rfl⟩
  dsimp only
  intro κW
  have hgeometry := native_member_pairing_eq_integral
    (positivePower L.bundle (D.power - 1)) D.powerMetricSmooth
    D.sections D.generated D.hyperplane D.regular
    (formProd (m + 1) (fun i => (beta i).val)) κW
  have hperiod := D.pairing_divisorMetric_eq_power_slotIntegral κ beta
  rw [pullback_closed_formProd D.inclusion.contMDiff (m + 1) beta] at hgeometry
  exact hgeometry.symm.trans hperiod

end NativeRegularCut
end SGPT.Projective.NumEq.CompleteIntersections
