import SGPT.Projective.NativeCITower
import SGPT.Projective.NumEqDivisorMixedPeriod
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Hodge.SourceSmoothMixedCohomology
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Literal original finite product pullbacks and actual original positive
power Chern periods for fixed whole native CI cuts. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set Bundle
open scoped Topology Distributions Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open ProductTestForms MixedMassClassInvariance NefMixedMass
open LelongPoincareDivisor CanonicalCurrentFrame ActualCompactGlobalPairingCalibration
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.BDivisor.NSKodaira HermitianHolomorphicLineBundle
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

/-- Actual global finite tensor products commute LITERALLY with actual
native holomorphic pullbacks in arbitrary source/target dimensions. -/
theorem pullback_closed_formProd {n k : ℕ} {X Y : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    {g : Y → X} (hg : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ g) :
    ∀ (q : ℕ) (beta : Fin q → ClosedRealOneOneForm n X),
      SmoothRealForm.pullback hg (formProd q (fun i => (beta i).val)) =
        formProd q (fun i => (ClosedRealOneOneForm.pullback hg (beta i)).val) := by
  intro q
  induction q with
  | zero => intro beta; exact pullback_unitForm hg
  | succ q ih =>
      intro beta
      rw [formProd, pullback_wedgeTwo hg, ih]
      rfl

/-- Genuine original mixed-period symmetry moves the final original slot
back to the front by the actual finite cyclic permutation. -/
theorem slotIntegral_snoc_eq_cons {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (κ : KahlerBackground (m + 1) X) (beta : Fin m → ClosedRealOneOneForm (m + 1) X)
    (theta : ClosedRealOneOneForm (m + 1) X) :
    slotIntegral κ (Fin.snoc beta theta) = slotIntegral κ (Fin.cons theta beta) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact slotIntegral_perm κ (Fin.cons theta beta) (finRotate (m + 1))

namespace NativeRegularCut
variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  {L : NativePositiveLine (m + 1) X} (D : NativeRegularCut L)

/-- The actual SAME original power's physical metric is smooth. -/
theorem powerMetricSmooth : IsSourceSmoothHermitianMetric (positivePower L.bundle (D.power - 1)) :=
  sourceNativePositivePower_smooth L.bundle L.smooth (D.power - 1)

/-- The actual original fixed cut produces its whole Cartier divisor's
physical metric, using the SAME cutting section and inherited power norm. -/
def divisorMetric : MeteredEffectiveQDivisor (m + 1) X :=
  nativeSectionDivisorMetric _ D.powerMetricSmooth D.cuttingSection (D.section_dense (Nat.succ_pos m))

/-- The actual original power Chern factor is proved, not supplied as a
chosen intersection or line-bundle comparison certificate. -/
theorem divisorMetric_curvature_geometrically :
    D.divisorMetric.curvature.val.GeometricallyEq ((D.power : ℝ) • L.curvature).val := by
  intro c z hz
  change (sourceNativeFirstChernForm (positivePower L.bundle (D.power - 1))
    D.powerMetricSmooth).val.coeff c z = _
  rw [sourceNativePositivePower_chern_coeff L.bundle L.smooth c hz (D.power - 1),
    Nat.sub_add_cancel D.power_pos,
    sourceNativeFirstChernForm_geometricallyEq L.bundle L.smooth L.own c hz]
  rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual fixed original cut's divisor current has the literal d-fold
ambient mixed Chern period, for every original complementary closed tuple.
No intrinsic curve/current identity or degree equality is a premise. -/
theorem pairing_divisorMetric_eq_power_slotIntegral
    (κ : KahlerBackground (m + 1) X) (beta : Fin m → ClosedRealOneOneForm (m + 1) X) :
    pairingLM (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) D.divisorMetric)
      (divisorPeriodComplement m ▸ formProd m (fun i => (beta i).val)) =
      (D.power : ℝ) * slotIntegral κ (Fin.snoc beta L.curvature) := by
  rw [divisorMetric, pairing_nativeSectionDivisor_eq_slotIntegral κ _ D.powerMetricSmooth
    D.cuttingSection (D.section_dense (Nat.succ_pos m)) beta]
  have hrel := ClosedRealOneOneForm.bottChernRel_of_geometricallyEq D.divisorMetric_curvature_geometrically
  have hslots : ∀ i : Fin (m + 1), ClosedRealOneOneForm.BottChernRel
      ((Fin.snoc beta D.divisorMetric.curvature : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) i)
      ((Fin.snoc beta ((D.power : ℝ) • L.curvature) : Fin (m + 1) → ClosedRealOneOneForm (m + 1) X) i) := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hrel
    · simp only [Fin.snoc_castSucc]
      exact ClosedRealOneOneForm.BottChernRel.refl (beta j)
  change slotIntegral κ (Fin.snoc beta D.divisorMetric.curvature) = _
  rw [slotIntegral_eq_of_bottChernRel κ _ _ hslots]
  simpa only [Fin.update_snoc_last, smul_eq_mul] using
    slotIntegral_update_smul κ (Fin.snoc beta L.curvature) (Fin.last m) (D.power : ℝ) L.curvature

end NativeRegularCut
end SGPT.Projective.NumEq.CompleteIntersections
