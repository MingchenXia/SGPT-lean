import SGPT.Projective.NumEqDivisorGlobalPairing
import SGPT.Foundations.Analysis.Pending.FullNativeGlobalPairingLimits
import SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed
import SGPT.Foundations.Analysis.Pending.NefMixedMass

/-! The original native section divisor current reads the SAME actual
ambient mixed slot integral on the actual closed complementary product. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq
open Set Filter MeasureTheory
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms ProductTestForms
open FirstPass.MongeAmpere FirstPass.HolomorphicIdealSheaves
open LocalProductCurrents CurrentPairing _root_.SGPT.Foundations.Analysis.LocalCurrents
open GlobalCurrents CanonicalCurrentFrame LelongPoincareDivisor
open IntegrationCurrent TopDegreeDensity
open ActualCompactGlobalPairingCalibration FullNativeGlobalPairingLimits
open MixedMassClassInvariance NefMixedMass ConstantFormProducts
open XiaoComplexProducts XiaoComplexDifferential XiaoKahlerPowerClosed
open XiaoGauduchonCrossDensity XiaoGauduchonIntegration XiaoPositiveGauduchonExtension
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.BDivisor.NSKodaira SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle

section Products
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Every actual finite closed real (1,1) product has its literal real
(q,q) tensor type in every original chart. -/
theorem closed_formProd_coeff_mem_formSpan : ∀ (q : ℕ)
    (beta : Fin q → ClosedRealOneOneForm n X) (c : ComplexChart n X)
    (z : ComplexModel n), z ∈ c.val.target →
    (formProd q (fun i => (beta i).val)).coeff c z ∈ formSpan n q
  | 0, _, _, _, _ => mem_formSpan_of_mem_spCone unit_mem_spCone
  | q + 1, beta, c, z, hz =>
    wedge_mem_formSpan (closed_formProd_coeff_mem_formSpan q
      (fun i => beta i.castSucc) c z hz) ((beta (Fin.last q)).property.2 c z hz)

/-- Actual differential closedness is manufactured from the original
closed factors and their actual local potentials, in every tensor degree. -/
theorem closed_formProd_isClosed : ∀ (q : ℕ) (beta : Fin q → ClosedRealOneOneForm n X),
    (formProd q (fun i => (beta i).val)).IsClosed := by
  intro q
  induction q with
  | zero =>
      intro beta c z _
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
        (fderiv ℝ (fun _ : ComplexModel n => (coordinateWedgeUnit : RealForm n 0)) z) = 0
      rw [fderiv_const_apply, map_zero]
  | succ q ih =>
      intro beta c z hz
      let P := formProd q (fun i => (beta i.castSucc).val)
      let B := beta (Fin.last q)
      obtain ⟨W, rho, hzW, hW, hWe, hrho, heq⟩ :=
        LocalPotentials.closedRealOneOne_hasLocalPotentials B c z hz
      have hlocal := extDeriv_wedgeTo_smoothDDC_eq_zero hW hrho
        ((P.smooth c).mono hWe) (fun y hy => ih (fun i => beta i.castSucc) c y (hWe hy)) hzW
      have hgerm : (formProd (q + 1) (fun i => (beta i).val)).coeff c =ᶠ[𝓝 z]
          fun y => wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
            (smoothDDC rho y) (P.coeff c y) := by
        filter_upwards [hW.mem_nhds hzW] with y hy
        change coordinateWedge (P.coeff c y) (B.val.coeff c y) = _
        rw [heq hy]
        exact wedgeTo_comm_of_mem_formSpan
          (closed_formProd_coeff_mem_formSpan q (fun i => beta i.castSucc) c y (hWe hy))
          (B.val.coeff c y) rfl (by omega)
      rw [hgerm.extDeriv_eq]
      exact hlocal

/-- The actual complex second derivative of the SAME closed product is
geometrically zero; this property is produced rather than assumed. -/
theorem closed_formProd_ddc_zero (q : ℕ) (beta : Fin q → ClosedRealOneOneForm n X) :
    (ddc (formProd q (fun i => (beta i).val))).GeometricallyEq 0 := by
  let G := formProd q (fun i => (beta i).val)
  have hinv : (complexTwist G).GeometricallyEq G :=
    complexTwist_geometricallyEq_of_formSpan G (closed_formProd_coeff_mem_formSpan q beta)
  have hdc : (dc G).GeometricallyEq 0 := by
    intro c z hz
    rw [dc_coeff_of_complex_invariant G hinv c hz]
    change (-1 / (4 * Real.pi) : ℝ) • (extDeriv (G.coeff c) z).compContinuousLinearMap
      (modelComplexStructure n) = 0
    rw [closed_formProd_isClosed q beta c z hz]
    ext v
    simp
  intro c z hz
  change extDeriv ((dc G).coeff c) z = 0
  rw [hdc.extDeriv_eqOn c hz]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
    (fderiv ℝ (fun _ : ComplexModel n => (0 : RealForm n (2 * q + 1))) z) = 0
  rw [fderiv_const_apply, map_zero]

end Products


private theorem mixedPeriod_cast_coeff {n a b : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    (h : a = b) (G : SmoothRealForm n X a) (c : ComplexChart n X) (z : ComplexModel n) :
    (h ▸ G : SmoothRealForm n X b).coeff c z = (h ▸ G.coeff c z : RealForm n b) := by
  cases h
  rfl

private theorem mixedPeriod_wedgeTo_cast_right {n p a b r : ℕ}
    (h : a = b) (hab : p + b = r) (hac : p + a = r)
    (A : RealForm n p) (B : RealForm n a) :
    wedgeTo hab A (h ▸ B) = wedgeTo hac A B := by
  cases h
  rfl

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual canonical full native smooth-current pairing is the literal
original smooth Chern wedge integral, with the complementary degree and
commutation of the actual original forms proved internally. -/
theorem pairing_smoothCurrent_eq_smoothPairing
    (κ : KahlerBackground (m + 1) X) (theta : SmoothRealForm (m + 1) X 2)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ c z, z ∈ c.val.target → G.coeff c z ∈ formSpan (m + 1) m) :
    pairingLM (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) theta) (divisorPeriodComplement m ▸ G) =
      smoothPairing κ theta G := by
  rw [pairing_smoothGlobalCurrent_eq_integral κ, smoothPairing_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  let c := complexChartAt (n := m + 1) x
  have hz : c.val x ∈ c.val.target := c.val.map_source (mem_complexChartAt_source x)
  unfold topRatio chartRatio
  congr 1
  rw [exteriorProductTo_coeff, mixedPeriod_cast_coeff,
    mixedPeriod_wedgeTo_cast_right _ _ (by omega : 2 + 2 * m = 2 * (m + 1)),
    wedgeTwo_coeff]
  exact congrArg topDensity ((wedgeTo_comm_of_mem_formSpan (hG c (c.val x) hz)
    (theta.coeff c (c.val x)) rfl (by omega : 2 + 2 * m = 2 * (m + 1))).symm)

/-- The literal original section divisor current pairs with the actual
closed complementary product as the SAME original ambient mixed integral.
All divisor, potential, dd-c cancellation, tensor and normalization data
are manufactured from the actual original native objects. -/
theorem pairing_nativeSectionDivisor_eq_slotIntegral
    (κ : KahlerBackground (m + 1) X)
    (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
    (hL : IsSourceSmoothHermitianMetric L)
    (s : HolomorphicSections (n := m + 1) L.Fiber)
    (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)
    (beta : Fin m → ClosedRealOneOneForm (m + 1) X) :
    pairingLM (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (nativeSectionDivisorMetric L hL s hdense))
      (divisorPeriodComplement m ▸ formProd m (fun i => (beta i).val)) =
        slotIntegral κ (Fin.snoc beta (sourceNativeFirstChernForm L hL)) := by
  rw [pairing_nativeSectionDivisor_eq_chern L hL s hdense _
    (closed_formProd_coeff_mem_formSpan m beta) (closed_formProd_ddc_zero m beta),
    pairing_smoothCurrent_eq_smoothPairing κ _ _ (closed_formProd_coeff_mem_formSpan m beta)]
  rw [smoothPairing_apply]
  have hprod : wedgeTwo (formProd m (fun i => (beta i).val))
      (sourceNativeFirstChernForm L hL).val =
      MixedMassClassInvariance.slotForm (Fin.snoc beta (sourceNativeFirstChernForm L hL)) := by
    unfold MixedMassClassInvariance.slotForm
    rw [formProd]
    congr 1
    · congr 1
      funext i
      simp only [Fin.snoc_castSucc]
    · simp only [Fin.snoc_last]
  rw [hprod]
  rfl

end SGPT.Projective.NumEq
