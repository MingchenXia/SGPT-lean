import SGPT.Bergman.SiuNativeSectionMetric
import SGPT.BDivisor.CurrentPushforward
import SGPT.Foundations.Analysis.Pending.GenuineFullStrongGlobalPairing
import SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
import SGPT.Foundations.Analysis.Pending.MeteredDivisorPositivity

/-! The actual original metered/native section divisor current has its
actual smooth Chern period on every complementary dd-c closed span form. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending StronglyPositiveForms ProductTestForms
open LocalProductCurrents CurrentPairing _root_.SGPT.Foundations.Analysis.LocalCurrents
open GlobalCurrents CanonicalCurrentFrame CanonicalComplementaryCurrentTests
open CanonicalDDCFullTestTranspose LelongPoincareDivisor ChartPartition
open ActualCompactGlobalPairingCalibration GenuineSingularDdcFunctional
open GenuineFullStrongGlobalPairing SingularTopFormLocalization XiaoChartLocalization
open ScalarFullTestTranspose XiaoComplexDifferential
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.BDivisor.NSKodaira SGPT.Bergman.NativeHermitianMetric SGPT.PSH.GlobalL2
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft

/-- Literal original complementary degree; no cycle or pairing information. -/
theorem divisorPeriodComplement (m : ℕ) :
    2 * m = Module.finrank ℝ (ComplexModel (m + 1)) -
      (degreeTwo (Nat.succ_pos m)).val := by
  change 2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2
  rw [SGPT.Foundations.Analysis.FirstPass.complexModel_real_finrank]
  omega

private theorem period_cast_coeff {N : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel N) X] [IsComplexManifold N X]
    {a b : ℕ} (h : a = b) (G : SmoothRealForm N X a)
    (e : ComplexChart N X) (z : ComplexModel N) :
    (h ▸ G : SmoothRealForm N X b).coeff e z = (h ▸ G.coeff e z : RealForm N b) := by
  cases h
  rfl

private theorem period_cast_test {N a b : ℕ} {U : Opens (ComplexModel N)}
    (h : a = b) (α : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm U a)
    (z : ComplexModel N) :
    castTestDegree h α z = (h ▸ α z : RealForm N b) := by
  cases h
  rfl

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

/-- Every genuine full span test reads the original divisor weight by the
literal canonical scalar adjoint, with all normalization factors proved. -/
theorem ddCWeight_castTest_eq_integral
    (E : MeteredEffectiveQDivisor (m + 1) X) (e : ComplexChart (m + 1) X)
    (α : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) (2 * m))
    (hα : ∀ z, α z ∈ formSpan (m + 1) m) :
    (ddCWeight (canonicalBasis (m + 1)) (Nat.succ_pos m) E).inChart e
      (castTestDegree (divisorPeriodComplement m) α) =
        ∫ z, scalarAdjointTest α z * (chartFunction E.weight e z).toReal := by
  change toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
    (chartDDC (canonicalBasis (m + 1)) E.weight e
      (chartLocallyIntegrable_weight (canonicalBasis (m + 1)) E e))
    (castTestDegree (divisorPeriodComplement m) α) = _
  rw [toLocalCurrent_castTestDegree]
  unfold chartDDC
  rw [(wedgePairing_ddC_eq_scalar_full_test _ α hα).1,
    regularDistribution_apply, addHaar_canonicalBasis]

variable [CompactSpace X]

/-- Actual compact LP/Stokes: the original divisor weight contributes zero
on every genuine complementary span form whose actual dd-c is zero.
No current-cohomology or intersection equality is supplied as a premise. -/
theorem pairing_ddCWeight_eq_zero
    (E : MeteredEffectiveQDivisor (m + 1) X) (hE : LocallyNondegenerate E.weight)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan (m + 1) m)
    (hddc : (ddc G).GeometricallyEq 0) :
    pairingLM (ddCWeight (canonicalBasis (m + 1)) (Nat.succ_pos m) E)
      (divisorPeriodComplement m ▸ G) = 0 := by
  classical
  have hu : IsThetaPshPotential E.curvature.val E.weight :=
    ⟨MeteredDivisorPositivity.thetaPlurisubharmonic_weight E, hE⟩
  obtain ⟨L, hzero, hloc⟩ := exists_genuine_singular_ddc_functional E.curvature.val E.weight hu
  obtain ⟨r, χ, idx, hχ, -, hχs, hχc, hχ1⟩ :=
    exists_chartSmooth_partitionOfUnity (n := m + 1)
      (fun x : X => (⟨(complexChartAt (n := m + 1) x).val.source,
        (complexChartAt (n := m + 1) x).val.open_source⟩ : Opens X))
      (fun x => ⟨x, mem_complexChartAt_source x⟩)
  let e (j : Fin r) := complexChartAt (n := m + 1) (idx j)
  let α (j : Fin r) := localizedTensorTest (e j) (χ j) (hχ j) G (hχc j) (hχs j)
  let η (j : Fin r) := castTestDegree (divisorPeriodComplement m) (α j)
  have hα (j : Fin r) (z : ComplexModel (m + 1)) : α j z ∈ formSpan (m + 1) m := by
    change localizedCoeff (e j) (χ j) G z ∈ _
    by_cases hz : z ∈ (e j).val.target
    · rw [localizedCoeff, indicator_of_mem hz]
      exact (formSpan (m + 1) m).smul_mem _ (hG (e j) z hz)
    · rw [localizedCoeff, indicator_of_notMem hz]
      exact (formSpan (m + 1) m).zero_mem
  have hη (j : Fin r) (z : ComplexModel (m + 1)) :
      η j z = (e j).val.target.indicator (fun w => χ j ((e j).val.symm w) •
        ((divisorPeriodComplement m ▸ G : SmoothRealForm (m + 1) X _).coeff (e j) w)) z := by
    rw [period_cast_test]
    change (divisorPeriodComplement m ▸ localizedCoeff (e j) (χ j) G z) = _
    by_cases hz : z ∈ (e j).val.target
    · rw [localizedCoeff, indicator_of_mem hz, indicator_of_mem hz, period_cast_coeff]
      exact (show ∀ {a b : ℕ} (h : a = b) (c : ℝ) (A : RealForm (m + 1) a),
        (h ▸ (c • A) : RealForm (m + 1) b) = c • (h ▸ A) from
          fun {_ _} h c A => by cases h; rfl) _ _ _
    · rw [localizedCoeff, indicator_of_notMem hz, indicator_of_notMem hz]
      exact (show ∀ {a b : ℕ} (h : a = b),
        (h ▸ (0 : RealForm (m + 1) a) : RealForm (m + 1) b) = 0 from
          fun {_ _} h => by cases h; rfl) _
  let A (j : Fin r) := smulFun (χ j) (hχ j) G
  have hsum : (∑ j, A j) = G := by
    apply smoothRealForm_ext
    intro c z
    let ev : SmoothRealForm (m + 1) X (2 * m) →+ RealForm (m + 1) (2 * m) :=
      { toFun := fun H => H.coeff c z
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    rw [show (∑ j, A j).coeff c z = ∑ j, (A j).coeff c z from map_sum ev _ _]
    simp only [A, smulFun_coeff, ← Finset.sum_smul, hχ1, one_smul]
  calc
    _ = ∑ j, (ddCWeight (canonicalBasis (m + 1)) (Nat.succ_pos m) E).inChart (e j) (η j) :=
      pairing_eq_sum _ _ r e χ hχ hχc hχs hχ1 η hη
    _ = ∑ j, L (ddc (A j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (ddCWeight_castTest_eq_integral E (e j) (α j) (hα j)).trans
        (hloc (e j) (χ j) (hχ j) (hχc j) (hχs j) G (hG (e j))).symm
    _ = L (∑ j, ddc (A j)) := (map_sum L _ _).symm
    _ = L (ddc G) := by
      rw [← linearFunctional_congr_of_geometricallyEq L hzero
        (ddc_finset_sum_geometricallyEq Finset.univ A), hsum]
    _ = 0 := hzero _ hddc


/-- The SAME original metered divisor current has its actual original
curvature pairing; its singular weight term cancels by compact Stokes. -/
theorem pairing_meteredDivisor_eq_curvature
    (E : MeteredEffectiveQDivisor (m + 1) X) (hE : LocallyNondegenerate E.weight)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan (m + 1) m)
    (hddc : (ddc G).GeometricallyEq 0) :
    pairingLM (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) E)
      (divisorPeriodComplement m ▸ G) =
    pairingLM (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) E.curvature.val) (divisorPeriodComplement m ▸ G) := by
  rw [integrationCurrent, SGPT.BDivisor.pairingLM_add,
    pairing_ddCWeight_eq_zero E hE G hG hddc, zero_add]

/-- A dense-nonzero actual original section manufactures all divisor and
potential data for the true global LP/Stokes Chern-period identity. This
holds for empty/disconnected manifolds and the whole original divisor. -/
theorem pairing_nativeSectionDivisor_eq_chern
    (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
    (hL : IsSourceSmoothHermitianMetric L)
    (s : HolomorphicSections (n := m + 1) L.Fiber)
    (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)
    (G : SmoothRealForm (m + 1) X (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan (m + 1) m)
    (hddc : (ddc G).GeometricallyEq 0) :
    pairingLM (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
      (nativeSectionDivisorMetric L hL s hdense)) (divisorPeriodComplement m ▸ G) =
    pairingLM (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) (sourceNativeFirstChernForm L hL).val)
      (divisorPeriodComplement m ▸ G) := by
  apply pairing_meteredDivisor_eq_curvature _ _ G hG hddc
  intro x U hU hx
  obtain ⟨y, hy, hsy⟩ := hdense U hU ⟨x, hx⟩
  exact ⟨y, hy, fun h => hsy ((logNormSq_eq_bot_iff (s y)).mp h)⟩

end SGPT.Projective.NumEq
