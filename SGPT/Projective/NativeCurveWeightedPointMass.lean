import SGPT.Projective.CurveDivisorPointMass
import SGPT.Projective.NativeSectionWeightedCurrentArea

/-! The FULL actual native global section current against its SAME physical
weighted zero-form has the actual curve zero multiplicity as point mass.
Blueprint: native-curve-weighted-point-mass.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira SGPT.Projective.NumEq.CompleteIntersections
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms ConstantFormProducts
open ActualCompactGlobalPairingCalibration DivisorRegularLocus StronglyPositiveForms
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth
open _root_.SGPT.Foundations.Analysis.LocalCurrents

/-- Literal true complementary degree of the original curve divisor current. -/
theorem curveCurrentComplement : 0 = Module.finrank ℝ (ComplexModel 1) - 2 := by
  rw [SGPT.Foundations.Analysis.FirstPass.complexModel_real_finrank]

private theorem curve_cast_coeff {n a b : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (h : a = b) (G : SmoothRealForm n M a) (c : ComplexChart n M) (z : ComplexModel n) :
    (h ▸ G : SmoothRealForm n M b).coeff c z = castForm h (G.coeff c z) := by
  cases h
  rfl

private theorem curve_uncast_smul {n a b : ℕ} (h : a = b) (r : ℝ) (A : RealForm n a) :
    castForm h.symm (r • castForm h A) = r • A := by
  cases h
  rfl

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel 1) M]
  [IsComplexManifold 1 M] [CompactSpace M]

/-- Actual global FULL current and actual SAME manufactured weighted test count
its literal physical zero; all casts and point normalizations are internal. -/
theorem native_curve_weighted_pairing_point_mass
    (L : HermitianHolomorphicLineBundle.{0,0} 1 M) (hL : IsSourceSmoothHermitianMetric L)
    (s : HolomorphicSections (n := 1) L.Fiber)
    (hdense : ∀ U : Set M, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)
    (e : AtlasFrame L) (c : ComplexChart 1 M) (p : M)
    (hp : p ∈ e.val.baseSet ∩ c.val.source)
    (P : RegularPresentation (sectionCoefficient L.Fiber e.val s ∘ c.val.symm) (c.val p))
    (hPzero : ∀ z ∈ P.U, (sectionCoefficient L.Fiber e.val s ∘ c.val.symm) z = 0 → z = c.val p)
    (χ : M → ℝ) (hχ : ChartSmooth (n := 1) χ) (hχc : IsCompact (tsupport χ))
    (hχdom : tsupport χ ⊆ e.val.baseSet ∩ c.val.source)
    (hχP : ∀ y ∈ tsupport χ, c.val y ∈ P.U)
    (γ : SmoothRealForm 1 M 0) :
    pairingLM (integrationCurrent (canonicalBasis 1) (Nat.succ_pos 0)
      (nativeSectionDivisorMetric L hL s hdense))
      (smulFun χ hχ (curveCurrentComplement ▸ γ)) =
        (P.m : ℝ) * (χ p * (γ.coeff c (c.val p)) ![]) := by
  let Q := nativeSectionFramePresentation L hL s hdense e
  obtain ⟨η, hη, hsupp, harea⟩ := exists_nativeSection_weighted_area_action
    L hL s hdense e c χ hχ hχc hχdom (curveCurrentComplement ▸ γ)
  have hzero : ∀ z ∈ tsupport (η : ComplexModel 1 →
      RealForm 1 (Module.finrank ℝ (ComplexModel 1) - 2)),
      (Q.chartG c ⟨0, by change 0 < 1; omega⟩) z = 0 → z = c.val p := by
    intro z hz hgz
    obtain ⟨y, hy, rfl⟩ := hsupp hz
    exact hPzero _ (hχP y hy) hgz
  have hx : c.val p ∈ Q.chartDomain c := by
    refine ⟨c.val.map_source hp.2, ?_⟩
    change c.val.symm (c.val p) ∈ e.val.baseSet
    rw [c.val.left_inv hp.2]
    exact hp.1
  have hmass := curve_divisorCurrent_point_mass
    (Q.differentiableOn_chartG c ⟨0, by change 0 < 1; omega⟩)
    (Q.frequently_chartG_ne c ⟨0, by change 0 < 1; omega⟩)
    (c.val p) hx P η hzero
  rw [divisorCurrent_wedgePairing_eq_integral] at hmass
  refine harea.trans (hmass.trans ?_)
  congr 1
  have hηp := hη (c.val p)
  rw [indicator_of_mem (c.val.map_source hp.2), c.val.left_inv hp.2,
    curve_cast_coeff] at hηp
  rw [hηp, curve_uncast_smul]
  rfl

end SGPT.Projective.NumEq.AlgebraicCurveDegree
