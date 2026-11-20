import SGPT.Projective.NativeMemberCurrentSupport
import SGPT.Projective.NativeMemberInverseWeightedArea
import SGPT.Projective.NativeMemberTestPullback
import SGPT.Projective.NativeRegularMemberConormal
import SGPT.Projective.DivisorNormalShuffleCalibration
import SGPT.Projective.ComplexNormalWedge

/-! Actual SAME weighted native divisor current is intrinsic integration
on the WHOLE regular member. Blueprint: `native-member-local-inclusion.tex`.
No target current/integral identity is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.BDivisor.NSKodaira
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms StronglyPositiveForms
open ActualCompactGlobalPairingCalibration IntegrationCurrent TopDegreeDensity
open ConstantFormProducts DivisorRegularLocus DivisorIntegrationCurrent
open _root_.SGPT.Foundations.Analysis.LocalCurrents

private theorem nativeMemberComplement (m : ℕ) :
    2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2 := by
  rw [SGPT.Foundations.Analysis.FirstPass.complexModel_real_finrank]
  omega

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1 + 1)) X] [IsComplexManifold (d + 1 + 1) X]
  [CompactSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1 + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := d + 1 + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)
  (hL : IsSourceSmoothHermitianMetric L)
  (hl : IsSmoothHypersurfaceMember (d + 1 + 1)
    (sourceNativeFiniteSectionProjectiveMap L s hgen) l)

/-- On one genuine original member window the SAME unchanged full
weighted native section current is the intrinsic integral on the ENTIRE
member, for every actual complementary smooth form and any actual member
Kahler background. Only true original domain memberships are assumed. -/
theorem native_member_weighted_pairing_eq_integral :
    let W := member (sourceNativeFiniteSectionProjectiveMap L s hgen) l
    let hW := fun x (hx : x ∈ W) => regularAtDim_member _
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl hx
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ (d + 1)) hW
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ (d + 1)) hW
    letI : MeasurableSpace W := borel W
    letI : BorelSpace W := ⟨rfl⟩
    letI : CompactSpace W := wholeMember_compact _
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
    let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (d + 1)) hW
    ∀ (E : AtlasFrame L) (c : ComplexChart (d + 1 + 1) X)
      (x₀ : ComplexModel (d + 1 + 1))
      (P : RegularPresentation
        (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm) x₀)
      (_hPm : P.m = 1) (e : ComplexChart (d + 1) W)
      (χ : X → ℝ) (hχ : ChartSmooth (n := d + 1 + 1) χ)
      (_hχc : IsCompact (tsupport χ))
      (_hχdom : tsupport χ ⊆ E.val.baseSet ∩ c.val.source)
      (_hχeP : ∀ y : W, y.1 ∈ tsupport χ → y ∈ e.val.source ∧ c.val y.1 ∈ P.U)
      (γ : SmoothRealForm (d + 1 + 1) X (2 * (d + 1)))
      (κW : KahlerBackground (d + 1) W),
      pairingLM
        (integrationCurrent (canonicalBasis (d + 1 + 1)) (Nat.succ_pos (d + 1))
          (nativeSectionDivisorMetric L hL (linearSection L s l)
            (linearSection_dense_nonzero (Nat.succ_pos (d + 1)) L s hgen l
              (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl)))
        (smulFun χ hχ (nativeMemberComplement (d + 1) ▸ γ)) =
          ∫ y : W, topRatio κW.form.val (SmoothRealForm.pullback hι (smulFun χ hχ γ)) y
            ∂(kahlerVolume κW) := by
  let W := member (sourceNativeFiniteSectionProjectiveMap L s hgen) l
  let hW := fun x (hx : x ∈ W) => regularAtDim_member _
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl hx
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ (d + 1)) hW
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ (d + 1)) hW
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let : CompactSpace W := wholeMember_compact _
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) l
  let hι := SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ (d + 1)) hW
  dsimp only
  intro E c x₀ P hPm e χ hχ hχc hχdom hχeP γ κW
  let S := linearSection L s l
  let hs := linearSection_dense_nonzero (Nat.succ_pos (d + 1)) L s hgen l
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl
  let Q := nativeSectionFramePresentation L hL S hs E
  let q := Module.finrank ℝ (ComplexModel (d + 1 + 1)) - 2
  let hcomp : 2 * (d + 1) = q := nativeMemberComplement (d + 1)
  let g := sectionCoefficient L.Fiber E.val S ∘ c.val.symm
  obtain ⟨η, hη, _hηsupport, hcurrent⟩ := exists_native_member_current_area_support
    L s hgen l hL hl E c χ hχ hχc hχdom (nativeMemberComplement (d + 1) ▸ γ)
  change _ = ∫ y in c.val '' (W ∩ tsupport χ),
    divisorShuffleDensity g
      (currentPairingBasis (canonicalBasis (d + 1 + 1)) (degreeTwo (Nat.succ_pos (d + 1))))
        η y ∂(μHE[2 * (d + 1 + 1) - 2] : Measure (ComplexModel (d + 1 + 1))) at hcurrent
  obtain ⟨A, hAG, harea⟩ := exists_native_member_weighted_area_with_inverse
    (Nat.le_succ (d + 1)) hW κW e c χ hχ hχc
      (fun x hx => (hχdom hx).2) (fun y hy => (hχeP y hy).1)
  rw [hcurrent, harea γ]
  have hmeasure : 2 * (d + 1 + 1) - 2 = 2 * (d + 1) := by omega
  rw [hmeasure]
  have hY : IsCompact (c.val '' (W ∩ tsupport χ)) := by
    have hWclosed := isClosed_member _
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen).continuous l
    exact (hχc.inter_left hWclosed).image_of_continuousOn
      (c.val.continuousOn.mono (fun _ hx => (hχdom hx.2).2))
  apply setIntegral_congr_fun hY.measurableSet
  rintro y ⟨w, ⟨hwW, hwχ⟩, rfl⟩
  let wW : W := ⟨w, hwW⟩
  let z := e.val wW
  let G := coordinateMap (Subtype.val : W → X) e c
  have hwE : w ∈ E.val.baseSet := (hχdom hwχ).1
  have hwc : w ∈ c.val.source := (hχdom hwχ).2
  have hwe : wW ∈ e.val.source := (hχeP wW hwχ).1
  have hwp : c.val w ∈ P.U := (hχeP wW hwχ).2
  have heinv : e.val.symm z = wW := e.val.left_inv hwe
  have hz : z ∈ coordinateDomain (Subtype.val : W → X) e c := by
    refine ⟨e.val.map_source hwe, ?_⟩
    change ((e.val.symm z : W) : X) ∈ c.val.source
    rw [heinv]
    exact hwc
  have hGz : G z = c.val w := by
    change c.val ((e.val.symm z : W) : X) = c.val w
    rw [heinv]
  have hAz : A (c.val w) = z := by
    rw [← hGz]
    exact hAG z hz
  dsimp only
  rw [hAz]
  have hzE : ((e.val.symm z : W) : X) ∈ E.val.baseSet := by
    simpa only [heinv] using hwE
  have hzP : G z ∈ P.U := by rwa [hGz]
  obtain ⟨_hDi, hℓ, hker, hdensity⟩ := native_member_conormal_density
    L s hgen l hl e c E x₀ P hPm z hz hzE hzP
  let D := fderiv ℂ G z
  let ℓ := fderiv ℂ P.h (G z)
  have hGd : DifferentiableAt ℂ G z :=
    (coordinateMap_contDiffAt hι e c hz).differentiableAt (by simp)
  have hDR : fderiv ℝ G z = D.restrictScalars ℝ := hGd.fderiv_restrictScalars ℝ
  have hnz : (fderiv ℝ G z : ComplexModel (d + 1) →ₗ[ℝ]
      ComplexModel (d + 1 + 1)).normDet ≠ 0 :=
    ((LinearMap.normDet_ne_zero_tfae _).out 0 4).mpr
      (SubmanifoldKahlerRestriction.injective_fderiv_coordinateMap_val
        (Nat.le_succ (d + 1)) hW e c z hz)
  have hβ : ∀ u v : ComplexModel (d + 1 + 1),
      ComplexNormalForm.normalForm ℓ ![u, v] = divisorDensity g u v (c.val w) := by
    intro u v
    rw [ComplexNormalForm.normalForm_pair]
    exact (hdensity u v).symm.trans (congrArg (divisorDensity g u v) hGz)
  have hshuffle := divisorShuffleDensity_eq_topDensity_standard g η (c.val w)
    (ComplexNormalForm.normalForm ℓ) hβ hcomp
  have hlinear : ((D.restrictScalars ℝ).toLinearMap).normDet *
      topDensity (wedgeTo (by omega : 2 + 2 * (d + 1) = 2 * (d + 1 + 1))
        (ComplexNormalForm.normalForm ℓ) (castForm hcomp.symm (η (c.val w)))) =
      topDensity ((castForm hcomp.symm (η (c.val w))).compContinuousLinearMap
        (D.restrictScalars ℝ)) := by
    exact ComplexNormalWedge.normal_wedge_area ℓ hℓ D hker _
  have hpull := native_weighted_test_pullback_coeff (Nat.le_succ (d + 1)) hW
    e c χ hχ γ q hcomp (Q.chartDomain c) η hη z hz
  have hpull' : topDensity ((SmoothRealForm.pullback hι (smulFun χ hχ γ)).coeff e z) =
      topDensity ((castForm hcomp.symm (η (c.val w))).compContinuousLinearMap
        (D.restrictScalars ℝ)) := by
    rw [hpull, hDR]
    change topDensity ((castForm hcomp.symm (η (G z))).compContinuousLinearMap
      (D.restrictScalars ℝ)) = _
    rw [hGz]
  change divisorShuffleDensity g
    (currentPairingBasis (canonicalBasis (d + 1 + 1)) (degreeTwo (Nat.succ_pos (d + 1))))
      η (c.val w) = _
  rw [hshuffle, hpull', hDR]
  apply (eq_div_iff (by simpa only [hDR] using hnz)).mpr
  exact (mul_comm _ _).trans hlinear

end SGPT.Projective.NumEq.CompleteIntersections
