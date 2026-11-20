import SGPT.Checks.Comparison.OperationCurveTransformBounds
import SGPT.Checks.Comparison.OperationSumSliceReader

/-! Actual complete ORIGINAL Legendre transform of the ORIGINAL sum.
Closed interval endpoints are controlled internally; no sum identity premise.
Blueprint: operation-sum-legendre.tex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.OperationComparison
open scoped ENNReal
open Set SGPT.PSH SGPT.NAPotential.BJPrep
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n X)}

/-- The ACTUAL original ordinary test-curve sum has the literal sum of
its ACTUAL original transforms, retaining BOTH cutoff terms internally. -/
theorem curveDivisorialTransform_sum (omega : KahlerBackground n X)
    (C : SourceTestCurve θ) (D : SourceTestCurve σ) (p : PrimePresentation n X)
    {t : ℝ} (ht : 0 < t) :
    curveDivisorialTransform (SourceTestCurve.sum omega C D).toSourceTestCurvePredata p t =
      curveDivisorialTransform C.toSourceTestCurvePredata p t +
        curveDivisorialTransform D.toSourceTestCurvePredata p t := by
  let S := SourceTestCurve.sum omega C D
  obtain ⟨A,hA⟩ := curveDivisorialTransform_finite C.toSourceTestCurvePredata p ht.le
  obtain ⟨B,hB⟩ := curveDivisorialTransform_finite D.toSourceTestCurvePredata p ht.le
  apply le_antisymm
  · rw [hA,hB,← EReal.coe_add]
    refine iSup₂_le fun τ hτ => ?_
    have hν := presentationReader_ne_top (S.thetaPSH ⟨τ,hτ⟩) p
    have hcost : ENNReal.ofReal ((τ-A-B)/t) ≤ presentationReader (S.potential ⟨τ,hτ⟩) p := by
      change ENNReal.ofReal ((τ-A-B)/t) ≤
        presentationReader ((SourceTestCurve.sum omega C D).potential ⟨τ,hτ⟩) p
      rw [presentationReader_sum_potential omega C D ⟨τ,hτ⟩ p]
      refine le_iInf fun r => ?_
      have hCp := (source_test_curve_extension_whole C.toSourceTestCurvePredata).2.2.2 r.1 r.2.2
      have hDr : τ-r.1 ≤ D.max := by have h := r.2.1; linarith
      have hDp := (source_test_curve_extension_whole D.toSourceTestCurvePredata).2.2.2 (τ-r.1) hDr
      have hCn := presentationReader_ne_top hCp p
      have hDn := presentationReader_ne_top hDp p
      have hCb := curveDivisorialTransform_at_le C.toSourceTestCurvePredata p ht.le r.2.2
      have hDb := curveDivisorialTransform_at_le D.toSourceTestCurvePredata p ht.le hDr
      rw [hA,← EReal.coe_ennreal_toReal hCn,← EReal.coe_mul,← EReal.coe_sub] at hCb
      rw [hB,← EReal.coe_ennreal_toReal hDn,← EReal.coe_mul,← EReal.coe_sub] at hDb
      have hCbR := EReal.coe_le_coe_iff.mp hCb
      have hDbR := EReal.coe_le_coe_iff.mp hDb
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨hCn,hDn⟩),
        ENNReal.toReal_add hCn hDn]
      apply (div_le_iff₀ ht).mpr
      nlinarith
    have hcostR := (ENNReal.ofReal_le_iff_le_toReal hν).mp hcost
    change (τ : EReal) - (t : EReal) *
      ((presentationReader (S.potential ⟨τ,hτ⟩) p : ℝ≥0∞) : EReal) ≤ ((A+B : ℝ) : EReal)
    rw [← EReal.coe_ennreal_toReal hν,← EReal.coe_mul,← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    have hmul := (div_le_iff₀ ht).mp hcostR
    nlinarith
  · apply EReal.add_le_of_forall_lt
    intro a ha b hb
    rw [curveDivisorialTransform] at ha hb
    obtain ⟨r,har⟩ := lt_iSup_iff.mp ha
    obtain ⟨hr,har⟩ := lt_iSup_iff.mp har
    obtain ⟨s,hbs⟩ := lt_iSup_iff.mp hb
    obtain ⟨hs,hbs⟩ := lt_iSup_iff.mp hbs
    let τ := r+s
    have hτ : τ < S.max := by change r+s < C.max+D.max; linarith
    have hreader : presentationReader (S.potential ⟨τ,hτ⟩) p ≤
        presentationReader (C.potential ⟨r,hr⟩) p +
          presentationReader (D.potential ⟨s,hs⟩) p := by
      change presentationReader ((SourceTestCurve.sum omega C D).potential ⟨τ,hτ⟩) p ≤ _
      rw [presentationReader_sum_potential omega C D ⟨τ,hτ⟩ p]
      refine iInf_le_of_le (⟨r,by constructor; dsimp only [τ]; linarith; exact hr.le⟩ :
        Icc (τ-D.max) C.max) ?_
      have hdiff : τ-r=s := by dsimp only [τ]; ring
      rw [hdiff,sourceTestCurveAt_of_lt C.toSourceTestCurvePredata hr,
        sourceTestCurveAt_of_lt D.toSourceTestCurvePredata hs]
    have hCn := presentationReader_ne_top (C.thetaPSH ⟨r,hr⟩) p
    have hDn := presentationReader_ne_top (D.thetaPSH ⟨s,hs⟩) p
    have hSn := presentationReader_ne_top (S.thetaPSH ⟨τ,hτ⟩) p
    have hreaderR := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hCn,hDn⟩) hreader
    rw [ENNReal.toReal_add hCn hDn] at hreaderR
    have hterms :
        ((r : EReal) - (t : EReal) * ((presentationReader (C.potential ⟨r,hr⟩) p : ℝ≥0∞) : EReal)) +
          ((s : EReal) - (t : EReal) * ((presentationReader (D.potential ⟨s,hs⟩) p : ℝ≥0∞) : EReal)) ≤
        (τ : EReal) - (t : EReal) * ((presentationReader (S.potential ⟨τ,hτ⟩) p : ℝ≥0∞) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hCn,← EReal.coe_ennreal_toReal hDn,
        ← EReal.coe_ennreal_toReal hSn]
      simp only [← EReal.coe_mul,← EReal.coe_sub,← EReal.coe_add]
      apply EReal.coe_le_coe_iff.mpr
      dsimp only [τ]
      nlinarith [mul_le_mul_of_nonneg_left hreaderR ht.le]
    exact (add_le_add har.le hbs.le).trans
      (hterms.trans (le_curveDivisorialTransform S.toSourceTestCurvePredata p t hτ))

end SGPT.NAPotential.OperationComparison
