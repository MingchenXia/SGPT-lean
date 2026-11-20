import SGPT.Checks.LiteratureBridge.BJFixedRayMax

/-! A prescribed ACTUAL rational Picard class with two true ample gaps
internally produces actual original rational GF data for the pointwise max.
No target line/atlas/metric/index/max-closure certificate is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.MaxClosure
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.NativeNumericalFubiniStudy
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- True canonical class of an actual positive-denominator original line. -/
theorem numericalClass_normalized_line {M : X.Modules} (a : LineBundleAtlas M) (m : ℕ) :
    NativePicard.numericalClass p ((1/(m:ℚ))•rationalPicardClass a)=
      (m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p M (isInvertible_of_atlas a) := by
  rw [NativePicard.numericalClass_rat_smul,NativePicard.numericalClass_line,
    ← Rat.cast_smul_eq_qsmul ℝ (1/(m:ℚ))]
  simp only [one_div,Rat.cast_inv,Rat.cast_natCast]

/-- Rational scalar extension has its SAME genuine real numerical scalar. -/
theorem numericalClass_rat_smul_real (r : ℚ) (L : RationalPicardSpace X) :
    NativePicard.numericalClass p (r•L)=(r:ℝ)•NativePicard.numericalClass p L := by
  rw [NativePicard.numericalClass_rat_smul]
  exact (Rat.cast_smul_eq_qsmul ℝ r _).symm

variable [IsIntegral X]

/-- Genuine original common-class max producer: target sheaf/presentation,
rational promotions, actual finite maximum and inverse source data are ALL
internally constructed from ordinary actual geometric ample-gap hypotheses. -/
theorem exists_sourceGF_max_of_ample_gaps (D E : Printed.RationalGFPackage X)
    (L : RationalPicardSpace X)
    (hDgap : NativePicard.numericalClass p L-D.numericalClass p∈NativeRealNumericalClasses.ampleCone p)
    (hEgap : NativePicard.numericalClass p L-E.numericalClass p∈NativeRealNumericalClasses.ampleCone p) :
    ∃ F : Printed.RationalGFPackage X,F.numericalClass p=NativePicard.numericalClass p L ∧
      ∀ v : BerkovichPoint p,F.eval p v=max (D.eval p v) (E.eval p v) := by
  obtain ⟨M,a,m,hm,hrep⟩ := exists_actual_line_presentation L
  let hM := isInvertible_of_atlas a
  have hclass : NativePicard.numericalClass p L=
      (m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p M hM := by
    rw [hrep,numericalClass_normalized_line]
  have hGapD : (((m:ℚ)⁻¹:ℚ):ℝ)•NativeRealNumericalClasses.lineClass p M hM-
      D.toNative.numericalClass p∈NativeRealNumericalClasses.ampleCone p := by
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass,D.toNative_numericalClass]
    exact hDgap
  have hGapE : (((m:ℚ)⁻¹:ℚ):ℝ)•NativeRealNumericalClasses.lineClass p M hM-
      E.toNative.numericalClass p∈NativeRealNumericalClasses.ampleCone p := by
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass,E.toNative_numericalClass]
    exact hEgap
  obtain ⟨R,hRatR,hNZR,hEvalR⟩ := RationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    D.toNative D.toNative_nonzero D.toNative_isRational M hM (m:ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGapD
  obtain ⟨S,hRatS,hNZS,hEvalS⟩ := RationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    E.toNative E.toNative_nonzero E.toNative_isRational M hM (m:ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGapE
  let W := FixedRay.maxDatum M hM R S
  have hRatW : W.IsRational := FixedRay.maxDatum_isRational M hM R S hRatR hRatS
  have hNZW : ∃ q∈W.terms,q.1≠0 := FixedRay.maxDatum_nonzero M hM p R S hNZR
  let N := FSData.ofRay M hM W
  have hNZ : N.Nonzero := hNZW
  have hRat : N.IsRational := hRatW
  let F := NativeGF.ofNativeRational N hNZ hRat
  refine ⟨F,?_,?_⟩
  · rw [NativeGF.ofNativeRational_numericalClass,FSData.ofRay_numericalClass]
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass]
  · intro v
    rw [NativeGF.ofNativeRational_eval,FSData.ofRay_eval,FixedRay.maxDatum_eval,
      hEvalR,hEvalS,D.toNative_eval,E.toNative_eval]

end SGPT.NAPotential.BJ.MaxClosure
