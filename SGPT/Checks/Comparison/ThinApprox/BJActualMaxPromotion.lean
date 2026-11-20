import SGPT.Checks.Comparison.ThinApprox.BJFixedRayMax

namespace SGPT.NAPotential.BJ
end SGPT.NAPotential.BJ
namespace SGPT.NAPotential.BJ.AppSeq
end SGPT.NAPotential.BJ.AppSeq
namespace SGPT.NAPotential.BJ.FixedRay
end SGPT.NAPotential.BJ.FixedRay
namespace SGPT.NAPotential.BJ.MaxClosure
end SGPT.NAPotential.BJ.MaxClosure
namespace SGPT.NAPotential.BJ.Pair3ClassStability
end SGPT.NAPotential.BJ.Pair3ClassStability
namespace SGPT.NAPotential.BJ.Pair3Div
end SGPT.NAPotential.BJ.Pair3Div
namespace SGPT.NAPotential.BJ.Printed
end SGPT.NAPotential.BJ.Printed
namespace SGPT.NAPotential.BJ.RationalPromotion
end SGPT.NAPotential.BJ.RationalPromotion
namespace SGPT.NAPotential.BJ.SourceDXZPositive
end SGPT.NAPotential.BJ.SourceDXZPositive
namespace SGPT.NAPotential.BJ.SourceDivUnique
end SGPT.NAPotential.BJ.SourceDivUnique
namespace SGPT.NAPotential.BJ.SourceNet
end SGPT.NAPotential.BJ.SourceNet
namespace SGPT.NAPotential.BJ.SourceRationalPromotion
end SGPT.NAPotential.BJ.SourceRationalPromotion
namespace SGPT.NAPotential.BJCycle
end SGPT.NAPotential.BJCycle
namespace SGPT.NAPotential.BJModel
end SGPT.NAPotential.BJModel
namespace SGPT.NAPotential.ThinApprox.BJ
end SGPT.NAPotential.ThinApprox.BJ
namespace SGPT.NAPotential.ThinApprox.BJ.AppSeq
end SGPT.NAPotential.ThinApprox.BJ.AppSeq
namespace SGPT.NAPotential.ThinApprox.BJ.FixedRay
end SGPT.NAPotential.ThinApprox.BJ.FixedRay
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
end SGPT.NAPotential.ThinApprox.BJ.Pair3ClassStability
namespace SGPT.NAPotential.ThinApprox.BJ.Pair3Div
end SGPT.NAPotential.ThinApprox.BJ.Pair3Div
namespace SGPT.NAPotential.ThinApprox.BJ.Printed
end SGPT.NAPotential.ThinApprox.BJ.Printed
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
end SGPT.NAPotential.ThinApprox.BJ.SourceDXZPositive
namespace SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
end SGPT.NAPotential.ThinApprox.BJ.SourceDivUnique
namespace SGPT.NAPotential.ThinApprox.BJ.SourceNet
end SGPT.NAPotential.ThinApprox.BJ.SourceNet
namespace SGPT.NAPotential.ThinApprox.BJCycle
end SGPT.NAPotential.ThinApprox.BJCycle
namespace SGPT.NAPotential.ThinApprox.BJModel
end SGPT.NAPotential.ThinApprox.BJModel


/-! A prescribed ACTUAL rational Picard class with two true ample gaps
internally produces actual original rational GF data for the pointwise max.
No target line/atlas/metric/index/max-closure certificate is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.ThinApprox.BJ.MaxClosure
open SGPT.NAPotential.BJ.MaxClosure
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.ThinApprox.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.ThinApprox.BJ.Printed
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p]

/-- True canonical class of an actual positive-denominator original line. -/
theorem numericalClass_normalized_line {M : X.Modules} (a : LineBundleAtlas M) (m : ℕ) :
    SGPT.NAPotential.BJ.NativePicard.numericalClass p ((1/(m:ℚ))•rationalPicardClass a)=
      (m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p M (isInvertible_of_atlas a) := by
  rw [SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul,SGPT.NAPotential.BJ.NativePicard.numericalClass_line,
    ← Rat.cast_smul_eq_qsmul ℝ (1/(m:ℚ))]
  simp only [one_div,Rat.cast_inv,Rat.cast_natCast]

/-- Rational scalar extension has its SAME genuine real numerical scalar. -/
theorem numericalClass_rat_smul_real (r : ℚ) (L : RationalPicardSpace X) :
    SGPT.NAPotential.BJ.NativePicard.numericalClass p (r•L)=(r:ℝ)•SGPT.NAPotential.BJ.NativePicard.numericalClass p L := by
  rw [SGPT.NAPotential.BJ.NativePicard.numericalClass_rat_smul]
  exact (Rat.cast_smul_eq_qsmul ℝ r _).symm

variable [IsIntegral X]

/-- Genuine original common-class max producer: target sheaf/presentation,
rational promotions, actual finite maximum and inverse source data are ALL
internally constructed from ordinary actual geometric ample-gap hypotheses. -/
theorem exists_sourceGF_max_of_ample_gaps (D E : SGPT.NAPotential.BJ.Printed.RationalGFPackage X)
    (L : RationalPicardSpace X)
    (hDgap : SGPT.NAPotential.BJ.NativePicard.numericalClass p L-D.numericalClass p∈NativeRealNumericalClasses.ampleCone p)
    (hEgap : SGPT.NAPotential.BJ.NativePicard.numericalClass p L-E.numericalClass p∈NativeRealNumericalClasses.ampleCone p) :
    ∃ F : SGPT.NAPotential.BJ.Printed.RationalGFPackage X,F.numericalClass p=SGPT.NAPotential.BJ.NativePicard.numericalClass p L ∧
      ∀ v : BerkovichPoint p,F.eval p v=max (D.eval p v) (E.eval p v) := by
  obtain ⟨M,a,m,hm,hrep⟩ := exists_actual_line_presentation L
  let hM := isInvertible_of_atlas a
  have hclass : SGPT.NAPotential.BJ.NativePicard.numericalClass p L=
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
  obtain ⟨R,hRatR,hNZR,hEvalR⟩ := SGPT.NAPotential.BJ.SourceRationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    D.toNative D.toNative_nonzero D.toNative_isRational M hM (m:ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGapD
  obtain ⟨S,hRatS,hNZS,hEvalS⟩ := SGPT.NAPotential.BJ.SourceRationalPromotion.exists_rationalRay_of_numerical_ampleGap p
    E.toNative E.toNative_nonzero E.toNative_isRational M hM (m:ℚ)⁻¹
    (inv_nonneg.mpr (Nat.cast_nonneg m)) hGapE
  let W := SGPT.NAPotential.ThinApprox.BJ.FixedRay.maxDatum M hM R S
  have hRatW : W.IsRational := SGPT.NAPotential.ThinApprox.BJ.FixedRay.maxDatum_isRational M hM R S hRatR hRatS
  have hNZW : ∃ q∈W.terms,q.1≠0 := SGPT.NAPotential.ThinApprox.BJ.FixedRay.maxDatum_nonzero M hM p R S hNZR
  let N := FSData.ofRay M hM W
  have hNZ : N.Nonzero := hNZW
  have hRat : N.IsRational := hRatW
  let F := SGPT.NAPotential.BJ.NativeGF.ofNativeRational N hNZ hRat
  refine ⟨F,?_,?_⟩
  · rw [SGPT.NAPotential.BJ.NativeGF.ofNativeRational_numericalClass,FSData.ofRay_numericalClass]
    rw [Rat.cast_inv,Rat.cast_natCast,← hclass]
  · intro v
    rw [SGPT.NAPotential.BJ.NativeGF.ofNativeRational_eval,FSData.ofRay_eval,SGPT.NAPotential.ThinApprox.BJ.FixedRay.maxDatum_eval,
      hEvalR,hEvalS,D.toNative_eval,E.toNative_eval]

end SGPT.NAPotential.ThinApprox.BJ.MaxClosure
