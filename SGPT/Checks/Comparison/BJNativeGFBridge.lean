import SGPT.Checks.Comparison.BJNativeLogNorm
import SGPT.Checks.Comparison.BJPrintedAmpleOrder
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalFubiniStudy

/-! Actual original rational GF sheaves/sections/weights produce genuine
native varying-line data with EXACT class and ALL-point value identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.BJ.Printed.RationalGFPackage
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalFubiniStudy
open SGPT.Foundations.Envelope.SchemeGlobalSectionModelNormIsometries
open scoped Classical NNReal ENNReal
variable {X : Scheme.{0}} (D : Printed.RationalGFPackage X)

/-- SAME original section-power line and SAME actual sections/weights/m,
with native invertibility internally produced by the original atlas. -/
def toNative : FSData X where
  line := bundleTensorPower D.line D.n
  invertible := isInvertible_of_atlas (powerAtlas D.atlas D.n)
  m := D.m
  m_pos := D.data.denominator_pos
  terms := Finset.univ.image (fun i : D.data.I => (D.data.sections i,(D.data.weight i:ℝ)))

theorem toNative_nonzero : D.toNative.Nonzero := by
  let i : D.data.I := Classical.choice D.data.nonempty
  exact ⟨(D.data.sections i,(D.data.weight i:ℝ)),
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,D.data.sections_ne_zero i⟩

theorem toNative_isRational : D.toNative.IsRational := by
  intro q hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  exact ⟨D.data.weight i,rfl⟩

variable (p : X ⟶ Spec (.of ℂ)) [IsProjective p]
local instance : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- The EXACT actual canonical numerical class, not a caller class dictionary. -/
theorem toNative_numericalClass : D.toNative.numericalClass p=D.numericalClass p := by
  change (D.m:ℝ)⁻¹•NativeRealNumericalClasses.lineClass p (bundleTensorPower D.line D.n)
      (isInvertible_of_atlas (powerAtlas D.atlas D.n))=
    NativePicard.numericalClass p (gfPicardClass D.atlas D.data)
  rw [gfPicardClass_eq_powerClass,NativePicard.numericalClass_rat_smul,
    NativePicard.numericalClass_line,← Rat.cast_smul_eq_qsmul ℝ]
  simp only [Rat.cast_inv,Rat.cast_natCast]

/-- Literal original finite maximum is retained on ALL source points,
including the trivial point and common-zero polar sets. -/
theorem toNative_eval (v : BerkovichPoint p) :
    D.toNative.eval p (pointEquiv p v)=D.eval p v := by
  change (((D.m:ℝ)⁻¹:ℝ):EReal)*
      (Finset.univ.image (fun i : D.data.I => (D.data.sections i,(D.data.weight i:ℝ)))).sup
        (fun q => ENNReal.log (globalSectionNorm Valuation.one_apply_le_one (pointEquiv p v)
          (bundleTensorPower D.line D.n) (isInvertible_of_atlas (powerAtlas D.atlas D.n)) q.1 : ℝ≥0∞)+
          (q.2:EReal))=
    (((1/(D.m:ℝ)):ℝ):EReal)*(⨆ i : D.data.I,
      sectionLogNorm D.atlas D.n (D.data.sections i) v+((D.data.weight i:ℝ):EReal))
  rw [Finset.sup_image]
  rw [Finset.sup_univ_eq_iSup,one_div]
  congr 1
  apply iSup_congr
  intro i
  exact congrArg (fun z : EReal => z+((D.data.weight i:ℝ):EReal))
    (nativeGlobalSectionLogNorm_eq_source p D.atlas D.n (D.data.sections i) v)

/-- Full original rational GF package now has its genuine native rational
FS membership, with every sheaf/section/class/value output constructed. -/
theorem eval_isNativeRationalFS : NativeNumericalFubiniStudy.IsRationalFS p
    (D.numericalClass p) (fun y => D.eval p ((pointEquiv p).symm y)) := by
  refine ⟨D.toNative,D.toNative_isRational,D.toNative_nonzero,D.toNative_numericalClass p,?_⟩
  intro y
  have h := D.toNative_eval p ((pointEquiv p).symm y)
  simpa only [Equiv.apply_symm_apply] using h.symm

end SGPT.NAPotential.BJ.Printed.RationalGFPackage
