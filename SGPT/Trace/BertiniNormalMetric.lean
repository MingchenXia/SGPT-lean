import SGPT.Trace.BertiniPencilNormal
import SGPT.Trace.TwistedL2Statement
import SGPT.Foundations.Analysis.Pending.FormPullbackCompMixed
import SGPT.Foundations.Analysis.Pending.ProductTestForms

/-!
# The literal normal derivative in the actual native incidence metric

The background norm bound is produced from the original flat-parameter plus
X product restriction, without supplying a derivative-norm certificate.
Blueprint: work/sgpt-resume-20261114/bert-e2-normal-metric/blueprint/bert-e2-normal-metric.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniNormalMetric
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses HolomorphicMaps
open SGPT.Foundations.Analysis.Pending ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.TwistedL2

/-- Flat pullback quadratic values are the squared original chart derivative. -/
theorem flat_pullback_quad {n m : ℕ} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {f : Y → ComplexModel m}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (c : ComplexChart n Y) {z : ComplexModel n} (hz : z ∈ c.val.target)
    (v : ComplexModel n) :
    (SmoothRealForm.pullback hf (flatKahlerForm m)).coeff c z ![v, Complex.I • v] =
      ‖fderiv ℂ (fun y => f (c.val.symm y)) z v‖ ^ 2 := by
  let d := complexChartAt (n := m) (f (c.val.symm z))
  have hzd : z ∈ coordinateDomain f c d := ⟨hz, by
    change f (c.val.symm z) ∈ d.val.source
    exact mem_complexChartAt_source _⟩
  have hmap : coordinateMap f c d = (fun y => f (c.val.symm y)) := by rfl
  rw [SmoothRealForm.pullback_coeff hf (flatKahlerForm m) c d hzd]
  have hvec : (fderiv ℝ (coordinateMap f c d) z) ∘ ![v, Complex.I • v] =
      ![fderiv ℝ (coordinateMap f c d) z v,
        Complex.I • fderiv ℝ (coordinateMap f c d) z v] := by
    funext j
    fin_cases j
    · rfl
    · exact coordinateMap_fderiv_map_smul_complex hf c d hzd Complex.I v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change Kahler.fundamentalFormAlt ((fderiv ℝ (coordinateMap f c d) z) ∘
    ![v, Complex.I • v]) = _
  rw [hvec]
  simp only [Kahler.fundamentalFormAlt_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [show Complex.I • fderiv ℝ (coordinateMap f c d) z v =
    Kahler.complexStructure (fderiv ℝ (coordinateMap f c d) z v) from rfl,
    Kahler.fundamentalForm_complexStructure_self,
    coordinateMap_fderiv_restrictScalars hf c d hzd, hmap]
  rfl

/-- Additivity is equality of the actual pullback forms, including off targets. -/
theorem closed_pullback_add {n m : ℕ} {Y Z : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z] [IsComplexManifold m Z]
    {f : Y → Z} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (a b : ClosedRealOneOneForm m Z) :
    ClosedRealOneOneForm.pullback hf (a + b) =
      ClosedRealOneOneForm.pullback hf a + ClosedRealOneOneForm.pullback hf b := by
  apply ClosedRealOneOneForm.ext
  intro c z
  ext v
  rfl

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
  (U : TopologicalSpace.Opens (ComplexModel 1))

def modelParameter (q : familyIncidence p i a v U) : ComplexModel 1 := q.val.1.val

theorem contMDiff_modelParameter
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞ (modelParameter p i a v U) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  exact OpensRestriction.contMDiff_val U |>.comp (contMDiff_familyProjection p i a v U hp hsm)

/-- Actual coefficient split along the SAME original parameter and X maps. -/
theorem family_form_split
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      (familyKahlerBackground p i a v U hp hsm omega).form.val.coeff c z =
        (SmoothRealForm.pullback (contMDiff_modelParameter p i a v U hp hsm)
          (flatKahlerForm 1)).coeff c z +
        (SmoothRealForm.pullback (contMDiff_snd.comp (contMDiff_familyInclusion p i a v U hp hsm))
          omega.form.val).coeff c z := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz
  have hι := contMDiff_familyInclusion p i a v U hp hsm
  have hP := contMDiff_familyProjection p i a v U hp hsm
  have hfst := FormPullbackCompMixed.pullback_comp_geometricallyEq
    (contMDiff_fst (X := U) (Y := X)) hι (parameterKahlerBackground U).form.val c hz
  have hsnd := FormPullbackCompMixed.pullback_comp_geometricallyEq
    (contMDiff_snd (X := U) (Y := X)) hι omega.form.val c hz
  have hval := FormPullbackCompMixed.pullback_comp_geometricallyEq
    (OpensRestriction.contMDiff_val U) hP (flatKahlerForm 1) c hz
  rw [familyKahlerBackground_form]
  change (ClosedRealOneOneForm.pullback hι
    (ClosedRealOneOneForm.pullback contMDiff_fst (parameterKahlerBackground U).form +
      ClosedRealOneOneForm.pullback contMDiff_snd omega.form)).val.coeff c z = _
  rw [closed_pullback_add]
  change (SmoothRealForm.pullback hι
      (SmoothRealForm.pullback contMDiff_fst (parameterKahlerBackground U).form.val)).coeff c z +
    (SmoothRealForm.pullback hι (SmoothRealForm.pullback contMDiff_snd omega.form.val)).coeff c z = _
  rw [← hfst, ← hsnd]
  congr 1
  exact hval.symm

/-- The actual model parameter derivative is bounded by the native metric. -/
theorem norm_sq_modelParameter_deriv_le
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n,
      ‖fderiv ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z w‖ ^ 2 ≤
        kahlerQuad (familyKahlerBackground p i a v U hp hsm omega) c z w := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w
  have hnonneg := SmoothRealForm.IsSemipositive.pullback
    (contMDiff_snd.comp (contMDiff_familyInclusion p i a v U hp hsm))
      omega.isSemipositive c z hz w
  rw [kahlerQuad, family_form_split p i a v U hp hsm omega c z hz,
    ContinuousAlternatingMap.add_apply,
    flat_pullback_quad (contMDiff_modelParameter p i a v U hp hsm) c hz w]
  linarith

/-- Unique scalar coordinate of the actual parameter has the same bound. -/
theorem norm_sq_scalarParameter_deriv_le
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n,
      ‖fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z w‖ ^ 2 ≤
        kahlerQuad (familyKahlerBackground p i a v U hp hsm omega) c z w := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w
  have hd := coordinateMap_contDiffAt (contMDiff_modelParameter p i a v U hp hsm)
    c (complexChartAt (n := 1) (modelParameter p i a v U (c.val.symm z)))
      ⟨hz, by
        change modelParameter p i a v U (c.val.symm z) ∈
          (complexChartAt (n := 1) (modelParameter p i a v U (c.val.symm z))).val.source
        exact mem_complexChartAt_source _⟩
  have hF : DifferentiableAt ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z :=
    hd.differentiableAt (by simp)
  have he : fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z =
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).comp
        (fderiv ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z) := by
    exact ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).hasFDerivAt.comp z
      hF.hasFDerivAt).fderiv
  rw [he]
  have hb := norm_sq_modelParameter_deriv_le p i a v U hp hsm omega c z hz w
  change ‖(fderiv ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z w) 0‖ ^ 2 ≤ _
  simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_one] using hb

/-- Literal normalized normal tau/rho: exact rho^-2 metric bound. -/
theorem norm_sq_scaled_normal_deriv_le
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) {ρ : ℝ} (hρ : 0 < ρ) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n,
      ‖fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y) / (ρ : ℂ)) z w‖ ^ 2 ≤
        kahlerQuad (familyKahlerBackground p i a v U hp hsm omega) c z w / ρ ^ 2 := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w
  have hd := coordinateMap_contDiffAt (contMDiff_modelParameter p i a v U hp hsm)
    c (complexChartAt (n := 1) (modelParameter p i a v U (c.val.symm z)))
      ⟨hz, by
        change modelParameter p i a v U (c.val.symm z) ∈
          (complexChartAt (n := 1) (modelParameter p i a v U (c.val.symm z))).val.source
        exact mem_complexChartAt_source _⟩
  have hM : DifferentiableAt ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z :=
    hd.differentiableAt (by simp)
  have hF : DifferentiableAt ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).differentiableAt.comp z hM
  have he := (hF.hasFDerivAt.mul_const' (ρ : ℂ)⁻¹).fderiv
  conv_lhs => simp only [div_eq_mul_inv]
  rw [he]
  change ‖fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z w * (ρ : ℂ)⁻¹‖ ^ 2 ≤ _
  rw [← div_eq_mul_inv, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_pow]
  exact div_le_div_of_nonneg_right
    (norm_sq_scalarParameter_deriv_le p i a v U hp hsm omega c z hz w) (sq_nonneg ρ)

end SGPT.Trace.BertiniNormalMetric
