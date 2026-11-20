import SGPT.Trace.OptimalNativeNormalBackground

/-!
# Original X positivity in the actual pencil normal kernel

The original pulled X form can vanish in a parameter direction. The actual
joint incidence metric proves its strictness precisely on ker of the SAME
normalized normal, retaining all common base-locus points.
Blueprint: work/sgpt-resume-20261114/bert-e2-relative-geometry/blueprint/bert-e2-relative-geometry.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniRelativeBasePositivity
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses HolomorphicMaps
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.BertiniNormalMetric
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalBackground

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)
  (U : TopologicalSpace.Opens (ComplexModel 1))

/-- Literal quadratic value of the SAME original X form pulled to full incidence. -/
def familyXQuad
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    ComplexChart n (familyIncidence p i a v U) → ComplexModel n → ComplexModel n → ℝ := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  exact fun c z w => (SmoothRealForm.pullback
    (contMDiff_snd.comp (contMDiff_familyInclusion p i a v U hp hsm)) omega.form.val).coeff c z
      ![w, Complex.I • w]

theorem familyXQuad_nonneg
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n, 0 ≤ familyXQuad p i a v U hp hsm omega c z w := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w
  exact SmoothRealForm.IsSemipositive.pullback
    (contMDiff_snd.comp (contMDiff_familyInclusion p i a v U hp hsm))
      omega.isSemipositive c z hz w

/-- The scalar normal kernel is the kernel of the actual one-coordinate model parameter. -/
theorem modelParameter_deriv_zero_of_normal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {ρ : ℝ} (hρ : 0 < ρ) :
    letI := familyChartedSpace p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n,
      fderiv ℂ (fun y => normalizedPencilNormal p i a v U ρ (c.val.symm y)) z w = 0 →
      fderiv ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z w = 0 := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w hdf
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
  have hzscalar : fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z w = 0 := by
    simp only [normalizedPencilNormal, div_eq_mul_inv] at hdf
    rw [he] at hdf
    change fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z w * (ρ : ℂ)⁻¹ = 0 at hdf
    exact (mul_eq_zero.mp hdf).resolve_right (inv_ne_zero (by exact_mod_cast hρ.ne'))
  have hproj : fderiv ℂ (fun y => scalarParameter p i a v U (c.val.symm y)) z =
      (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).comp
        (fderiv ℂ (fun y => modelParameter p i a v U (c.val.symm y)) z) :=
    ((EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).hasFDerivAt.comp z
      hM.hasFDerivAt).fderiv
  rw [hproj] at hzscalar
  ext j
  fin_cases j
  exact hzscalar

/-- Original X positivity follows from the actual joint product metric on ker(df). -/
theorem familyXQuad_pos_on_normal_kernel
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) {ρ : ℝ} (hρ : 0 < ρ) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ w : ComplexModel n, w ≠ 0 →
      fderiv ℂ (fun y => normalizedPencilNormal p i a v U ρ (c.val.symm y)) z w = 0 →
      0 < familyXQuad p i a v U hp hsm omega c z w := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz w hw hdf
  have hzero := modelParameter_deriv_zero_of_normal p i a v U hp hsm hρ c z hz w hdf
  have hpos := kahlerQuad_pos (familyKahlerBackground p i a v U hp hsm omega) c hz hw
  rw [kahlerQuad, family_form_split p i a v U hp hsm omega c z hz,
    ContinuousAlternatingMap.add_apply,
    flat_pullback_quad (contMDiff_modelParameter p i a v U hp hsm) c hz w,
    hzero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hpos
  exact hpos

/-- Quantitative ORIGINAL X curvature gives precisely the needed relative positivity. -/
theorem relative_base_levi_conditions
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (c : ComplexChart n (familyIncidence p i a v U)) (z : ComplexModel n), z ∈ c.val.target →
      ∀ (P : ComplexModel n → ℝ),
      (∀ w : ComplexModel n, κ * familyXQuad p i a v U hp hsm omega c z w ≤ leviForm P z w) →
      (∀ w : ComplexModel n, 0 ≤ leviForm P z w) ∧
      (∀ w : ComplexModel n, w ≠ 0 →
        fderiv ℂ (fun y => normalizedPencilNormal p i a v U ρ (c.val.symm y)) z w = 0 →
        0 < leviForm P z w) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro c z hz P hP
  constructor
  · intro w
    exact (mul_nonneg hκ.le (familyXQuad_nonneg p i a v U hp hsm omega c z hz w)).trans (hP w)
  · intro w hw hdf
    exact (mul_pos hκ (familyXQuad_pos_on_normal_kernel p i a v U hp hsm omega hρ c z hz w hw hdf)).trans_le (hP w)

end SGPT.Trace.BertiniRelativeBasePositivity
