import SGPT.Trace.OptimalNativeNormalDatum
import SGPT.Trace.BertiniNormalMetric

/-!
# The actual physical normal background datum

The vanishing radius factor is proved from the SAME original normal and
physical section; the literal native pencil supplies its metric bound.
Blueprint: work/sgpt-resume-20261114/bert-e2-native-background/blueprint/bert-e2-native-background.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNativeNormalBackground
open Set Filter Bundle
open scoped Topology Manifold ContDiff InnerProductSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.BertiniNormalMetric

/-- Exact scalar radius derivative, with no division by the actual normal. -/
theorem holDerivSq_original_scalar_radius {n : ℕ} {f : ComplexModel n → ℂ}
    {z : ComplexModel n} (hf : DifferentiableAt ℂ f z) (v : ComplexModel n) :
    holDerivSq (fun y => ‖f y‖ ^ 2) z v = ‖f z‖ ^ 2 * ‖fderiv ℂ f z v‖ ^ 2 := by
  have h := (hasStrictFDerivAt_norm_sq (f z)).hasFDerivAt.comp z
    (hf.restrictScalars ℝ).hasFDerivAt
  have hD (w : ComplexModel n) : fderiv ℝ (fun y => ‖f y‖ ^ 2) z w =
      2 * inner ℝ (f z) (fderiv ℂ f z w) := by
    change fderiv ℝ ((fun x : ℂ => ‖x‖ ^ 2) ∘ f) z w = _
    rw [h.fderiv, hf.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      _root_.smul_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  let a := f z
  let b := fderiv ℂ f z v
  have h1 : inner ℝ a b = (inner ℂ a b).re := real_inner_eq_re_inner ℂ a b
  have h2 : inner ℝ a (Complex.I • b) = -(inner ℂ a b).im := by
    rw [real_inner_eq_re_inner ℂ, inner_smul_right]
    change (Complex.I * inner ℂ a b).re = -(inner ℂ a b).im
    simp only [Complex.I_mul_re]
  have hnorm : ‖inner ℂ a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    rw [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_pow, mul_comm]
  have hsq : ‖inner ℂ a b‖ ^ 2 = (inner ℂ a b).re ^ 2 + (inner ℂ a b).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [holDerivSq, hD, hD, map_smul]
  change ((2 * inner ℝ a b) ^ 2 + (2 * inner ℝ a (Complex.I • b)) ^ 2) / 4 = _
  rw [h1, h2]
  nlinarith

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The literal physical background density retains the genuine R factor. -/
def backgroundDatum (f : X → ℂ) (ε ρ : ℝ) (F : (x : X) → L.Fiber x) (x : X) : ℝ :=
  ε ^ 2 * nativeRadius f x / (ρ ^ 2 * (ε + nativeRadius f x) ^ 4) * ‖F x‖ ^ 2

theorem exact_physical_cutoff_derivative {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    (c : ComplexChart n X) (e : AtlasFrame L) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) {ε : ℝ} (hε : 0 < ε) (v : ComplexModel n) :
    ‖dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v‖ ^ 2 *
        frameNormSq L e (c.val.symm z) =
      ε ^ 2 * nativeRadius f (c.val.symm z) / (ε + nativeRadius f (c.val.symm z)) ^ 4 *
        ‖F (c.val.symm z)‖ ^ 2 * ‖fderiv ℂ (fun y => f (c.val.symm y)) z v‖ ^ 2 := by
  have hfn := differentiableOn_native_normal_chart hf c
  have hfd := (hfn z hz.1).differentiableAt (c.val.open_target.mem_nhds hz.1)
  have hR := contDiffAt_normalRadius c.val.open_target hfn hz.1
  have he : ε + normalRadius (fun y => f (c.val.symm y)) z ≠ 0 :=
    (add_pos_of_pos_of_nonneg hε (sq_nonneg _)).ne'
  have hh := (differentiableOn_original_section_coefficient L hF c e z hz).differentiableAt
    ((isOpen_chartFrameDomain L c e).mem_nhds hz)
  have hscalar := norm_dbarPairing_holo_mul_ofReal_sq hh
    ((contDiffAt_normalCutoff hR hε (sq_nonneg _)).differentiableAt (by simp)) v
  rw [holDerivSq_normalCutoff (hR.differentiableAt (by simp)) he] at hscalar
  unfold normalRadius at hscalar
  rw [holDerivSq_original_scalar_radius hfd v] at hscalar
  have heq : dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v =
      dbarPairing (fun y => chartCoeff L c e F y *
        (normalCutoff ε (nativeRadius f (c.val.symm y)) : ℂ)) z v := by
    rw [dbarPairing_eq_dbarDir, dbarDir_congr_of_eventuallyEq
      (chartCoeff_cutoffSection_eventuallyEq L f ε F c e hz), ← dbarPairing_eq_dbarDir]
  rw [heq]
  simp only [nativeRadius]
  rw [hscalar, norm_sq_eq_frameCoeff e hz.2]
  simp only [chartCoeff, frameCoeff]
  field_simp

/-- Generic physical readback; the actual-pencil theorem below PRODUCES
this original geometric differential bound from the literal family metric. -/
theorem physical_background_datum_of_original_normal_bound {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    (omega : KahlerBackground n X) (c : ComplexChart n X) (e : AtlasFrame L)
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e) {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (v : ComplexModel n)
    (hdf : ‖fderiv ℂ (fun y => f (c.val.symm y)) z v‖ ^ 2 ≤ kahlerQuad omega c z v / ρ ^ 2) :
    ‖dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v‖ ^ 2 *
        frameNormSq L e (c.val.symm z) ≤
      backgroundDatum L f ε ρ F (c.val.symm z) * kahlerQuad omega c z v := by
  rw [exact_physical_cutoff_derivative L hf hF c e hz hε v]
  have hA : 0 ≤ ε ^ 2 * nativeRadius f (c.val.symm z) /
      (ε + nativeRadius f (c.val.symm z)) ^ 4 * ‖F (c.val.symm z)‖ ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  convert mul_le_mul_of_nonneg_left hdf hA using 1 <;>
    first | rfl | (unfold backgroundDatum; field_simp)

variable {N : ℕ} (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1))
  (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))

def normalizedPencilNormal (ρ : ℝ) (q : familyIncidence p i a v U) : ℂ :=
  scalarParameter p i a v U q / (ρ : ℂ)

theorem contMDiff_normalizedPencilNormal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) (ρ : ℝ) :
    letI := familyChartedSpace p i a v U hp hsm
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (normalizedPencilNormal p i a v U ρ) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  have hc := ((ContinuousLinearMap.mul ℂ ℂ).flip (ρ : ℂ)⁻¹).contDiff.contMDiff.comp
    (contMDiff_scalarParameter p i a v U hp hsm)
  change ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
    (fun q => scalarParameter p i a v U q * (ρ : ℂ)⁻¹) at hc
  convert hc using 1
  funext q
  exact div_eq_mul_inv _ _

theorem surjective_mfderiv_normalizedPencilNormal
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    {ρ : ℝ} (hρ : 0 < ρ) (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U hp hsm
    Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ)
      (normalizedPencilNormal p i a v U ρ) q) := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  have heq : normalizedPencilNormal p i a v U ρ = (ρ : ℂ)⁻¹ • scalarParameter p i a v U := by
    funext y
    simp only [normalizedPencilNormal, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, const_smul_mfderiv
    ((contMDiff_scalarParameter p i a v U hp hsm).contMDiffAt.mdifferentiableAt (by simp))]
  intro c
  change ℂ at c
  obtain ⟨w, hw⟩ := surjective_mfderiv_scalarParameter p i a v U hp hsm q ((ρ : ℂ) * c)
  refine ⟨w, ?_⟩
  change (ρ : ℂ)⁻¹ * (show ℂ from
    mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q w) = c
  rw [hw, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hρ.ne'), one_mul]

/-- The actual native pencil discharges the original metric hypothesis;
no derivative or background datum inequality is an input here. -/
theorem actual_pencil_physical_background_datum
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    letI := familyChartedSpace p i a v U hp hsm
    haveI := isComplexManifold_family p i a v U hp hsm
    ∀ (B : HermitianHolomorphicLineBundle.{0, 0} n (familyIncidence p i a v U))
      (F : (q : familyIncidence p i a v U) → B.Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) B.Fiber F univ →
      ∀ (c : ComplexChart n (familyIncidence p i a v U)) (e : AtlasFrame B)
      (z : ComplexModel n), z ∈ chartFrameDomain B c e → ∀ w : ComplexModel n,
      ‖dbarPairing (chartCoeff B c e (cutoffSection B (normalizedPencilNormal p i a v U ρ) ε F)) z w‖ ^ 2 *
        frameNormSq B e (c.val.symm z) ≤
      backgroundDatum B (normalizedPencilNormal p i a v U ρ) ε ρ F (c.val.symm z) *
        kahlerQuad (familyKahlerBackground p i a v U hp hsm omega) c z w := by
  let := familyChartedSpace p i a v U hp hsm
  have := isComplexManifold_family p i a v U hp hsm
  intro B F hF c e z hz w
  exact physical_background_datum_of_original_normal_bound B
    (contMDiff_normalizedPencilNormal p i a v U hp hsm ρ) hF
    (familyKahlerBackground p i a v U hp hsm omega) c e hz hε hρ w
      (norm_sq_scaled_normal_deriv_le p i a v U hp hsm omega hρ c z hz.1 w)

end SGPT.Trace.OptimalNativeNormalBackground
