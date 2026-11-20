import SGPT.Trace.BertiniFamilyBaseCanonical
import SGPT.Trace.BertiniFamilyDensityTransport

/-! Actual cross-family native coordinate determinant, matched density
Jacobian and genuine ordinary coordinate integral base-change. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyBaseCoordinateTangentMap :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q : familyIncidence p i a v V) (_he : q ∈ e.val.source)
    (_hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source),
      ComplexModel (d + 1) →ₗ[ℂ] ComplexModel (d + 1) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f q he hf
  exact
    (nativeOriginalChartTangentEquiv f (familyBaseInclusion p i a v U V hVU q) hf).toLinearMap.comp
        ((mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
          (nativeFamilyBaseInclusion p i a v U V hVU hsm) q).toLinearMap.comp
            (nativeOriginalChartTangentEquiv e q he).symm.toLinearMap)

theorem familyBaseCanonicalCoordinateValue_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q : familyIncidence p i a v V) (he : q ∈ e.val.source)
    (hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source)
    (s : (familyNativeCanonicalModel p i a v U hsm).Fiber (familyBaseInclusion p i a v U V hVU q)),
      familyCanonicalCoordinateValue p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e q he
          (familyCanonicalBaseFiberEquiv p i a v U V hVU hsm q s) =
        LinearMap.det (familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf) *
          familyCanonicalCoordinateValue p i a v U hsm f (familyBaseInclusion p i a v U V hVU q) hf s := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f q he hf s
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let A := nativeOriginalChartTangentEquiv f (familyBaseInclusion p i a v U V hVU q) hf
  let B := nativeOriginalChartTangentEquiv e q he
  let D := mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
    (nativeFamilyBaseInclusion p i a v U V hVU hsm) q
  let M := familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let beta := (AlternatingMap.domLCongr ℂ ℂ (Fin (d + 1)) ℂ A)
    (familyNativeCanonicalFiberEquiv p i a v U hsm (familyBaseInclusion p i a v U V hVU q) s)
  have htuple : (fun k => A.symm (M (b k))) = fun k => D (B.symm (b k)) := by
    funext k
    exact A.symm_apply_apply (D (B.symm (b k)))
  have h := congrArg (fun t : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ => t (M ∘ b))
    (beta.eq_smul_basis_det b)
  change familyNativeCanonicalFiberEquiv p i a v U hsm (familyBaseInclusion p i a v U V hVU q) s
    (fun k => A.symm (M (b k))) = beta b * b.det (M ∘ b) at h
  rw [htuple,Module.Basis.det_comp,Module.Basis.det_self,mul_one] at h
  have hFt := congrArg (fun t => t (fun k => B.symm (b k)))
    (familyBaseInclusion_canonicalNaturality p i a v U V hVU hsm q s)
  change familyNativeCanonicalFiberEquiv p i a v U hsm (familyBaseInclusion p i a v U V hVU q) s
    (fun k => D (B.symm (b k))) =
    familyCanonicalCoordinateValue p i a v V hsV e q he (familyCanonicalBaseFiberEquiv p i a v U V hVU hsm q s) at hFt
  exact hFt.symm.trans (h.trans (mul_comm _ _))

theorem familyBaseCoordinateCanonicalUnit_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q : familyIncidence p i a v V) (he : q ∈ e.val.source)
    (hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source),
      familyCanonicalBaseFiberEquiv p i a v U V hVU hsm q
        (familyCoordinateCanonicalUnit p i a v U hsm f (familyBaseInclusion p i a v U V hVU q) hf) =
        LinearMap.det (familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf) •
          familyCoordinateCanonicalUnit p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e q he := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f q he hf
  apply (familyCanonicalCoordinateEquiv p i a v V
    (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e q he).injective
  rw [familyCanonicalCoordinateEquiv_apply,
    familyBaseCanonicalCoordinateValue_change p i a v U V hVU hsm e f q he hf,
    familyCoordinateCanonicalUnit_value,mul_one,map_smul,familyCanonicalCoordinateEquiv_apply,
    familyCoordinateCanonicalUnit_value,smul_eq_mul,mul_one]

theorem familyBaseMatchedChartDensity_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q : familyIncidence p i a v V) (he : q ∈ e.val.source)
    (hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source),
      familyMatchedChartDensity p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e q he =
        ‖LinearMap.det (familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf)‖ ^ 2 *
          familyMatchedChartDensity p i a v U hsm f (familyBaseInclusion p i a v U V hVU q) hf := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f q he hf
  let det := LinearMap.det (familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf)
  have hu := familyBaseCoordinateCanonicalUnit_change p i a v U V hVU hsm e f q he hf
  have hd : det ≠ 0 := by
    intro hz
    have hz' : LinearMap.det (familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf) = 0 := hz
    rw [hz',zero_smul] at hu
    apply familyCoordinateCanonicalUnit_ne_zero p i a v U hsm f (familyBaseInclusion p i a v U V hVU q) hf
    apply (familyCanonicalBaseFiberEquiv p i a v U V hVU hsm q).injective
    exact hu.trans (map_zero _).symm
  have hn := congrArg norm hu
  rw [LinearIsometryEquiv.norm_map,norm_smul] at hn
  unfold familyMatchedChartDensity
  rw [hn,mul_pow,mul_inv_rev]
  change _ = ‖det‖ ^ 2 * (_ * (‖det‖ ^ 2)⁻¹)
  rw [mul_left_comm,mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)),mul_one]

omit [CompactSpace X] in
private theorem actualBaseCoordinate_fderiv :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q : familyIncidence p i a v V) (he : q ∈ e.val.source)
    (hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source),
      (fderiv ℂ (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) (e.val q)).toLinearMap =
        familyBaseCoordinateTangentMap p i a v U V hVU hsm e f q he hf := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f q he hf
  apply LinearMap.ext
  intro u
  exact coordinateMap_fderiv_fixed_native_charts_apply
    (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f q he hf u

omit [CompactSpace X] in
theorem familyBaseCoordinate_realJacobian :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (z : ComplexModel (d + 1))
    (_hz : z ∈ coordinateDomain (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f),
      |(fderiv ℝ (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) z).det| =
        ‖LinearMap.det (fderiv ℂ (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) z).toLinearMap‖ ^ 2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f z hz
  let F := coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f
  have hF : DifferentiableAt ℂ F z :=
    (coordinateMap_contDiffAt (nativeFamilyBaseInclusion p i a v U V hVU hsm).contMDiff e f hz).differentiableAt (by simp)
  rw [hF.fderiv_restrictScalars ℝ]
  change |LinearMap.det (((fderiv ℂ F z).toLinearMap).restrictScalars ℝ)| = _
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply,
    abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq]

private theorem actualBaseDensity_point_eq :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (q r : familyIncidence p i a v U) (hq : q ∈ f.val.source) (hr : r ∈ f.val.source) (_h : q = r),
      familyMatchedChartDensity p i a v U hsm f q hq = familyMatchedChartDensity p i a v U hsm f r hr := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro f q r hq hr h
  subst r
  rfl

theorem familyBaseMatchedCoordinateDensity_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (z : ComplexModel (d + 1))
    (_hz : z ∈ coordinateDomain (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f),
      familyMatchedCoordinateDensity p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e z =
        |(fderiv ℝ (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) z).det| *
          familyMatchedCoordinateDensity p i a v U hsm f
            (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f z) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f z hz
  let I := nativeFamilyBaseInclusion p i a v U V hVU hsm
  let F := coordinateMap I e f
  let q := e.val.symm z
  have he : q ∈ e.val.source := e.val.map_target hz.1
  have hf : familyBaseInclusion p i a v U V hVU q ∈ f.val.source := hz.2
  have hFz : F z ∈ f.val.target := coordinateMap_mem_target hz
  have hq : f.val.symm (F z) = I q := f.val.left_inv hf
  have hD := actualBaseCoordinate_fderiv p i a v U V hVU hsm e f q he hf
  rw [e.val.right_inv hz.1] at hD
  have hreal := familyBaseCoordinate_realJacobian p i a v U V hVU hsm e f z hz
  rw [hD] at hreal
  unfold familyMatchedCoordinateDensity
  rw [dif_pos hz.1,dif_pos hFz]
  rw [actualBaseDensity_point_eq p i a v U hsm f _ _ _ hf hq]
  rw [familyBaseMatchedChartDensity_change p i a v U V hVU hsm e f q he hf,hreal]

theorem familyBaseMatchedCoordinateIntegral_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v V))
    (f : ComplexChart (d + 1) (familyIncidence p i a v U))
    (A : Set (ComplexModel (d + 1))) (_hA : MeasurableSet A)
    (_hsub : A ⊆ coordinateDomain (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f)
    (w : familyIncidence p i a v U → ℝ≥0∞),
      (∫⁻ z in (coordinateMap (nativeFamilyBaseInclusion p i a v U V hVU hsm) e f) '' A,
        ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm f z) * w (f.val.symm z)) =
        ∫⁻ z in A, ENNReal.ofReal
          (familyMatchedCoordinateDensity p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) e z) *
            w (familyBaseInclusion p i a v U V hVU (e.val.symm z)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  let := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
  intro e f A hA hsub w
  let I := nativeFamilyBaseInclusion p i a v U V hVU hsm
  let F := coordinateMap I e f
  have hderiv : ∀ z ∈ A, HasFDerivWithinAt F (fderiv ℝ F z) A z := by
    intro z hz
    have hF : DifferentiableAt ℂ F z := (coordinateMap_contDiffAt I.contMDiff e f (hsub hz)).differentiableAt (by simp)
    exact (hF.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hI : Function.Injective I := by
    intro q r hqr
    apply (familyBaseTubeHomeomorph p i a v U V hVU).injective
    exact Subtype.ext hqr
  have hinj : InjOn F A := by
    intro z hz t ht hzt
    have h := hI (f.val.injOn (hsub hz).2 (hsub ht).2 hzt)
    calc
      z = e.val (e.val.symm z) := (e.val.right_inv (hsub hz).1).symm
      _ = e.val (e.val.symm t) := congrArg e.val h
      _ = t := e.val.right_inv (hsub ht).1
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv hinj
    (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm f z) * w (f.val.symm z))
  apply h.trans
  apply setLIntegral_congr_fun hA
  intro z hz
  dsimp only
  have hpoint : f.val.symm (F z) = I (e.val.symm z) := f.val.left_inv (hsub hz).2
  rw [hpoint,← mul_assoc,← ENNReal.ofReal_mul (abs_nonneg _),
    ← familyBaseMatchedCoordinateDensity_change p i a v U V hVU hsm e f z (hsub hz)]
  rfl

end SGPT.Trace.BertiniFamilyCanonical
