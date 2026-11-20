import SGPT.Trace.BertiniFamilyMatchedDensity
import SGPT.Trace.NativeCanonicalPhysicalChartIntegral

/-! Literal original-chart Jacobians transport the produced matched density. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
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
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

theorem familyCanonicalCoordinateValue_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (he : q ∈ e.val.source) (hf : q ∈ f.val.source)
      (s : (familyNativeCanonicalModel p i a v U hsm).Fiber q),
      familyCanonicalCoordinateValue p i a v U hsm f q hf s =
        LinearMap.det ((nativeOriginalChartTangentEquiv e q he).toLinearMap.comp
          (nativeOriginalChartTangentEquiv f q hf).symm.toLinearMap) *
        familyCanonicalCoordinateValue p i a v U hsm e q he s := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f q he hf s
  let A := nativeOriginalChartTangentEquiv e q he
  let B := nativeOriginalChartTangentEquiv f q hf
  let b := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis
  let M := A.toLinearMap.comp B.symm.toLinearMap
  let beta := (AlternatingMap.domLCongr ℂ ℂ (Fin (d + 1)) ℂ A)
    (familyNativeCanonicalFiberEquiv p i a v U hsm q s)
  have htuple : (fun k => A.symm (M (b k))) = fun k => B.symm (b k) := by
    funext k
    exact A.symm_apply_apply (B.symm (b k))
  have h := congrArg (fun (t : (ComplexModel (d + 1)) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) => t (M ∘ b))
    (beta.eq_smul_basis_det b)
  change familyNativeCanonicalFiberEquiv p i a v U hsm q s
    (fun k => A.symm (M (b k))) = beta b * b.det (M ∘ b) at h
  rw [htuple, Module.Basis.det_comp, Module.Basis.det_self, mul_one] at h
  exact h.trans (mul_comm _ _)

theorem familyCoordinateCanonicalUnit_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (he : q ∈ e.val.source) (hf : q ∈ f.val.source),
      familyCoordinateCanonicalUnit p i a v U hsm e q he =
        LinearMap.det ((nativeOriginalChartTangentEquiv e q he).toLinearMap.comp
          (nativeOriginalChartTangentEquiv f q hf).symm.toLinearMap) •
        familyCoordinateCanonicalUnit p i a v U hsm f q hf := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f q he hf
  apply (familyCanonicalCoordinateEquiv p i a v U hsm f q hf).injective
  rw [familyCanonicalCoordinateEquiv_apply, familyCanonicalCoordinateValue_change p i a v U hsm e f q he hf,
    familyCoordinateCanonicalUnit_value, mul_one, map_smul, familyCanonicalCoordinateEquiv_apply,
    familyCoordinateCanonicalUnit_value, smul_eq_mul, mul_one]

theorem familyMatchedChartDensity_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U)) (q : familyIncidence p i a v U)
      (he : q ∈ e.val.source) (hf : q ∈ f.val.source),
      familyMatchedChartDensity p i a v U hsm f q hf =
        ‖LinearMap.det ((nativeOriginalChartTangentEquiv e q he).toLinearMap.comp
          (nativeOriginalChartTangentEquiv f q hf).symm.toLinearMap)‖ ^ 2 *
        familyMatchedChartDensity p i a v U hsm e q he := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f q he hf
  let det := LinearMap.det ((nativeOriginalChartTangentEquiv e q he).toLinearMap.comp
    (nativeOriginalChartTangentEquiv f q hf).symm.toLinearMap)
  have hu := familyCoordinateCanonicalUnit_change p i a v U hsm e f q he hf
  have hd : det ≠ 0 := by
    intro hz
    have hz' : LinearMap.det ((nativeOriginalChartTangentEquiv e q he).toLinearMap.comp
      (nativeOriginalChartTangentEquiv f q hf).symm.toLinearMap) = 0 := hz
    rw [hz', zero_smul] at hu
    exact familyCoordinateCanonicalUnit_ne_zero p i a v U hsm e q he hu
  unfold familyMatchedChartDensity
  rw [hu, norm_smul, mul_pow, mul_inv_rev]
  change _ = ‖det‖ ^ 2 * (_ * (‖det‖ ^ 2)⁻¹)
  rw [mul_left_comm, mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)), mul_one]

private theorem actualMatchedDensity_point_eq :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U)) (q r : familyIncidence p i a v U)
      (hq : q ∈ e.val.source) (hr : r ∈ e.val.source) (_h : q = r),
      familyMatchedChartDensity p i a v U hsm e q hq =
        familyMatchedChartDensity p i a v U hsm e r hr := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e q r hq hr h
  subst r
  rfl

theorem familyMatchedCoordinateDensity_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U)) (z : ComplexModel (d + 1))
      (_hz : z ∈ coordinateDomain id f e),
      familyMatchedCoordinateDensity p i a v U hsm f z =
        |(fderiv ℝ (coordinateMap id f e) z).det| *
        familyMatchedCoordinateDensity p i a v U hsm e (coordinateMap id f e z) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f z hz
  let q := f.val.symm z
  have hf : q ∈ f.val.source := f.val.map_target hz.1
  have he : q ∈ e.val.source := hz.2
  have hfq : f.val q = z := f.val.right_inv hz.1
  have het : coordinateMap id f e z ∈ e.val.target := e.val.map_source he
  have heq : e.val.symm (coordinateMap id f e z) = q := e.val.left_inv he
  unfold familyMatchedCoordinateDensity
  rw [dif_pos hz.1, dif_pos het,
    actualMatchedDensity_point_eq p i a v U hsm e _ q _ he heq]
  have h := familyMatchedChartDensity_change p i a v U hsm e f q he hf
  rw [← nativeCanonicalPhysicalTransition_realJacobian e f q he hf, hfq] at h
  exact h

theorem familyMatchedCoordinateIntegral_change :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e f : ComplexChart (d + 1) (familyIncidence p i a v U))
      (A : Set (ComplexModel (d + 1))) (_hA : MeasurableSet A)
      (_hsub : A ⊆ coordinateDomain id f e) (w : familyIncidence p i a v U → ℝ≥0∞),
      (∫⁻ z in (coordinateMap id f e) '' A,
        ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z) * w (e.val.symm z) ∂volume) =
      ∫⁻ z in A, ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm f z) * w (f.val.symm z) ∂volume := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e f A hA hsub w
  let F := coordinateMap id f e
  have hderiv : ∀ z ∈ A, HasFDerivWithinAt F (fderiv ℝ F z) A z := by
    intro z hz
    have hc : DifferentiableAt ℂ F z :=
      (coordinateMap_contDiffAt contMDiff_id f e (hsub hz)).differentiableAt (by simp)
    exact (hc.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn F A := by
    intro z hz t ht hzt
    have h := e.val.injOn (hsub hz).2 (hsub ht).2 hzt
    calc
      z = f.val (f.val.symm z) := (f.val.right_inv (hsub hz).1).symm
      _ = f.val (f.val.symm t) := congrArg f.val h
      _ = t := f.val.right_inv (hsub ht).1
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv hinj
    (fun z => ENNReal.ofReal (familyMatchedCoordinateDensity p i a v U hsm e z) * w (e.val.symm z))
  apply h.trans
  apply setLIntegral_congr_fun hA
  intro z hz
  dsimp only
  have hpoint : e.val.symm (F z) = f.val.symm z := e.val.left_inv (hsub hz).2
  rw [hpoint, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← familyMatchedCoordinateDensity_change p i a v U hsm e f z (hsub hz)]

end SGPT.Trace.BertiniFamilyCanonical
