import SGPT.Trace.BertiniGlobalOriginalTangentSequence

/-! Actual native canonical adjunction fibres at EVERY original smooth
member point. Pointwise normals and tangent kernels are PRODUCED from
original data. Holomorphic gluing and global Hodge integration remain
separate; full incidence retains the base O_Lambda(1) factor. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

/-- Actual original conormal in actual original preferred ambient coordinates,
with actual physical P-frame scalarization. -/
def nativeBertiniCoordinateConormal (y : member p (affinePoint i ζ)) :
    ComplexModel (d + 1) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (((nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
      (mem_affineChart_chartIndex (p y.val))).toLinearMap.comp
      (nativeBertiniIntrinsicConormal p i ζ y.val y.property)).comp
      (nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
        (mem_complexChartAt_source y.val)).symm.toLinearMap)

/-- Actual original produced native normal transported by actual original chart. -/
def nativeBertiniCoordinateNormal
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) : ComplexModel (d + 1) :=
  nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val)
    (nativeBertiniNormalLift p i ζ y.val y.property hsm
      (nativeBertiniCoordinateSection p (chartIndex (p y.val)) y.val))

theorem nativeBertiniCoordinateNormal_spec
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    nativeBertiniCoordinateConormal p i ζ y (nativeBertiniCoordinateNormal p i ζ hsm y) = 1 := by
  change nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
    (mem_affineChart_chartIndex (p y.val))
    (nativeBertiniIntrinsicConormal p i ζ y.val y.property
      ((nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
          (mem_complexChartAt_source y.val)).symm
        ((nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
          (mem_complexChartAt_source y.val))
          (nativeBertiniNormalLift p i ζ y.val y.property hsm
            (nativeBertiniCoordinateSection p (chartIndex (p y.val)) y.val))))) = 1
  rw [LinearEquiv.symm_apply_apply, nativeBertiniNormalLift_spec,
    nativeBertiniCoordinateFiberEquiv_coordinate]

private def intrinsicCoordinateKernelEquiv (y : member p (affinePoint i ζ)) :
    LinearMap.ker (nativeBertiniIntrinsicConormal p i ζ y.val y.property) ≃ₗ[ℂ]
      LinearMap.ker (nativeBertiniCoordinateConormal p i ζ y).toLinearMap := by
  let A := nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val)
  let C := nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
    (mem_affineChart_chartIndex (p y.val))
  exact {
    toFun := fun v => ⟨A v.val, by
      change C (nativeBertiniIntrinsicConormal p i ζ y.val y.property (A.symm (A v.val))) = 0
      rw [LinearEquiv.symm_apply_apply, v.property, map_zero]⟩
    invFun := fun w => ⟨A.symm w.val, by
      apply C.injective
      change C (nativeBertiniIntrinsicConormal p i ζ y.val y.property (A.symm w.val)) = C 0
      have hw : C (nativeBertiniIntrinsicConormal p i ζ y.val y.property (A.symm w.val)) = 0 := w.property
      rw [hw, map_zero]⟩
    left_inv := by intro v; apply Subtype.ext; exact A.symm_apply_apply v.val
    right_inv := by intro w; apply Subtype.ext; exact A.apply_symm_apply w.val
    map_add' := by intro u v; apply Subtype.ext; exact map_add A u.val v.val
    map_smul' := by intro a v; apply Subtype.ext; exact map_smul A a v.val }

/-- Actual original native member tangent to actual scalarized coordinate
conormal kernel, with underlying actual chart composed literal inclusion mfderiv. -/
def nativeBertiniCoordinateTangentKernelEquiv
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    TangentSpace 𝓘(ℂ, ComplexModel d) y ≃ₗ[ℂ]
      LinearMap.ker (nativeBertiniCoordinateConormal p i ζ y).toLinearMap := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  exact (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y).trans (intrinsicCoordinateKernelEquiv p i ζ y)

variable [CompactSpace X]

/-- Produced ACTUAL canonical residue fibre isomorphism at EVERY original member point. -/
def nativeBertiniCanonicalResidue
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val ≃ₗ[ℂ]
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ))).Fiber y := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  exact (nativeCanonicalFiberInChart (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val)).trans
    ((conormalResidueLinearEquiv (nativeBertiniCoordinateConormal p i ζ y).toLinearMap
      (nativeBertiniCoordinateNormal p i ζ hsm y) (nativeBertiniCoordinateNormal_spec p i ζ hsm y)).trans
      ((AlternatingMap.domLCongr ℂ ℂ (Fin d) ℂ (nativeBertiniCoordinateTangentKernelEquiv p i ζ hsm y).symm).trans
        (nativeCanonicalFiberEquiv (n := d) y).symm))

theorem nativeBertiniCanonicalResidue_intrinsic
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y),
      nativeCanonicalFiberEquiv (n := d) y (nativeBertiniCanonicalResidue p i ζ hsm y α) v =
      nativeCanonicalFiberEquiv (n := d + 1) y.val α
        (Matrix.vecCons (nativeBertiniNormalLift p i ζ y.val y.property hsm
          (nativeBertiniCoordinateSection p (chartIndex (p y.val)) y.val))
          (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
            (Subtype.val : member p (affinePoint i ζ) → X) y (v j))) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro α v
  let A := nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val)
  unfold nativeBertiniCanonicalResidue
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  change nativeCanonicalFiberInChart (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val) α
    (Matrix.vecCons (nativeBertiniCoordinateNormal p i ζ hsm y)
      (fun j => (nativeBertiniCoordinateTangentKernelEquiv p i ζ hsm y (v j)).val)) = _
  change nativeCanonicalFiberEquiv (n := d + 1) y.val α
    (fun k => A.symm (Matrix.vecCons (nativeBertiniCoordinateNormal p i ζ hsm y)
      (fun j => (nativeBertiniCoordinateTangentKernelEquiv p i ζ hsm y (v j)).val) k)) = _
  apply congrArg (nativeCanonicalFiberEquiv (n := d + 1) y.val α)
  funext k
  cases k using Fin.cases with
  | zero => exact A.symm_apply_apply _
  | succ k =>
    change A.symm (A ((nativeBertiniMemberTangentKernelEquiv p i ζ hsm y (v k)).val)) = _
    rw [LinearEquiv.symm_apply_apply, nativeBertiniMemberTangentKernelEquiv_apply]
    rfl

/-- Actual global fixed-member normal-line canonical adjunction fibres. -/
def nativeBertiniAdjunctionFiberEquiv
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    TensorProduct ℂ ((nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      ((nativeBertiniHyperplaneBundle p).Fiber y.val) ≃ₗ[ℂ]
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ))).Fiber y := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  exact (TensorProduct.congr (nativeBertiniCanonicalResidue p i ζ hsm y)
    (nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
      (mem_affineChart_chartIndex (p y.val)))).trans (TensorProduct.rid ℂ _)

theorem nativeBertiniAdjunctionFiberEquiv_tmul
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      (w : (nativeBertiniHyperplaneBundle p).Fiber y.val),
      nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w) =
        nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
          (mem_affineChart_chartIndex (p y.val)) w • nativeBertiniCanonicalResidue p i ζ hsm y α := by
  intros
  rfl

theorem nativeBertiniAdjunctionFiberEquiv_intrinsic
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      (w : (nativeBertiniHyperplaneBundle p).Fiber y.val)
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y),
      nativeCanonicalFiberEquiv (n := d) y
        (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)) v =
      nativeCanonicalFiberEquiv (n := d + 1) y.val α
        (Matrix.vecCons (nativeBertiniNormalLift p i ζ y.val y.property hsm w)
          (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
            (Subtype.val : member p (affinePoint i ζ) → X) y (v j))) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro α w v
  let C := nativeBertiniCoordinateFiberEquiv p (chartIndex (p y.val)) y.val
    (mem_affineChart_chartIndex (p y.val))
  let s := nativeBertiniCoordinateSection p (chartIndex (p y.val)) y.val
  have hC : C s = 1 := nativeBertiniCoordinateFiberEquiv_coordinate p _ _ _
  have hw : w = C w • s := by
    apply C.injective
    rw [map_smul, hC, smul_eq_mul, mul_one]
  have hR : nativeBertiniNormalLift p i ζ y.val y.property hsm w =
      C w • nativeBertiniNormalLift p i ζ y.val y.property hsm s := by
    conv_lhs => rw [hw]
    exact map_smul _ _ _
  rw [nativeBertiniAdjunctionFiberEquiv_tmul, map_smul, AlternatingMap.smul_apply,
    nativeBertiniCanonicalResidue_intrinsic, hR, AlternatingMap.map_vecCons_smul]

end SGPT.Trace.Bertini
