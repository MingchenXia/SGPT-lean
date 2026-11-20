import SGPT.Trace.BertiniGlobalOriginalCanonicalAdjunction

/-! Actual all-point normal independence and equality with ORIGINAL local
SliceChart adjunction. Same actual affine defining section is fixed; full
incidence retains the base O_Lambda(1). Holomorphic gluing and Hodge integral
remain distinct downstream assertions. -/

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

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)

theorem nativeBertiniTopForm_zero_in_kernel
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ))
    (α : (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val)
    (hv : ∀ k, nativeBertiniIntrinsicConormal p i ζ y.val y.property (v k) = 0) : α v = 0 := by
  let A := nativeOriginalChartTangentEquiv (complexChartAt (n := d + 1) y.val) y.val
    (mem_complexChartAt_source y.val)
  let : FiniteDimensional ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) := A.symm.finiteDimensional
  apply α.map_linearDependent
  intro hli
  have hdim : Fintype.card (Fin (d + 1)) =
      Module.finrank ℂ (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) := by simpa using A.finrank_eq.symm
  have htop := hli.span_eq_top_of_card_eq_finrank hdim
  have hle : Submodule.span ℂ (Set.range v) ≤
      LinearMap.ker (nativeBertiniIntrinsicConormal p i ζ y.val y.property) :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hv k)
  rw [htop] at hle
  let s := nativeBertiniCoordinateSection p (chartIndex (p y.val)) y.val
  have hz : nativeBertiniIntrinsicConormal p i ζ y.val y.property
      (nativeBertiniNormalLift p i ζ y.val y.property hsm s) = 0 := hle Submodule.mem_top
  rw [nativeBertiniNormalLift_spec] at hz
  exact nativeBertiniCoordinateSection_ne_zero p (chartIndex (p y.val)) y.val
    (mem_affineChart_chartIndex (p y.val)) hz

theorem nativeBertiniContraction_independent
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    ∀ (α : (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ)
      (ν ν' : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val)
      (_hν : nativeBertiniIntrinsicConormal p i ζ y.val y.property ν =
        nativeBertiniIntrinsicConormal p i ζ y.val y.property ν')
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y),
      α (Matrix.vecCons ν (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
        (Subtype.val : member p (affinePoint i ζ) → X) y (v k))) =
      α (Matrix.vecCons ν' (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
        (Subtype.val : member p (affinePoint i ζ) → X) y (v k))) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  intro α ν ν' hν v
  let D := mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
    (Subtype.val : member p (affinePoint i ζ) → X) y
  have hz := nativeBertiniTopForm_zero_in_kernel p i ζ hsm y α
    (Matrix.vecCons (ν - ν') (fun k => D (v k))) (by
      intro k
      cases k using Fin.cases with
      | zero =>
        change nativeBertiniIntrinsicConormal p i ζ y.val y.property (ν - ν') = 0
        rw [map_sub, hν, sub_self]
      | succ k =>
        have h := (nativeBertiniMemberTangentKernelEquiv p i ζ hsm y (v k)).property
        rw [nativeBertiniMemberTangentKernelEquiv_apply] at h
        exact h)
  have hsub : α (Matrix.vecCons (ν - ν') (fun k => D (v k))) =
      α (Matrix.vecCons ν (fun k => D (v k))) - α (Matrix.vecCons ν' (fun k => D (v k))) :=
    congrArg (fun β : (TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val) [⋀^Fin d]→ₗ[ℂ] ℂ =>
      β (fun k => D (v k))) ((α.curryLeft).map_sub ν ν')
  exact sub_eq_zero.mp (hsub.symm.trans hz)

variable [CompactSpace X]

theorem nativeBertiniAdjunctionFiberEquiv_any_normal
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (y : member p (affinePoint i ζ)) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ (α : (nativeCanonicalBundle (n := d + 1) (X := X)).Fiber y.val)
      (w : (nativeBertiniHyperplaneBundle p).Fiber y.val)
      (ν : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) y.val)
      (_hν : nativeBertiniIntrinsicConormal p i ζ y.val y.property ν = w)
      (v : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) y),
      nativeCanonicalFiberEquiv (n := d) y
        (nativeBertiniAdjunctionFiberEquiv p i ζ hsm y (α ⊗ₜ[ℂ] w)) v =
      nativeCanonicalFiberEquiv (n := d + 1) y.val α
        (Matrix.vecCons ν (fun k => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
          (Subtype.val : member p (affinePoint i ζ) → X) y (v k))) := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro α w ν hν v
  rw [nativeBertiniAdjunctionFiberEquiv_intrinsic]
  exact nativeBertiniContraction_independent p i ζ hsm y
    (nativeCanonicalFiberEquiv (n := d + 1) y.val α)
    (nativeBertiniNormalLift p i ζ y.val y.property hsm w) ν
    ((nativeBertiniNormalLift_spec p i ζ y.val y.property hsm w).trans hν.symm) v

namespace SliceChart

variable {p} {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalAdjunctionFiberEquiv_eq_global
    (q : (Metric.ball c.ζ₀ c.r) × c.tangentPatch)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i q.1.val)) :
    let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
      by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
    letI := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
    letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
    ∀ T, c.originalSliceAdjunctionFiberEquiv p.contMDiff q hdim T =
      nativeBertiniAdjunctionFiberEquiv p c.i q.1.val hsm (c.originalSliceMemberPoint q) T := by
  dsimp only
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i q.1.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  let := SubmanifoldChartedSpace.chartedSpace (Nat.le_succ d) hdim.1
  let := SubmanifoldChartedSpace.isComplexManifold_chartedSpace (Nat.le_succ d) hdim.1
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i q.1.val)).isCompact
  intro T
  induction T using TensorProduct.induction_on with
  | zero => simp
  | add A B hA hB =>
    have hF := (c.originalSliceAdjunctionFiberEquiv p.contMDiff q hdim).map_add A B
    have hG := (nativeBertiniAdjunctionFiberEquiv p c.i q.1.val hsm (c.originalSliceMemberPoint q)).map_add A B
    exact hF.trans ((congrArg₂ (fun a b => a + b) hA hB).trans hG.symm)
  | tmul α w =>
    apply (nativeCanonicalFiberEquiv (n := d) (c.originalSliceMemberPoint q)).injective
    apply AlternatingMap.ext
    intro v
    rw [nativeBertiniAdjunctionFiberEquiv_intrinsic]
    let ν := nativeBertiniNormalLift p c.i q.1.val (c.tangentPoint q)
      (c.tangentPoint_mem_member q) hsm w
    have hν : c.originalIntrinsicConormal p.contMDiff q ν = w :=
      nativeBertiniNormalLift_spec p c.i q.1.val (c.tangentPoint q) (c.tangentPoint_mem_member q) hsm w
    exact c.originalAdjunctionFiber_any_normal p.contMDiff q hdim α w ν hν v

end SliceChart
end SGPT.Trace.Bertini
