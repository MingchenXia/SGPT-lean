import SGPT.Trace.BertiniFamilyBasePhysical
import SGPT.Trace.BertiniFamilyCanonicalFibres

/-! Actual total canonical Ft is natural under literal smaller-base native
family inclusion, from true scalar/member chain rules and any-normal residue. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

omit [CompactSpace X] in
theorem familyBaseInclusion_scalarDifferential :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ q : familyIncidence p i a v V,
      (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U)
        (familyBaseInclusion p i a v U V hVU q)).comp
        (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
          (nativeFamilyBaseInclusion p i a v U V hVU hsm) q) =
      mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v V) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro q
  exact (mfderiv_comp q
    ((contMDiff_scalarParameter p i a v U p.contMDiff hsm).contMDiffAt.mdifferentiableAt (by simp))
    ((nativeFamilyBaseInclusion p i a v U V hVU hsm).contMDiff.contMDiffAt.mdifferentiableAt (by simp))).symm

omit [CompactSpace X] in
theorem familyBaseInclusion_memberLift (t : V) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    (nativeFamilyBaseInclusion p i a v U V hVU hsm).comp
      (familyMemberLift p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) t) =
      familyMemberLift p i a v U hsm ⟨t.val,hVU t.property⟩ := by
  rfl

omit [CompactSpace X] in
theorem familyBaseInclusion_memberTangent (t : V)
    (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v)
      (familyBaseRestrictedSmoothness p i a v U V hVU hsm t)
    (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
      (nativeFamilyBaseInclusion p i a v U V hVU hsm)
      (familyMemberLift p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) t y)).comp
        (familyMemberTangent p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) t y) =
      familyMemberTangent p i a v U hsm ⟨t.val,hVU t.property⟩ y := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
  exact (mfderiv_comp y
    ((nativeFamilyBaseInclusion p i a v U V hVU hsm).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((familyMemberLift p i a v V hsV t).contMDiff.contMDiffAt.mdifferentiableAt (by simp))).symm

theorem familyBaseInclusion_canonicalNaturality :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (q : familyIncidence p i a v V)
      (A : (familyNativeCanonicalModel p i a v U hsm).Fiber (familyBaseInclusion p i a v U V hVU q)),
      (familyNativeCanonicalFiberEquiv p i a v U hsm (familyBaseInclusion p i a v U V hVU q) A).compLinearMap
        (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
          (nativeFamilyBaseInclusion p i a v U V hVU hsm) q).toLinearMap =
      familyNativeCanonicalFiberEquiv p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) q
        (familyCanonicalBaseFiberEquiv p i a v U V hVU hsm q A) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro q A
  let t := q.val.1
  let tU : U := ⟨t.val,hVU t.property⟩
  let y : member p (affinePoint i (a - t.val 0 • v)) := ⟨q.val.2,q.property⟩
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let D := mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
    (nativeFamilyBaseInclusion p i a v U V hVU hsm) q
  let ell := (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v V) q).toLinearMap
  let nu := familyScalarNormal p i a v V hsV q
  have hnu : ell nu = (1 : ℂ) := familyScalarNormal_spec p i a v V hsV q
  have hnuU : mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U)
      (familyBaseInclusion p i a v U V hVU q) (D nu) = (1 : ℂ) := by
    have h := congrArg (fun L => L nu) (familyBaseInclusion_scalarDifferential p i a v U V hVU hsm q)
    exact h.trans hnu
  let K := familyMemberTangentKernelEquiv p i a v V hsV t y
  let R := conormalResidueLinearEquiv ell nu hnu
  apply R.injective
  ext u
  let z (k : Fin d) : TangentSpace 𝓘(ℂ, ComplexModel d) y := K.symm (u k)
  have hu (k : Fin d) : familyMemberTangent p i a v V hsV t y (z k) = (u k).val := by
    exact congrArg Subtype.val (K.apply_symm_apply (u k))
  have hDu (k : Fin d) : D (u k).val = familyMemberTangent p i a v U hsm tU y (z k) := by
    rw [← hu k]
    exact congrArg (fun L => L (z k)) (familyBaseInclusion_memberTangent p i a v U V hVU hsm t y)
  have htuple : (fun k => D (Matrix.vecCons nu (fun j => (u j).val) k)) =
      Matrix.vecCons (D nu) (fun k => familyMemberTangent p i a v U hsm tU y (z k)) := by
    funext k
    cases k using Fin.cases with
    | zero => rfl
    | succ k => exact hDu k
  change familyNativeCanonicalFiberEquiv p i a v U hsm (familyBaseInclusion p i a v U V hVU q) A
    (fun k => D (Matrix.vecCons nu (fun j => (u j).val) k)) =
    familyNativeCanonicalFiberEquiv p i a v V hsV q A (Matrix.vecCons nu (fun j => (u j).val))
  have hutuple : (fun k => familyMemberTangent p i a v V hsV t y (z k)) = fun k => (u k).val := funext hu
  let J := nativeBertiniAdjunctionFiberEquiv p i (a - t.val 0 • v) (hsV t) y
  have hleft : familyNativeCanonicalFiberEquiv p i a v U hsm
      (familyBaseInclusion p i a v U V hVU q) A
      (Matrix.vecCons (D nu) (fun k => familyMemberTangent p i a v U hsm tU y (z k))) =
      nativeCanonicalFiberEquiv (n := d) y (J A) z :=
    familyNativeCanonicalFiberEquiv_any_normal p i a v U hsm _ A (D nu) hnuU z
  have hright : familyNativeCanonicalFiberEquiv p i a v V hsV q A
      (Matrix.vecCons nu (fun k => familyMemberTangent p i a v V hsV t y (z k))) =
      nativeCanonicalFiberEquiv (n := d) y (J A) z :=
    familyNativeCanonicalFiberEquiv_any_normal p i a v V hsV q A nu hnu z
  exact (congrArg (familyNativeCanonicalFiberEquiv p i a v U hsm
      (familyBaseInclusion p i a v U V hVU q) A) htuple).trans
    (hleft.trans (hright.symm.trans (congrArg
      (fun b => familyNativeCanonicalFiberEquiv p i a v V hsV q A (Matrix.vecCons nu b)) hutuple)))

end SGPT.Trace.BertiniFamilyCanonical
