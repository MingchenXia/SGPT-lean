import SGPT.Trace.BertiniFamilyVerticalTangent
import SGPT.Trace.BertiniGlobalOriginalCanonicalAdjunction

/-! Actual total-family top covectors from original member adjunction and dTau.
No compactness is assumed on the original open family. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyScalarNormal (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact (surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm q (1 : ℂ)).choose

theorem familyScalarNormal_spec (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q
      (familyScalarNormal p i a v U hsm q) = (1 : ℂ) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact (surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm q (1 : ℂ)).choose_spec

variable [CompactSpace X]

def familyNativeCanonicalFiberEquiv (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (familyNativeCanonicalModel p i a v U hsm).Fiber q ≃ₗ[ℂ]
      ((TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q) [⋀^Fin (d + 1)]→ₗ[ℂ] ℂ) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2, q.property⟩
  let J := nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1) y
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  let ell := (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q).toLinearMap
  let nu := familyScalarNormal p i a v U hsm q
  exact ((J.trans (nativeCanonicalFiberEquiv (n := d) y)).trans
    (AlternatingMap.domLCongr ℂ ℂ (Fin d) ℂ K)).trans
    (conormalResidueLinearEquiv ell nu (familyScalarNormal_spec p i a v U hsm q)).symm

theorem familyNativeCanonicalFiberEquiv_contraction
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
    ∀ (A : (familyNativeCanonicalModel p i a v U hsm).Fiber q)
      (u : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))),
      familyNativeCanonicalFiberEquiv p i a v U hsm q A
        (Matrix.vecCons (familyScalarNormal p i a v U hsm q)
          (fun k => familyMemberTangent p i a v U hsm q.val.1
            (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) (u k))) =
      nativeCanonicalFiberEquiv (n := d) (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))
        (nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1)
          (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) A) u := by
  dsimp only
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  intro A u
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2, q.property⟩
  let J := nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1) y
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  let ell := (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q).toLinearMap
  let nu := familyScalarNormal p i a v U hsm q
  let R := conormalResidueLinearEquiv ell nu (familyScalarNormal_spec p i a v U hsm q)
  let psi := (AlternatingMap.domLCongr ℂ ℂ (Fin d) ℂ K) (nativeCanonicalFiberEquiv (n := d) y (J A))
  have h := congrArg (fun b : (LinearMap.ker ell) [⋀^Fin d]→ₗ[ℂ] ℂ => b (fun k => K (u k)))
    (R.apply_symm_apply psi)
  change familyNativeCanonicalFiberEquiv p i a v U hsm q A
    (Matrix.vecCons nu (fun k => (K (u k)).val)) =
    nativeCanonicalFiberEquiv (n := d) y (J A) (fun k => K.symm (K (u k))) at h
  have hcancel : (fun k => K.symm (K (u k))) = u := by
    funext k
    exact K.symm_apply_apply (u k)
  rw [hcancel] at h
  have htuple : (fun k => (K (u k)).val) =
      fun k => familyMemberTangent p i a v U hsm q.val.1 y (u k) := by
    funext k
    rfl
  rw [htuple] at h
  exact h

theorem familyNativeCanonicalFiberEquiv_any_normal
    (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
    ∀ (A : (familyNativeCanonicalModel p i a v U hsm).Fiber q)
      (nu : TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) q)
      (_hnu : mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ)
        (scalarParameter p i a v U) q nu = (1 : ℂ))
      (u : Fin d → TangentSpace 𝓘(ℂ, ComplexModel d) (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))),
      familyNativeCanonicalFiberEquiv p i a v U hsm q A
        (Matrix.vecCons nu (fun k => familyMemberTangent p i a v U hsm q.val.1
          (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) (u k))) =
      nativeCanonicalFiberEquiv (n := d) (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v)))
        (nativeBertiniAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1)
          (⟨q.val.2, q.property⟩ : member p (affinePoint i (a - q.val.1.val 0 • v))) A) u := by
  dsimp only
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  intro A nu hnu u
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2, q.property⟩
  let K := familyMemberTangentKernelEquiv p i a v U hsm q.val.1 y
  let ell := (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ) (scalarParameter p i a v U) q).toLinearMap
  have h := congrArg
    (fun F => F (familyNativeCanonicalFiberEquiv p i a v U hsm q A) (fun k => K (u k)))
    (conormalResidueLinearMap_independent ell nu (familyScalarNormal p i a v U hsm q)
      hnu (familyScalarNormal_spec p i a v U hsm q))
  change familyNativeCanonicalFiberEquiv p i a v U hsm q A
      (Matrix.vecCons nu (fun k => (K (u k)).val)) =
    familyNativeCanonicalFiberEquiv p i a v U hsm q A
      (Matrix.vecCons (familyScalarNormal p i a v U hsm q) (fun k => (K (u k)).val)) at h
  have htuple : (fun k => (K (u k)).val) =
      fun k => familyMemberTangent p i a v U hsm q.val.1 y (u k) := by
    funext k
    rfl
  rw [htuple] at h
  exact h.trans (familyNativeCanonicalFiberEquiv_contraction p i a v U hsm q A u)

end SGPT.Trace.BertiniFamilyCanonical
