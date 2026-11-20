import SGPT.Trace.BertiniFamilyCanonicalModel
import SGPT.Trace.BertiniGlobalOriginalTangentSequence
import SGPT.Trace.BertiniPencilNormal

/-! Actual original member lift and exact native vertical tangent kernel.
No compactness is required on the original open incidence family. -/

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
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def familyMemberLift (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
      (member p (affinePoint i (a - t.val 0 • v))) (familyIncidence p i a v U) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let g : member p (affinePoint i (a - t.val 0 • v)) → familyIncidence p i a v U :=
    fun y => ⟨(t, y.val), y.property⟩
  refine ⟨g, ?_⟩
  intro y
  apply contMDiffAt_familyLift p i a v U p.contMDiff hsm
  exact (contMDiff_prodMk contMDiff_const
    (SubmanifoldChartedSpace.contMDiff_val (Nat.le_succ d)
      (nativeBertiniMemberRegularity p i (a - t.val 0 • v) (hsm t)))).contMDiffAt

theorem familyMemberLift_at (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    letI := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
    familyMemberLift p i a v U hsm q.val.1 ⟨q.val.2, q.property⟩ = q := by
  apply Subtype.ext
  rfl

def familyMemberTangent (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    TangentSpace 𝓘(ℂ, ComplexModel d) y →L[ℂ]
      TangentSpace 𝓘(ℂ, ComplexModel (d + 1)) (familyMemberLift p i a v U hsm t y) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  exact mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
    (familyMemberLift p i a v U hsm t) y

theorem familyMemberTangent_X (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
      (familyNativeXMap p i a v U hsm) (familyMemberLift p i a v U hsm t y)).comp
      (familyMemberTangent p i a v U hsm t y) =
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel (d + 1))
        (Subtype.val : member p (affinePoint i (a - t.val 0 • v)) → X) y := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  exact (mfderiv_comp y ((familyNativeXMap p i a v U hsm).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((familyMemberLift p i a v U hsm t).contMDiff.contMDiffAt.mdifferentiableAt (by simp))).symm

theorem familyMemberTangent_parameter (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ)
      (scalarParameter p i a v U) (familyMemberLift p i a v U hsm t y)).comp
      (familyMemberTangent p i a v U hsm t y) = 0 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  have h := mfderiv_comp y
    ((contMDiff_scalarParameter p i a v U p.contMDiff hsm).contMDiffAt.mdifferentiableAt (by simp))
    ((familyMemberLift p i a v U hsm t).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have heq : (scalarParameter p i a v U ∘ familyMemberLift p i a v U hsm t) = fun _ => t.val 0 := rfl
  rw [heq, mfderiv_const] at h
  exact h.symm

theorem familyMemberTangent_injective (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    Function.Injective (familyMemberTangent p i a v U hsm t y) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  intro u w huw
  apply nativeBertiniMemberInclusion_injective p i (a - t.val 0 • v) (hsm t) y
  have h := congrArg
    (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (d + 1))
      (familyNativeXMap p i a v U hsm) (familyMemberLift p i a v U hsm t y)) huw
  have hX := familyMemberTangent_X p i a v U hsm t y
  exact ((congrArg (fun A => A u) hX).symm.trans h).trans (congrArg (fun A => A w) hX)

private def actualVerticalKernelEquiv {d : ℕ}
    (D : ComplexModel d →L[ℂ] ComplexModel (d + 1)) (hD : Function.Injective D)
    (ℓ : ComplexModel (d + 1) →L[ℂ] ℂ) (hs : Function.Surjective ℓ)
    (hzero : ℓ.comp D = 0) : ComplexModel d ≃ₗ[ℂ] LinearMap.ker ℓ.toLinearMap := by
  let R : ComplexModel d →ₗ[ℂ] LinearMap.ker ℓ.toLinearMap :=
    D.toLinearMap.codRestrict (LinearMap.ker ℓ.toLinearMap) (by
      intro v
      exact congrArg (fun A : ComplexModel d →L[ℂ] ℂ => A v) hzero)
  have hi : Function.Injective R := by
    intro u v huv
    exact hD (congrArg Subtype.val huv)
  have hdim := ℓ.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at hdim
  have hdim' : Module.finrank ℂ (ComplexModel d) =
      Module.finrank ℂ (LinearMap.ker ℓ.toLinearMap) := by
    simp at hdim ⊢
    exact (Nat.add_left_cancel (hdim.trans (Nat.add_comm d 1))).symm
  exact LinearEquiv.ofBijective R
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').mp hi⟩

def familyMemberTangentKernelEquiv (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    TangentSpace 𝓘(ℂ, ComplexModel d) y ≃ₗ[ℂ]
      LinearMap.ker (mfderiv 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ℂ)
        (scalarParameter p i a v U) (familyMemberLift p i a v U hsm t y)).toLinearMap := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  exact actualVerticalKernelEquiv (familyMemberTangent p i a v U hsm t y)
    (familyMemberTangent_injective p i a v U hsm t y) _
    (surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm _)
    (familyMemberTangent_parameter p i a v U hsm t y)

theorem familyMemberTangentKernelEquiv_apply (t : U) (y : member p (affinePoint i (a - t.val 0 • v))) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    ∀ u : TangentSpace 𝓘(ℂ, ComplexModel d) y,
      (familyMemberTangentKernelEquiv p i a v U hsm t y u).val =
        familyMemberTangent p i a v U hsm t y u := by
  intros
  rfl

end SGPT.Trace.BertiniFamilyCanonical
