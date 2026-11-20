import SGPT.Trace.BertiniGlobalPhysicalResidueDensity
import SGPT.Trace.NativeCanonicalOpenCoordinateIntegral

/-! Actual full-parameter original member map from the genuine n-1 open tangent domain. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace

def originalMemberCoordinateDelete {d : ℕ} (m : Fin (d + 1)) :
    ComplexModel (d + 1) →L[ℂ] ComplexModel d :=
  LinearMap.toContinuousLinearMap {
    toFun z := WithLp.toLp 2 (fun j => z (m.succAbove j))
    map_add' _ _ := by ext j; rfl
    map_smul' _ _ := by ext j; rfl }

namespace SliceChart
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem originalMemberCoordinateDelete_tangentLift (b : ComplexModel d) :
    originalMemberCoordinateDelete c.m (c.tangentLift b) = b := by
  ext j
  simp [originalMemberCoordinateDelete,tangentLift,tangentCoordinateInsert,Fin.succAbove_ne]

def originalTangentPatchOpen : TopologicalSpace.Opens (ComplexModel d) :=
  ⟨c.tangentPatch,c.isOpen_tangentPatch⟩

def originalOpenMemberParameter (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ContMDiffMap 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
      c.originalTangentPatchOpen (member p (affinePoint c.i ζ.val)) ∞ := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  refine ⟨fun u => c.originalSliceMemberPoint (ζ,u),?_⟩
  intro u
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i ζ.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  have hP := c.contMDiffAt_originalMemberParameter p.contMDiff (ζ,u) hdim
  have hV : ContMDiffAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (Subtype.val : c.originalTangentPatchOpen → ComplexModel d) u :=
    (contMDiff_subtype_val (U := c.originalTangentPatchOpen)).contMDiffAt
  apply (hP.comp u hV).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun v => (c.originalMemberParameter_apply (ζ,u) v.property).symm

theorem originalOpenMemberParameter_apply (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ∀ u : c.originalTangentPatchOpen, (c.originalOpenMemberParameter ζ hsm u).val = c.tangentPoint (ζ,u) := by
  intros
  rfl

theorem originalOpenMemberParameter_coordinateDelete (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ∀ u : c.originalTangentPatchOpen,
      originalMemberCoordinateDelete c.m (c.e.val (c.originalOpenMemberParameter ζ hsm u).val) = u.val := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  intro u
  rw [c.originalOpenMemberParameter_apply ζ hsm u,(c.tangentPoint_chart_coordinates (ζ,u)).2.1]
  ext j
  exact c.originalTangentCoordinateMap_succAbove (ζ,u) j

theorem originalOpenMemberParameter_injective (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    Function.Injective (c.originalOpenMemberParameter ζ hsm) := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  intro u v huv
  apply Subtype.ext
  have h := congrArg (fun y : member p (affinePoint c.i ζ.val) => originalMemberCoordinateDelete c.m (c.e.val y.val)) huv
  rw [c.originalOpenMemberParameter_coordinateDelete ζ hsm u,c.originalOpenMemberParameter_coordinateDelete ζ hsm v] at h
  exact h

end SliceChart
end SGPT.Trace.Bertini
