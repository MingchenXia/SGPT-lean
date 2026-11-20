import SGPT.Trace.BertiniFamilyCanonicalModel
import Mathlib.Geometry.Manifold.Diffeomorph

/-! Actual smaller-base native pencil family = actual larger-family open
tube, with produced genuine complex diffeomorphism and literal X/parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
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
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)

include hVU in
omit [IsComplexManifold n X] in
theorem familyBaseRestrictedSmoothness
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    ∀ t : V, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val) :=
  fun t => hsm ⟨t.val,hVU t.property⟩

def familyBaseInclusion : familyIncidence p i a v V → familyIncidence p i a v U :=
  fun q => ⟨(⟨q.val.1.val,hVU q.val.1.property⟩,q.val.2),q.property⟩

omit [IsComplexManifold n X] in
theorem familyBaseInclusion_parameter (q : familyIncidence p i a v V) :
    (familyBaseInclusion p i a v U V hVU q).val.1.val = q.val.1.val := rfl

omit [IsComplexManifold n X] in
theorem familyBaseInclusion_X (q : familyIncidence p i a v V) :
    (familyBaseInclusion p i a v U V hVU q).val.2 = q.val.2 := rfl

def familyBaseTube : TopologicalSpace.Opens (familyIncidence p i a v U) :=
  ⟨{q | q.val.1.val ∈ V}, V.isOpen.preimage
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))⟩

def familyBaseTubeHomeomorph : familyIncidence p i a v V ≃ₜ familyBaseTube p i a v U V where
  toEquiv := {
    toFun q := ⟨familyBaseInclusion p i a v U V hVU q,q.val.1.property⟩
    invFun q := ⟨(⟨q.val.val.1.val,q.property⟩,q.val.val.2),q.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  continuous_toFun :=
    ((((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (((continuous_subtype_val.comp (continuous_fst.comp
      (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _).prodMk
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _

omit [IsComplexManifold n X] in
theorem familyBaseTubeHomeomorph_apply (q : familyIncidence p i a v V) :
    (familyBaseTubeHomeomorph p i a v U V hVU q).val = familyBaseInclusion p i a v U V hVU q := rfl

def nativeFamilyBaseInclusion
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (familyIncidence p i a v V) (familyIncidence p i a v U) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  refine ⟨familyBaseInclusion p i a v U V hVU,?_⟩
  intro q
  apply contMDiffAt_familyLift p i a v U p.contMDiff hsm
  have ht := (contMDiff_inclusion hVU).comp (contMDiff_familyProjection p i a v V p.contMDiff hsV)
  have hx := (familyNativeXMap p i a v V hsV).contMDiff
  exact contMDiffAt_nativePair ht.contMDiffAt hx.contMDiffAt

def nativeFamilyBaseTubeInverse
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ContMDiffMap 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (familyBaseTube p i a v U V) (familyIncidence p i a v V) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  let f := (familyBaseTubeHomeomorph p i a v U V hVU).symm
  have htu := (contMDiff_familyProjection p i a v U p.contMDiff hsm).comp
    (contMDiff_subtype_val (U := familyBaseTube p i a v U V))
  have htc : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (fun q : familyBaseTube p i a v U V => q.val.val.1.val) := contMDiff_subtype_val.comp htu
  have ht : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel 1) ∞
      (fun q : familyBaseTube p i a v U V => (f q).val.1) :=
    (ContMDiff.subtypeVal_comp_iff V _).mp htc
  have hx := (familyNativeXMap p i a v U hsm).contMDiff.comp
    (contMDiff_subtype_val (U := familyBaseTube p i a v U V))
  refine ⟨f,?_⟩
  intro q
  apply contMDiffAt_familyLift p i a v V p.contMDiff hsV
  exact contMDiffAt_nativePair ht.contMDiffAt hx.contMDiffAt

def familyBaseTubeDiffeomorph
    (hsm : ∀ t : U, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val)) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    Diffeomorph 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (familyIncidence p i a v V) (familyBaseTube p i a v U V) ∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  exact {
    toEquiv := (familyBaseTubeHomeomorph p i a v U V hVU).toEquiv
    contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (familyBaseTube p i a v U V) _).mp
      (nativeFamilyBaseInclusion p i a v U V hVU hsm).contMDiff
    contMDiff_invFun := (nativeFamilyBaseTubeInverse p i a v U V hVU hsm).contMDiff }

end SGPT.Trace.BertiniFamilyCanonical
