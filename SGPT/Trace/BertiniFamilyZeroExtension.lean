import SGPT.Trace.BertiniFamilyRawMemberIntegral
import SGPT.Trace.BertiniFamilyBasePhysical

/-! Actual family normal-residue density and original member intrinsic Hodge integral. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

def familyPhysicalZeroExtension :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    (∀ q, (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q) → ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  exact fun S q => if hq : q.val.1.val ∈ V then
    S ⟨(⟨q.val.1.val,hq⟩,q.val.2),q.property⟩ else 0

theorem familyPhysicalZeroExtension_inside :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q) (q : familyIncidence p i a v V),
      familyPhysicalZeroExtension p i a v U V hVU hsm L S (familyBaseInclusion p i a v U V hVU q) = S q := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S q
  unfold familyPhysicalZeroExtension
  exact dif_pos q.val.1.property

theorem familyPhysicalZeroExtension_outside :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q) (q : familyIncidence p i a v U), q.val.1.val ∉ V →
      familyPhysicalZeroExtension p i a v U V hVU hsm L S q = 0 := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S q hq
  unfold familyPhysicalZeroExtension
  exact dif_neg hq

variable [MeasurableSpace X] [BorelSpace X] in
theorem familyPhysicalZeroExtension_normSq_measurable :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber),
      Measurable (fun q => ENNReal.ofReal (‖familyPhysicalZeroExtension p i a v U V hVU hsm L S q‖ ^ 2)) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  let H := (familyBaseTubeHomeomorph p i a v U V hVU).symm
  have hS := familyPhysical_normSq_measurable p i a v V hsV L S
    ((S.contMDiff.mdifferentiable (by simp)).mdifferentiableOn)
  have hsub : Measurable (fun q : familyBaseTube p i a v U V => ENNReal.ofReal (‖S (H q)‖ ^ 2)) :=
    hS.comp H.continuous.measurable
  have hpaste : Measurable (fun q => if hq : q ∈ familyBaseTube p i a v U V then
      ENNReal.ofReal (‖S (H ⟨q,hq⟩)‖ ^ 2) else 0) :=
    Measurable.dite hsub measurable_const (familyBaseTube p i a v U V).isOpen.measurableSet
  have heq : (fun q => ENNReal.ofReal (‖familyPhysicalZeroExtension p i a v U V hVU hsm L S q‖ ^ 2)) =
      (fun q => if hq : q ∈ familyBaseTube p i a v U V then
        ENNReal.ofReal (‖S (H ⟨q,hq⟩)‖ ^ 2) else 0) := by
    funext q
    by_cases hq : q.val.1.val ∈ V
    · simp only [familyPhysicalZeroExtension,dif_pos hq,
        dif_pos (show q ∈ familyBaseTube p i a v U V from hq)]
      rfl
    · simp only [familyPhysicalZeroExtension,dif_neg hq,
        dif_neg (show q ∉ familyBaseTube p i a v U V from hq),
        norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero]
  rw [heq]
  exact hpaste

theorem familyPhysicalZeroExtension_rawMember_inside :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ t : V,
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm ⟨t.val,hVU t.property⟩)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm ⟨t.val,hVU t.property⟩)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
      ∀ (S : ∀ q, (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q),
        familyRawMemberAdjunctionSection p i a v U hsm L ⟨t.val,hVU t.property⟩ (familyPhysicalZeroExtension p i a v U V hVU hsm L S) =
          familyRawMemberAdjunctionSection p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L t S := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm ⟨t.val,hVU t.property⟩)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm ⟨t.val,hVU t.property⟩)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S
  funext y
  unfold familyRawMemberAdjunctionSection familyPhysicalZeroExtension
  rw [dif_pos t.property]

theorem familyPhysicalZeroExtension_rawMember_outside :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ t : U,
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
      ∀ (S : ∀ q, (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber q), t.val ∉ V →
        familyRawMemberAdjunctionSection p i a v U hsm L t (familyPhysicalZeroExtension p i a v U V hVU hsm L S) = (fun _ => 0) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro S ht
  funext y
  unfold familyRawMemberAdjunctionSection familyPhysicalZeroExtension
  rw [dif_neg ht,map_zero]

end SGPT.Trace.BertiniFamilyCanonical
