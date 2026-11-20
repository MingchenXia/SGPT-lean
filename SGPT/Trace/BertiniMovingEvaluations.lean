import SGPT.Trace.BertiniPencilLocalSection
import SGPT.Trace.BertiniFamilyMemberRestriction

/-! Actual finite central member H0 detector, genuine moving-point lifts
on one common original parameter neighbourhood, and literal physical readback. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))

def memberFamilyFrameEvaluation
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (y : member p (affinePoint i (a - t.val 0 • v))) (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L))
      (_he : (⟨(t,y.val),y.property⟩ : familyIncidence p i a v U) ∈ e.val.baseSet),
      HolomorphicSections (n := d) (tensor
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i (a - t.val 0 • v))))
      (nativeHolomorphicPullbackBundle L
        (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))).Fiber →ₗ[ℂ] ℂ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro y e he
  let := e.property
  let q : familyIncidence p i a v U := ⟨(t,y.val),y.property⟩
  let J := nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - t.val 0 • v) (hsm t) L y
  let E := e.val.linearEquivAt ℂ q he
  exact {
    toFun S := E (J.symm (S y))
    map_add' S T := by
      change E (J.symm (S y + T y)) = _
      rw [map_add,map_add]
    map_smul' c S := by
      change E (J.symm (c • S y)) = _
      rw [map_smul,map_smul]
      rfl }

theorem memberFamilyFrameEvaluation_familyImage
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∀ (y : member p (affinePoint i (a - t.val 0 • v))) (e : AtlasFrame (familyNativePhysicalModel p i a v U hsm L))
      (he : (⟨(t,y.val),y.property⟩ : familyIncidence p i a v U) ∈ e.val.baseSet)
      (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber),
      memberFamilyFrameEvaluation p i a v U hsm L t y e he
        (familyNativeMemberAdjunctionSection p i a v U hsm L t S) =
      (e.val ⟨(⟨(t,y.val),y.property⟩ : familyIncidence p i a v U),
        S ⟨(t,y.val),y.property⟩⟩).2 := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  intro y e he S
  let := e.property
  let q : familyIncidence p i a v U := ⟨(t,y.val),y.property⟩
  let J := nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - t.val 0 • v) (hsm t) L y
  change (e.val.linearEquivAt ℂ q he) (J.symm (J (S q))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem exists_finite_member_movingEvaluations
    (L : HermitianHolomorphicLineBundle (d + 1) X) (t : U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    letI := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    ∃ (A : Finset (member p (affinePoint i (a - t.val 0 • v))))
      (e : ∀ _y : A, AtlasFrame (familyNativePhysicalModel p i a v U hsm L))
      (he : ∀ y : A, (⟨(t,y.val.val),y.val.property⟩ : familyIncidence p i a v U) ∈ (e y).val.baseSet),
      (∀ S : HolomorphicSections (n := d) (tensor
      (nativeCanonicalBundle (n := d) (X := member p (affinePoint i (a - t.val 0 • v))))
      (nativeHolomorphicPullbackBundle L
        (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))).Fiber,
        (∀ y : A, memberFamilyFrameEvaluation p i a v U hsm L t y.val (e y) (he y) S = 0) → S = 0) ∧
      ∃ (V : TopologicalSpace.Opens (ComplexModel 1)), V ≤ U ∧
        ∃ (ht : t.val ∈ V)
          (g : ∀ _y : A, ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel (d + 1))
            V (familyIncidence p i a v U) ∞),
          (∀ y : A, g y ⟨t.val,ht⟩ = ⟨(t,y.val.val),y.val.property⟩ ∧
            ∀ z : V, (g y z).val.1.val = z.val) ∧
          (∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber) (y : A),
            ContMDiffAt 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ℂ) ∞
              (fun z => ((e y).val ⟨g y z,S (g y z)⟩).2) ⟨t.val,ht⟩) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  classical
  let H := member p (affinePoint i (a - t.val 0 • v))
  let T := tensor (nativeCanonicalBundle (n := d) (X := H))
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))
  let B := familyNativePhysicalModel p i a v U hsm L
  obtain ⟨A,hA⟩ := exists_finite_section_detecting_set (n := d) T.Fiber
  let q (y : H) : familyIncidence p i a v U := ⟨(t,y.val),y.property⟩
  let e (y : A) : AtlasFrame B := ⟨trivializationAt ℂ B.Fiber (q y.val),inferInstance⟩
  have he (y : A) : q y.val ∈ (e y).val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  refine ⟨A,e,he,?_,?_⟩
  · intro S hS
    apply hA S
    intro y hy
    let yy : A := ⟨y,hy⟩
    let J := nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - t.val 0 • v) (hsm t) L y
    let E := (e yy).val.linearEquivAt ℂ (q y) (he yy)
    have h0 := hS yy
    change E (J.symm (S y)) = 0 at h0
    have h1 : J.symm (S y) = 0 := E.injective (h0.trans (map_zero E).symm)
    exact J.symm.injective (h1.trans (map_zero J.symm).symm)
  · have hlocal (y : A) := exists_familyProjection_localSection p i a v U hsm (q y.val)
    choose V₀ hV₀ ht₀ g₀ hg₀ hp₀ using hlocal
    let V : TopologicalSpace.Opens (ComplexModel 1) :=
      ⟨(U : Set (ComplexModel 1)) ∩ ⋂ y : A, (V₀ y : Set (ComplexModel 1)),
        U.isOpen.inter (isOpen_iInter_of_finite fun y => (V₀ y).isOpen)⟩
    have ht : t.val ∈ V := ⟨t.property,mem_iInter.mpr ht₀⟩
    have hVU : V ≤ U := fun _ hz => hz.1
    have hsub (y : A) : V ≤ V₀ y := fun _ hz => mem_iInter.mp hz.2 y
    let inc (y : A) : ContMDiffMap 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel 1) V (V₀ y) ∞ :=
      ⟨TopologicalSpace.Opens.inclusion (hsub y),contMDiff_inclusion (hsub y)⟩
    let g (y : A) := (g₀ y).comp (inc y)
    have hg (y : A) : g y ⟨t.val,ht⟩ = q y.val := hg₀ y
    refine ⟨V,hVU,ht,g,?_,?_⟩
    · intro y
      exact ⟨hg y,fun z => hp₀ y (inc y z)⟩
    · intro S y
      apply contMDiffAt_nativeSection_movingPointCoefficient B (e y) S V (g y) ⟨t.val,ht⟩
      rw [hg y]
      exact he y

end SGPT.Trace.BertiniFamilyCanonical
