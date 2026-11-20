import SGPT.Trace.BertiniOriginalOpenMemberImage
import SGPT.Trace.BertiniFamilyNormalParameterDerivative

/-! True intrinsic Hodge integration in the ORIGINAL full-parameter moving slice. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini.SliceChart

open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft
open SGPT.Trace.BertiniFamilyCanonical

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem mfderiv_originalOpenMemberParameter (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    ∀ u : c.originalTangentPatchOpen,
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalOpenMemberParameter ζ hsm) u =
        mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter (ζ,u)) u.val := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  intro u
  let hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint c.i ζ.val) d :=
    by simpa using isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  have hP := (c.contMDiffAt_originalMemberParameter p.contMDiff (ζ,u) hdim).mdifferentiableAt (by simp)
  have hV : MDifferentiableAt 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
      (Subtype.val : c.originalTangentPatchOpen → ComplexModel d) u :=
    (show ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) ∞
      (Subtype.val : c.originalTangentPatchOpen → ComplexModel d) from contMDiff_subtype_val).mdifferentiable (by simp) u
  have hc := mfderiv_comp u hP hV
  have heq : (c.originalMemberParameter (ζ,u)) ∘ (Subtype.val : c.originalTangentPatchOpen → ComplexModel d) =
      c.originalOpenMemberParameter ζ hsm := by
    funext v
    exact c.originalMemberParameter_apply (ζ,u) v.property
  have heqd :
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        ((c.originalMemberParameter (ζ,u)) ∘ (Subtype.val : c.originalTangentPatchOpen → ComplexModel d)) u =
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalOpenMemberParameter ζ hsm) u :=
    mfderiv_congr heq
  have hright :
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter (ζ,u)) u.val).comp
        (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (Subtype.val : c.originalTangentPatchOpen → ComplexModel d) u) =
      mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter (ζ,u)) u.val :=
    (congrArg (fun D : ComplexModel d →L[ℂ] ComplexModel d =>
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter (ζ,u)) u.val).comp D)
      (mfderiv_openComplexModel_val c.originalTangentPatchOpen u)).trans (ContinuousLinearMap.comp_id _)
  exact heqd.symm.trans (hc.trans hright)

variable [CompactSpace X]

def originalOpenResidueDensity (ζ : ball c.ζ₀ c.r)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : HolomorphicSections (n := d + 1) (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
      (nativeBertiniHyperplaneBundle p)) L).Fiber)
    (w : member p (affinePoint c.i ζ.val) → ℝ≥0∞) (z : ComplexModel d) : ℝ≥0∞ := by
  classical
  exact if hz : z ∈ c.tangentPatch then
    ENNReal.ofReal (‖(c.tangentNormalDenominator (ζ,⟨z,hz⟩))⁻¹ •
      c.originalAmbientLValue p.contMDiff (ζ,⟨z,hz⟩) L (T (c.tangentPoint (ζ,⟨z,hz⟩)))‖ ^ 2) *
      w (c.originalSliceMemberPoint (ζ,⟨z,hz⟩)) else 0

theorem originalOpenPhysicalDensity_eq_residueDensity (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
    ∀ (T : HolomorphicSections (n := d + 1) (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) (w : member p (affinePoint c.i ζ.val) → ℝ≥0∞),
      nativeCanonicalPhysicalOpenDensity c.originalTangentPatchOpen (c.originalOpenMemberParameter ζ hsm)
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i ζ.val hsm))
        (nativeBertiniPhysicalAdjunctionSection p c.i ζ.val hsm L T) w =
      c.originalOpenResidueDensity ζ L T w := by
  classical
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
  intro T w
  funext z
  by_cases hz : z ∈ c.tangentPatch
  · let u : c.originalTangentPatchOpen := ⟨z,hz⟩
    let q := (ζ,u)
    let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i ζ.val hsm)
    let g := c.originalOpenMemberParameter ζ hsm
    have hb (j : Fin d) : (EuclideanSpace.basisFun (Fin d) ℂ).toBasis j = EuclideanSpace.single j 1 := by
      ext k
      simp [EuclideanSpace.basisFun_apply]
    have htup : (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g u
        ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)) =
        fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter q) u.val
          (EuclideanSpace.single j 1) := by
      funext j
      rw [c.mfderiv_originalOpenMemberParameter ζ hsm u,hb j]
      rfl
    have hvalue : nativeCanonicalPhysicalValue LH (g u)
        (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g u
          ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j))
        (nativeBertiniPhysicalAdjunctionSection p c.i ζ.val hsm L T (g u)) =
        c.originalGlobalPhysicalResidueValue q hsm L (T (c.tangentPoint q)) := by
      rw [nativeBertiniPhysicalAdjunctionSection_apply]
      change nativeCanonicalPhysicalValue LH (c.originalSliceMemberPoint q)
        (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g u
          ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j))
        (nativeBertiniPhysicalAdjunctionFiberEquiv p c.i ζ.val hsm L (c.originalSliceMemberPoint q) (T (c.tangentPoint q))) =
        nativeCanonicalPhysicalValue LH (c.originalSliceMemberPoint q)
          (fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) (c.originalMemberParameter q) u.val
            (EuclideanSpace.single j 1))
          (nativeBertiniPhysicalAdjunctionFiberEquiv p c.i ζ.val hsm L (c.originalSliceMemberPoint q) (T (c.tangentPoint q)))
      rw [htup]
    have hnormal := hvalue.trans (c.originalGlobalPhysicalResidueValue_eq_normalDivision q hsm L (T (c.tangentPoint q)))
    unfold nativeCanonicalPhysicalOpenDensity originalOpenResidueDensity
    rw [dif_pos (show z ∈ c.originalTangentPatchOpen from hz),dif_pos hz]
    exact congrArg (fun s : L.Fiber (c.tangentPoint q) => ENNReal.ofReal (‖s‖ ^ 2) * w (c.originalSliceMemberPoint q)) hnormal
  · unfold nativeCanonicalPhysicalOpenDensity originalOpenResidueDensity
    rw [dif_neg (show z ∉ c.originalTangentPatchOpen from hz),dif_neg hz]

theorem originalMemberPhysicalHodgeEnergy_residueCoordinates (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
    letI : MeasurableSpace (member p (affinePoint c.i ζ.val)) := borel _
    letI : BorelSpace (member p (affinePoint c.i ζ.val)) := ⟨rfl⟩
    ∀ (T : HolomorphicSections (n := d + 1) (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
        (nativeBertiniHyperplaneBundle p)) L).Fiber) (w : member p (affinePoint c.i ζ.val) → ℝ≥0∞),
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i ζ.val hsm))
        (nativeBertiniPhysicalAdjunctionSection p c.i ζ.val hsm L T)
        ((c.originalSliceMemberSource ζ.val : Set _).indicator w) =
      ∫⁻ z in c.originalTangentPatchOpen, c.originalOpenResidueDensity ζ L T w z ∂volume := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
  let : MeasurableSpace (member p (affinePoint c.i ζ.val)) := borel _
  let : BorelSpace (member p (affinePoint c.i ζ.val)) := ⟨rfl⟩
  intro T w
  have h := nativePhysicalHodgeEnergy_openCoordinates c.originalTangentPatchOpen (c.originalOpenMemberParameter ζ hsm)
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i ζ.val hsm))
    (nativeBertiniPhysicalAdjunctionSection p c.i ζ.val hsm L T) w (c.originalSliceMemberSource ζ.val)
    (c.originalOpenMemberParameter_injective ζ hsm) (c.originalOpenMemberParameter_range ζ hsm)
  exact h.trans (congrArg (fun f : ComplexModel d → ℝ≥0∞ => ∫⁻ z in c.originalTangentPatchOpen, f z ∂volume)
    (c.originalOpenPhysicalDensity_eq_residueDensity ζ hsm L T w))

end SGPT.Trace.Bertini.SliceChart
