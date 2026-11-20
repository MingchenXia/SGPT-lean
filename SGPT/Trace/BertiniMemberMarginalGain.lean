import SGPT.Trace.BertiniFamilySmallMemberMarginal
import SGPT.Trace.BertiniPhysicalHodgeWeightScalar

/-! The SAME original full native smaller-member Hodge marginal extracts
the actual finite parameter gain, retaining original singular poles. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N)
  (U V : TopologicalSpace.Opens (ComplexModel 1)) (hVU : V ≤ U)
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

theorem familySmallMemberHodgeMarginal_finite_base_weight :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber)
      (w : familyIncidence p i a v U → ℝ≥0∞) (g : ℂ → ℝ≥0∞), (∀ τ, g τ ≠ ⊤) → ∀ τ : ℂ,
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => g (scalarParameter p i a v U q) * w q) τ =
      g τ * familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w τ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S w g hg τ
  by_cases hτ : modelOneScalarEquiv.symm τ ∈ V
  · let t : V := ⟨modelOneScalarEquiv.symm τ,hτ⟩
    let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
    let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
    let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
    let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsV t))
    let R := familyNativeMemberAdjunctionSection p i a v V hsV L t S
    let l := fun y => familyBaseInclusion p i a v U V hVU (familyMemberLift p i a v V hsV t y)
    have hpoint (y : member p (affinePoint i (a - t.val 0 • v))) : scalarParameter p i a v U (l y) = τ := by
      change (modelOneScalarEquiv.symm τ) 0 = τ
      exact modelOneScalarEquiv.apply_symm_apply τ
    unfold familySmallMemberHodgeMarginal
    rw [dif_pos hτ,dif_pos hτ]
    change nativePhysicalHodgeEnergy LH R (fun y => g (scalarParameter p i a v U (l y)) * w (l y)) =
      g τ * nativePhysicalHodgeEnergy LH R (fun y => w (l y))
    have hw : (fun y => g (scalarParameter p i a v U (l y)) * w (l y)) = (fun y => g τ * w (l y)) := by
      funext y
      rw [hpoint]
    rw [hw,nativePhysicalHodgeEnergy_weight_const_mul LH R (fun y => w (l y)) (g τ) (hg τ)]
  · unfold familySmallMemberHodgeMarginal
    rw [dif_neg hτ,dif_neg hτ,mul_zero]

theorem familySmallMemberHodgeMarginal_originalPotential (φ : X → EReal) (τ : ℂ)
    (hτ : modelOneScalarEquiv.symm τ ∈ V) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber,
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => multiplierWeight 1 (φ q.val.2)) τ =
      familyNativeMemberHodgeEnergy p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L φ
        ⟨modelOneScalarEquiv.symm τ,hτ⟩ S := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  unfold familySmallMemberHodgeMarginal
  rw [dif_pos hτ]
  rfl

theorem familySmallMemberHodgeMarginal_gain_factor (φ : X → EReal) (G : ℂ → ℝ) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber) (τ : ℂ),
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => ENNReal.ofReal (G (scalarParameter p i a v U q)) * multiplierWeight 1 (φ q.val.2)) τ =
      ENNReal.ofReal (G τ) * familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => multiplierWeight 1 (φ q.val.2)) τ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S τ
  exact familySmallMemberHodgeMarginal_finite_base_weight p i a v U V hVU hsm L S
    (fun q => multiplierWeight 1 (φ q.val.2)) (fun z => ENNReal.ofReal (G z))
    (fun _ => ENNReal.ofReal_ne_top) τ

theorem familySmallMemberHodgeMarginal_gain_originalPotential (φ : X → EReal) (G : ℂ → ℝ) (τ : ℂ)
    (hτ : modelOneScalarEquiv.symm τ ∈ V) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ S : HolomorphicSections (n := d + 1)
      (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber,
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L S
        (fun q => ENNReal.ofReal (G (scalarParameter p i a v U q)) * multiplierWeight 1 (φ q.val.2)) τ =
      ENNReal.ofReal (G τ) * familyNativeMemberHodgeEnergy p i a v V
        (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L φ ⟨modelOneScalarEquiv.symm τ,hτ⟩ S := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S
  rw [familySmallMemberHodgeMarginal_gain_factor,familySmallMemberHodgeMarginal_originalPotential]

end SGPT.Trace.BertiniFamilyCanonical
