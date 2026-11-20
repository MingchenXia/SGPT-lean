import SGPT.Trace.BertiniFamilyLocalMemberFubini

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

def familySmallMemberHodgeMarginal :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (_S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber) (_w : familyIncidence p i a v U → ℝ≥0∞), ℂ → ℝ≥0∞ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro S w τ
  by_cases hτ : modelOneScalarEquiv.symm τ ∈ V
  · let t : V := ⟨modelOneScalarEquiv.symm τ,hτ⟩
    let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
    let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
    let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
    exact nativePhysicalHodgeEnergy
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsV t)))
      (familyNativeMemberAdjunctionSection p i a v V hsV L t S)
      (fun y => w (familyBaseInclusion p i a v U V hVU (familyMemberLift p i a v V hsV t y)))
  · exact 0

private theorem actualRawHodgeZero {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] [CompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (E : HermitianHolomorphicLineBundle.{0,0} n Y)
    (w : Y → ℝ≥0∞) : nativePhysicalHodgeEnergy E (fun _ => 0) w = 0 := by
  have h := nativePhysicalHodgeEnergy_smul E (fun _ => 0) w (0 : ℂ)
  have hzero : (0 : ℂ) • (fun y => (0 : (tensor (nativeCanonicalBundle (n := n) (X := Y)) E).Fiber y)) =
      (fun y => (0 : (tensor (nativeCanonicalBundle (n := n) (X := Y)) E).Fiber y)) := by
    funext y
    exact zero_smul ℂ (0 : (tensor (nativeCanonicalBundle (n := n) (X := Y)) E).Fiber y)
  rw [hzero] at h
  simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0),ENNReal.ofReal_zero,zero_mul] using h

variable [MeasurableSpace X] [BorelSpace X] in
theorem familySmallMemberHodgeMarginal_partition :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (k : ℕ) (F : Fin k → FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}) (_hF : ∀ j, ∀ y ∈ (F j).ambSource, fcoord (F j) y (Fin.last d) = scalarParameter p i a v U y)
      (β : Fin k → familyIncidence p i a v U → ℝ)
      (_hβ : ∀ j, Continuous (β j)) (_hβ0 : ∀ j q, 0 ≤ β j q)
      (_hβs : ∀ j, tsupport (β j) ⊆ (F j).ambSource)
      (_hone : ∀ q ∈ familyBaseTube p i a v U V, ∑ j, β j q = 1)
      (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber) (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w → ∀ τ : ℂ,
      familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w τ = ∑ j,
        familyRawNormalMemberMarginal p i a v U hsm L (F j)
          (familyPhysicalZeroExtension p i a v U V hVU hsm L S) (fun q => ENNReal.ofReal (β j q) * w q) τ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro k F _hF β hβ hβ0 hβs hone S w hw τ
  let S0 := familyPhysicalZeroExtension p i a v U V hVU hsm L S
  by_cases hτ : modelOneScalarEquiv.symm τ ∈ V
  · let t : V := ⟨modelOneScalarEquiv.symm τ,hτ⟩
    let tU : U := ⟨t.val,hVU t.property⟩
    let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsV t)
    let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsV t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
    let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
    let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsV t))
    let R := familyNativeMemberAdjunctionSection p i a v V hsV L t S
    let l := fun y => familyBaseInclusion p i a v U V hVU (familyMemberLift p i a v V hsV t y)
    let W := fun y => w (l y)
    let α := fun j y => ENNReal.ofReal (β j (l y))
    have hl : Continuous l := (nativeFamilyBaseInclusion p i a v U V hVU hsm).contMDiff.continuous.comp
      (familyMemberLift p i a v V hsV t).contMDiff.continuous
    have hW : Measurable W := hw.comp hl.measurable
    have hα (j : Fin k) : Measurable (α j) := (ENNReal.continuous_ofReal.comp ((hβ j).comp hl)).measurable
    have hsum (y : member p (affinePoint i (a - t.val 0 • v))) : ∑ j, α j y = 1 := by
      change (∑ j, ENNReal.ofReal (β j (l y))) = 1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hβ0 j (l y)),hone (l y) t.property,ENNReal.ofReal_one]
    have himage : familyRawMemberAdjunctionSection p i a v U hsm L tU S0 = (R : ∀ _y, _) := by
      exact (familyPhysicalZeroExtension_rawMember_inside p i a v U V hVU hsm L t S).trans
        (familyRawMemberAdjunctionSection_genuine p i a v V hsV L t S)
    have hlocal (j : Fin k) : familyRawNormalMemberMarginal p i a v U hsm L (F j) S0
        (fun q => ENNReal.ofReal (β j q) * w q) τ =
        nativePhysicalHodgeEnergy LH R (fun y => α j y * W y) := by
      unfold familyRawNormalMemberMarginal
      rw [dif_pos (hVU hτ)]
      change familyRawNormalMemberEnergy p i a v U hsm L (F j) tU S0 _ = _
      unfold familyRawNormalMemberEnergy
      rw [himage]
      change nativePhysicalHodgeEnergy LH R
        ((familyNormalMemberSource p i a v U hsm (F j) tU : Set _).indicator
          (fun y => ENNReal.ofReal (β j (familyMemberLift p i a v U hsm tU y)) *
            w (familyMemberLift p i a v U hsm tU y))) =
        nativePhysicalHodgeEnergy LH R (fun y => α j y * W y)
      apply congrArg (nativePhysicalHodgeEnergy LH R)
      funext y
      by_cases hy : familyMemberLift p i a v U hsm tU y ∈ (F j).ambSource
      · rw [indicator_of_mem (show y ∈ familyNormalMemberSource p i a v U hsm (F j) tU from hy)]
        rfl
      · have hb : β j (l y) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hβs j h))
        have ha : α j y = 0 := by
          change ENNReal.ofReal (β j (l y)) = 0
          rw [hb,ENNReal.ofReal_zero]
        rw [indicator_of_notMem (show y ∉ familyNormalMemberSource p i a v U hsm (F j) tU from hy),ha,zero_mul]
    have hp := nativePhysicalHodgeEnergy_weight_partition LH R W hW α hα hsum
    unfold familySmallMemberHodgeMarginal
    rw [dif_pos hτ]
    change nativePhysicalHodgeEnergy LH R W = _
    rw [hp]
    apply Finset.sum_congr rfl
    intro j _
    exact (hlocal j).symm
  · have hQ : familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w τ = 0 := by
      unfold familySmallMemberHodgeMarginal
      rw [dif_neg hτ]
    rw [hQ]
    symm
    apply Finset.sum_eq_zero
    intro j _
    unfold familyRawNormalMemberMarginal
    by_cases hτU : modelOneScalarEquiv.symm τ ∈ U
    · rw [dif_pos hτU]
      let tU : U := ⟨modelOneScalarEquiv.symm τ,hτU⟩
      let := nativeBertiniMemberChartedSpace p i (a - tU.val 0 • v) (hsm tU)
      let := nativeBertiniMemberComplex p i (a - tU.val 0 • v) (hsm tU)
      let := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - tU.val 0 • v))).isCompact
      let : MeasurableSpace (member p (affinePoint i (a - tU.val 0 • v))) := borel _
      let : BorelSpace (member p (affinePoint i (a - tU.val 0 • v))) := ⟨rfl⟩
      unfold familyRawNormalMemberEnergy
      rw [familyPhysicalZeroExtension_rawMember_outside p i a v U V hVU hsm L tU S hτ]
      exact actualRawHodgeZero _ _
    · exact dif_neg hτU

variable [MeasurableSpace X] [BorelSpace X] in
theorem familySmallMemberHodgeMarginal_measurable_partition :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    letI := familyChartedSpace p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    letI := isComplexManifold_family p i a v V p.contMDiff (familyBaseRestrictedSmoothness p i a v U V hVU hsm)
    ∀ (k : ℕ) (F : Fin k → FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}) (_hF : ∀ j, ∀ y ∈ (F j).ambSource, fcoord (F j) y (Fin.last d) = scalarParameter p i a v U y)
      (β : Fin k → familyIncidence p i a v U → ℝ)
      (_hβ : ∀ j, Continuous (β j)) (_hβ0 : ∀ j q, 0 ≤ β j q)
      (_hβs : ∀ j, tsupport (β j) ⊆ (F j).ambSource)
      (_hone : ∀ q ∈ familyBaseTube p i a v U V, ∑ j, β j q = 1)
      (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v V (familyBaseRestrictedSmoothness p i a v U V hVU hsm) L).Fiber) (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w → Measurable (familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let hsV := familyBaseRestrictedSmoothness p i a v U V hVU hsm
  let := familyChartedSpace p i a v V p.contMDiff hsV
  let := isComplexManifold_family p i a v V p.contMDiff hsV
  intro k F hF β hβ hβ0 hβs hone S w hw
  have hnorm := familyPhysicalZeroExtension_normSq_measurable p i a v U V hVU hsm L S
  have hm (j : Fin k) := familyRawNormalMemberMarginal_measurable p i a v U hsm L (F j) (hF j)
    (familyPhysicalZeroExtension p i a v U V hVU hsm L S) hnorm
    (fun q => ENNReal.ofReal (β j q) * w q)
    ((ENNReal.continuous_ofReal.comp (hβ j)).measurable.mul hw)
  have heq : familySmallMemberHodgeMarginal p i a v U V hVU hsm L S w = fun τ => ∑ j,
      familyRawNormalMemberMarginal p i a v U hsm L (F j)
        (familyPhysicalZeroExtension p i a v U V hVU hsm L S) (fun q => ENNReal.ofReal (β j q) * w q) τ := by
    funext τ
    exact familySmallMemberHodgeMarginal_partition p i a v U V hVU hsm L k F hF β hβ hβ0 hβs hone S w hw τ
  rw [heq]
  exact Finset.measurable_sum _ (fun j _ => hm j)

end SGPT.Trace.BertiniFamilyCanonical
