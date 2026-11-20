import SGPT.Trace.BertiniUniversalCutoffMeasurable

/-! Genuine ordinary tangent cutoff marginal is the SAME native original
member adjunction Hodge energy, with true original source support. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
attribute [local instance] Classical.propDecidable
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace (k + 1)) φ)

private theorem actualCutoffSource_product
    (ζ : ball c.ζ₀ c.r) (u : c.tangentPatch)
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber)
    (β : X → ℝ) (w : X → ℝ≥0∞) :
    originalCutoffResidueSourceDensity p c L T β w (prodModelEquiv (k + 1) d (ζ.val,u.val)) =
      ENNReal.ofReal (β (c.tangentPoint (ζ,u))) *
        ENNReal.ofReal (‖(c.tangentNormalDenominator (ζ,u))⁻¹ •
          c.originalAmbientLValue p.contMDiff (ζ,u) L (T (c.tangentPoint (ζ,u)))‖ ^ 2) * w (c.tangentPoint (ζ,u)) := by
  let z := prodModelEquiv (k + 1) d (ζ.val,u.val)
  have hz : z ∈ originalQSourceDomain p c := by
    change (prodModelEquiv (k + 1) d).symm (prodModelEquiv (k + 1) d (ζ.val,u.val)) ∈
      ((ball c.ζ₀ c.r) ×ˢ c.tangentPatch)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨ζ.property,u.property⟩
  let q := originalQSourcePair p c ⟨z,hz⟩
  have hq : q = (ζ,u) := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((prodModelEquiv (k + 1) d).symm_apply_apply (ζ.val,u.val))
    · apply Subtype.ext
      exact congrArg Prod.snd ((prodModelEquiv (k + 1) d).symm_apply_apply (ζ.val,u.val))
  have hs : originalMemberResidueSourceDensity p c L T w z =
      ENNReal.ofReal (‖(c.tangentNormalDenominator q)⁻¹ •
        c.originalAmbientLValue p.contMDiff q L (T (c.tangentPoint q))‖ ^ 2) * w (c.tangentPoint q) := dif_pos hz
  rw [hq] at hs
  have hx : originalQSourceX p c z = c.tangentPoint (ζ,u) := by
    change c.point ((prodModelEquiv (k + 1) d).symm (prodModelEquiv (k + 1) d (ζ.val,u.val))).1
      (c.tangentLift ((prodModelEquiv (k + 1) d).symm (prodModelEquiv (k + 1) d (ζ.val,u.val))).2) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  change ENNReal.ofReal (β (originalQSourceX p c z)) * originalMemberResidueSourceDensity p c L T w z = _
  rw [hx,hs,mul_assoc]

theorem originalCutoffResidue_tangent_integral_eq_commonHodge
    (i : Fin (k + 1 + 1)) (hi : c.i = i) (ζ : ComplexModel (k + 1)) (hζ : ζ ∈ ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (T : HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber)
    (β : X → ℝ) (w : X → ℝ≥0∞) (hsupport : tsupport β ⊆ c.originalSliceAmbientSource ζ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
    let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
    (∫⁻ b : ComplexModel d, originalCutoffResidueSourceDensity p c L T β w (prodModelEquiv (k + 1) d (ζ,b))) =
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
        (nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T)
        (fun y => ENNReal.ofReal (β y.val) * w y.val) := by
  subst i
  let := nativeBertiniMemberChartedSpace p c.i ζ hsm
  let := nativeBertiniMemberComplex p c.i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint c.i ζ)) := borel _
  let : BorelSpace (member p (affinePoint c.i ζ)) := ⟨rfl⟩
  let H : Fin 1 → HolomorphicSections (n := d + 1) (OriginalAmbientPhysicalBundle p L).Fiber := fun _ => T
  have hsingle : nativeSectionCombination (OriginalAmbientPhysicalBundle p L) H (fun _ => (1 : ℂ)) = T := by simp [nativeSectionCombination,H]
  let f : ComplexModel d → ℝ≥0∞ := fun b => originalCutoffResidueSourceDensity p c L T β w (prodModelEquiv (k + 1) d (ζ,b))
  have houtside (b : ComplexModel d) (hb : b ∉ c.tangentPatch) : f b = 0 := by
    have hnot : prodModelEquiv (k + 1) d (ζ,b) ∉ originalQSourceDomain p c := by
      intro h
      apply hb
      simpa only [originalQSourceDomain,Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h.2
    have hs : originalMemberResidueSourceDensity p c L T w (prodModelEquiv (k + 1) d (ζ,b)) = 0 := dif_neg hnot
    unfold f originalCutoffResidueSourceDensity
    rw [hs,mul_zero]
  have hmass : (∫⁻ b, f b) = c.originalPhysicalCombinationSliceMass L H β w ((fun _ => 1),⟨ζ,hζ⟩) := by
    calc
      _ = ∫⁻ b in c.tangentPatch, f b := by
        rw [← lintegral_indicator c.isOpen_tangentPatch.measurableSet f]
        apply lintegral_congr
        intro b
        by_cases hb : b ∈ c.tangentPatch
        · exact (indicator_of_mem hb f).symm
        · rw [indicator_of_notMem hb f,houtside b hb]
      _ = ∫⁻ u : c.tangentPatch, f u.val ∂c.tangentPatchVolume :=
        (lintegral_subtype_comap c.isOpen_tangentPatch.measurableSet f).symm
      _ = _ := by
        apply lintegral_congr
        intro u
        dsimp only [f,SliceChart.originalPhysicalCombinationSliceMass,SliceChart.originalPhysicalCombinationSliceDensity]
        rw [hsingle]
        exact actualCutoffSource_product p c ⟨ζ,hζ⟩ u L T β w
  have hHodge := c.originalPhysicalCombinationSliceMass_eq_localHodge L H ⟨ζ,hζ⟩ hsm (fun _ => 1) β w
  rw [hsingle] at hHodge
  refine hmass.trans (hHodge.trans ?_)
  apply congrArg (nativePhysicalHodgeEnergy _ _)
  funext y
  by_cases hy : y.val ∈ c.originalSliceAmbientSource ζ
  · exact indicator_of_mem (show y ∈ c.originalSliceMemberSource ζ from hy) _
  · have hb : β y.val = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hy (hsupport ht))
    rw [indicator_of_notMem (show y ∉ c.originalSliceMemberSource ζ from hy),hb,ENNReal.ofReal_zero,zero_mul]

end SGPT.Trace.BertiniUniversal
