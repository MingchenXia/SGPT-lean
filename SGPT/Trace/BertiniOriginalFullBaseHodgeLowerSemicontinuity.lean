import SGPT.Trace.BertiniOriginalPhysicalSliceFatou
import SGPT.Trace.BertiniOriginalPreferredCutoffs
import SGPT.Trace.BertiniHodgeWeightLinearity

/-! Genuine joint FULL affine-base/coefficient ORIGINAL intrinsic Hodge LSC. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  {φ : X → EReal}

private theorem actualPreferredSliceMass_commonMember (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)
    (i : Fin (N + 1)) (hi : c.i = i) (ζ : ComplexModel N) (hζ : ζ ∈ ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) {m : ℕ}
    (H : Fin m → HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber)
    (v : Fin m → ℂ) (β : X → ℝ) (w : X → ℝ≥0∞)
    (hs : tsupport β ⊆ c.originalSliceAmbientSource ζ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    letI : MeasurableSpace (member p (affinePoint i ζ)) := borel _
    letI : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
    c.originalPhysicalCombinationSliceMass L H β w (v,⟨ζ,hζ⟩) =
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))
        (nativeBertiniPhysicalAdjunctionSection p i ζ hsm L
          (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
            (nativeBertiniHyperplaneBundle p)) L) H v))
        (fun y => ENNReal.ofReal (β y.val) * w y.val) := by
  subst i
  let := nativeBertiniMemberChartedSpace p c.i ζ hsm
  let := nativeBertiniMemberComplex p c.i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint c.i ζ)) := borel _
  let : BorelSpace (member p (affinePoint c.i ζ)) := ⟨rfl⟩
  have h := c.originalPhysicalCombinationSliceMass_eq_localHodge L H ⟨ζ,hζ⟩ hsm v β w
  refine h.trans ?_
  apply congrArg (nativePhysicalHodgeEnergy _ _)
  funext y
  by_cases hy : y.val ∈ c.originalSliceAmbientSource ζ
  · exact indicator_of_mem (show y ∈ c.originalSliceMemberSource ζ from hy) _
  · have hb : β y.val = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht))
    rw [indicator_of_notMem (show y ∉ c.originalSliceMemberSource ζ from hy),hb,ENNReal.ofReal_zero,zero_mul]

theorem exists_original_fullBase_adjunctionHodge_lowerSemicontinuity
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) (ℓ₀ : HyperplaneSpace N)
    (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀) :
    ∃ V : TopologicalSpace.Opens (ComplexModel N), affineChart (chartIndex ℓ₀) ℓ₀ ∈ V ∧
      ∃ hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val),
      ∀ (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (m : ℕ)
        (H : Fin m → HolomorphicSections (n := d + 1)
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber),
        LowerSemicontinuous (fun q : (Fin m → ℂ) × V =>
          nativeBertiniAdjunctionHodgeEnergy p (chartIndex ℓ₀) q.2.val (hsV q.2) L φ
            (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
              (nativeBertiniHyperplaneBundle p)) L) H q.1)) := by
  classical
  obtain ⟨k,c,a,V,β,hV,hc,hs,hball,hβ,_hβc,hsub,hone⟩ :=
    exists_originalPreferredSliceCutoffs p hφ ℓ₀ hsm₀
  let hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val) :=
    fun ζ => hs ζ.val ζ.property
  refine ⟨V,hV,hsV,?_⟩
  intro L m H
  let E := tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L
  let w : X → ℝ≥0∞ := fun x => multiplierWeight 1 (φ x)
  have hw : LowerSemicontinuous w := lowerSemicontinuous_originalMultiplierWeight hφ
  let M : Fin k → ((Fin m → ℂ) × V) → ℝ≥0∞ := fun j q =>
    (c j).originalPhysicalCombinationSliceMass L H (β j) w
      (q.1,⟨q.2.val,hball q.2.val q.2.property j⟩)
  have hM (j : Fin k) : LowerSemicontinuous (M j) := by
    have hloc := (c j).lowerSemicontinuous_originalPhysicalCombinationSliceMass L H (a j) (hc j).2.1
      (β j) (β j).continuous w hw
    have hmap : Continuous (fun q : (Fin m → ℂ) × V =>
        (q.1,(⟨q.2.val,hball q.2.val q.2.property j⟩ : ball (c j).ζ₀ (c j).r))) :=
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
    exact hloc.comp hmap
  have heq : (fun q : (Fin m → ℂ) × V =>
      nativeBertiniAdjunctionHodgeEnergy p (chartIndex ℓ₀) q.2.val (hsV q.2) L φ
        (nativeSectionCombination E H q.1)) = fun q => ∑ j, M j q := by
    funext q
    let i := chartIndex ℓ₀
    let ζ := q.2.val
    let hsm := hsV q.2
    let := nativeBertiniMemberChartedSpace p i ζ hsm
    let := nativeBertiniMemberComplex p i ζ hsm
    let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
    let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
    let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)
    let S := nativeBertiniPhysicalAdjunctionSection p i ζ hsm L (nativeSectionCombination E H q.1)
    let W : member p (affinePoint i ζ) → ℝ≥0∞ := fun y => w y.val
    let α : Fin k → member p (affinePoint i ζ) → ℝ≥0∞ := fun j y => ENNReal.ofReal (β j y.val)
    have hW : Measurable W := (hw.comp continuous_subtype_val).measurable
    have hα (j : Fin k) : Measurable (α j) :=
      (ENNReal.continuous_ofReal.comp ((β j).continuous.comp continuous_subtype_val)).measurable
    have hsum (y : member p (affinePoint i ζ)) : ∑ j, α j y = 1 := by
      change (∑ j, ENNReal.ofReal (β j y.val)) = 1
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hβ j y.val).1),
        hone ζ q.2.property y.val y.property,ENNReal.ofReal_one]
    have hp := nativePhysicalHodgeEnergy_weight_partition LH S W hW α hα hsum
    change nativePhysicalHodgeEnergy LH S W = _
    rw [hp]
    apply Finset.sum_congr rfl
    intro j _
    exact (actualPreferredSliceMass_commonMember p (c j) i (hc j).1 ζ
      (hball ζ q.2.property j) hsm L H q.1 (β j) w (hsub ζ q.2.property j)).symm
  rw [heq]
  exact lowerSemicontinuous_sum (fun j _ => hM j)

end SGPT.Trace.Bertini
