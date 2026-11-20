import SGPT.Trace.BertiniAmbientPhysicalContinuity

/-! Actual FULL-base original physical slice Fatou and intrinsic Hodge readback. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini.SliceChart
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
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) {m : ℕ}
  (H : Fin m → HolomorphicSections (n := d + 1)
    (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber)

def originalPhysicalCombinationSliceDensity (β : X → ℝ) (w : X → ℝ≥0∞)
    (q : ((Fin m → ℂ) × (ball c.ζ₀ c.r)) × c.tangentPatch) : ℝ≥0∞ :=
  ENNReal.ofReal (β (c.tangentPoint (q.1.2,q.2))) *
    ENNReal.ofReal (‖(c.tangentNormalDenominator (q.1.2,q.2))⁻¹ •
      c.originalAmbientLValue p.contMDiff (q.1.2,q.2) L
        (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
          (nativeBertiniHyperplaneBundle p)) L) H q.1.1 (c.tangentPoint (q.1.2,q.2)))‖ ^ 2) *
    w (c.tangentPoint (q.1.2,q.2))

def originalPhysicalCombinationSliceMass (β : X → ℝ) (w : X → ℝ≥0∞)
    (q : (Fin m → ℂ) × (ball c.ζ₀ c.r)) : ℝ≥0∞ :=
  ∫⁻ u, c.originalPhysicalCombinationSliceDensity L H β w (q,u) ∂c.tangentPatchVolume

theorem lowerSemicontinuous_originalPhysicalCombinationSliceDensity (a : X)
    (ha : c.e = complexChartAt (n := d + 1) a) (β : X → ℝ) (hβ : Continuous β)
    (w : X → ℝ≥0∞) (hw : LowerSemicontinuous w) :
    LowerSemicontinuous (c.originalPhysicalCombinationSliceDensity L H β w) := by
  let R : (((Fin m → ℂ) × (ball c.ζ₀ c.r)) × c.tangentPatch) →
      (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) := fun q => (q.1.1,(q.1.2,q.2))
  have hR : Continuous R := (continuous_fst.fst).prodMk ((continuous_fst.snd).prodMk continuous_snd)
  have hpoint : Continuous (fun q : ((Fin m → ℂ) × (ball c.ζ₀ c.r)) × c.tangentPatch => c.tangentPoint (q.1.2,q.2)) :=
    c.continuous_tangentPoint.comp ((continuous_fst.snd).prodMk continuous_snd)
  have hn := (c.continuous_originalNormalDivision_combination_norm a ha L H).comp hR
  have hb := ENNReal.continuous_ofReal.comp (hβ.comp hpoint)
  have hs := ENNReal.continuous_ofReal.comp (hn.pow 2)
  have hweight := hw.comp hpoint
  intro q
  exact SGPT.PSH.DirImg2.lowerSemicontinuousAt_mul
    (SGPT.PSH.DirImg2.lowerSemicontinuousAt_mul (hb.lowerSemicontinuous q) (hs.lowerSemicontinuous q)) (hweight q)

theorem lowerSemicontinuous_originalPhysicalCombinationSliceMass (a : X)
    (ha : c.e = complexChartAt (n := d + 1) a) (β : X → ℝ) (hβ : Continuous β)
    (w : X → ℝ≥0∞) (hw : LowerSemicontinuous w) :
    LowerSemicontinuous (c.originalPhysicalCombinationSliceMass L H β w) := by
  have hl := c.lowerSemicontinuous_originalPhysicalCombinationSliceDensity L H a ha β hβ w hw
  have hm (q : (Fin m → ℂ) × (ball c.ζ₀ c.r)) :
      Measurable (fun u : c.tangentPatch => c.originalPhysicalCombinationSliceDensity L H β w (q,u)) :=
    (hl.comp (continuous_const.prodMk continuous_id)).measurable
  have hp (u : c.tangentPatch) : LowerSemicontinuousOn
      (fun q : (Fin m → ℂ) × (ball c.ζ₀ c.r) => c.originalPhysicalCombinationSliceDensity L H β w (q,u)) univ :=
    (hl.comp (continuous_id.prodMk continuous_const)).lowerSemicontinuousOn univ
  exact lowerSemicontinuousOn_univ_iff.mp
    (SGPT.BBJ.lowerSemicontinuousOn_lintegral c.tangentPatchVolume
      (fun u q => c.originalPhysicalCombinationSliceDensity L H β w (q,u)) univ hm hp)

theorem originalPhysicalCombinationSliceMass_eq_localHodge (ζ : ball c.ζ₀ c.r)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint c.i ζ.val)) :
    letI := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
    letI := nativeBertiniMemberComplex p c.i ζ.val hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
    letI : MeasurableSpace (member p (affinePoint c.i ζ.val)) := borel _
    letI : BorelSpace (member p (affinePoint c.i ζ.val)) := ⟨rfl⟩
    ∀ (v : Fin m → ℂ) (β : X → ℝ) (w : X → ℝ≥0∞),
      c.originalPhysicalCombinationSliceMass L H β w (v,ζ) =
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p c.i ζ.val hsm))
        (nativeBertiniPhysicalAdjunctionSection p c.i ζ.val hsm L
          (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
            (nativeBertiniHyperplaneBundle p)) L) H v))
        ((c.originalSliceMemberSource ζ.val : Set _).indicator
          (fun y => ENNReal.ofReal (β y.val) * w y.val)) := by
  let := nativeBertiniMemberChartedSpace p c.i ζ.val hsm
  let := nativeBertiniMemberComplex p c.i ζ.val hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint c.i ζ.val)).isCompact
  let : MeasurableSpace (member p (affinePoint c.i ζ.val)) := borel _
  let : BorelSpace (member p (affinePoint c.i ζ.val)) := ⟨rfl⟩
  intro v β w
  let T := nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
    (nativeBertiniHyperplaneBundle p)) L) H v
  let W : member p (affinePoint c.i ζ.val) → ℝ≥0∞ := fun y => ENNReal.ofReal (β y.val) * w y.val
  have heq : c.originalPhysicalCombinationSliceMass L H β w (v,ζ) =
      ∫⁻ u : c.tangentPatch, c.originalOpenResidueDensity ζ L T W u.val ∂c.tangentPatchVolume := by
    apply lintegral_congr
    intro u
    unfold originalPhysicalCombinationSliceDensity originalOpenResidueDensity
    rw [dif_pos u.property]
    change ENNReal.ofReal (β (c.tangentPoint (ζ,u))) * _ * w (c.tangentPoint (ζ,u)) =
      _ * (ENNReal.ofReal (β (c.tangentPoint (ζ,u))) * w (c.tangentPoint (ζ,u)))
    ac_rfl
  exact heq.trans ((lintegral_subtype_comap c.isOpen_tangentPatch.measurableSet
    (c.originalOpenResidueDensity ζ L T W)).trans
      (c.originalMemberPhysicalHodgeEnergy_residueCoordinates ζ hsm L T W).symm)

end SGPT.Trace.Bertini.SliceChart
