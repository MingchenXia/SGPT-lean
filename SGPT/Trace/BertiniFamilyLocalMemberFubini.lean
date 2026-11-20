import SGPT.Trace.BertiniFamilyZeroExtension

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
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

def familyRawNormalMemberEnergy :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (_F : FlatData (d + 1) d (familyIncidence p i a v U)
      {y | scalarParameter p i a v U y = 0}) (_t : U) (_S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) (_w : familyIncidence p i a v U → ℝ≥0∞), ℝ≥0∞ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F t S w
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  exact nativePhysicalHodgeEnergy
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))
    (familyRawMemberAdjunctionSection p i a v U hsm L t S)
    ((familyNormalMemberSource p i a v U hsm F t : Set _).indicator
      (fun y => w (familyMemberLift p i a v U hsm t y)))

def familyRawNormalMemberMarginal :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (_F : FlatData (d + 1) d (familyIncidence p i a v U)
      {y | scalarParameter p i a v U y = 0}) (_S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) (_w : familyIncidence p i a v U → ℝ≥0∞), ℂ → ℝ≥0∞ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun F S w τ => if hτ : modelOneScalarEquiv.symm τ ∈ U then
    familyRawNormalMemberEnergy p i a v U hsm L F ⟨modelOneScalarEquiv.symm τ,hτ⟩ S w else 0

theorem familyRawNormalMemberMarginal_eq_normal :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U)
      {y | scalarParameter p i a v U y = 0}) (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) (w : familyIncidence p i a v U → ℝ≥0∞) (τ : ℂ),
      familyRawNormalMemberMarginal p i a v U hsm L F S w τ =
        ∫⁻ u : ComplexModel d, familyNormalBorelDensity p i a v U hsm L F S w
          (normalProductEquiv d (u,τ)) ∂volume := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S w τ
  have hinside (t : U) : familyRawNormalMemberEnergy p i a v U hsm L F t S w =
      ∫⁻ u : ComplexModel d, familyNormalBorelDensity p i a v U hsm L F S w
        (normalProductEquiv d (u,t.val 0)) ∂volume := by
    let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
    let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
    let := isCompact_iff_compactSpace.mp
      (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
    let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
    let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
    unfold familyRawNormalMemberEnergy
    rw [familyRawMemberPhysicalEnergy_normalResidue p i a v U hsm L F hF t S w]
    let D := fun u : ComplexModel d => familyNormalBorelDensity p i a v U hsm L F S w
      (normalProductEquiv d (u,t.val 0))
    have hsupp : Function.support D ⊆ familyNormalSliceDomain p i a v U hsm F t := by
      intro u hu
      by_contra hut
      exact hu (if_neg hut)
    calc
      _ = ∫⁻ u in familyNormalSliceDomain p i a v U hsm F t, D u ∂volume := by
        apply setLIntegral_congr_fun (familyNormalSliceDomain p i a v U hsm F t).isOpen.measurableSet
        intro u hu
        exact (if_pos hu).symm
      _ = _ := setLIntegral_eq_of_support_subset hsupp
  unfold familyRawNormalMemberMarginal
  by_cases hτ : modelOneScalarEquiv.symm τ ∈ U
  · rw [dif_pos hτ]
    have he : (modelOneScalarEquiv.symm τ) 0 = τ := modelOneScalarEquiv.apply_symm_apply τ
    simpa only [he] using hinside ⟨modelOneScalarEquiv.symm τ,hτ⟩
  · rw [dif_neg hτ]
    symm
    have hall : ∀ u : ComplexModel d, familyNormalBorelDensity p i a v U hsm L F S w
        (normalProductEquiv d (u,τ)) = 0 := by
      intro u
      by_cases hz : normalProductEquiv d (u,τ) ∈ F.flat.target
      · have hp := SGPT.Trace.BertiniExactNormalCoordinates.exact_normal_inverse hF hz
        rw [normalProductEquiv_last] at hp
        let q := finv F (normalProductEquiv d (u,τ))
        have he : q.val.1.val = modelOneScalarEquiv.symm τ := by
          apply modelOneScalarEquiv.injective
          rw [modelOneScalarEquiv.apply_symm_apply]
          exact hp
        exact False.elim (hτ (he ▸ q.val.1.property))
      · exact if_neg hz
    simp only [hall,lintegral_zero]

variable [MeasurableSpace X] [BorelSpace X] in
theorem familyRawNormalMemberMarginal_measurable :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U)
      {y | scalarParameter p i a v U y = 0}) (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      Measurable (fun q => ENNReal.ofReal (‖S q‖ ^ 2)) →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w → Measurable (familyRawNormalMemberMarginal p i a v U hsm L F S w) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S hS w hw
  have heq : familyRawNormalMemberMarginal p i a v U hsm L F S w =
      fun τ : ℂ => ∫⁻ u : ComplexModel d, familyNormalBorelDensity p i a v U hsm L F S w
        (normalProductEquiv d (u,τ)) ∂volume := by
    funext τ
    exact familyRawNormalMemberMarginal_eq_normal p i a v U hsm L F hF S w τ
  rw [heq]
  exact familyNormalMarginal_measurable_norm p i a v U hsm L F S hS w hw

variable [MeasurableSpace X] [BorelSpace X] in
theorem familyPhysical_integral_local_member_fubini :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U)
      {y | scalarParameter p i a v U y = 0}) (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      Measurable (fun q => ENNReal.ofReal (‖S q‖ ^ 2)) →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      (∫⁻ q in F.ambSource, ENNReal.ofReal (‖S q‖ ^ 2) * w q ∂familyMatchedVolume p i a v U hsm) =
        ∫⁻ τ : ℂ, familyRawNormalMemberMarginal p i a v U hsm L F S w τ ∂volume := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF S hS w hw
  rw [familyPhysical_integral_normal_fubini_measurable p i a v U hsm L F S hS w hw]
  apply lintegral_congr
  intro τ
  exact (familyRawNormalMemberMarginal_eq_normal p i a v U hsm L F hF S w τ).symm

end SGPT.Trace.BertiniFamilyCanonical
