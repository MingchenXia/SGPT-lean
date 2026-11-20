import SGPT.Trace.NativeCanonicalOpenCoordinateIntegral

/-! Produced actual member geometry specializes the genuine intrinsic Hodge COV. -/
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
open SGPT.Bergman.TensorDictionaryDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))

theorem familyNormalMemberParameter_injective :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      Function.Injective (familyNormalMemberParameter p i a v U hsm F hF t) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  intro u w huw
  let H := familyNormalMemberHomeomorph p i a v U hsm F hF t
  apply H.symm.injective
  exact Subtype.ext huw

theorem familyNormalMemberParameter_range :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      Set.range (familyNormalMemberParameter p i a v U hsm F hF t) =
        familyNormalMemberSource p i a v U hsm F t := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  dsimp only
  ext y
  constructor
  · rintro ⟨u,rfl⟩
    exact (familyNormalMemberOpenParameter p i a v U hsm F hF t u).property
  · intro hy
    refine ⟨familyNormalMemberCoordinates p i a v U hsm F hF t ⟨y,hy⟩,?_⟩
    exact congrArg Subtype.val (familyNormalMemberOpenParameter_coordinates p i a v U hsm F hF t ⟨y,hy⟩)

variable [CompactSpace X] (L : HermitianHolomorphicLineBundle (d + 1) X)

theorem familyMemberPhysicalEnergy_normalCoordinates :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
      letI : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
      letI : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
      ∀ (S : ∀ y, (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i (a - t.val 0 • v))))
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))).Fiber y)
        (w : member p (affinePoint i (a - t.val 0 • v)) → ℝ≥0∞),
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))) S
        ((familyNormalMemberSource p i a v U hsm F t : Set _).indicator w) =
      ∫⁻ z in familyNormalSliceDomain p i a v U hsm F t,
        nativeCanonicalPhysicalOpenDensity (familyNormalSliceDomain p i a v U hsm F t)
          (familyNormalMemberParameter p i a v U hsm F hF t)
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))) S w z ∂volume := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  intro S w
  exact nativePhysicalHodgeEnergy_openCoordinates
    (familyNormalSliceDomain p i a v U hsm F t) (familyNormalMemberParameter p i a v U hsm F hF t)
    (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t))) S w
    (familyNormalMemberSource p i a v U hsm F t)
    (familyNormalMemberParameter_injective p i a v U hsm F hF t)
    (familyNormalMemberParameter_range p i a v U hsm F hF t)

end SGPT.Trace.BertiniFamilyCanonical
