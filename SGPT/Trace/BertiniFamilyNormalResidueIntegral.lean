import SGPT.Trace.BertiniFamilyMemberNormalIntegral
import SGPT.Trace.BertiniFamilyMemberRestriction

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

private def actualMemberTangentModel (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexModel d → ComplexModel (d + 1) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  exact fun u => familyMemberTangent p i a v U hsm q.val.1 y u


def familyNormalMemberModelTangent :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0}),
      (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) →
      ∀ (z : ComplexModel (d + 1)), z ∈ F.flat.target → Fin d → ComplexModel d := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF z hz
  exact fun j => familyNormalMemberTangent p i a v U hsm F hF z hz j

theorem familyNormalMemberParameter_tangent :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      ∀ (u : familyNormalSliceDomain p i a v U hsm F t) (j : Fin d),
      (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d)
        (familyNormalMemberParameter p i a v U hsm F hF t) u
        ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j) : ComplexModel d) =
      familyNormalMemberModelTangent p i a v U hsm F hF (normalProductEquiv d (u.val,t.val 0)) u.property j := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  dsimp only
  intro u j
  let g := familyNormalMemberParameter p i a v U hsm F hF t
  let z := normalProductEquiv d (u.val,t.val 0)
  let q := finv F z
  let q' := familyMemberLift p i a v U hsm t (g u)
  have hq : q' = q := familyNormalMemberParameter_familyLift p i a v U hsm F hF t u
  let C := actualMemberTangentModel p i a v U hsm
  have hC : C q' = C q := congrArg C hq
  have h := mfderiv_familyNormalMemberParameter_lift p i a v U hsm F hF t u
    ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)
  change C q' (mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g u
    ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)) =
    familyNormalChartTangentEquiv p i a v U hsm F z u.property
      (normalProductEquiv d ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j,0)) at h
  rw [hC,normalProductEquiv_basis] at h
  have hi : Function.Injective (C q) := familyMemberTangent_injective p i a v U hsm q.val.1 ⟨q.val.2,q.property⟩
  apply hi
  exact h.trans (familyNormalMemberTangent_lift p i a v U hsm F hF z u.property j).symm


variable [CompactSpace X] (L : HermitianHolomorphicLineBundle (d + 1) X)

private def actualMemberTopNormSq (q : familyIncidence p i a v U) :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    (Fin d → ComplexModel d) → (familyNativePhysicalModel p i a v U hsm L).Fiber q → ℝ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  let := nativeBertiniMemberChartedSpace p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := nativeBertiniMemberComplex p i (a - q.val.1.val 0 • v) (hsm q.val.1)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - q.val.1.val 0 • v))).isCompact
  let LH := nativeHolomorphicPullbackBundle L
    (nativeBertiniMemberInclusionMap p i (a - q.val.1.val 0 • v) (hsm q.val.1))
  let y : member p (affinePoint i (a - q.val.1.val 0 • v)) := ⟨q.val.2,q.property⟩
  exact fun tuple T => ‖nativeCanonicalPhysicalValue LH y tuple
    (nativeBertiniPhysicalAdjunctionFiberEquiv p i (a - q.val.1.val 0 • v) (hsm q.val.1) L y T)‖ ^ 2


theorem familyNormalPhysicalDensity_eq_memberOpenDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
      ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
        (w : familyIncidence p i a v U → ℝ≥0∞) (u : familyNormalSliceDomain p i a v U hsm F t),
      familyNormalPhysicalDensity p i a v U hsm L F S w (normalProductEquiv d (u.val,t.val 0)) =
      nativeCanonicalPhysicalOpenDensity (familyNormalSliceDomain p i a v U hsm F t)
        (familyNormalMemberParameter p i a v U hsm F hF t)
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))
        (familyNativeMemberAdjunctionSection p i a v U hsm L t S)
        (fun y => w (familyMemberLift p i a v U hsm t y)) u.val := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  dsimp only
  intro S w u
  let g := familyNormalMemberParameter p i a v U hsm F hF t
  let z := normalProductEquiv d (u.val,t.val 0)
  let q := finv F z
  let q' := familyMemberLift p i a v U hsm t (g u)
  let tuple : Fin d → ComplexModel d := fun j => mfderiv 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel d) g u
    ((EuclideanSpace.basisFun (Fin d) ℂ).toBasis j)
  have hq : q' = q := familyNormalMemberParameter_familyLift p i a v U hsm F hF t u
  have htup : tuple = familyNormalMemberTangent p i a v U hsm F hF z u.property := by
    funext j
    exact familyNormalMemberParameter_tangent p i a v U hsm F hF t u j
  have hnorm := congrArg (fun r => actualMemberTopNormSq p i a v U hsm L r tuple (S r)) hq
  have hnorm' : actualMemberTopNormSq p i a v U hsm L q' tuple (S q') =
      ‖familyNormalMemberValue p i a v U hsm L F hF z u.property (S q)‖ ^ 2 := by
    apply hnorm.trans
    rw [htup]
    rfl
  rw [familyNormalPhysicalDensity_eq_member p i a v U hsm L F hF S w z u.property]
  unfold nativeCanonicalPhysicalOpenDensity
  rw [dif_pos u.property]
  change ENNReal.ofReal (‖familyNormalMemberValue p i a v U hsm L F hF z u.property (S q)‖ ^ 2) * w q =
    ENNReal.ofReal (actualMemberTopNormSq p i a v U hsm L q' tuple (S q')) * w q'
  rw [hnorm',hq]


theorem familyMemberPhysicalEnergy_normalResidue :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0})
      (_hF : ∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) (t : U),
      letI := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
      letI := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
      letI := isCompact_iff_compactSpace.mp
        (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
      letI : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
      letI : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
      ∀ (S : HolomorphicSections (n := d + 1) (familyNativePhysicalModel p i a v U hsm L).Fiber)
        (w : familyIncidence p i a v U → ℝ≥0∞),
      nativePhysicalHodgeEnergy
        (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i (a - t.val 0 • v) (hsm t)))
        (familyNativeMemberAdjunctionSection p i a v U hsm L t S)
        ((familyNormalMemberSource p i a v U hsm F t : Set _).indicator
          (fun y => w (familyMemberLift p i a v U hsm t y))) =
      ∫⁻ z in familyNormalSliceDomain p i a v U hsm F t,
        familyNormalPhysicalDensity p i a v U hsm L F S w (normalProductEquiv d (z,t.val 0)) ∂volume := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro F hF t
  let := nativeBertiniMemberChartedSpace p i (a - t.val 0 • v) (hsm t)
  let := nativeBertiniMemberComplex p i (a - t.val 0 • v) (hsm t)
  let := isCompact_iff_compactSpace.mp
    (isClosed_member p p.contMDiff.continuous (affinePoint i (a - t.val 0 • v))).isCompact
  let : MeasurableSpace (member p (affinePoint i (a - t.val 0 • v))) := borel _
  let : BorelSpace (member p (affinePoint i (a - t.val 0 • v))) := ⟨rfl⟩
  dsimp only
  intro S w
  rw [familyMemberPhysicalEnergy_normalCoordinates p i a v U hsm L F hF t]
  apply setLIntegral_congr_fun (familyNormalSliceDomain p i a v U hsm F t).isOpen.measurableSet
  intro z hz
  exact (familyNormalPhysicalDensity_eq_memberOpenDensity p i a v U hsm L F hF t S w ⟨z,hz⟩).symm

end SGPT.Trace.BertiniFamilyCanonical
