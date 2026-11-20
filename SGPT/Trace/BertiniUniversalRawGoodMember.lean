import SGPT.Trace.BertiniUniversalStep2IdealEquality
import SGPT.Trace.BertiniUniversalRawWeight

/-! RAW original book good-set membership, consuming only actual all-high
Step1.4 H0-image equalities on the nondegenerate branch. The all-bot
branch, reduced smooth member and actual book stalk identity are produced. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter TensorProduct
open scoped Manifold ContDiff Topology ENNReal TensorProduct
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.NativeKodairaPullback
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft SGPT.Trace.Bertini
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X] [ConnectedSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (ζ : ComplexModel N)
  (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))

theorem mem_book_bertiniGoodSet_of_raw_step14
    (G U : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    (hG : IsSourceSmoothHermitianMetric G) (hU : IsSourceSmoothHermitianMetric U)
    (hGpos : (sourceNativeFirstChernForm G hG).val.IsKahler)
    (φ : X → EReal) (hφraw : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    (∀ hφ : IsGlobalQuasiPshPotential (n := d + 1) φ, ∃ k₀ : ℕ,
      ∀ k : ℕ, k₀ ≤ k → let L := twistedPower G U k
        (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ).range =
          fullHolomorphicIdealSections (n := d)
            (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
              (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
            (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val))) →
    affinePoint i ζ ∈ bertiniGoodSet p p.contMDiff φ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  intro hStep14
  have hdim : IsSmoothMemberOfDim p p.contMDiff (affinePoint i ζ) d :=
    isSmoothMemberOfDim_of_isSmoothHypersurfaceMember p p.contMDiff hsm
  refine ⟨d,Nat.le_succ d,hdim,?_⟩
  obtain hbot | hglobal := raw_qpsh_eq_bot_or_original_global hφraw
  · have hφeq : φ = (⊥ : X → EReal) := funext hbot
    have hφres : (fun y : member p (affinePoint i ζ) => φ y.val) =
        (⊥ : member p (affinePoint i ζ) → EReal) := funext (fun y => hbot y.val)
    rw [hφres,hφeq]
    exact regular_bot_multiplierIdeal_book_restriction
      (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)) (Nat.le_succ d) hdim.1 (c := 1) zero_lt_one
  · obtain ⟨k₀,hImages⟩ := hStep14 hglobal
    exact book_multiplierIdeal_equality_of_all_high_physical_H0_images p i ζ hsm G U hG hU hGpos
      φ hglobal k₀ hImages

end SGPT.Trace.BertiniUniversal
