import SGPT.Projective.OkounkovOriginalMultiplierEmbeddings
import SGPT.Projective.OkounkovOriginalQuotientMetric

/-! ONE genuine common ORIGINAL fixed twist, before ALL degrees and weights, with BOTH multiplier-value inclusions.
Blueprint: okounkov-original-common-multiplier-twist.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalCommonMultiplierTwist
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.AlmostSemigroup SGPT.Okounkov.AlgebraicValuation SGPT.Okounkov.OriginalDifference
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f) [IsSeparated f] [QuasiCompact f]
local instance commonMultiplierTwistTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance commonMultiplierTwistCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance commonMultiplierTwistManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- SAME genuine original fixed target twist and BOTH actual multiplier slice inclusions, no section/unit supplied. -/
theorem exists_common_fixed_positive_twist_multiplier_inclusions {L L' A : X.Modules}
    (a : LineBundleAtlas L) (b : LineBundleAtlas L') (d : LineBundleAtlas A)
    (H : SchemeLineBundleMetric f n E L) (K : SchemeLineBundleMetric f n E L')
    (J : SchemeLineBundleMetric f n E A) (hJ : (J.curvature d).val.IsKahler)
    (hclass : RealBottChern.ofRepresentative (H.curvature a) = RealBottChern.ofRepresentative (K.curvature b)) :
    ∃ k : ℕ, 0<k ∧ ∀ m : ℕ, 0<m →
      ∀ v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))), ∀ c : X, IsNonnegAt v c →
      ∀ r : LineBundleAtlas (bundleTensor (bundleTensorPower A k) (bundleTensorPower L' m)),
      ∀ φ ψ : SchemeComplexPoint f → EReal,
      (∀ z : ℝ, multiplierIdeal (n:=n) z φ = multiplierIdeal (n:=n) z ψ) →
        slice (AlgebraicValuation.multiplierSectionSet f n E v c a φ) (m:ℤ) ⊆
          AlgebraicValuation.twistedMultiplierValues f n E v c m r φ ∧
        slice (AlgebraicValuation.multiplierSectionSet f n E v c b ψ) (m:ℤ) ⊆
          AlgebraicValuation.twistedMultiplierValues f n E v c m r φ := by
  let q := originalDifferenceAtlas a b
  let Q := originalDifferenceMetric a b f n E H K
  have hQ := originalDifferenceMetric_class_zero a b f n E H K hclass
  let q' := originalDifferenceAtlas b b
  let Q' := originalDifferenceMetric b b f n E K K
  have hQ' := originalDifferenceMetric_class_zero b b f n E K K rfl
  obtain ⟨k,hk,huniform⟩ := NativeFrames.exists_uniform_original_class_zero_sections f n E d J hJ
  refine ⟨k,hk,?_⟩
  intro m hm v c hc r φ ψ hI
  obtain ⟨t,ht⟩ := huniform k le_rfl q Q hQ m hm c
  obtain ⟨t',ht'⟩ := huniform k le_rfl q' Q' hQ' m hm c
  refine ⟨OriginalMultiplierEmbeddings.multiplier_slice_subset_twisted_of_support_section f n E a b d
    v hc m k hm (NativeFrames.originalMixedPowerAtlas q d m k) r t ht φ,?_⟩
  have hother := OriginalMultiplierEmbeddings.multiplier_slice_subset_twisted_of_support_section f n E b b d
    v hc m k hm (NativeFrames.originalMixedPowerAtlas q' d m k) r t' ht' ψ
  have heq : AlgebraicValuation.twistedMultiplierValues f n E v c m r φ =
      AlgebraicValuation.twistedMultiplierValues f n E v c m r ψ := by
    unfold AlgebraicValuation.twistedMultiplierValues
    rw [hI (m:ℝ)]
  rw [heq]
  exact hother

end SGPT.Okounkov.OriginalCommonMultiplierTwist
