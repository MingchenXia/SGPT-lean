import SGPT.Foundations.Analysis.Pending.NormalizedTraceBackgroundMonotonicity
import SGPT.Foundations.Analysis.Pending.TraceIdealOrderMonotonicity

set_option autoImplicit false

/-! # Actual normalized trace input ideal-order and background comparison -/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.NormalizedTraceIdealOrderComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder FirstPass.IEnvelope
  DiagonalMass PositiveNormalizedTrace NumericalTraceMass NormalizedTraceBackgroundMonotonicity
  SingularGlobalPOrder

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]


/-- Full original readers produce genuine global trace order; positive right
mass and actual background semipositivity yield literal normalized comparison. -/
theorem normalizedTraceAlong_le_of_iOrder_of_semipositive_difference
    (omega₀ omega₁ : KahlerBackground n M) (omegaV₀ omegaV₁ : KahlerBackground k V)
    {ι : V → M} (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ σ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (horder : IOrderOnManifold (n := n) u v)
    (hsemi : (σ - θ).val.IsSemipositive)
    (hdefined₀ : HasPositiveTraceRepresentativeAlong omega₀ omegaV₀ hι θ u)
    (hdefined₁ : HasPositiveTraceRepresentativeAlong omega₁ omegaV₁ hι σ v) :
    normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀ ≤
      normalizedTraceAlong omega₁ omegaV₁ hι σ v hdefined₁ := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ξ := ClosedRealOneOneForm.pullback hι σ
  let A := normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀
  let B := normalizedTraceAlong omega₁ omegaV₁ hι σ v hdefined₁
  have hA : IsModelPotential η A := (normalizedTraceAlong_models omega₀ omegaV₀ hι θ u hdefined₀).1
  have hB : IsModelPotential ξ B := (normalizedTraceAlong_models omega₁ omegaV₁ hι σ v hdefined₁).1
  have hTu := isTraceRepresentativeAlong_normalizedTraceAlong omega₀ omegaV₀ hι θ u hdefined₀
  have hTv := isTraceRepresentativeAlong_normalizedTraceAlong omega₁ omegaV₁ hι σ v hdefined₁
  have hglobal : SourcePOrder (n := k) A B :=
    TraceIdealOrderMonotonicity.sourcePOrder_of_iOrder_of_isTraceRepresentativeAlong
      omegaV₀ omegaV₁ hι hTu hTv horder
  have hpull : ClosedRealOneOneForm.pullback hι (σ - θ) = ξ - η := by
    apply ClosedRealOneOneForm.ext
    intro e z
    ext w
    rfl
  have hdiff : (ξ - η).val.IsSemipositive := by
    rw [← hpull]
    exact ClosedRealOneOneForm.pullback_isSemipositive hι hsemi
  have hAξ : IsThetaPshPotential ξ.val A := by
    simpa only [add_sub_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hA.plurisubharmonic hdiff
  have hfixed : POrderWith ξ A B :=
    PositiveReferenceGlobalPOrder.pOrderWith_of_sourcePOrder_of_positive_right_mass
      omegaV₀ ξ hAξ hB.plurisubharmonic hB.positive_mass hglobal
  have hA0 : A ≤ 0 := by
    rw [hA.envelope_eq]
    exact singularityEnvelope_le_zero η.val A
  have hself : A ≤ singularityEnvelope ξ.val A :=
    le_singularityEnvelope hAξ hA0 ⟨0, by intro x _; simp⟩
  intro x
  exact (hself x).trans ((hfixed x).trans_eq (congrFun hB.envelope_eq x).symm)

end
end SGPT.Foundations.Analysis.Pending.NormalizedTraceIdealOrderComparison
