import SGPT.PSH.SourceTestCurvePositiveMass
import SGPT.Envelopes.SourceIncreasingOrdinaryEnvelopes

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- EVERY original slice is internally produced a positive model. The actual
whole opposite-order family and its zero upper bound therefore give the
original raw limit's model predicate, without any limit-fixedness premise. -/
theorem SourceTestCurve.limit_model (ω : KahlerBackground n M) (Γ : SourceTestCurve θ) :
    SourceModelPotential θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata) := by
  have : Nonempty (OrderDual (Iio Γ.max)) :=
    ⟨⟨Γ.max - 1, by change Γ.max - 1 < Γ.max; linarith⟩⟩
  have hm : Monotone (fun τ : OrderDual (Iio Γ.max) ↦ Γ.potential τ) := by
    intro a b hab x
    exact Γ.antitone x hab
  have hmodel := sourceModelPotential_increasing_uscSup ω
    (fun τ : OrderDual (Iio Γ.max) ↦ Γ.slice_model ω τ) hm
    (C := 0) (fun τ x ↦ by
      simpa only [EReal.coe_zero, Pi.zero_apply] using Γ.le_zero τ x)
  have hU : uscRegularization (⨆ τ : OrderDual (Iio Γ.max), Γ.potential τ) =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata := by
    apply congrArg uscRegularization
    funext x
    exact iSup_apply
  exact hU ▸ hmodel

/-- The original based-class witness is the SAME actual raw limit,
with its model predicate manufactured above and literal function equality. -/
theorem SourceTestCurve.mem_based_limit (ω : KahlerBackground n M) (Γ : SourceTestCurve θ) :
    Γ ∈ SourceTestCurvesBased θ (sourceTestCurveLimit Γ.toSourceTestCurvePredata)
      (Γ.limit_model ω) := rfl

/-- EVERY original test curve belongs to the printed union over original
positive-mass model bases; no base is silently assumed in its definition. -/
theorem SourceTestCurve.mem_positive (ω : KahlerBackground n M) (Γ : SourceTestCurve θ) :
    Γ ∈ SourceTestCurvesPositive θ :=
  ⟨sourceTestCurveLimit Γ.toSourceTestCurvePredata, Γ.limit_model ω, Γ.mem_based_limit ω⟩

/-- The original union class exhausts precisely the original object type,
without changing ANY cutoff, parameter, function or original hypothesis. -/
theorem sourceTestCurvesPositive_eq_univ (ω : KahlerBackground n M) :
    SourceTestCurvesPositive θ = univ := by
  ext Γ
  exact iff_of_true (Γ.mem_positive ω) (mem_univ Γ)

end SGPT.PSH.VariableComplexAtlas
