import SGPT.Okounkov.TranscendentalWNRegDNTEnvelope

/-! In complex dimension zero, every real obstacle is chart-smooth, so the
existing smooth-obstacle source contact formula applies without regularity.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/ZeroDimensionalEnvelope.lean` (module `ZeroDimensionalEnvelope`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ProductTestForms
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.PSH.VariableComplexAtlas SGPT.Okounkov.TranscendentalWNReg

namespace SGPT.NPP.Codex.ZeroDimensionalEnvelope
variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Every real function is chart-smooth in complex dimension zero. -/
theorem chartSmooth_of_dimension_zero (f : M → ℝ) : ChartSmooth (n := 0) f := by
  intro e
  have heq : (fun z : ComplexModel 0 => f (e.val.symm z)) = fun _ => f (e.val.symm 0) := by
    funext z
    rw [Subsingleton.elim z (0 : ComplexModel 0)]
  rw [heq]
  exact contDiffOn_const

/-- The original source obstacle-envelope formula in complex dimension zero,
for any real obstacle and any nonempty θ-PSH class. -/
theorem source_obstacle_formula_dimension_zero
    (w : KahlerBackground 0 M) (θ : AtlasClosedRealOneOneForm (ofFixedModel 0 M))
    (hne : ∃ ψ : M → EReal, (ofFixedModel 0 M).IsThetaPSH θ ψ) (f : M → ℝ) :
    ∃ hP : (ofFixedModel 0 M).IsThetaPSH θ
        (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)),
      sourcePotentialNonPluripolarMeasure θ
          (sourceRelativeEnvelope θ (fun _ => ⊤) fun x => (f x : EReal)) hP =
        (positiveTopMeasure w (atlasClosedFormToNative θ + ddcClosedForm f (chartSmooth_of_dimension_zero f))).restrict
          {x | sourceRelativeEnvelope θ (fun _ => ⊤) (fun y => (f y : EReal)) x = (f x : EReal)} := by
  exact sourceObstacleEnvelope_measure_eq w θ hne (chartSmooth_of_dimension_zero f)
end SGPT.NPP.Codex.ZeroDimensionalEnvelope
