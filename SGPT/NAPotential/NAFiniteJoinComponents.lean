import SGPT.NAPotential.Supremum
import SGPT.NAPotential.IncreasingDivisorialSup

/-! Literal actual finite NA components and original USC-supremum transforms.
Blueprint: operation-usc-supremum.tex. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace SGPT.PSH.VariableComplexAtlas
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The literal actual finite NA join has the actual finite curve join
at EACH original geometric component. No supplied component identity. -/
theorem SourceNAPotential.finiteJoin_component_val {I : Type v}
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (s : Finset I) (hs : s.Nonempty) (κ : SourceKahlerForm n M) :
    ((SourceNAPotential.finiteJoin omega Γ s hs).component κ).val =
      SourceTestCurve.finiteJoin (sourceKahlerFormRepresentative κ)
        (fun i => ((Γ i).component κ).val) s hs := by
  let finiteComponentNASup : SemilatticeSup (SourceNAPotential θ) := sourceNASemilatticeSup omega θ
  let finiteComponentCurveSup : SemilatticeSup (SourceTestCurve (sourceNAComponentBackground θ κ)) :=
    sourceTestCurveSemilatticeSup (sourceKahlerFormRepresentative κ) _
  exact Finset.apply_sup'_eq_sup'_comp hs
    (fun G : SourceNAPotential θ => (G.component κ).val) (fun _ _ => rfl)

end SGPT.PSH.VariableComplexAtlas
namespace SGPT.NAPotential.BJPrep
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The SAME actual source USC supremum has the supremum of the actual
finite NA join transforms, with all finite-component/net data internal. -/
theorem naDivisorialTransform_uscSup_finiteJoin {I : Type v} [Nonempty I]
    (omega : KahlerBackground n M) (Γ : I → SourceNAPotential θ)
    (hb : BddAbove (range fun i => sourceNAPotentialCutoff omega (Γ i)))
    (κ : SourceKahlerForm n M) (p : PrimePresentation n M)
    {t : ℝ} (ht : 0 < t) :
    naDivisorialTransform (SourceNAPotential.uscSup omega Γ hb) κ p t =
      ⨆ F : SourceTestCurveFiniteIndex I,
        naDivisorialTransform (SourceNAPotential.finiteJoin omega Γ F.1 F.2) κ p t := by
  change curveDivisorialTransform
    (SourceTestCurve.generalSup (sourceKahlerFormRepresentative κ)
      (fun i => ((Γ i).component κ).val)
      (sourceNAFamily_component_bddAbove omega Γ hb κ)).toSourceTestCurvePredata p t = _
  rw [SourceTestCurve.generalSup,curveDivisorialTransform_increasingSup _ _ _ _ p ht]
  apply iSup_congr
  intro F
  simp only [naDivisorialTransform,SourceNAPotential.finiteJoin_component_val,
    sourceTestCurveFiniteJoinFamily]

end SGPT.NAPotential.BJPrep
