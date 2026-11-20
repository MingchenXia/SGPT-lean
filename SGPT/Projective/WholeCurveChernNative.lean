import SGPT.Projective.WholeCurveChernDegree
import SGPT.Bergman.SiuNativeProjectiveNS

/-! Actual component backgrounds manufactured from original whole background;
ENTIRE original effective-section degree/Chern endpoint with no component input.
Blueprint: whole-curve-chern-native.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass
open SGPT.Okounkov SGPT.BDivisor.NSKodaira
open scoped Topology Manifold BigOperators ContDiff
attribute [local instance] componentPeriodTopology componentPeriodCharts componentPeriodManifold
  componentPeriodMeasurable componentPeriodBorel actualComponentSmooth actualComponentSeparated
  actualComponentQuasiCompact actualComponentTopology actualComponentCharts actualComponentManifold
  actualComponentMeasurable actualComponentBorel actualComponentCompact

/-- SAME original pullback background on EVERY original whole actual projective component, all dimensions. -/
def originalProjectiveComponentBackground {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) (κ : KahlerBackground n (SchemeComplexPoint f))
    (C : ↥(_root_.irreducibleComponents X)) : KahlerBackground n
      (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) := by
  let hι := schemeComplexPointMap_contMDiff f
    (smoothProjectiveComponentOpen f n E C.val C.property).ι n n ∞
  refine ⟨ClosedRealOneOneForm.pullback hι κ.form, ?_⟩
  have hd := SGPT.NAPotential.NativeSchemeImmersion.openImmersion_mfderiv_injective
    ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f) f
    (smoothProjectiveComponentOpen f n E C.val C.property).ι rfl n
  have hc := coordinateMap_fderiv_injective_of_native_mfderiv hι hd
  exact SmoothRealForm.IsKahler.pullback_of_injective hι (fun e d _ hz => hc e d hz) κ.isKahler

/-- ENTIRE original curve effective-section degree/Chern identity, ONLY original whole κ supplied. -/
theorem wholeCurveSectionZeroCycleDegree_eq_ChernPeriod {X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
    (s : Γ(L, ⊤)) (hs : SectionNonzeroOnComponents f E s)
    (b : Spec (.of ℂ)) (κ : KahlerBackground 1 (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ((wholeCurveSectionZeroCycleDegree f E a s hs b : ℤ) : ℝ) =
      slotIntegral κ (Fin.snoc (fun i : Fin 0 => Fin.elim0 i) (H.curvature a)) :=
  wholeCurveSectionZeroCycleDegree_eq_originalChernPeriod f E a H s hs b κ
    (originalProjectiveComponentBackground f 1 E κ)

end SGPT.Projective.NumEq.AlgebraicCurveDegree
