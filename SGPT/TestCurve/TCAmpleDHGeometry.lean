import SGPT.LineBundle.AmpleCurvatureDomain
import SGPT.TestCurve.SrcRevDHMass

/-! Original ample geometry supplies the class data and a single flag-free DH limit. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.TestCurve.SrcRev
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Filter Set SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.TestCurve.TCEnc SGPT.NAPotential.NANS.TestConfig SGPT.TestCurve.MiscM
open scoped Topology ENNReal Nat

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] {E : ClosedProjectiveEmbedding f}

local instance : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (m + 1)
local instance [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- One original DH measure, with genuine ample class and mass data produced internally. -/
theorem geomLinearized_ample_DH_without_class_or_flag_input [IsIntegral X]
    {L : X.Modules} {a : LineBundleAtlas L} (H : SchemeLineBundleMetric f (m + 1) E L)
    (T : SGPT.TestCurve.GeomLin.GeomLinearizedTestConfiguration f a)
    (hA : T.IsAmple) (P : AmplePolarization f L) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∃ hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)),
      ∃ μ : FiniteMeasure ℝ,
        (μ.mass : ℝ) = P.selfIntersection (m + 1) ∧
        Tendsto (fun j : ℕ => (rescaledFiniteMeasure
          (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j).normalize)
            atTop (𝓝 μ.normalize) ∧
        μ = (P.selfIntersection (m + 1)).toNNReal • μ.normalize.toFiniteMeasure ∧
        ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
          μ = filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
            H Y hY hbig := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  obtain ⟨hHodge, hbig⟩ := AmpleChern.originalAmple_curvature_domain f (m + 1) E P a H
  obtain ⟨μ, hnorm, hmass, hμ⟩ := testConfiguration_normalized_tendsto_hodge H T.toTestConfiguration
    (T.filtrationFinitelyGenerated E hA) hHodge hbig
  have hR := (NNReal.continuous_coe.tendsto _).comp hmass
  have hRR := (P.tendsto_h0_selfIntersection (m + 1) a).comp (tendsto_add_atTop_nat 1)
  have hm : (μ.mass : ℝ) = P.selfIntersection (m + 1) :=
    tendsto_nhds_unique hR (hRR.congr fun j =>
      (rescaledFiniteMeasure_mass_coe (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j).symm)
  refine ⟨hbig, μ, hm, hnorm, ?_, hμ⟩
  conv_lhs => rw [μ.self_eq_mass_smul_normalize]
  rw [← hm, Real.toNNReal_coe]

end SGPT.TestCurve.SrcRev
