import SGPT.TestCurve.TCZeroWeightMeasure
import SGPT.TestCurve.RWNClauseReduction
import SGPT.LineBundle.AmpleCurvatureDomain
import SGPT.PSH.SourceNonArchimedeanPotentials

/-! The literal original filtration source curve, manufactured from original ample data in dim 0. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.ZeroSource
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  [IsIntegral X] [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f)
local instance zeroSourceTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance zeroSourceCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance zeroSourceManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0
local instance zeroSourceMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance zeroSourceBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [IsIntegral X] in
private theorem envelope_eq_minimal [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace (SchemeComplexPoint f)] (θ : ClosedRealOneOneForm 0 (SchemeComplexPoint f))
    (u : SchemeComplexPoint f → EReal) (hu : IsThetaPshPotential θ.val u) :
    singularityEnvelope θ.val u = thetaPshSupremum θ.val := by
  let : Subsingleton (SchemeComplexPoint f) := SGPT.NPP.subsingleton_of_dim_zero
  let x : SchemeComplexPoint f := Classical.choice (inferInstance : Nonempty (SchemeComplexPoint f))
  have hfin := hu.quasiPshPotential.exists_finite x isOpen_univ (mem_univ x)
  obtain ⟨y, -, hybot, hytop⟩ := hfin
  have hc (z : SchemeComplexPoint f) : ((u y).toReal : EReal) = u z :=
    (EReal.coe_toReal hytop hybot).trans (congrArg u (Subsingleton.elim y z))
  have hz : IsThetaPshPotential θ.val (fun _ => (0 : EReal)) :=
    RooftopDimZero.isThetaPshPotential_of_dim_zero rfl
      (LocalPotentials.closedRealOneOne_hasLocalPotentials θ)
      (fun _ => by simp) (fun _ => by simp)
  have hV : thetaPshSupremum θ.val = 0 :=
    le_antisymm (thetaPshSupremum_le_zero θ.val) (le_thetaPshSupremum hz le_rfl)
  rw [hV]
  apply le_antisymm (singularityEnvelope_le_zero θ.val u)
  apply le_singularityEnvelope hz le_rfl
  refine ⟨-(u y).toReal, fun z _ => ?_⟩
  rw [← hc z, ← EReal.coe_add]
  simp

variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f 0 E L)

/-- Actual original low-parameter minimality, including its original closed endpoint. -/
theorem filtration_minimalClause :
  let := E.isSeparated
  let := E.quasiCompact
  TestConf.RWNMinimalClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0

  let : FiniteDimensional ℂ (SectionSpace f L 1) := SectionSpace.finiteDimensional f E a 1
  let : Nontrivial (SectionSpace f L 1) := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank ℂ (SectionSpace f L 1) by rw [ZeroDH.original_h0_eq_one E a 1]; omega)
  have hτ := RWN.neg_bound_sub_one_lt_slope_of_nontrivial F (k := 1) (by omega) inferInstance
  dsimp only
  intro τ hτC
  rw [F.testCurvePotential_eq_of_le_neg_bound H hτC
    (show -(F.bound : ℝ) - 1 ≤ -(F.bound : ℝ) by linarith)]
  exact envelope_eq_minimal (H.curvature a) _ (F.obstacle_isThetaPshPotential H hτ)

omit [IsIntegral X] in
/-- The actual original metric Chern class is big, from the same original ample line. -/
theorem filtration_curvature_big (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  IsBigClass (RealBottChern.ofRepresentative (H.curvature a)) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact (AmpleChern.originalAmple_curvature_domain f 0 E P a H).2

/-- All original open filtration slices are I-model; no clause is an input. -/
theorem filtration_iModelClause (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  TestConf.RWNIModelClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  exact RWN.rwnIModelClause_of_minimalClause F H (filtration_curvature_big E H P)
    (filtration_minimalClause E F H)

/-- The genuine original positive source curve with original filtration potential and cutoff. -/
def filtrationSourceCurve (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  SourcePositiveIModelTestCurve (TestConf.curvatureAtlasForm (a := a) H) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  exact ⟨TestConf.filtrationTestCurve F H (filtration_curvature_big E H P)
    (filtration_iModelClause E F H P) (filtration_minimalClause E F H),
   ⟨_, _, TestConf.filtrationTestCurve_mem_iModel F H (filtration_curvature_big E H P)
    (filtration_iModelClause E F H P) (filtration_minimalClause E F H)⟩⟩

@[simp] theorem filtrationSourceCurve_max (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  (filtrationSourceCurve E F H P).val.max = F.slope.toReal := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  rfl

/-- The original EReal cutoff is retained, rather than supplied as a certificate. -/
theorem filtrationSourceCurve_coe_max (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  (((filtrationSourceCurve E F H P).val.max : ℝ) : EReal) = F.slope := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  exact TestConf.coe_filtrationTestCurve_max F H (filtration_curvature_big E H P)
    (filtration_iModelClause E F H P) (filtration_minimalClause E F H)

@[simp] theorem filtrationSourceCurve_potential (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  ∀ τ : Iio (filtrationSourceCurve E F H P).val.max,
    (filtrationSourceCurve E F H P).val.potential τ = F.testCurvePotential H τ.val := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  dsimp only
  intro τ
  rfl

/-- Its literal original limit is V_theta of the same original metric. -/
theorem filtrationSourceCurve_limit (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  sourceTestCurveLimit (filtrationSourceCurve E F H P).val.toSourceTestCurvePredata =
      thetaPshSupremum (H.curvature a).val := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  rw [← TestConf.sourceMinimalEnvelope_curvatureAtlasForm H]
  exact TestConf.filtrationTestCurvePredata_limit F H (filtration_curvature_big E H P)
    (filtration_iModelClause E F H P) (filtration_minimalClause E F H)

end SGPT.TestCurve.ZeroSource
