import SGPT.LineBundle.AmpleChernZeroEnvelope
import SGPT.LineBundle.IntersectionAmple
import SGPT.GAGA.SmoothFlagsScheme

/-! The independent algebraic flag-length Hilbert limit and analytic/GAGA
Bergman limit of the SAME original section dimensions give the Chern integral. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.LineBundle.AmpleChern
open Set Filter MeasureTheory CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open scoped Topology ENNReal Nat
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Okounkov SGPT.IGood.Misc2VolBigL

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [Nonempty (SchemeComplexPoint f)]

local instance ampleChernTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance ampleChernCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance ampleChernManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance ampleChernMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance ampleChernBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- The algebraic ample self-intersection is the actual smooth Chern top
integral. The same original h0 dimensions are used for both limits, and
both asymptotic theorems and GAGA are already proved producers. -/
theorem selfIntersection_eq_slotIntegral_of_semipositive
    {L : X.Modules} (P : AmplePolarization f L) (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f (m + 1) E L)
    (hsemi : let := E.isSeparated; let := E.quasiCompact;
      (H.curvature a).val.IsSemipositive) :
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    ∀ κ : KahlerBackground (m + 1) (SchemeComplexPoint f),
      P.selfIntersection (m + 1) = slotIntegral κ (fun _ : Fin (m + 1) => H.curvature a) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  dsimp only
  intro κ
  let θ := H.curvature a
  have hzero : IsThetaPshPotential θ.val (fun _ : SchemeComplexPoint f => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff θ).mpr hsemi
  have hV0 := thetaPshSupremum_eq_zero_of_semipositive θ hsemi
  have hV : IsThetaPshPotential θ.val (thetaPshSupremum θ.val) := by
    rw [hV0]
    exact hzero
  have hDX := SGPT.GAGA.SmoothFlags.dxMain1UntwistedStatement X f E m L a H _ hV
  have hAna := tendsto_normalized_h0_of_dxMain1Holds f E a H hV hDX
  have hAlg := P.tendsto_h0_selfIntersection (m + 1) a
  have hAlgE : Tendsto (fun k : ℕ => ENNReal.ofReal
      (((m + 1)! : ℝ) * (h0 f L k : ℝ) / (k : ℝ) ^ (m + 1))) atTop
      (𝓝 (ENNReal.ofReal (P.selfIntersection (m + 1)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hAlg
  have hsame : (fun k : ℕ => ENNReal.ofReal
      (((m + 1)! : ℝ) * (h0 f L k : ℝ) / (k : ℝ) ^ (m + 1))) =ᶠ[atTop]
      (fun k : ℕ => (((m + 1)! : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    rw [ENNReal.ofReal_div_of_pos (pow_pos (by exact_mod_cast hk) _),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hEq : ENNReal.ofReal (P.selfIntersection (m + 1)) =
      diagonalPotentialMass θ (thetaPshSupremum θ.val) hV :=
    tendsto_nhds_unique (hAlgE.congr' hsame) hAna
  have hreal := congrArg ENNReal.toReal hEq
  rw [ENNReal.toReal_ofReal (P.selfIntersection_nonneg (m + 1))] at hreal
  exact hreal.trans (minimal_mass_toReal_eq_slotIntegral_of_semipositive
    (Nat.succ_pos m) κ θ hsemi hV)

end SGPT.LineBundle.AmpleChern
