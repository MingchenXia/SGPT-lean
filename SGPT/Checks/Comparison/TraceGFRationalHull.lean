import SGPT.Checks.Comparison.TraceGFSectionPullback
import SGPT.Checks.Comparison.GFRationalHull

/-! Actual original rational hulls under the actual semi-valuation restriction map.
Source `thm:comp_traceop`, `eq:varphiAncordF`; blueprint `trace-na-compatibility.tex`.
The common-degree products come from the ORIGINAL rational-hull producer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open SGPT.Foundations.Envelope
open scoped ENNReal Classical

variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]

local instance traceHullProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceHullPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceHullPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceHullPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {g : Y ⟶ Spec (.of ℂ)} [IsProper g]
  (H : SchemeLineBundleMetric f n E L)

/-- The ACTUAL normalized original section maximum on X, evaluated at the
ACTUAL image of ANY original point of Y, is the SAME valuation of the entire
actual restricted family. Sections restricting to zero remain in the family. -/
theorem potentialAn_sectionMaximum_schemeAnMap_eq (a : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K) {J : Type} [Fintype J] [Nonempty J]
    (t : J → bundlePowerGlobalSections L N) (ht : ∀ j, t j ≠ 0)
    (i : Y ⟶ X) (hi : i ≫ f = g) (w : BerkovichPoint g) :
    potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
        sectionsMaxLog f n E a N t H p) (schemeAnMap i hi w) =
      -((w.idealVal (⨆ j, sectionZeroIdealSheaf ((a.tensorPower N).nativePullback i)
          (Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j))) /
            K : ℝ≥0∞) : EReal) := by
  rw [potentialAn_sectionsMaxLog_all_narrow f n E H a N t ht hK]
  exact (normalized_actual_sectionFamily_pullback i hi (a.tensorPower N) t K w).symm

/-- Every ORIGINAL rational hull slice has a manufactured actual common-degree
family of products whose TRUE restriction computes its value on ALL original
points of Y. No hull, section, ideal or valuation equality is a supplied premise. -/
theorem exists_originalHull_actual_restrictedSectionFamily (a : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (D : PiecewiseLinearData θ) (hτ : ∀ j, ∃ q : ℚ, D.τ j = q)
    (I : Fin (D.N + 1) → Type) [∀ j, Fintype (I j)] [∀ j, Nonempty (I j)]
    (t : (j : Fin (D.N + 1)) → I j → bundlePowerGlobalSections L N)
    (ht : ∀ j k, t j k ≠ 0)
    (hA : ∀ j, D.A j = fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      finiteMaximum (fun k => H.sectionLogNormSq a N (t j k)) p)
    (q : ℚ) (hq : (q : ℝ) ≤ D.τ 0) (i : Y ⟶ X) (hi : i ≫ f = g) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ F : ActualSectionFamily L (N * Q),
      (∀ j, F.sections j ≠ 0) ∧
      ∀ w : BerkovichPoint g,
        potentialAn n E (uscRegularization (D.pointwiseUpperConcaveEnvelope (q : ℝ)))
            (schemeAnMap i hi w) =
          -((w.idealVal (⨆ j, sectionZeroIdealSheaf
              ((a.tensorPower (N * Q)).nativePullback i)
              (Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L (N * Q))
                (F.sections j))) / (K * Q) : ℝ≥0∞) : EReal) := by
  obtain ⟨Q, hQ, F, hF, heq, _hval⟩ :=
    exists_originalHull_commonSectionFamily n E H a N K hK D hτ I t ht hA q hq
  refine ⟨Q, hQ, F, hF, fun w => ?_⟩
  rw [heq]
  simpa only [Nat.cast_mul, sectionsMaxLog, RationalHull.finiteMaximum] using
    potentialAn_sectionMaximum_schemeAnMap_eq f n E H a (N * Q) (K * Q)
      (Nat.mul_pos hK hQ) F.sections hF i hi w

end SGPT.NAPotential.TraceComparison
