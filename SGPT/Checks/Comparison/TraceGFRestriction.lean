import SGPT.Checks.Comparison.TraceRawSectionTransport
import SGPT.Checks.Comparison.TraceGFGlobalAnalyticType
import SGPT.Checks.Comparison.TraceGFNonzeroFamily
import SGPT.Checks.Comparison.TraceGFRationalHull
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Okounkov.AlgebraicSectionBodies

/-! Literal original physical FS restriction, with true actual sections/metrics/ideals.
Source `eq:varphiAncordF` in `thm:comp_traceop`; blueprint `trace-gf-restriction.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.GfIm
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves GlobalAnalyticSingularities
open scoped Topology Manifold ContDiff

variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))

local instance traceFSXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceFSYProper : IsProper (i ≫ f) :=
  (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceFSXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceFSYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceFSXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceFSYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceFSXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceFSYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k

/-- **The literal ORIGINAL normalized physical FS function analytifies compatibly
with its literal ORIGINAL analytic restriction at EVERY original Y-point.**
Actual pulled sections, a physical metric, whole ideal equality and bounded
singularity comparison are manufactured internally. All poles/dimension0 included. -/
theorem potentialAn_sectionMaximum_restriction_eq (a : LineBundleAtlas L)
    (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∀ j, t j ≠ 0)
    (htY : ∃ j, Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j) ≠ 0)
    (w : BerkovichPoint (i ≫ f)) :
    potentialAn k EY
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p)) w =
      potentialAn n EX (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
        sectionsMaxLog f n EX a N t H p) (schemeAnMap i rfl w) := by
  classical
  let : CompactSpace (SchemeComplexPoint (i ≫ f)) := EY.analyticCompact
  let P := (Scheme.Modules.pullback i).obj (bundleTensorPower L N)
  let b : LineBundleAtlas P := (a.tensorPower N).nativePullback i
  let HP := schemeLineBundleMetric (i ≫ f) k EY b
  let s : J → bundlePowerGlobalSections P 1 := fun j => rawPowerOneLift P
    (Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j))
  have hs : ∃ j, s j ≠ 0 := by
    obtain ⟨j, hj⟩ := htY
    exact ⟨j, rawPowerOneLift_ne_zero P hj⟩
  let φ : SchemeComplexPoint f → EReal := fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
    sectionsMaxLog f n EX a N t H p
  let F := schemeComplexPointMap (i ≫ f) f i rfl
  let ψ : SchemeComplexPoint (i ≫ f) → EReal := fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
    sectionsMaxLog (i ≫ f) k EY b 1 s HP p
  have hideal : sectionsIdeal b 1 s = (sectionsIdeal a N t).comap i :=
    actual_restricted_firstPower_family_ideal i (a.tensorPower N) t
  have hφtype := normalized_sectionMaximum_restriction_has_global_actual_ideal_type
    f n EX H i k EY a N K hK t
  have hψtype := normalized_sectionMaximum_has_global_actual_ideal_type
    (i ≫ f) k EY HP b 1 K hK s
  rw [hideal] at hψtype
  have hsame : SameSingularityTypeOn (fun p => φ (F p)) ψ univ :=
    IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφtype hψtype
  have hφ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul
    (isThetaPshPotential_sectionsMaxLog f n EX a N t H ht)
    (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
  have hφq : ManifoldQuasiPlurisubharmonic (n := k) (fun p => φ (F p)) :=
    GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (schemeComplexPointMap_contMDiff f i k n ∞) hφ.quasiPshPotential.1
  have hψq : ManifoldQuasiPlurisubharmonic (n := k) ψ := by
    let : Nonempty {j : J // s j ≠ 0} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    have hψ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul
      (isThetaPshPotential_sectionsMaxLog (i ≫ f) k EY b 1
        (fun j : {j : J // s j ≠ 0} => s j) HP (fun j => j.property))
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
    change ManifoldQuasiPlurisubharmonic (n := k)
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog (i ≫ f) k EY b 1 s HP p)
    rw [sectionMaximum_erase_zero (i ≫ f) k EY HP b 1 s hs]
    exact hψ.quasiPshPotential.1
  have hAn : potentialAn k EY (fun p => φ (F p)) = potentialAn k EY ψ :=
    potentialAn_congr k EY fun m => multiplierIdeal_eq_of_sameSingularityType hφq hψq hsame m
  change potentialAn k EY (fun p => φ (F p)) w = _
  rw [hAn]
  change potentialAn k EY (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
    sectionsMaxLog (i ≫ f) k EY b 1 s HP p) w = _
  rw [potentialAn_sectionMaximum_of_exists_nonzero (i ≫ f) k EY HP b 1 K hK s hs w, hideal]
  rw [idealVal_comap_schemeAnMap i rfl w]
  exact (SGPT.NAPotential.BJ.GfIm.RationalHull.potentialAn_sectionsMaxLog_all_narrow
    f n EX H a N t ht hK (schemeAnMap i rfl w)).symm

end SGPT.NAPotential.TraceComparison
