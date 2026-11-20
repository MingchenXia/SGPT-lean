import SGPT.Checks.Comparison.TraceGFNontrivialRestriction

/-! Actual zero pulled families and the ORIGINAL literal zero restriction.
Blueprint: `trace-gf-zero-restriction.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.GAGAMult SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.GfIm
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves GlobalAnalyticSingularities
open scoped Topology Manifold ContDiff ENNReal

variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  [Nonempty (SchemeComplexPoint (i ≫ f))]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
local instance traceZeroXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceZeroYProper : IsProper (i ≫ f) := (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceZeroXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceZeroYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceZeroXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceZeroYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceZeroXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceZeroYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k

include k EY

/-- A genuine actual nonzero pulled section forces the BOOK'S literal
physical restriction to be nontrivial. The bounded comparison with a true
target physical maximum is manufactured internally from the SAME whole ideal. -/
theorem sectionMaximum_restriction_nontrivial_of_actual_nonzero_pulledSection
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (htY : ∃ j, Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j) ≠ 0) :
    ∃ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) ≠ ⊥ := by
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
  let ψ : SchemeComplexPoint (i ≫ f) → EReal := fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
    sectionsMaxLog (i ≫ f) k EY b 1 s HP p
  have hideal : sectionsIdeal b 1 s = (sectionsIdeal a N t).comap i :=
    actual_restricted_firstPower_family_ideal i (a.tensorPower N) t
  have hφtype := normalized_sectionMaximum_restriction_has_global_actual_ideal_type
    f n EX H i k EY a N K hK t
  have hψtype := normalized_sectionMaximum_has_global_actual_ideal_type
    (i ≫ f) k EY HP b 1 K hK s
  rw [hideal] at hψtype
  have hsame := IdealWeightComparison.sameSingularityTypeOn_univ_of_eq_type hφtype hψtype
  have hψ : IsGlobalQuasiPshPotential (n := k) ψ := by
    let : Nonempty {j : J // s j ≠ 0} := ⟨⟨hs.choose, hs.choose_spec⟩⟩
    change IsGlobalQuasiPshPotential (n := k)
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog (i ≫ f) k EY b 1 s HP p)
    rw [sectionMaximum_erase_zero (i ≫ f) k EY HP b 1 s hs]
    exact (SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul
      (isThetaPshPotential_sectionsMaxLog (i ≫ f) k EY b 1
        (fun j : {j : J // s j ≠ 0} => s j) HP (fun j => j.property))
      (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))).quasiPshPotential
  obtain ⟨p, _, hp⟩ := hψ.2 (Classical.arbitrary _) univ isOpen_univ (mem_univ _)
  obtain ⟨C, hC⟩ := hsame.2
  refine ⟨p, fun hbot => hp ?_⟩
  have hle := hC p (mem_univ _)
  change ψ p ≤ (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
    (schemeComplexPointMap (i ≫ f) f i rfl p) + (C : EReal) at hle
  rw [hbot, EReal.bot_add] at hle
  exact le_bot_iff.mp hle

/-- A literal identically minus-infinite original restriction forces EVERY
actual pulled section to be zero. No ideal or valuation output is a premise. -/
theorem actual_pulledSection_eq_zero_of_sectionMaximum_restriction_eq_bot
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (hbot : ∀ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) = ⊥) :
    ∀ j, Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j) = 0 := by
  intro j
  by_contra hj
  obtain ⟨p, hp⟩ := sectionMaximum_restriction_nontrivial_of_actual_nonzero_pulledSection
    f i n k EX EY a H N K hK t ⟨j, hj⟩
  exact hp (hbot p)

/-- The literal original restriction vanishes identically EXACTLY when the
entire original pulled section family vanishes. -/
theorem sectionMaximum_restriction_eq_bot_iff_actual_pulledSection_eq_zero
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N) :
    (∀ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) = ⊥) ↔
      ∀ j, Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j) = 0 := by
  constructor
  · exact actual_pulledSection_eq_zero_of_sectionMaximum_restriction_eq_bot f i n k EX EY a H N K hK t
  · intro hzero p
    have hideal : (sectionsIdeal a N t).comap i = ⊥ := by
      change (⨆ j, sectionZeroIdealSheaf (a.tensorPower N) (t j)).comap i = ⊥
      rw [sectionFamilyIdeal_comap]
      simp_rw [hzero]
      simp only [actual_sectionZeroIdealSheaf_zero, iSup_bot]
    have htype := normalized_sectionMaximum_restriction_has_global_actual_ideal_type
      f n EX H i k EY a N K hK t
    rw [hideal] at htype
    exact eq_bot_of_global_type_zero_ideal (i ≫ f) k EY htype p

/-- Every original image semi-valuation sees minus infinity when the SAME
original literal physical restriction is identically minus infinity. -/
theorem potentialAn_sectionMaximum_schemeAnMap_eq_bot_of_restriction_eq_bot
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∀ j, t j ≠ 0)
    (hbot : ∀ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) = ⊥)
    (w : BerkovichPoint (i ≫ f)) :
    potentialAn n EX (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
      sectionsMaxLog f n EX a N t H p) (schemeAnMap i rfl w) = ⊥ := by
  have hzero := actual_pulledSection_eq_zero_of_sectionMaximum_restriction_eq_bot
    f i n k EX EY a H N K hK t hbot
  rw [potentialAn_sectionMaximum_schemeAnMap_eq f n EX H a N K hK t ht i rfl w]
  simp_rw [hzero]
  simp only [actual_sectionZeroIdealSheaf_zero, iSup_bot, BJModel.idealVal_bot]
  simp [ENNReal.top_div_of_ne_top (by simp : (K : ℝ≥0∞) ≠ ⊤)]

end SGPT.NAPotential.TraceComparison
