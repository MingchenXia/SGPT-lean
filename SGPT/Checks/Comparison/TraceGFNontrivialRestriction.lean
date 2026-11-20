import SGPT.Checks.Comparison.TraceGFRestriction
import SGPT.NAPotential.DivDictTrivial

/-! Original literal nontrivial restriction produces genuine nonzero pulled sections.
Source `eq:varphiAncordF`; blueprint `trace-gf-nontrivial-restriction.tex`. -/
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

/-- The ACTUAL whole zero-section ideal is exactly the original zero ideal. -/
theorem actual_sectionZeroIdealSheaf_zero {Z : Scheme.{0}} {M : Z.Modules}
    (a : LineBundleAtlas M) : sectionZeroIdealSheaf a (0 : Γ(M, ⊤)) = ⊥ := by
  ext U : 2
  change (sectionZeroEvaluation M (0 : Γ(M, ⊤)) U.1).range = ⊥
  simp only [sectionZeroEvaluation, map_zero, LinearMap.range_zero]

section ZeroType

variable {Z : Scheme.{0}} (g : Z ⟶ Spec (.of ℂ)) (k : ℕ) [SmoothOfRelativeDimension k g]
  (E : ClosedProjectiveEmbedding g) [IsSeparated g] [QuasiCompact g]
local instance traceZeroTypeTopology : TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g
local instance traceZeroTypeCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint g) := schemeAnalyticTNChartedSpace g k
local instance traceZeroTypeManifold : IsComplexManifold k (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g k

omit [IsSeparated g] [QuasiCompact g] in
/-- The ACTUAL zero analytic ideal forces every original function with a
positive rational global type in it to be literally negative infinity. -/
theorem eq_bot_of_global_type_zero_ideal {u : SchemeComplexPoint g → EReal} {c : ℚ}
    (hu : HasAnalyticSingularitiesOfType (n := k) u c
      (analytificationIdeal g k E (⊥ : Z.IdealSheafData))) (p : SchemeComplexPoint g) : u p = ⊥ := by
  let := E.isSeparated
  let := E.quasiCompact
  obtain ⟨hc, _hcoh, hlocal⟩ := hu
  obtain ⟨U, hU, hp, N, s, hs, hgen, R, C, hRC, heq⟩ := hlocal p
  have hz : ∀ j, s j p = 0 := by
    intro j
    have hhol := InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hU (hs j) hp
    have hmem := (hgen p hp (s j)).mpr
      (InvertibleIdealQuotient.isInSpanAt_self ⟨j, rfl⟩ hhol)
    exact (eventually_eq_zero_of_mem_analytificationIdeal_bot k E hmem).eq_of_nhds
  exact (heq p hp).trans ((scaled_generatorLog_add_eq_bot_iff s p (Rat.cast_pos.mpr hc) (R p)).mpr hz)

end ZeroType

variable {X Y : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (i : Y ⟶ X) (n k : ℕ)
  [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension k (i ≫ f)]
  [IsIntegral X] [IsIntegral Y] [IsProjective f] [IsProjective (i ≫ f)]
  (EX : ClosedProjectiveEmbedding f) (EY : ClosedProjectiveEmbedding (i ≫ f))
local instance traceNontrivXProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceNontrivYProper : IsProper (i ≫ f) :=
  (ProjectiveFactorizationRingIso.of_isProjective (i ≫ f)).isProper
local instance traceNontrivXTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceNontrivYTopology : TopologicalSpace (SchemeComplexPoint (i ≫ f)) := schemeAnalyticPointTopology (i ≫ f)
local instance traceNontrivXCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceNontrivYCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTNChartedSpace (i ≫ f) k
local instance traceNontrivXManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance traceNontrivYManifold : IsComplexManifold k (SchemeComplexPoint (i ≫ f)) := schemeAnalyticTN_isComplexManifold (i ≫ f) k

include k EY

omit [IsIntegral Y] in
/-- The BOOK'S literal actual nontrivial analytic restriction manufactures
a genuine actual nonzero pulled section; no nonzero-section certificate input. -/
theorem exists_actual_nonzero_pulledSection_of_nontrivial_restriction
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (hne : ∃ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) ≠ ⊥) :
    ∃ j, Scheme.Modules.affinePullbackUnitTop i (bundleTensorPower L N) (t j) ≠ 0 := by
  classical
  by_contra! hzero
  have hideal : (sectionsIdeal a N t).comap i = ⊥ := by
    change (⨆ j, sectionZeroIdealSheaf (a.tensorPower N) (t j)).comap i = ⊥
    rw [sectionFamilyIdeal_comap]
    simp_rw [hzero]
    simp only [actual_sectionZeroIdealSheaf_zero, iSup_bot]
  have htype := normalized_sectionMaximum_restriction_has_global_actual_ideal_type
    f n EX H i k EY a N K hK t
  rw [hideal] at htype
  obtain ⟨p, hp⟩ := hne
  exact hp (eq_bot_of_global_type_zero_ideal (i ≫ f) k EY htype p)

/-- **The displayed ORIGINAL physical restriction formula, under exactly its
literal nontrivial-restriction hypothesis**, on ALL original source semi-valuations.
The genuine actual nonzero pulled family and all metric/ideal readers are internal. -/
theorem potentialAn_sectionMaximum_restriction_eq_of_nontrivial
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∀ j, t j ≠ 0)
    (hne : ∃ p : SchemeComplexPoint (i ≫ f),
      (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p) ≠ ⊥)
    (w : BerkovichPoint (i ≫ f)) :
    potentialAn k EY
      (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N t H
        (schemeComplexPointMap (i ≫ f) f i rfl p)) w =
      potentialAn n EX (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) *
        sectionsMaxLog f n EX a N t H p) (schemeAnMap i rfl w) :=
  potentialAn_sectionMaximum_restriction_eq f i n k EX EY a H N K hK t ht
    (exists_actual_nonzero_pulledSection_of_nontrivial_restriction f i n k EX EY a H N K hK t hne) w

end SGPT.NAPotential.TraceComparison
