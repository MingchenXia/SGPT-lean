import SGPT.Checks.Comparison.TraceNativeIdealValue
import SGPT.Checks.Comparison.TraceGermIdealPullback

/-! ENTIRE actual analytic ideal order at the SAME native image valuation.
Blueprint: `trace-native-image-valuation.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ENNReal

section Chart
variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- The ACTUAL whole original chart ideal is exactly the original native
whole germ ideal transported through the genuine centered chart equivalence. -/
theorem wholeChartStalkIdeal_eq_map_spanGerms (A : GermIdeal k M) (x : M) :
    wholeChartStalkIdeal A x x (mem_chart_source _ x) =
      (spanGerms (A.mem x) x).map (NativeHolGerm.chartEquiv x).toRingHom := by
  unfold wholeChartStalkIdeal spanGerms
  rw [Ideal.map_span]
  congr 1
  ext γ
  constructor
  · rintro ⟨u, hu, hAu, rfl⟩
    refine ⟨NativeHolGerm.mk u hu, ⟨u, hu, hAu, rfl⟩, ?_⟩
    rfl
  · rintro ⟨_, ⟨u, hu, hAu, rfl⟩, rfl⟩
    exact ⟨u, hu, hAu, rfl⟩

end Chart

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsProper f]
local instance traceAnalyticOrderTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceAnalyticOrderCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceAnalyticOrderManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {m : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
  [IsComplexManifold (m+1) Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)
  {E : Set Z} (Φ : DivisorFlattening (m := m) E z)

/-- The ENTIRE original pulled analytic ideal, in the SAME original chart,
is exactly the actual map of the entire original algebraic stalk ideal. -/
theorem wholeChartStalkIdeal_pullback_analytificationIdeal_eq_map_stalk
    (EX : ClosedProjectiveEmbedding f) (J : X.IdealSheafData) :
    wholeChartStalkIdeal (GermIdeal.pullback (m := m+1) G (analytificationIdeal f n EX J))
      z z (mem_chart_source _ z) =
      (stalkIdeal J (schemeComplexPointImage f (G z))).map (stalkToPrimeGerm f n G hG z) := by
  rw [wholeChartStalkIdeal_eq_map_spanGerms,
    spanGerms_pullback_eq_map hG (analytificationIdeal f n EX J) z (fun a ha => ha.1),
    spanGerms_analytificationIdeal_eq f n EX J (G z),
    analyticIdeal_germ_eq_map_stalk f n EX J (G z)]
  simp only [Ideal.map_map]
  rfl

/-- Every original affine ideal section computes the order of the ENTIRE
actual mapped stalk ideal; all localized coefficients are included. -/
theorem idealNormalOrder_map_stalkIdeal_eq_iInf (U : X.affineOpens)
    (hU : schemeComplexPointImage f (G z) ∈ (U : X.Opens)) (J : X.IdealSheafData) :
    idealNormalOrder Φ ((stalkIdeal J (schemeComplexPointImage f (G z))).map
      (stalkToPrimeGerm f n G hG z)) =
      ⨅ r ∈ J.ideal U, normalOrder Φ (stalkToPrimeGerm f n G hG z
        ((X.presheaf.germ (U : X.Opens) _ hU).hom r)) := by
  have hspan : Ideal.span (range fun r : J.ideal U => r.val) = J.ideal U := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact r.property)
    · intro r hr
      exact Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩
  rw [stalkIdeal_eq_map J U hU]
  conv_lhs => rw [← hspan, Ideal.map_map, Ideal.map_span, ← Set.range_comp,
    idealNormalOrder_span]
  rw [iInf_subtype]
  rfl

/-- **The actual native image semi-valuation reads the ENTIRE original
pulled analytic ideal as the SAME scaled original normal order.** No
scheme target, dominance, ideal-value or native-germ square is a premise. -/
theorem nativeImagePoint_idealVal_eq_originalStalkNormalOrder
    (EX : ClosedProjectiveEmbedding f) (t : ℝ) (ht : 0 < t) (J : X.IdealSheafData) :
    (nativeImagePoint f n G hG z Φ t ht).idealVal J = ENNReal.ofReal t *
      (originalStalkNormalOrder Φ (GermIdeal.pullback (m := m+1) G
        (analytificationIdeal f n EX J)) : ℝ≥0∞) := by
  obtain ⟨U, hU⟩ := exists_affineOpen_mem (schemeComplexPointImage f (G z))
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  rw [nativeImagePoint_idealVal f n G hG z Φ t ht U hU J]
  unfold originalStalkNormalOrder
  rw [wholeChartStalkIdeal_pullback_analytificationIdeal_eq_map_stalk f n G hG z EX J,
    idealNormalOrder_map_stalkIdeal_eq_iInf f n G hG z Φ U hU J]
  simp only [ENat.toENNReal_iInf]
  rw [ENNReal.mul_iInf_of_ne ht0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun r => ?_
  rw [ENNReal.mul_iInf_of_ne ht0 ENNReal.ofReal_ne_top]

end SGPT.NAPotential.TraceComparison.NativeImage
