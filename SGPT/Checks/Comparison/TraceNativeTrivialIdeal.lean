import SGPT.Checks.Comparison.TraceNativeTrivialPoint
import SGPT.Checks.Comparison.TraceGermIdealPullback

/-! ENTIRE original ideal value at the ACTUAL native trivial image.
Blueprint: `trace-native-trivial.tex`. All native dimensions, including zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeTrivial

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ENNReal Classical

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsProper f]
local instance traceTrivialIdealTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceTrivialIdealCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceTrivialIdealManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {k : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel k) Z]
  [IsComplexManifold k Z]
  (G : Z → SchemeComplexPoint f)
  (hG : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)

/-- The actual trivial image reads the ENTIRE original algebraic ideal as
infinite iff its ENTIRE native pulled stalk ideal is zero, and zero otherwise. -/
theorem point_idealVal_eq_if_stalk (J : X.IdealSheafData) :
    (point f n G hG z).idealVal J =
      if (stalkIdeal J (schemeComplexPointImage f (G z))).map (stalkToGerm f n G hG z) = ⊥
        then ⊤ else 0 := by
  obtain ⟨U, hU⟩ := exists_affineOpen_mem (schemeComplexPointImage f (G z))
  have hiff : (stalkIdeal J (schemeComplexPointImage f (G z))).map (stalkToGerm f n G hG z) = ⊥ ↔
      ∀ r ∈ J.ideal U, stalkToGerm f n G hG z ((X.presheaf.germ (U : X.Opens) _ hU).hom r) = 0 := by
    rw [stalkIdeal_eq_map J U hU, Ideal.map_map, Ideal.map_eq_bot_iff_le_ker]
    rfl
  by_cases h : (stalkIdeal J (schemeComplexPointImage f (G z))).map (stalkToGerm f n G hG z) = ⊥
  · rw [if_pos h, point_idealVal f n G hG z U hU]
    apply iInf_eq_top.mpr
    intro r
    apply iInf_eq_top.mpr
    intro hr
    exact if_pos (hiff.mp h r hr)
  · rw [if_neg h, point_idealVal f n G hG z U hU]
    have hex := hiff.not.mp h
    push Not at hex
    obtain ⟨r, hr, hr0⟩ := hex
    exact le_antisymm (iInf_le_of_le r (iInf_le_of_le hr (le_of_eq (if_neg hr0)))) bot_le

/-- The ENTIRE original native analytic pullback germ is the actual map
of the ENTIRE original algebraic ideal stalk, in the SAME centered chart. -/
theorem analyticIdeal_chart_map (EX : ClosedProjectiveEmbedding f) (J : X.IdealSheafData) :
    (spanGerms (n := k) ((GermIdeal.pullback (m := k) G (analytificationIdeal f n EX J)).mem z) z).map
      (NativeHolGerm.chartEquiv (n := k) z).toRingHom =
      (stalkIdeal J (schemeComplexPointImage f (G z))).map (stalkToGerm f n G hG z) := by
  rw [spanGerms_pullback_eq_map hG (analytificationIdeal f n EX J) z (fun a ha => ha.1),
    spanGerms_analytificationIdeal_eq f n EX J (G z),
    analyticIdeal_germ_eq_map_stalk f n EX J (G z)]
  simp only [Ideal.map_map]
  rfl

/-- EXACT entire analytic ideal readback, with no target scheme or
nonzero/zero-family certificate. -/
theorem point_idealVal_eq_if_analytic (EX : ClosedProjectiveEmbedding f) (J : X.IdealSheafData) :
    (point f n G hG z).idealVal J =
      if spanGerms (n := k) ((GermIdeal.pullback (m := k) G (analytificationIdeal f n EX J)).mem z) z = ⊥
        then ⊤ else 0 := by
  rw [point_idealVal_eq_if_stalk, ← analyticIdeal_chart_map f n G hG z EX J]
  simp only [Ideal.map_eq_bot_iff_of_injective
      (f := (NativeHolGerm.chartEquiv (n := k) z).toRingHom) (NativeHolGerm.chartEquiv (n := k) z).injective]

end SGPT.NAPotential.TraceComparison.NativeTrivial
