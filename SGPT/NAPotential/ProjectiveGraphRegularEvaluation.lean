import SGPT.Okounkov.SchemeComplexPointStalkEvaluation
import SGPT.Foundations.Analysis.Pending.InvertibleIdealQuotient

/-!
# Actual global regular functions on arbitrary smooth native schemes

Canonical original complex-point residue evaluation, with holomorphy supplied
by existing actual whole-stalk regular-section representatives. No projectivity.
Blueprint: `projective-graph-analytic-map.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularEvaluation

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable {M : Scheme.{0}} (f : M ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance evaluationTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance evaluationCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance evaluationManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The actual global-section-to-original-complex-point ring homomorphism. -/
def sectionEvaluationHom (p : SchemeComplexPoint f) : Γ(M, ⊤) →+* ℂ :=
  (schemeComplexPointStalkEval f p).comp (M.presheaf.germ ⊤ (schemeComplexPointImage f p) trivial).hom

/-- Canonical original values of the actual original global regular section. -/
def sectionEvaluation (r : Γ(M, ⊤)) : SchemeComplexPoint f → ℂ := fun p => sectionEvaluationHom f p r

/-- Whole original-stalk readback makes the actual canonical function holomorphic at every original point. -/
theorem sectionEvaluation_holomorphicAt (r : Γ(M, ⊤)) (p : SchemeComplexPoint f) :
    HolomorphicAt n (sectionEvaluation f r) p := by
  obtain ⟨W, hW, hpW, _, H, hH, hread⟩ :=
    SmoothSchemeGerms.regularSection_locally_holomorphic f n ⊤ r p trivial
  have hHhol : ∀ q ∈ W, HolomorphicAt n H q := fun q hq =>
    InvertibleIdealQuotient.holomorphicAt_of_mdifferentiableOn hW hH hq
  have heq : sectionEvaluation f r =ᶠ[𝓝 p] H := by
    filter_upwards [hW.mem_nhds hpW] with q hq
    have hgerm : schemeNativeStalkGerm f n q
        (M.presheaf.germ ⊤ (schemeComplexPointImage f q) trivial r) = NativeHolGerm.mk H (hHhol q hq) := by
      apply Subtype.ext
      exact hread q hq trivial
    change schemeComplexPointStalkEval f q _ = H q
    rw [← schemeNativeStalkGerm_eval f n q, hgerm, NativeHolGerm.eval_mk]
  exact (hHhol p hpW).congr heq.symm

/-- The actual global original regular function is holomorphic in every order in the same original charts. -/
theorem sectionEvaluation_contMDiff (r : Γ(M, ⊤)) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (sectionEvaluation f r) := by
  intro p
  exact contMDiffAt_of_eventually_mdifferentiableAt (sectionEvaluation_holomorphicAt f n r p)

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularEvaluation
