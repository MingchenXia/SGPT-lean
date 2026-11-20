import SGPT.Checks.Comparison.BJAsmVarphian
import SGPT.Checks.Comparison.BJCompareFiniteMax
import SGPT.NAPotential.QwNAConcavity

/-!
# `lma:pltest`: analytifications of piecewise linear curves are psh metrics

Source: `chapter_NApotential.tex`, `lma:pltest` (*The algebraic setting*): for a piecewise linear
curve `Γ` in `PSH(X, θ)` (`def:piecewiselincurv`), `Γ^An ∈ PSH(L^An)`. The book's proof: by
`eq:psianvlinear`, `Γ^An = max_i (Γ_{τ_i}^An + τ_i)`; conclude by `prop:BJclosedmax` and
`lma:varphian`.

Formal setting as in `SGPT.Checks.Comparison.BJAsmVarphian`: `L = m⁻¹ [M]` with the metric `h_M^{1/m}`,
and the closed `(1,1)`-form `θ` of the piecewise linear data (an atlas form, the setting of
`SGPT.NAPotential.Berkovich.PiecewiseLinearData`) is `c₁(L, h) = m⁻¹ c₁(M, h_M)` (equality of
coefficients in every chart). `Γ^An` is `PiecewiseLinearData.curveAn`, the supremum
`sup_{τ ≤ τ_0} (Γ_τ^An + τ)` of `eq:psianvlinear`; its equality with the finite maximum is
`PiecewiseLinearData.curveAn_eq_iSup`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ.Assembly

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance asmPLProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance asmPLPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance asmPLPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance asmPLPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **`lma:pltest`**: for `L = m⁻¹ [M]` with the metric `h_M^{1/m}`, `θ = c₁(L, h)` and a piecewise
linear curve `Γ` in `PSH(X, θ)` (data `A_0, …, A_N ∈ PSH(X, θ)`, `τ_0 > ⋯ > τ_N`), the
analytification `Γ^An = sup_{τ ≤ τ_0} (Γ_τ^An + τ)` lies in `PSH(L^An)`. -/
theorem curveAn_isModuleTopologyPSH {M : X.Modules} (b : LineBundleAtlas M)
    (HM : SchemeLineBundleMetric f n E M) {m : ℕ} (hm : 0 < m)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (D : PiecewiseLinearData θ) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (D.curveAn n E) := by
  have hA : ∀ i, IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b)
      (potentialAn n E (D.A i)) := fun i =>
    potentialAn_isModuleTopologyPSH f n E b HM hm
      ((hθ.thetaPshPotential_iff _).mp ((isThetaPSH_iff_nativeThetaPotential θ _).mp
        (D.isThetaPSH i)))
  have h := IsModuleTopologyPSH.finset_sup'_add_const f Finset.univ Finset.univ_nonempty
    (fun i => potentialAn n E (D.A i)) D.τ (fun i _ => hA i)
  convert h using 1
  funext v
  rw [D.curveAn_eq_iSup n E v, Finset.sup'_univ_eq_ciSup]

end SGPT.NAPotential.BJ.Assembly
