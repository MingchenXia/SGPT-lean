import SGPT.Okounkov.OkoLelongMin
import SGPT.GAGA.H0LOkounkov
import SGPT.GAGA.SmoothFlagsScheme

/-!
# `cor:numin` for smooth prime divisors: `ν(V_θ, E) = lim_k k⁻¹ ord_E H⁰(X, L^k)`

Lane QW-OKO, blueprint `claude-qw-oko.tex`. Source: chapter *The theory of Okounkov bodies*,
subsection *Recover Lelong numbers from partial Okounkov bodies*, `cor:numin`.

Setting of lanes OKO-A / H0-GAGA3 / SMOOTH-FLAGS: `X` an integral smooth projective complex scheme
of dimension `m + 1`, `L` a big line bundle with atlas `a` and smooth metric `H`,
`θ = c₁(L, H)`, `V_θ` the potential with minimal singularities (`thetaPshSupremum`).

* `tendsto_firstFlagOrder_div_firstFlagLelong`: for a smooth flag `Y•` and `E = Y₁`,
  `k⁻¹ ord_E H⁰(X, L^k) → ν(V_θ, E)` (`ord_E H⁰(X, L^k)` is `firstFlagOrder`, the minimal
  `ν(s)₁ = ord_E(s)` over the nonzero sections of `L^k`). The book's proof: the limit is
  `min_{x ∈ Δ_{Y•}(L)} x₁` (`OkoLelong.tendsto_firstFlagOrder_div`), `Δ_{Y•}(L) = Δ_{Y•}(θ, V_θ)`
  (`SGPT.GAGA.H0L.lineBundleOkounkovBody_eq_generalPartialBody`) and `thm:nuOk`
  (`OkoLelong.isLeast_firstCoordinate_generalPartialBody`: `min_{Δ_{Y•}(θ, V_θ)} x₁ = ν(V_θ, Y₁)`).
  This proves both inequalities of eq:nuVthetaE, in particular the reverse inequality
  `lim_k k⁻¹ ord_E H⁰(X, L^k) ≤ ν(V_θ, E)` left open by lane OKO-LELONG.
* `tendsto_firstFlagOrder_div_of_smoothDivisor`: for every smooth prime divisor `E` of `X(ℂ)`
  (a closed connected complex submanifold of dimension `m`) there is a smooth flag with `Y₁ = E`
  (`SGPT.GAGA.SmoothFlags.exists_schemeSmoothFlag_one_eq`, "since `X` is projective, we can
  always find a flag with `E` being the first component"), and for every such flag
  `k⁻¹ ord_E H⁰(X, L^k) → ν(V_θ, E)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Okounkov.QwOko

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Okounkov SGPT.Okounkov.OkoLelong SGPT.Okounkov.AlgPOB SGPT.AlmostSemigroup
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open scoped Topology ENNReal NNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance qwOkoNuminTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance qwOkoNuminCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance qwOkoNuminManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **Source `cor:numin`, eq:nuVthetaE, for `E = Y₁`**: for a big line bundle `L` and the first
member `E = Y₁` of a smooth flag, `lim_{k → ∞} k⁻¹ ord_E H⁰(X, L^k) = ν(V_θ, E)`
(`θ = c₁(L, H)`, `V_θ` the potential with minimal singularities). -/
theorem tendsto_firstFlagOrder_div_firstFlagLelong
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (hL : SGPT.LineBundle.IsBig f L (m + 1)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    Tendsto (fun k : ℕ => (firstFlagOrder f E Y hY a k : ℝ) / k) atTop
      (𝓝 (firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val))) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : Nonempty (SchemeComplexPoint f) :=
    PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
  have hV := isThetaPshPotential_thetaPshSupremum_of_isBig f E a H hL
  have hℓ : IsLeast ((fun x : Fin (m + 1) → ℝ => x 0) ''
      lineBundleOkounkovBody f (m + 1) E Y hY a)
      (firstFlagLelong f Y (thetaPshSupremum (H.curvature a).val)) := by
    rw [SGPT.GAGA.H0L.lineBundleOkounkovBody_eq_generalPartialBody f E Y hY a H hL]
    exact isLeast_firstCoordinate_generalPartialBody
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) hV
  exact tendsto_firstFlagOrder_div f E Y hY a hL hℓ

/-- **Source `cor:numin`, eq:nuVthetaE, for every smooth prime divisor `E` of `X`** (a closed
connected complex submanifold of `X(ℂ)` of dimension `m`): there is a smooth flag `Y•` with
`Y₁ = E`, and for every smooth flag with `Y₁ = E`,
`lim_{k → ∞} k⁻¹ ord_E H⁰(X, L^k) = ν(V_θ, E)` (`ord_E H⁰(X, L^k)` is computed as the minimal
first flag coordinate `ν(s)₁ = ord_E(s)`). -/
theorem tendsto_firstFlagOrder_div_of_smoothDivisor (hL : SGPT.LineBundle.IsBig f L (m + 1))
    {W : Set (SchemeComplexPoint f)} (hW : IsClosedConnectedSubmanifold (m + 1) W m) :
    letI := E.isSeparated
    letI := E.quasiCompact
    (∃ Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f), IsSmoothFlag Y ∧ Y 1 = W) ∧
      ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y), Y 1 = W →
        Tendsto (fun k : ℕ => (firstFlagOrder f E Y hY a k : ℝ) / k) atTop
          (𝓝 (sourceGenericLelongNumber (n := m + 1) (Subtype.val : W → SchemeComplexPoint f)
            (thetaPshSupremum (H.curvature a).val)).toReal) := by
  let := E.isSeparated
  let := E.quasiCompact
  refine ⟨SGPT.GAGA.SmoothFlags.exists_schemeSmoothFlag_one_eq f E hW, fun Y hY h1 => ?_⟩
  subst h1
  exact tendsto_firstFlagOrder_div_firstFlagLelong f E a H Y hY hL

end SGPT.Okounkov.QwOko
