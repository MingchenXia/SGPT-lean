import SGPT.NAPotential.FSPosKahler
import SGPT.NAPotential.GAGAMult2Limit

/-!
# Algebraicity of multiplier ideals and the limit defining `φ^An`, up to GAGA for sections

Blueprint `claude-fs-pos:mult-alg`, `claude-fs-pos:limit`.

Let `X` be smooth projective over `ℂ` (relative dimension `n`, closed projective embedding `E`),
`𝒪_X(1) = E.map^* 𝒪(1)` with its coordinate atlas and the Fubini–Study metric
(`fubiniStudyMetric`), whose Chern form is Kähler (`fubiniStudy_isKahler`).  The positivity input
of `multiplierIdealAlgebraic_of_positive` is therefore discharged, and the only
remaining hypothesis is **GAGA for the sections of `𝒪_X(j)`, `j ≫ 0`**
(`HyperplaneSectionsAlgebraic`: every holomorphic section of `𝒪_X(j)^an` is the analytification
of an algebraic section).

* `multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic`: `MultiplierIdealAlgebraic`.
* For `φ ∈ PSH(X, θ)` and `v ∈ X^An` (source `def:NApotential:L975`, `eq:varphiAnalt`):
  `k⁻¹ v(𝓘(kφ)) → v(φ) = sup_{k ≥ 1} k⁻¹ v(𝓘(kφ)) = sup_j 2^{-j} v(𝓘(2^j φ))`, and
  `φ ≤ ψ ⟹ φ^An ≤ ψ^An`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.FSPos

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov SGPT.NAPotential.Berkovich SGPT.NAPotential.GAGAMult
open scoped Topology Manifold

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f)

local instance fsPosAlgTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fsPosAlgCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

/-- **Positivity of `𝒪_X(1)`**: the Chern form of the Fubini–Study metric is a Kähler form on
`X(ℂ)` (with the manifold structure supplied by the projective embedding). -/
theorem fubiniStudy_curvature_isKahler :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI := schemeAnalyticTN_isComplexManifold f n
    ((fubiniStudyMetric f E n).curvature (hyperplaneAtlas E)).val.IsKahler := by
  let := E.isSeparated
  let := E.quasiCompact
  exact fubiniStudy_isKahler f E n

/-- **GAGA for the sections of `𝒪_X(j)`** (statement only): every holomorphic section of
`(𝒪_X(1), h_FS)^an)^{⊗ j}` on `X(ℂ)` is the analytification of an algebraic section of
`𝒪_X(j)`. -/
abbrev HyperplaneSectionsAlgebraic (j : ℕ) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  SchemeSectionsAlgebraic f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n) j

/-- **Algebraicity of multiplier ideals, up to GAGA for sections**: if every holomorphic section
of `𝒪_X(j)` is algebraic for `j ≫ 0`, then `𝓘(cφ) ⊆ alg(𝓘(cφ))^an` for every quasi-psh `φ` on
`X(ℂ)` and `c > 0`. -/
theorem multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j) :
    MultiplierIdealAlgebraic f n E :=
  multiplierIdealAlgebraic_of_positive f n E (hyperplaneAtlas E) (fubiniStudyMetric f E n)
    (fubiniStudy_curvature_isKahler f n E) hgaga

/-- Up to GAGA for sections: `alg(𝓘(cφ))^an = 𝓘(cφ)` for quasi-psh `φ` and `c > 0`. -/
theorem analytificationIdeal_algebraization_eq_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j)
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsGlobalQuasiPshPotential (n := n) φ)
    {c : ℝ} (hc : 0 < c) :
    analytificationIdeal f n E (algebraization f n E (multiplierIdeal (n := n) c φ)) =
      multiplierIdeal (n := n) c φ :=
  analytificationIdeal_algebraization_eq f n E
    (multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E hgaga) hφ hc

variable {f} [IsProper f]

/-- **`def:NApotential:L975`, existence of the limit, up to GAGA for sections**: for
`φ ∈ PSH(X, θ)` and `v ∈ X^An`, `k⁻¹ v(𝓘(kφ)) → v(φ)`. -/
theorem tendsto_potentialVal_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => v.multiplierIdealVal n E φ k / k) atTop
      (𝓝 (v.potentialVal n E φ)) :=
  BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E hgaga) hφ v

/-- Up to GAGA for sections: `v(φ) = sup_{k ≥ 1} k⁻¹ v(𝓘(kφ))`. -/
theorem potentialVal_eq_iSup_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ k : ℕ, ⨆ (_ : 0 < k), v.multiplierIdealVal n E φ k / k :=
  BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E hgaga) hφ v

/-- **`eq:varphiAnalt`, up to GAGA for sections**: `v(φ) = sup_j 2^{-j} v(𝓘(2^j φ))`, i.e.
`φ^An(v) = inf_j -2^{-j} v(𝓘(2^j φ))`. -/
theorem potentialVal_eq_iSup_dyadic_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j)
    {φ : SchemeComplexPoint f → EReal}
    {θ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (v : BerkovichPoint f) :
    v.potentialVal n E φ = ⨆ j : ℕ, v.multiplierIdealVal n E φ (2 ^ j) / (2 ^ j : ℕ) :=
  BerkovichPoint.potentialVal_eq_iSup_dyadic_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E hgaga) hφ v

/-- Up to GAGA for sections: `φ ≤ ψ ⟹ φ^An ≤ ψ^An` on `X^An`. -/
theorem potentialAn_mono_of_hyperplaneSectionsAlgebraic
    (hgaga : ∀ᶠ j in atTop, HyperplaneSectionsAlgebraic f n E j)
    {φ ψ : SchemeComplexPoint f → EReal}
    {θ θ' : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; SmoothRealForm n (SchemeComplexPoint f) 2}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ φ)
    (hψ : letI := E.isSeparated; letI := E.quasiCompact;
      letI := schemeAnalyticTN_isComplexManifold f n; IsThetaPshPotential θ' ψ)
    (hle : ∀ x, φ x ≤ ψ x) (v : BerkovichPoint f) :
    potentialAn n E φ v ≤ potentialAn n E ψ v :=
  BerkovichPoint.potentialAn_mono_of_multiplierIdealAlgebraic n E
    (multiplierIdealAlgebraic_of_hyperplaneSectionsAlgebraic f n E hgaga) hφ hψ hle v

end SGPT.NAPotential.FSPos
