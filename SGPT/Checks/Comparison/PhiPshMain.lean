import SGPT.Checks.Comparison.PhiPshStatement
import SGPT.Checks.Comparison.BJExistCurve

/-!
# `prop:PhiinducePSH`

Source: `chapter_NApotential.tex`, `prop:PhiinducePSH` (*The algebraic setting*):

*Let `φ ∈ PSH(X, θ)_{>0}` be a model potential and `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`. Let `Φ`
be the complexification of `ℓ`. Then the function `v ↦ -σ(v)(Φ)` for `v ∈ X^Div` admits a unique
extension to an element of `PSH(L^An)`.*

## Formal setting

As for `lma:varphian` (`SGPT.Checks.Comparison.BJAsmVarphian`): `X` is an integral scheme, projective and
smooth of relative dimension `d + 1` over `ℂ` with a closed projective embedding `E`, `X(ℂ)`
connected with its Borel structure; `L = m⁻¹ [M]` is a `ℚ`-line bundle (`M` an algebraic line
bundle with atlas `b` and smooth metric `h_M`), `h = h_M^{1/m}` and `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)`
(equal coefficients in every chart). The objects of the statement are those of
`SGPT.Checks.Comparison.PhiPshStatement`: `SourceModelPotential θ φ`, `ℓ ∈ sourceGeodesicRays omega θ φ hφ`,
`IsRayComplexificationOf ℓ Φ`, `σ(v)(Φ) = NAGaga.gaussPotentialVal`, `X^Div = sourceDivisorialSet`
and `PSH(L^An) = IsModuleTopologyPSH` (`def:BJpshmetric`).

## Proof

Not the book's route (Siu's theorem on `X × Δ`, `lma:istab`, `lma:GAGA` and `lma:fibIeq`).
Instead: by the Ross–Witt Nyström inversion the complexification of `ℓ` is the complexification of
`ℓ^*`, so the multiplier-ideal squeeze of `prop:psiandPhi` gives
`-σ(v)(Φ) = sup_{τ < ℓ^*_max} ((ℓ^*_τ)^An(v) + τ) = Γ_ℓ^An(v)` for every `v ∈ X^An`, with
`Γ_ℓ = P_θ[ℓ^*]_𝓘 ∈ PSH^NA(X, θ)_{>0}` (`neg_gaussPotentialVal_ray_eq_naPotentialAnAt`); and
`Γ_ℓ^An ∈ PSH(L^An)` is the existence clause of `cor:testcurvegivepshme`
(`SGPT.NAPotential.BJ.Exist.naPotentialAnAt_isModuleTopologyPSH`, lane BJ-EXIST, proved with Siu's
theorem on `X` and GAGA for sections). Uniqueness is `thm:pshdetbydiv`.

## Main results

* `isModuleTopologyPSH_negGaussVal`: `v ↦ -σ(v)(Φ)` (on all of `X^An`) lies in `PSH(L^An)`.
* `phiInducePSH`: **`prop:PhiinducePSH`**.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.PhiPsh

open Set
open scoped ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich SGPT.NAPotential.NAGaga
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.Assembly
open SGPT.NAPotential.BJ.Exist
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (d : ℕ) [SmoothOfRelativeDimension (d + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance phiPshMainProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance phiPshMainPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance phiPshMainPointCharts : ChartedSpace (ComplexModel (d + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (d + 1)
local instance phiPshMainPointManifold : IsComplexManifold (d + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (d + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f (d + 1) E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel (d + 1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
  {φ : SchemeComplexPoint f → EReal} {hφ : SourceModelPotential θ φ}
  {ℓ : SourceRayFamily (SchemeComplexPoint f)}

include hm hθ in
/-- **`v ↦ -σ(v)(Φ)` is a psh metric on `L^An`** (every universe), for the complexification `Φ` of
`ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`. -/
theorem isModuleTopologyPSH_negGaussVal (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (negGaussVal f d E Φ) := by
  let ω : SourceKahlerForm (d + 1) (SchemeComplexPoint f) := sourceKahlerFormOfBackground omega
  rw [negGaussVal_eq_naPotentialAnAt f d E omega hℓ hsup hΦ ω]
  exact naPotentialAnAt_isModuleTopologyPSH f (d + 1) E b HM hm hθ (rayNAPotential omega hℓ) ω

include hm hθ in
/-- **`prop:PhiinducePSH`.** Let `X` be a connected projective manifold, `L = m⁻¹ [M]` a
`ℚ`-line bundle with the Hermitian metric `h_M^{1/m}` and `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)`. Let
`φ ∈ PSH(X, θ)_{>0}` be a model potential, `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0` and `Φ` the
complexification of `ℓ`. Then `v ↦ -σ(v)(Φ)` on `X^Div` admits a unique extension to an element
of `PSH(L^An)`; this extension is `v ↦ -σ(v)(Φ)` on all of `X^An`. -/
theorem phiInducePSH (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    (∃! ψ : BerkovichPoint f → EReal,
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ ∧
        ∀ v ∈ sourceDivisorialSet f, ψ v = -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal)) ∧
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) (negGaussVal f d E Φ) := by
  have h := isModuleTopologyPSH_negGaussVal.{0} f d E b HM hm hθ omega hℓ hsup hΦ
  exact ⟨existsUnique_of_isModuleTopologyPSH_gauss f d E h, h⟩

end SGPT.NAPotential.PhiPsh
