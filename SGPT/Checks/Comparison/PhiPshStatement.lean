import SGPT.Checks.Comparison.PhiPshGauss
import SGPT.Checks.Comparison.BJAsmUnique

/-!
# `prop:PhiinducePSH`: statement, uniqueness, and reduction of existence to `Γ_ℓ^An`

Source: `chapter_NApotential.tex`, `prop:PhiinducePSH` (*The algebraic setting*):

*Let `φ ∈ PSH(X, θ)_{>0}` be a model potential and `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`. Let `Φ`
be the complexification of `ℓ`. Then the function `v ↦ -σ(v)(Φ)` for `v ∈ X^Div` admits a unique
extension to an element of `PSH(L^An)`.*

## Formal setting

As for `lma:varphian` (`SGPT.Checks.Comparison.BJAsmVarphian`) and `prop:psiandPhi`
(`SGPT.NAPotential.NAGaga.source_psiandPhi`): `X` is an integral scheme, projective and smooth of
relative dimension `d + 1` over `ℂ` with a closed projective embedding `E` (the dimension is
positive as in the formal `prop:psiandPhi`, whose `σ(v)(Φ)` we use); `X(ℂ)` is connected (the
standing hypothesis of the chapter) and carries its Borel structure. `L` is any element of
`Pic(X) ⊗ ℚ` here (the relation `θ = c₁(L, h)` is only needed to *produce* the psh metric, see
`SGPT.Checks.Comparison.PhiPshMain`). The model potential is `SourceModelPotential θ φ`, `𝓡(X, θ; φ)` is
`sourceGeodesicRays omega θ φ hφ` (`def:geodraydef`), the complexification is any `Φ` with
`IsRayComplexificationOf ℓ Φ`, `σ(v)(Φ)` is `NAGaga.gaussPotentialVal`, `X^Div` is
`sourceDivisorialSet` (the divisorial valuations `t ord_E`, `t ∈ ℚ_{>0}`, and `v_triv`) and
`PSH(L^An)` is `IsModuleTopologyPSH` (`def:BJpshmetric`).

## Main results

* `existsUnique_of_isModuleTopologyPSH_gauss`: once `v ↦ -σ(v)(Φ)` (on all of `X^An`) is a psh
  metric, it is the unique psh extension of its restriction to `X^Div`.
* `isModuleTopologyPSH_gauss_iff`: `v ↦ -σ(v)(Φ)` is a psh metric on `L^An` iff
  `Γ_ℓ^An = naPotentialAnAt (rayNAPotential omega hℓ) ω` is, where `Γ_ℓ = P_θ[ℓ^*]_𝓘`.
* `phiInducePSH_of_naPotentialAnAt`: **`prop:PhiinducePSH` from the existence clause of
  `cor:testcurvegivepshme` for `Γ_ℓ`**.

The book derives `cor:testcurvegivepshme` from `prop:PhiinducePSH` (Siu's theorem on `X × Δ`); the
formalization reverses the arrow: `-σ(v)(Φ) = Γ_ℓ^An(v)` on `X^An`
(`neg_gaussPotentialVal_ray_eq_naPotentialAnAt`) and `Γ_ℓ^An` is a psh metric by the direct proof
of `cor:testcurvegivepshme` (lane BJ-EXIST, `SGPT.Checks.Comparison.BJExistCurve`), which uses Siu's
theorem on `X` only.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.PhiPsh

open Set
open scoped ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich SGPT.NAPotential.NAGaga
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.Assembly
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (d : ℕ) [SmoothOfRelativeDimension (d + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance phiPshStatementProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance phiPshStatementPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance phiPshStatementPointCharts :
    ChartedSpace (ComplexModel (d + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (d + 1)
local instance phiPshStatementPointManifold : IsComplexManifold (d + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (d + 1)

/-- The function `v ↦ -σ(v)(Φ)` on `X^An` (`σ(v)(Φ) = NAGaga.gaussPotentialVal`). -/
def negGaussVal (Φ : SchemeComplexPoint f × unitDisc → EReal) (v : BerkovichPoint f) : EReal :=
  -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal)

/-- **Uniqueness** (`prop:PhiinducePSH`, by `thm:pshdetbydiv`): if `v ↦ -σ(v)(Φ)` is a psh metric
on `L^An`, it is the unique psh metric on `L^An` extending its restriction to `X^Div`. -/
theorem existsUnique_of_isModuleTopologyPSH_gauss {L : RationalPicardSpace X}
    {Φ : SchemeComplexPoint f × unitDisc → EReal}
    (h : IsModuleTopologyPSH.{0} f L (negGaussVal f d E Φ)) :
    ∃! ψ : BerkovichPoint f → EReal, IsModuleTopologyPSH.{0} f L ψ ∧
      ∀ v ∈ sourceDivisorialSet f, ψ v = -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal) :=
  existsUnique_of_isModuleTopologyPSH f h

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (d + 1) (SchemeComplexPoint f))}
  {φ : SchemeComplexPoint f → EReal} {hφ : SourceModelPotential θ φ}
  {ℓ : SourceRayFamily (SchemeComplexPoint f)}

/-- `v ↦ -σ(v)(Φ)` is `Γ_ℓ^An` (`eq:psiandef`) for the complexification of `ℓ ∈ 𝓡(X, θ; φ)`
with `sup_X ℓ₁ ≤ 0`, at every Kähler index `ω`. -/
theorem negGaussVal_eq_naPotentialAnAt
    (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (ω : SourceKahlerForm (d + 1) (SchemeComplexPoint f)) :
    negGaussVal f d E Φ = naPotentialAnAt (d + 1) E (rayNAPotential omega hℓ) ω :=
  funext fun v => neg_gaussPotentialVal_ray_eq_naPotentialAnAt E omega hℓ hsup hΦ ω v

/-- `v ↦ -σ(v)(Φ)` is a psh metric on `L^An` iff `Γ_ℓ^An` is (any Kähler index, any universe). -/
theorem isModuleTopologyPSH_gauss_iff.{u} {L : RationalPicardSpace X}
    (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (ω : SourceKahlerForm (d + 1) (SchemeComplexPoint f)) :
    IsModuleTopologyPSH.{u} f L (negGaussVal f d E Φ) ↔
      IsModuleTopologyPSH.{u} f L (naPotentialAnAt (d + 1) E (rayNAPotential omega hℓ) ω) := by
  rw [negGaussVal_eq_naPotentialAnAt f d E omega hℓ hsup hΦ ω]

/-- **`prop:PhiinducePSH` from the existence clause of `cor:testcurvegivepshme`.** Let
`φ ∈ PSH(X, θ)_{>0}` be a model potential, `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0` and `Φ` the
complexification of `ℓ`. If `Γ_ℓ^An ∈ PSH(L^An)` for the non-Archimedean potential
`Γ_ℓ = P_θ[ℓ^*]_𝓘 ∈ PSH^NA(X, θ)_{>0}` (`cor:testcurvegivepshme`, existence), then
`v ↦ -σ(v)(Φ)` on `X^Div` admits a unique extension to `PSH(L^An)`, namely `v ↦ -σ(v)(Φ)` on
`X^An`. -/
theorem phiInducePSH_of_naPotentialAnAt {L : RationalPicardSpace X}
    (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (ω : SourceKahlerForm (d + 1) (SchemeComplexPoint f))
    (hex : IsModuleTopologyPSH.{0} f L (naPotentialAnAt (d + 1) E (rayNAPotential omega hℓ) ω)) :
    IsModuleTopologyPSH.{0} f L (negGaussVal f d E Φ) ∧
      ∃! ψ : BerkovichPoint f → EReal, IsModuleTopologyPSH.{0} f L ψ ∧
        ∀ v ∈ sourceDivisorialSet f, ψ v = -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal) := by
  have h := (isModuleTopologyPSH_gauss_iff f d E omega hℓ hsup hΦ ω).mpr hex
  exact ⟨h, existsUnique_of_isModuleTopologyPSH_gauss f d E h⟩

end SGPT.NAPotential.PhiPsh
