import SGPT.Checks.Comparison.PhiPshMain
import SGPT.NAPotential.DimZeroPsiPhi

/-!
# `prop:PhiinducePSH` in every dimension, including dimension zero

Source: `chapter_NApotential.tex`, `prop:PhiinducePSH` (*The algebraic setting*):

*Let `φ ∈ PSH(X, θ)_{>0}` be a model potential and `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`. Let `Φ`
be the complexification of `ℓ`. Then the function `v ↦ -σ(v)(Φ)` for `v ∈ X^Div` admits a unique
extension to an element of `PSH(L^An)`.*

The chapter's `X` is a connected projective manifold of any dimension. Lane PHI-PSH proved the
statement (`SGPT.NAPotential.PhiPsh.phiInducePSH`) for `X` of relative dimension `d + 1 ≥ 1`,
because the value `σ(v)(Φ)` it used (`NAGaga.gaussPotentialVal`) is only defined in positive
dimension. Here the same statement for `X` of every relative dimension `n`, with the
dimension-independent value `σ(v)(Φ) = DimZero.gaussPotentialValDim n E v Φ` (definitionally
NA-GAGA's value when `n = d + 1`: `negGaussValDim_succ`). Blueprint `claude-dim-zero.tex`, node
`claude-dim-zero:PhiinducePSH`.

## Formal setting

As for `SGPT.NAPotential.PhiPsh.phiInducePSH`: `X` is an integral scheme, projective and smooth of
relative dimension `n` over `ℂ` with a closed projective embedding `E`, `X(ℂ)` connected and
compact with its Borel structure; `L = m⁻¹ [M]`, `h = h_M^{1/m}`, `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)`
chartwise; `SourceModelPotential θ φ`, `ℓ ∈ sourceGeodesicRays omega θ φ hφ`,
`IsRayComplexificationOf ℓ Φ`, `X^Div = sourceDivisorialSet`, `PSH(L^An) = IsModuleTopologyPSH`.

## Proof

The route of lane PHI-PSH, now in every dimension: the complexification of `ℓ` is that of `ℓ^*`
(`PhiPsh.isComplexificationOf_rayLegendre`, dimension-free), the squeeze of `prop:psiandPhi` in
every dimension (`DimZero.gaussPotentialValDim_of_isComplexificationOf`) gives
`-σ(v)(Φ) = Γ_ℓ^An(v)` on `X^An` for `Γ_ℓ = P_θ[ℓ^*]_𝓘`, and `Γ_ℓ^An ∈ PSH(L^An)` is the
existence clause of `cor:testcurvegivepshme` (`BJ.Exist.naPotentialAnAt_isModuleTopologyPSH`,
already stated for every dimension `n`). Uniqueness is `thm:pshdetbydiv`. In dimension `0`,
`X(ℂ)` is a point and the extension is the constant `ℓ^*_max` (`phiInducePSH_dim_zero`).

## Main results

* `neg_gaussPotentialValDim_ray_eq_naPotentialAnAt`: `-σ(v)(Φ) = Γ_ℓ^An(v)` on `X^An`.
* `isModuleTopologyPSH_negGaussValDim`: `v ↦ -σ(v)(Φ)` lies in `PSH(L^An)` (every universe).
* **`phiInducePSH_dim`**: `prop:PhiinducePSH` for `X` of every relative dimension `n`.
* **`phiInducePSH_dim_zero`**: the dimension-zero case, with the extension computed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace SGPT.NAPotential.DimZero

open Set Filter
open scoped ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.NAGaga (unitDisc)
open SGPT.NAPotential.PhiPsh (IsRayComplexificationOf rayNAPotential rayIModelTestCurve)
open SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.Assembly
open SGPT.NAPotential.BJ.Exist
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance dimZeroPhiPshProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance dimZeroPhiPshPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroPhiPshPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dimZeroPhiPshPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

section General

/-- The function `v ↦ -σ(v)(Φ)` on `X^An`, for `X` of relative dimension `n`
(`σ(v)(Φ) = gaussPotentialValDim`). -/
def negGaussValDim (Φ : SchemeComplexPoint f × unitDisc → EReal) (v : BerkovichPoint f) : EReal :=
  -((gaussPotentialValDim n E v Φ : ℝ≥0∞) : EReal)

/-- In positive dimension `d + 1` this is the `negGaussVal`. -/
theorem negGaussValDim_succ (d : ℕ) [SmoothOfRelativeDimension (d + 1) f]
    (Φ : SchemeComplexPoint f × unitDisc → EReal) :
    negGaussValDim f (d + 1) E Φ = PhiPsh.negGaussVal f d E Φ :=
  rfl

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  {φ : SchemeComplexPoint f → EReal} {hφ : SourceModelPotential θ φ}
  {ℓ : SourceRayFamily (SchemeComplexPoint f)}

/-- **`-σ(v)(Φ) = Γ_ℓ^An(v)` on `X^An`, in every dimension.** For `ℓ ∈ 𝓡(X, θ; φ)` with
`sup_X ℓ₁ ≤ 0`, `Φ` its complexification, every Kähler index `ω` and every `v ∈ X^An`, the limit
defining `σ(v)(Φ)` exists and `-σ(v)(Φ)` is the analytification `eq:psiandef` of
`Γ_ℓ = P_θ[ℓ^*]_𝓘` (`PhiPsh.rayNAPotential`). -/
theorem neg_gaussPotentialValDim_ray_eq_naPotentialAnAt
    (omega : KahlerBackground n (SchemeComplexPoint f))
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierValDim n E v Φ k / k) atTop
        (nhds (gaussPotentialValDim n E v Φ)) ∧
      -((gaussPotentialValDim n E v Φ : ℝ≥0∞) : EReal) =
        naPotentialAnAt n E (rayNAPotential omega h) ω v := by
  set Γ := sourceRayLegendreTestCurve omega h with hΓ
  set G := rayIModelTestCurve omega h with hG
  have hGval : G.val = Γ.iEnvelope omega := rfl
  have hmaxG : G.val.max = sourceRayLegendreCutoff omega h := by
    rw [hGval, SourceTestCurve.iEnvelope_max, hΓ, sourceRayLegendreTestCurve_max]
  have hpot : ∀ (τ : Iio (sourceRayLegendreCutoff omega h)) (τ' : Iio G.val.max), τ.1 = τ'.1 →
      potentialAn n E (G.val.potential τ') = potentialAn n E (Γ.potential τ) := by
    rintro ⟨τ, h1⟩ ⟨τ', h2⟩ (rfl : τ = τ')
    have hp1 : G.val.potential ⟨τ, h2⟩ = sourceIEnvelope θ (Γ.potential ⟨τ, h1⟩) :=
      SourceTestCurve.iEnvelope_potential omega Γ ⟨τ, h1⟩
    rw [hp1]
    exact potentialAn_sourceIEnvelope n E (Γ.thetaPSH ⟨τ, h1⟩)
  have hsq := gaussPotentialValDim_of_isComplexificationOf n E omega Γ.toSourceTestCurvePredata
    (PhiPsh.rayLegendreCutoff_nonpos omega h hsup) (PhiPsh.isComplexificationOf_rayLegendre omega h hΦ) v
  refine ⟨hsq.1, ?_⟩
  rw [hsq.2, rayNAPotential, naPotentialAnAt_sourcePositiveTestCurveToNA_dim n E G ω v]
  have hmaxΓ : Γ.toSourceTestCurvePredata.max = sourceRayLegendreCutoff omega h :=
    sourceRayLegendreTestCurve_max omega h
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have h1 : τ.1 < sourceRayLegendreCutoff omega h := by rw [← hmaxΓ]; exact τ.2
    have h2 : τ.1 ∈ Iio G.val.max := by rw [mem_Iio, hmaxG]; exact h1
    rw [show potentialAn n E (Γ.toSourceTestCurvePredata.potential τ) =
      potentialAn n E (Γ.potential ⟨τ.1, h1⟩) from rfl, ← hpot ⟨τ.1, h1⟩ ⟨τ.1, h2⟩ rfl]
    exact le_iSup (fun σ : Iio G.val.max =>
      potentialAn n E (G.val.potential σ) v + ((σ : ℝ) : EReal)) ⟨τ.1, h2⟩
  · refine iSup_le fun τ => ?_
    have h1 : τ.1 < sourceRayLegendreCutoff omega h := by rw [← hmaxG]; exact τ.2
    have h1' : τ.1 < Γ.toSourceTestCurvePredata.max := by rw [hmaxΓ]; exact h1
    rw [hpot ⟨τ.1, h1⟩ τ rfl]
    exact le_iSup (fun σ : Iio Γ.toSourceTestCurvePredata.max =>
      potentialAn n E (Γ.toSourceTestCurvePredata.potential σ) v + ((σ : ℝ) : EReal)) ⟨τ.1, h1'⟩

variable {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m)
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

include hm hθ in
/-- **`v ↦ -σ(v)(Φ)` is a psh metric on `L^An`** (every universe, every dimension), for the
complexification `Φ` of `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`. -/
theorem isModuleTopologyPSH_negGaussValDim (omega : KahlerBackground n (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    IsModuleTopologyPSH.{u} f ((m : ℚ)⁻¹ • rationalPicardClass b) (negGaussValDim f n E Φ) := by
  let ω : SourceKahlerForm n (SchemeComplexPoint f) := sourceKahlerFormOfBackground omega
  have heq : negGaussValDim f n E Φ = naPotentialAnAt n E (rayNAPotential omega hℓ) ω :=
    funext fun v => (neg_gaussPotentialValDim_ray_eq_naPotentialAnAt f n E omega hℓ hsup hΦ ω v).2
  rw [heq]
  exact naPotentialAnAt_isModuleTopologyPSH f n E b HM hm hθ (rayNAPotential omega hℓ) ω

include hm hθ in
/-- **`prop:PhiinducePSH`, every dimension.** Let `X` be a connected projective manifold of any
dimension `n` (including `0`), `L = m⁻¹ [M]` a `ℚ`-line bundle with the Hermitian metric
`h_M^{1/m}` and `θ = c₁(L, h) = m⁻¹ c₁(M, h_M)`. Let `φ ∈ PSH(X, θ)_{>0}` be a model potential,
`ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0` and `Φ` the complexification of `ℓ`. Then `v ↦ -σ(v)(Φ)` on
`X^Div` admits a unique extension to an element of `PSH(L^An)`; this extension is `v ↦ -σ(v)(Φ)`
on all of `X^An`. -/
theorem phiInducePSH_dim (omega : KahlerBackground n (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    (∃! ψ : BerkovichPoint f → EReal,
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ ∧
        ∀ v ∈ sourceDivisorialSet f, ψ v = -((gaussPotentialValDim n E v Φ : ℝ≥0∞) : EReal)) ∧
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) (negGaussValDim f n E Φ) := by
  have h := isModuleTopologyPSH_negGaussValDim.{0} f n E b HM hm hθ omega hℓ hsup hΦ
  exact ⟨existsUnique_of_isModuleTopologyPSH f h, h⟩

end General

section Zero

variable [SmoothOfRelativeDimension 0 f]
  [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}
  {φ : SchemeComplexPoint f → EReal} {hφ : SourceModelPotential θ φ}
  {ℓ : SourceRayFamily (SchemeComplexPoint f)}
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f 0 E M) {m : ℕ}
  (hm : 0 < m)
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)

/-- In dimension zero `-σ(v)(Φ) = sup_X ℓ₁ = ℓ^*_max` at every `v ∈ X^An`: the function is the
constant `sup_X ℓ₁`. -/
theorem negGaussValDim_eq_const_of_dim_zero (omega : KahlerBackground 0 (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    negGaussValDim f 0 E Φ = fun _ => ⨆ x, ℓ ⟨1, by norm_num⟩ x := by
  funext v
  let ω : SourceKahlerForm 0 (SchemeComplexPoint f) := sourceKahlerFormOfBackground omega
  have hmaxG : (rayIModelTestCurve omega hℓ).val.max = sourceRayLegendreCutoff omega hℓ := by
    change ((sourceRayLegendreTestCurve omega hℓ).iEnvelope omega).max = _
    rw [SourceTestCurve.iEnvelope_max, sourceRayLegendreTestCurve_max]
  change -((gaussPotentialValDim 0 E v Φ : ℝ≥0∞) : EReal) = _
  rw [(neg_gaussPotentialValDim_ray_eq_naPotentialAnAt f 0 E omega hℓ hsup hΦ ω v).2,
    NANS.naPotentialAnAt_eq_of_dim_zero, rayNAPotential, sourcePositiveTestCurveToNA_max, hmaxG,
    (sourceRayLegendre_normalized omega hℓ).1 ⟨1, by norm_num⟩, one_mul]

include hm hθ in
/-- **`prop:PhiinducePSH` in dimension zero.** `X` smooth projective of relative dimension `0`
with `X(ℂ)` connected (a point), `L`, `θ`, `φ`, `ℓ`, `Φ` as in `phiInducePSH_dim`. Then
`v ↦ -σ(v)(Φ)` on `X^Div` admits a unique extension to an element of `PSH(L^An)`; this extension
is `v ↦ -σ(v)(Φ)` on all of `X^An`, the constant `sup_X ℓ₁`. -/
theorem phiInducePSH_dim_zero (omega : KahlerBackground 0 (SchemeComplexPoint f))
    (hℓ : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ) :
    (∃! ψ : BerkovichPoint f → EReal,
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) ψ ∧
        ∀ v ∈ sourceDivisorialSet f, ψ v = -((gaussPotentialValDim 0 E v Φ : ℝ≥0∞) : EReal)) ∧
      IsModuleTopologyPSH.{0} f ((m : ℚ)⁻¹ • rationalPicardClass b) (negGaussValDim f 0 E Φ) ∧
      negGaussValDim f 0 E Φ = fun _ => ⨆ x, ℓ ⟨1, by norm_num⟩ x :=
  ⟨(phiInducePSH_dim f 0 E b HM hm hθ omega hℓ hsup hΦ).1,
    (phiInducePSH_dim f 0 E b HM hm hθ omega hℓ hsup hΦ).2,
    negGaussValDim_eq_const_of_dim_zero f E omega hℓ hsup hΦ⟩

end Zero

end SGPT.NAPotential.DimZero
