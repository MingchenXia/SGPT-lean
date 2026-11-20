import SGPT.TestCurve.PhongSturmFinal
import SGPT.TestCurve.RWNClauses
import SGPT.TestCurve.TestConfigJumpMeasure
import SGPT.GAGA.OkoCloseDXMain
import SGPT.GAGA.H0LTestCurve
import SGPT.NAPotential.DHMeasure

/-! # Volumes of the test curve of a test configuration and its jumping measures

Source `chapter_NApotential.tex`, `rmk:NApotential:L862`: *when `{θ}` is a Hodge class and `Γ` is
induced by a test configuration as in `ex:RWN` and `rmk:PhongSturm`, our Duistermaat–Heckman
measure coincides with the more traditional definition of [BHJ17, §3.2]; this is explained in
[Xia21, Remark 7.17].*  Blueprint `claude-na-ns`, section on test configurations.

The Duistermaat–Heckman measure of [BHJ17, §3.2] of an ample test configuration is the weak limit
of the rescaled weight measures; by [BHJ17, §1.1, §5] the weights of `H⁰(𝓧₀, k𝓛₀)` are the
successive minima of the induced filtration `𝓕` of `R(X, L)`, so the rescaled weight measure is
`N_k⁻¹ ν_k` with the jumping measure `ν_k = ∑_j δ_{λ^{(k)}_j / k}`
(`SGPT.LineBundle.SectionFiltration.jumpMeasure`, lane TESTCONF2), whose tails are
`ν_k[τ, ∞) = dim 𝓕^{kτ}_k`.  The book's `DH(Γ)` has tails `DH(Γ)[τ, ∞) = vol(Γ_τ)`
(`SGPT.NAPotential.DH.naDuistermaatHeckman_Ici`).  The comparison in [Xia21, Remark 7.17] rests on
[Xia21, Theorem 5.28]: `vol(θ, Γ^𝓕_τ) = lim_k n! dim 𝓕^{kτ}_k / kⁿ`.  This file proves this
identity in the following form (the sandwich at every `τ < τ(𝓕)`):

`vol θ_{ψ_τ} ≤ liminf_k n! k⁻ⁿ ν_k[τ', ∞) ≤ limsup_k n! k⁻ⁿ ν_k[τ', ∞) ≤ vol θ_{ψ_{τ'}}`

for `τ' < τ < τ(𝓕)`, where `ψ_τ` is the obstacle of `ex:RWN` and `vol θ_{ψ}` the volume of
`thm:DXmain1`; for `L` with a positive volume `vol θ_{ψ_τ} = ∫_X θ_{Γ^𝓕_τ}ⁿ`.  Above the slope
the tails vanish: `ν_k[τ', ∞) = 0` for `τ' > τ(𝓕)`.

## Ingredients

* `𝓕^{kτ}_k ⊆ H⁰(X, L^k ⊗ 𝓘(kψ_τ))` (`SGPT.TestCurve.RWN.isMultiplierSection_obstacle`) and the
  upper bound of `thm:DXmain1` (`SGPT.IGood.DXMain.limsup_multiplierH0_le`, on `X` with a smooth
  flag).
* The Skoda inclusion `H⁰(X, L^k ⊗ 𝓘(kψ_τ)) ⊆ 𝓕^{kτ'}_k` for `k ≫ 0`
  (`SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal`, proved for the finitely generated filtrations
  of ample test configurations: `SGPT.TestCurve.SkodaInc.skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision`
  with GAGA and Skoda's division theorem) and the lower bound of `thm:DXmain1`
  (`SGPT.GAGA.OkoClose.dxMainLowerBound_of_isIntegral`).

## Formal setting

As in `SGPT.TestCurve.RWN`: `X` an integral smooth projective complex scheme of dimension
`n = m + 1`, `L` a line bundle with atlas `a` and smooth metric `H`, `θ = c₁(L, H)`, `𝓕` a
filtration of `R(X, L)` (`def:testcurve:L1134`); a test configuration enters through its
finitely generated normalized `ℤ`-filtration (the encoding, [BHJ17, Prop. 2.15]).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH.VariableComplexAtlas
open scoped Topology ENNReal

namespace SGPT.NAPotential.NANS.TestConfig

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance nansTCTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance nansTCCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance nansTCManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance nansTCMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance nansTCBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-! ### Rescaled tails of the jumping measures -/

section Tails

variable {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)

/-- `n! dim 𝓕^{kτ}_k / kⁿ`. -/
def normalizedPieceDim (n : ℕ) (τ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ((n.factorial : ℝ≥0∞) * (F.pieceDim ((k : ℝ) * τ) k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ n

/-- The rescaled tail `n! k⁻ⁿ ν_k[τ, ∞)` of the jumping measure is `n! dim 𝓕^{kτ}_k / kⁿ`
(`k > 0`). -/
theorem jumpMeasure_tail_eq (n : ℕ) {k : ℕ} (hk : 0 < k)
    [FiniteDimensional ℂ (SectionSpace f L k)] (τ : ℝ) :
    ((n.factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ)) / (k : ℝ≥0∞) ^ n =
      normalizedPieceDim F n τ k := by
  rw [F.jumpMeasure_Ici hk τ, normalizedPieceDim]

/-- **The tails vanish above the slope**: `𝓕^{kτ}_k = 0` for `τ > τ(𝓕)` and `k > 0`. -/
theorem pieceDim_eq_zero_of_slope_lt {τ : ℝ} (hτ : F.slope < τ) {k : ℕ} (hk : 0 < k)
    [FiniteDimensional ℂ (SectionSpace f L k)] : F.pieceDim ((k : ℝ) * τ) k = 0 := by
  by_contra hne
  have hbot : F.piece ((k : ℝ) * τ) k ≠ ⊥ := by
    intro h
    apply hne
    rw [SectionFiltration.pieceDim, h, finrank_bot]
  have hjump := (F.piece_ne_bot_iff ((k : ℝ) * τ)).mp hbot
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiv : ((τ : ℝ) : EReal) ≤ F.jump k / ((k : ℝ) : EReal) := by
    have h1 : (((k : ℝ) * τ : ℝ) : EReal) / ((k : ℝ) : EReal) ≤ F.jump k / ((k : ℝ) : EReal) :=
      EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkpos.le) hjump
    have h2 : (((k : ℝ) * τ : ℝ) : EReal) / ((k : ℝ) : EReal) = ((τ : ℝ) : EReal) := by
      rw [← EReal.coe_div]
      congr 1
      field_simp
    rwa [h2] at h1
  have hslope : F.jump k / ((k : ℝ) : EReal) ≤ F.slope :=
    le_iSup₂ (f := fun (k : ℕ) (_ : 0 < k) => F.jump k / ((k : ℝ) : EReal)) k hk
  exact absurd (hdiv.trans hslope) (not_le.mpr hτ)

/-- `n! k⁻ⁿ ν_k[τ, ∞) = 0` for `τ > τ(𝓕)` and `k > 0`. -/
theorem jumpMeasure_tail_eq_zero_of_slope_lt (n : ℕ) {τ : ℝ} (hτ : F.slope < τ) {k : ℕ}
    (hk : 0 < k) [FiniteDimensional ℂ (SectionSpace f L k)] :
    ((n.factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ)) / (k : ℝ≥0∞) ^ n = 0 := by
  rw [jumpMeasure_tail_eq F n hk τ, normalizedPieceDim, pieceDim_eq_zero_of_slope_lt F hτ hk]
  simp

end Tails

/-! ### The volume sandwich -/

section Volume

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H : SchemeLineBundleMetric f (m + 1) E L)

/-- `𝓕^{kτ}_k ⊆ H⁰(X, L^k ⊗ 𝓘(kψ_τ))`, so `dim 𝓕^{kτ}_k ≤ h⁰(X, L^k ⊗ 𝓘(kψ_τ))`. -/
theorem pieceDim_le_multiplierH0 {τ : ℝ} (hτ : (τ : EReal) < F.slope) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    F.pieceDim ((k : ℝ) * τ) k ≤ SGPT.IGood.DXMain.multiplierH0 f (m + 1) E
      (F.obstacle_isThetaPshPotential H hτ).1.quasiPlurisubharmonic L k := by
  let := E.isSeparated
  let := E.quasiCompact
  have := SectionSpace.finiteDimensional f E a k
  exact Submodule.finrank_mono
    (fun s hs => SGPT.TestCurve.RWN.isMultiplierSection_obstacle F H hτ hs)

/-- **Upper bound** ([Xia21, Thm. 5.28], `≤`): on `X` with a smooth flag, for `τ < τ(𝓕)`,
`limsup_k n! dim 𝓕^{kτ}_k / kⁿ ≤ vol θ_{ψ_τ}`. -/
theorem limsup_normalizedPieceDim_le [Nonempty (SchemeComplexPoint f)]
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) {τ : ℝ}
    (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    limsup (normalizedPieceDim F (m + 1) τ) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  refine le_trans (limsup_le_limsup (Eventually.of_forall fun k => ?_))
    (SGPT.IGood.DXMain.limsup_multiplierH0_le f E Y hY a H (F.obstacle_isThetaPshPotential H hτ))
  unfold normalizedPieceDim
  gcongr
  exact_mod_cast pieceDim_le_multiplierH0 F H hτ k

/-- **Lower bound** ([Xia21, Thm. 5.28], `≥`): if the Skoda inclusion holds for `𝓕` (true for the
filtration of an ample test configuration), then for `τ' < τ < τ(𝓕)`,
`vol θ_{ψ_τ} ≤ liminf_k n! dim 𝓕^{kτ'}_k / kⁿ`. -/
theorem iVolume_le_liminf_normalizedPieceDim [Nonempty (SchemeComplexPoint f)]
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H) {τ' τ : ℝ} (hlt : τ' < τ)
    (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) ≤
      liminf (normalizedPieceDim F (m + 1) τ') atTop := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  obtain ⟨k₀, hk₀⟩ := hSk τ' τ hlt hτ
  have hlow := SGPT.GAGA.OkoClose.dxMainLowerBound_of_isIntegral a H
    (F.obstacle_isThetaPshPotential H hτ)
  refine le_trans hlow (liminf_le_liminf ?_)
  filter_upwards [eventually_ge_atTop k₀] with k hk
  have := SectionSpace.finiteDimensional f E a k
  unfold SGPT.IGood.DXMain.normalizedMultiplierH0 normalizedPieceDim
  gcongr
  exact_mod_cast Submodule.finrank_mono (fun s hs => hk₀ k hk s hs)

/-- **The volume sandwich for the jumping measures** ([Xia21, Thm. 5.28] in the form used for
[Xia21, Remark 7.17], `rmk:NApotential:L862`): on `X` with a smooth flag, if the Skoda inclusion
holds for `𝓕`, then for `τ' < τ < τ(𝓕)`,
`vol θ_{ψ_τ} ≤ liminf_k n! k⁻ⁿ ν_k[τ', ∞) ≤ limsup_k n! k⁻ⁿ ν_k[τ', ∞) ≤ vol θ_{ψ_{τ'}}`. -/
theorem jumpMeasure_tail_sandwich [Nonempty (SchemeComplexPoint f)]
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (hSk : SGPT.TestCurve.SkodaRWN.SkodaInclusionIdeal F H) {τ' τ : ℝ} (hlt : τ' < τ)
    (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) ≤
      liminf (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
        (k : ℝ≥0∞) ^ (m + 1)) atTop ∧
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
        (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ') (F.obstacle_isThetaPshPotential H
          ((EReal.coe_lt_coe_iff.mpr hlt).trans hτ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have heq : (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
      (k : ℝ≥0∞) ^ (m + 1)) =ᶠ[atTop] normalizedPieceDim F (m + 1) τ' := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have := SectionSpace.finiteDimensional f E a k
    exact jumpMeasure_tail_eq F (m + 1) hk τ'
  rw [liminf_congr heq, limsup_congr heq]
  exact ⟨iVolume_le_liminf_normalizedPieceDim F H hSk hlt hτ,
    limsup_normalizedPieceDim_le F H Y hY ((EReal.coe_lt_coe_iff.mpr hlt).trans hτ)⟩

end Volume

/-! ### Volumes of the test curve `Γ^𝓕` and ample test configurations -/

section Mass

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H : SchemeLineBundleMetric f (m + 1) E L)

/-- On `X` with a smooth flag and `{θ}` big, the obstacle `ψ_τ` of `ex:RWN` is `𝓘`-good with
respect to `θ` itself for every `τ < τ(𝓕)`: it has positive mass and `P_θ[ψ_τ] = P_θ[ψ_τ]_𝓘`. -/
theorem iGoodWith_obstacle (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    IGoodWith (H.curvature a) (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have hvol := SGPT.GAGA.H0L.volume_pos H Y hY hbig
  have hpos₀ := (SGPT.TestCurve.RWN.obstacle_iGoodWith_of_volume_pos F H Y hY hvol).positiveMass
  have hpos := SGPT.TestCurve.RWN.obstacle_hasPositiveMass_of_pos F H
    (SGPT.TestCurve.RWN.neg_bound_sub_one_lt_slope F hvol) hpos₀ hτ
  obtain ⟨θ', hu', hg'⟩ := F.obstacle_iGood_of_lt_slope H hτ
  exact (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
    (schemeProjectiveTNKahlerBackground f (m + 1) E) θ' (H.curvature a) hu' _ hg'.positiveMass
    hpos).mp hg'

/-- **`vol θ_{ψ_τ} = ∫_X θ_{Γ^𝓕_τ}ⁿ`** for `τ < τ(𝓕)` (`X` with a smooth flag, `{θ}` big): the
volume of `thm:DXmain1` of the obstacle is the mass of the slice `Γ^𝓕_τ = P_θ[ψ_τ]` of the test
curve of `ex:RWN`, i.e. the tail `DH(Γ^𝓕)[τ, ∞)` of the book's Duistermaat–Heckman measure. -/
theorem iVolume_obstacle_eq_mass (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
    iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (F.obstacle H τ) (F.obstacle_isThetaPshPotential H hτ) =
      diagonalPotentialMass (H.curvature a) (F.testCurvePotential H τ)
        (F.testCurvePotential_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hgw := iGoodWith_obstacle F H Y hY hbig hτ
  unfold iVolume
  exact SGPT.IGood.Misc2VolBigL.diagonalPotentialMass_congr _ hgw.envelope_eq.symm _ _

/-- **[Xia21, Theorem 5.28] for ample test configurations, in the form behind
`rmk:NApotential:L862`**: let `𝓕` be the filtration of `R(X, L)` induced by an ample test
configuration (a finitely generated normalized `ℤ`-filtration, [BHJ17, Prop. 2.15]), `h` a smooth
metric with Kähler curvature `θ = c₁(L, h)`, and `X` with a smooth flag.  Then for
`τ' < τ < τ(𝓕)`,
`∫_X θ_{Γ^𝓕_τ}ⁿ ≤ liminf_k n! k⁻ⁿ ν_k[τ', ∞) ≤ limsup_k n! k⁻ⁿ ν_k[τ', ∞) ≤ ∫_X θ_{Γ^𝓕_{τ'}}ⁿ`,
where `ν_k` is the jumping measure (the weights of the central fibre).  Consequently (not
formalized here) `n! k⁻ⁿ ν_k[τ', ∞) → ∫_X θ_{Γ^𝓕_{τ'}}ⁿ` at every `τ' < τ(𝓕)` where
`τ ↦ ∫_X θ_{Γ^𝓕_τ}ⁿ` is right-continuous. -/
theorem testConfig_jumpMeasure_tail_sandwich
    (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (G : SGPT.TestCurve.TestConfig.SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ' τ : ℝ} (hlt : τ' < τ) (hτ : (τ : EReal) < (G.fgFiltration hG h0).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
    diagonalPotentialMass (H.curvature a) ((G.fgFiltration hG h0).testCurvePotential H τ)
        ((G.fgFiltration hG h0).testCurvePotential_isThetaPshPotential H hτ) ≤
      liminf (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (G.fgFiltration hG h0).jumpMeasure k (Ici τ')) / (k : ℝ≥0∞) ^ (m + 1)) atTop ∧
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (G.fgFiltration hG h0).jumpMeasure k (Ici τ')) / (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      diagonalPotentialMass (H.curvature a) ((G.fgFiltration hG h0).testCurvePotential H τ')
        ((G.fgFiltration hG h0).testCurvePotential_isThetaPshPotential H
          ((EReal.coe_lt_coe_iff.mpr hlt).trans hτ)) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) := SGPT.GAGA.H0L.nonempty_of_smoothFlag Y hY
  set F := G.fgFiltration hG h0
  have hgaga : ∀ᶠ j in atTop, SGPT.NAPotential.GAGAMult.SchemeSectionsAlgebraic f (m + 1) E a H j :=
    Eventually.of_forall fun j => SGPT.GAGA.H0L.schemeSectionsAlgebraic a H j
  have hSk := SGPT.TestCurve.SkodaInc.skodaInclusionIdeal_of_sectionsAlgebraic_of_globalSkodaDivision
    G hG h0 H hK hgaga (SGPT.TestCurve.GlobalSkoda.globalSkodaDivision_of_sectionsAlgebraic H a hgaga)
  have hτ' : (τ' : EReal) < F.slope := (EReal.coe_lt_coe_iff.mpr hlt).trans hτ
  obtain ⟨h1, h2⟩ := jumpMeasure_tail_sandwich F H Y hY hSk hlt hτ
  rw [iVolume_obstacle_eq_mass F H Y hY hbig hτ] at h1
  rw [iVolume_obstacle_eq_mass F H Y hY hbig hτ'] at h2
  exact ⟨h1, h2⟩

end Mass

/-! ### The Duistermaat–Heckman measure of `Γ^𝓕` -/

section DH

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L} (F : SectionFiltration f a)
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`Γ^𝓕 ∈ PSH^NA(X, θ)_{>0}`** (`ex:RWN`, `X` with a smooth flag, `{θ}` big): the test curve
`(Γ^𝓕_τ)_{τ < τ(𝓕)}` of the filtration as a positive `𝓘`-model test curve (both clauses of
`ex:RWN` are supplied by lanes RWN and H0-GAGA3). -/
def filtrationNACurve [IsSeparated f] [QuasiCompact f] [CompactSpace (SchemeComplexPoint f)]
    [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    SourcePositiveIModelTestCurve (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H) :=
  ⟨SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig
      (SGPT.TestCurve.RWN.rwnIModelClause_of_lowerBound F H Y hY hbig
        (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig))
      (SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
        (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)),
    ⟨_, _, (SGPT.TestCurve.RWN.filtrationTestCurve_mem_iModel_and_isBounded_of_lowerBound F H Y hY
      hbig (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)).1⟩⟩

omit [IsIntegral X] in
/-- The bigness of `{θ}` read through the atlas form of the curvature. -/
theorem curvatureAtlasForm_isBig [IsSeparated f] [QuasiCompact f]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))) := by
  rw [SGPT.TestCurve.TestConf.curvatureAtlasForm_native]
  exact hbig

omit [IsIntegral X] in
theorem diagonalPotentialMass_form_congr [IsSeparated f] [QuasiCompact f]
    [CompactSpace (SchemeComplexPoint f)]
    {θ₁ θ₂ : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f)} (h : θ₁ = θ₂)
    (u : SchemeComplexPoint f → EReal) (h₁ : IsThetaPshPotential θ₁.val u)
    (h₂ : IsThetaPshPotential θ₂.val u) :
    diagonalPotentialMass θ₁ u h₁ = diagonalPotentialMass θ₂ u h₂ := by
  subst h
  rfl

/-- **The tails of `DH(Γ^𝓕)`** (`X` with a smooth flag, `{θ}` big): for `τ < τ(𝓕)`,
`DH(Γ^𝓕)[τ, ∞) = ∫_X θ_{Γ^𝓕_τ}ⁿ` (`naDuistermaatHeckman_Ici`, computed with the flag `Y`). -/
theorem naDuistermaatHeckman_filtration_Ici [IsSeparated f] [QuasiCompact f]
    [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {t : ℝ} (ht : t < SGPT.TestCurve.TestConf.slopeReal F) :
    @SGPT.NAPotential.DH.naDuistermaatHeckman m
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
        (@BorelSpace.mk _ _ (borel _) rfl) _
        (curvatureAtlasForm_isBig H hbig) (filtrationNACurve F H Y hY hbig) (Ici t) =
      diagonalPotentialMass (H.curvature a) (F.testCurvePotential H t)
        (F.testCurvePotential_isThetaPshPotential H
          (SGPT.TestCurve.TestConf.coe_lt_slope_of_lt F H (hbig := hbig)
            (hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
              (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)) ht)) := by
  have h := @SGPT.NAPotential.DH.naDuistermaatHeckman_Ici m
    (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
    (@BorelSpace.mk _ _ (borel _) rfl) _
    (curvatureAtlasForm_isBig H hbig) (filtrationNACurve F H Y hY hbig) ⟨t, ht⟩
  refine h.trans ?_
  unfold sourcePotentialNonPluripolarMeasure
  exact diagonalPotentialMass_form_congr (SGPT.TestCurve.TestConf.curvatureAtlasForm_native H) _ _ _

/-- **`rmk:NApotential:L862`: the tails of the BHJ weight measures against `DH(Γ^𝓕)`.**  Let `𝓕`
be the filtration of an ample test configuration (a finitely generated normalized `ℤ`-filtration
of `R(X, L)`), `h` a smooth metric with Kähler curvature `θ = c₁(L, h)` (so `{θ}` is a Hodge
class), and `X` with a smooth flag.  For `τ' < τ < τ(𝓕)`,
`DH(Γ^𝓕)[τ, ∞) ≤ liminf_k n! k⁻ⁿ ν_k[τ', ∞) ≤ limsup_k n! k⁻ⁿ ν_k[τ', ∞) ≤ DH(Γ^𝓕)[τ', ∞)`,
where `DH(Γ^𝓕)` is the book's Duistermaat–Heckman measure (`def:DHm`) of the test curve of
`ex:RWN` and `ν_k` the jumping measure of `𝓕` (the weights of `H⁰(𝓧₀, k𝓛₀)`, [BHJ17, §1.1,
§5]). -/
theorem testConfig_DH_tail_sandwich
    (G : SGPT.TestCurve.TestConfig.SectionZFiltration f a) (hG : G.IsFinitelyGenerated)
    (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ' τ : ℝ} (hlt : τ' < τ) (hτ : τ < SGPT.TestCurve.TestConf.slopeReal (G.fgFiltration hG h0)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    @SGPT.NAPotential.DH.naDuistermaatHeckman m
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
        (@BorelSpace.mk _ _ (borel _) rfl) _ (curvatureAtlasForm_isBig H hbig)
        (filtrationNACurve (G.fgFiltration hG h0) H Y hY hbig) (Ici τ) ≤
      liminf (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (G.fgFiltration hG h0).jumpMeasure k (Ici τ')) / (k : ℝ≥0∞) ^ (m + 1)) atTop ∧
    limsup (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) *
        (G.fgFiltration hG h0).jumpMeasure k (Ici τ')) / (k : ℝ≥0∞) ^ (m + 1)) atTop ≤
      @SGPT.NAPotential.DH.naDuistermaatHeckman m
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
        (@BorelSpace.mk _ _ (borel _) rfl) _ (curvatureAtlasForm_isBig H hbig)
        (filtrationNACurve (G.fgFiltration hG h0) H Y hY hbig) (Ici τ') := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  rw [naDuistermaatHeckman_filtration_Ici (G.fgFiltration hG h0) H Y hY hbig hτ,
    naDuistermaatHeckman_filtration_Ici (G.fgFiltration hG h0) H Y hY hbig (hlt.trans hτ)]
  exact testConfig_jumpMeasure_tail_sandwich H Y hY G hG h0 hK hbig hlt
    (SGPT.TestCurve.TestConf.coe_lt_slope_of_lt (G.fgFiltration hG h0) H (hbig := hbig)
      (hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound (G.fgFiltration hG h0) H Y hY hbig
        (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)) hτ)

/-- **Above the slope** both sides vanish: for `τ' > τ(𝓕)`, `n! k⁻ⁿ ν_k[τ', ∞) = 0` for every
`k > 0` and `DH(Γ^𝓕)[τ', ∞) = 0`. -/
theorem filtration_tails_eq_zero_of_slope_lt [IsSeparated f] [QuasiCompact f]
    [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
    (hbig : IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    {τ' : ℝ} (hτ' : SGPT.TestCurve.TestConf.slopeReal F < τ') :
    (∀ k : ℕ, 0 < k → (((m + 1).factorial : ℝ≥0∞) * F.jumpMeasure k (Ici τ')) /
        (k : ℝ≥0∞) ^ (m + 1) = 0) ∧
      @SGPT.NAPotential.DH.naDuistermaatHeckman m
        (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
        (@BorelSpace.mk _ _ (borel _) rfl) _ (curvatureAtlasForm_isBig H hbig)
        (filtrationNACurve F H Y hY hbig) (Ici τ') = 0 := by
  have hb := SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (SGPT.GAGA.H0L.dxMainLowerBound_thetaPshSupremum H Y hY hbig)
  have hslope : F.slope < (τ' : EReal) := by
    rw [← SGPT.TestCurve.TestConf.coe_slopeReal F H hbig hb]
    exact EReal.coe_lt_coe_iff.mpr hτ'
  refine ⟨fun k hk => ?_, ?_⟩
  · have := SectionSpace.finiteDimensional f E a k
    exact jumpMeasure_tail_eq_zero_of_slope_lt F (m + 1) hslope hk
  · have h := @SGPT.NAPotential.DH.naDuistermaatHeckman_Ioi_max m
      (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY) (borel _)
      (@BorelSpace.mk _ _ (borel _) rfl) _
      (curvatureAtlasForm_isBig H hbig) (filtrationNACurve F H Y hY hbig)
    exact measure_mono_null (Ici_subset_Ioi.mpr hτ') h

end DH

end SGPT.NAPotential.NANS.TestConfig

end
