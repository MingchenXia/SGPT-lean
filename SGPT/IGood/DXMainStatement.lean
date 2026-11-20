import SGPT.IGood.DXMainUpper
import SGPT.IGood.SectionMinimalMultiplier
import SGPT.LineBundle.BigLineBundle

/-!
# The statement of the asymptotic Riemann–Roch formula `thm:DXmain1` and what is proved

Source `thm:DXmain1` (chapter *`𝓘`-good singularities*, Section *The volumes of Hermitian
pseudo-effective line bundles*): for a Hermitian pseudo-effective line bundle
`(L, h = h₀ e^{-φ})` on a connected compact Kähler manifold of dimension `n`
(`θ = c₁(L, h₀)`, `φ ∈ PSH(X, θ)`) and a holomorphic line bundle `T`,
`lim_{k → ∞} n! h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. Blueprint `claude-dxmain`.

## Formal setting

The projective case with `T = 𝒪_X`, in the algebraic section setting of the Okounkov chapter
(`SGPT.IGood.DXMainSections`): `X` an integral smooth projective complex scheme of dimension
`n = m + 1`, `L` a line bundle with atlas `a` and smooth metric `H` (`θ = c₁(L, H)`), and
`vol θ_φ = iVolume θ φ = ∫_X θ_{P_θ[φ]_𝓘}ⁿ` (`def:volcurr` / the book's `vol θ_φ`).

* `DXMain1Holds`: the conclusion of `thm:DXmain1` for one `(X, L, H, φ)`;
  `DXMain1UntwistedStatement`: for all of them (projective `X`, `T = 𝒪_X`).
* `DXMainLowerBound`: the inequality `vol θ_φ ≤ liminf n! h⁰ / kⁿ` (the open half).
* `dxMain1Holds_of_lowerBound`: on `X` carrying a smooth flag, the lower bound implies the
  theorem (the upper bound is `limsup_multiplierH0_le`).
* `dxMain1Holds_of_iVolume_eq_zero`: `thm:DXmain1` holds when `vol θ_φ = 0`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXMain

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.LineBundle SGPT.PSH
open scoped Topology ENNReal

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance dxStatementTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dxStatementCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance dxStatementManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- The normalized dimensions `n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ ∈ [0, ∞]`. -/
def normalizedMultiplierH0 {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) (k : ℕ) : ℝ≥0∞ :=
  letI := E.isSeparated
  letI := E.quasiCompact
  (((m + 1).factorial : ℝ≥0∞) * (multiplierH0 f (m + 1) E hφ.1.quasiPlurisubharmonic L k : ℝ≥0∞)) /
    (k : ℝ≥0∞) ^ (m + 1)

/-- **The conclusion of `thm:DXmain1`** (`T = 𝒪_X`) for `(X, L, H, φ)`:
`lim_{k → ∞} n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ` (in particular the limit exists). -/
def DXMain1Holds [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  Tendsto (normalizedMultiplierH0 f E a H hφ) atTop
    (𝓝 (iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ))

/-- **The lower bound of `thm:DXmain1`** (the half not proved here):
`vol θ_φ ≤ liminf_{k → ∞} n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ`. -/
def DXMainLowerBound [Nonempty (SchemeComplexPoint f)] {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) : Prop :=
  letI := E.isSeparated
  letI := E.quasiCompact
  letI : MeasurableSpace (SchemeComplexPoint f) := borel _
  haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
  haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ ≤
    liminf (normalizedMultiplierH0 f E a H hφ) atTop

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

include Y hY in
/-- The upper bound `limsup ≤ vol θ_φ` in the notation of this file. -/
theorem limsup_normalizedMultiplierH0_le [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    limsup (normalizedMultiplierH0 f E a H hφ) atTop ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ :=
  limsup_multiplierH0_le f E Y hY a H hφ

include Y hY in
/-- **`thm:DXmain1` follows from its lower bound** (blueprint `claude-dxmain:main-of-lower`): on
`X` carrying a smooth flag, `DXMainLowerBound` implies `DXMain1Holds`. -/
theorem dxMain1Holds_of_lowerBound [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (hlow : DXMainLowerBound f E a H hφ) : DXMain1Holds f E a H hφ :=
  tendsto_of_le_liminf_of_limsup_le hlow (limsup_normalizedMultiplierH0_le f E a H Y hY hφ)

include Y hY in
/-- **`thm:DXmain1` for currents of zero volume** (blueprint `claude-dxmain:volume-zero`): if
`vol θ_φ = 0`, then `n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ → 0 = vol θ_φ`. -/
theorem dxMain1Holds_of_iVolume_eq_zero [Nonempty (SchemeComplexPoint f)]
    {φ : SchemeComplexPoint f → EReal}
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ)
    (h0 : letI := E.isSeparated; letI := E.quasiCompact;
      letI : MeasurableSpace (SchemeComplexPoint f) := borel _;
      haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _) φ hφ = 0) :
    DXMain1Holds f E a H hφ := by
  refine dxMain1Holds_of_lowerBound f E a H Y hY hφ ?_
  unfold DXMainLowerBound
  rw [h0]
  exact zero_le

/-- With the weight `V_θ` of minimal singularities every section is a multiplier section:
`h⁰(X, L^k ⊗ 𝓘(k V_θ)) = h⁰(X, L^k)` (`eq:H0eqH0IVtheta`). -/
theorem multiplierH0_thetaPshSupremum
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) (k : ℕ) :
    letI := E.isSeparated
    letI := E.quasiCompact
    multiplierH0 f (m + 1) E hV.1.quasiPlurisubharmonic L k = h0 f L k := by
  let := E.isSeparated
  let := E.quasiCompact
  have htop : multiplierSubmodule f (m + 1) E hV.1.quasiPlurisubharmonic L k = ⊤ := by
    rw [eq_top_iff]
    intro s _
    exact SGPT.IGood.isMultiplierSection_thetaPshSupremum_all H a k s
  rw [multiplierH0, htop, finrank_top]
  rfl

include Y hY in
/-- **Source `cor:volbigL`, the inequality `≤`** (`X` projective with a smooth flag): for a
pseudo-effective line bundle `L` with a smooth metric `H`, `θ = c₁(L, H)`,
`vol L = limsup_k n! h⁰(X, L^k) / kⁿ ≤ vol θ_{V_θ} = ∫_X θ_{P_θ[V_θ]_𝓘}ⁿ`. -/
theorem volume_le_iVolume_thetaPshSupremum
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      PartialBody.nonempty_carrier (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
    SGPT.LineBundle.volume f L (m + 1) ≤
      iVolume (H.curvature a) (LocalPotentials.closedRealOneOne_hasLocalPotentials _)
        (thetaPshSupremum (H.curvature a).val) hV := by
  let := E.isSeparated
  let := E.quasiCompact
  have h := limsup_multiplierH0_le f E Y hY a H hV
  unfold SGPT.LineBundle.volume
  simp only [multiplierH0_thetaPshSupremum f E a H hV] at h
  exact h

/-- **Source `thm:DXmain1` with `T = 𝒪_X`, projective setting** (statement only): for every
integral smooth projective complex scheme `X` of positive dimension `m + 1`, every line bundle
`L` with a smooth Hermitian metric `H` and every `φ ∈ PSH(X, c₁(L, H))`,
`lim_k n! h⁰(X, L^k ⊗ 𝓘(kφ)) / kⁿ = vol θ_φ`. The upper bound is `limsup_multiplierH0_le` (for
`X` with a smooth flag); the lower bound is open. -/
def DXMain1UntwistedStatement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f) [IsIntegral X]
    (m : ℕ) [SmoothOfRelativeDimension (m + 1) f] [Nonempty (SchemeComplexPoint f)]
    (L : X.Modules) (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (φ : SchemeComplexPoint f → EReal)
    (hφ : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val φ),
    DXMain1Holds f E a H hφ

end SGPT.IGood.DXMain
