import SGPT.NAPotential.BerkovichNAPotential
import SGPT.NAPotential.BJDivisorialSpecComplex
import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Foundations.Analysis.Pending.PositiveCurrentTraceMultiplier

/-! # `Γ^An` does not depend on the Kähler index

Source `def:Gammaana` (`chapter_NApotential.tex`, Section *The transcendental setting*): for
`Γ ∈ PSH^NA(X, θ)` and `ω ∈ Kah(X)`,
`Γ^An(v) := sup_{τ ≤ Γ_max} (Γ^{θ+ω, An}_τ(v) + τ)`, and *clearly this is independent of the
choice of `ω`*.

The reason is that the components of `Γ` at two Kähler indices `ω ≤ η` are related by the
`𝓘`-projection `P_{θ+η}[•]_𝓘`, which does not change the multiplier ideals `𝓘(kφ)`, and `φ^An`
only depends on these ideals.  The workspace `𝓘`-order `sourceIOrder` is formulated chartwise;
`multiplierIdeal_eq_of_sourceIEquivalent` transports it to the germ ideals
`SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves.multiplierIdeal` used by `φ^An`.

## Main results

* `multiplierIdeal_eq_of_sourceIEquivalent`: `𝓘`-equivalent potentials have the same multiplier
  ideals `𝓘(cφ)` for every `c > 0`.
* `potentialAn_congr_of_pos`, `potentialAn_eq_of_sourceIEquivalent`,
  `potentialAn_sourceIEnvelope`: `φ^An` only depends on the `𝓘`-class of `φ`; in particular
  `(P_θ[φ]_𝓘)^An = φ^An`.
* `naComponent_potential_of_le`: the slices of the component at `η ≥ ω` are the
  `𝓘`-envelopes of those at `ω`.
* `naPotentialAnAt_independent`, `naPotentialAn_independent`: source `def:Gammaana`,
  independence of `ω`.
* `naPotentialAnDiv`: `Γ^An` on the revised divisorial set `X^Div` of the source (the
  divisorial valuations together with the trivial valuation, `sourceDivisorialSet`), with
  `naPotentialAnDiv_independent` and its restriction `naPotentialAnDiv_divisorial` to the strict
  divisorial points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.Berkovich

open Set Filter
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.PSH.VariableComplexAtlas

section Manifold

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- `𝓘`-equivalent potentials (the chartwise workspace relation `sourceIEquivalent`) have the
same multiplier ideal sheaves `𝓘(cφ) = 𝓘(cψ)` for every `c > 0`. -/
theorem multiplierIdeal_eq_of_sourceIEquivalent {φ ψ : M → EReal}
    (h : sourceIEquivalent (ofFixedModel k M) φ ψ) {c : ℝ} (hc : 0 < c) :
    multiplierIdeal (n := k) c φ = multiplierIdeal (n := k) c ψ := by
  have h1 := Pending.PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    ((sourceIOrder_iff_native h.1.1 h.1.2.1).mp h.1) hc
  have h2 := Pending.PositiveCurrentTraceMultiplier.multiplierIdeal_le_of_iOrderOnManifold
    ((sourceIOrder_iff_native h.2.1 h.2.2.1).mp h.2) hc
  ext x g
  exact ⟨h1 x g, h2 x g⟩

end Manifold

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (k : ℕ) [SmoothOfRelativeDimension k f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance anTransPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance anTransPointCharts : ChartedSpace (ComplexModel k) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f k
local instance anTransPointManifold : IsComplexManifold k (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f k

/-- `φ^An` only depends on the multiplier ideals `𝓘(mφ)` for `m > 0` (the value at `m = 0`
does not enter the limit `lim_m m⁻¹ v(𝓘(mφ))`). -/
theorem potentialAn_congr_of_pos {φ ψ : SchemeComplexPoint f → EReal}
    (h : ∀ m : ℕ, 0 < m →
      multiplierIdeal (n := k) (m : ℝ) φ = multiplierIdeal (n := k) (m : ℝ) ψ) :
    potentialAn k E φ = potentialAn k E ψ := by
  funext v
  unfold potentialAn BerkovichPoint.potentialVal
  have hev : (fun m : ℕ => v.multiplierIdealVal k E φ m / m) =ᶠ[atTop]
      (fun m : ℕ => v.multiplierIdealVal k E ψ m / m) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    unfold BerkovichPoint.multiplierIdealVal
    rw [h m hm]
  unfold limUnder
  rw [Filter.map_congr hev]

/-- `𝓘`-equivalent potentials have the same analytification. -/
theorem potentialAn_eq_of_sourceIEquivalent {φ ψ : SchemeComplexPoint f → EReal}
    (h : sourceIEquivalent (ofFixedModel k (SchemeComplexPoint f)) φ ψ) :
    potentialAn k E φ = potentialAn k E ψ :=
  potentialAn_congr_of_pos k E fun _ hm =>
    multiplierIdeal_eq_of_sourceIEquivalent h (Nat.cast_pos.mpr hm)

/-- The `𝓘`-projection does not change the analytification: `(P_α[φ]_𝓘)^An = φ^An`. -/
theorem potentialAn_sourceIEnvelope [CompactSpace (SchemeComplexPoint f)]
    [Nonempty (SchemeComplexPoint f)]
    {α : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}
    {φ : SchemeComplexPoint f → EReal}
    (hφ : (ofFixedModel k (SchemeComplexPoint f)).IsThetaPSH α φ) :
    potentialAn k E (sourceIEnvelope α φ) = potentialAn k E φ :=
  (potentialAn_eq_of_sourceIEquivalent k E (sourceIEquivalent_iEnvelope hφ)).symm

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel k (SchemeComplexPoint f))}

omit [BorelSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)] in
private theorem potential_congr_of_eq {β : AtlasClosedRealOneOneForm
      (ofFixedModel k (SchemeComplexPoint f))}
    {G H : SourcePositiveIModelTestCurve β} (hGH : G = H) (r : ℝ) (hr : r < G.val.max)
    (hs : r < H.val.max) : G.val.potential ⟨r, hr⟩ = H.val.potential ⟨r, hs⟩ := by
  subst hGH
  rfl

/-- For Kähler indices `ω ≤ η`, every slice of the component of `Γ` at `η` is the
`𝓘`-envelope `P_{θ+η}[Γ^{θ+ω}_τ]_𝓘` of the corresponding slice at `ω`. -/
theorem naComponent_potential_of_le (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm k (SchemeComplexPoint f)} (h : sourceKahlerFormLE ω η) (r : ℝ)
    (hr : r < (Γ.component ω).val.max) (hs : r < (Γ.component η).val.max) :
    (Γ.component η).val.potential ⟨r, hs⟩ =
      sourceIEnvelope (sourceNAComponentBackground θ η)
        ((Γ.component ω).val.potential ⟨r, hr⟩) := by
  have hc := Γ.compatible ω η h
  have ht : r < (sourceIModelTestCurveTransition (sourceKahlerFormRepresentative η)
      (sourceNAComponentBackground_difference θ h) (Γ.component ω)).val.max := by
    rwa [sourceIModelTestCurveTransition_max]
  rw [← potential_congr_of_eq k hc r ht hs]
  exact sourceIModelTestCurveTransition_potential _ _ _ r hr ht

/-- For Kähler indices `ω ≤ η`, corresponding slices of the two components are
`𝓘`-equivalent. -/
theorem naComponent_potential_iEquivalent_of_le (Γ : SourceNAPotential θ)
    {ω η : SourceKahlerForm k (SchemeComplexPoint f)} (h : sourceKahlerFormLE ω η) (r : ℝ)
    (hr : r < (Γ.component ω).val.max) (hs : r < (Γ.component η).val.max) :
    sourceIEquivalent (ofFixedModel k (SchemeComplexPoint f))
      ((Γ.component ω).val.potential ⟨r, hr⟩) ((Γ.component η).val.potential ⟨r, hs⟩) := by
  rw [naComponent_potential_of_le k Γ h r hr hs]
  exact sourceIEquivalent_iEnvelope (sourceThetaPSH_of_semipositive_difference
    (sourceNAComponentBackground_difference θ h) ((Γ.component ω).val.thetaPSH ⟨r, hr⟩))

/-- The analytification of corresponding slices of two components of `Γ` agree. -/
theorem potentialAn_naComponent_potential (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm k (SchemeComplexPoint f)) (r : ℝ)
    (hr : r < (Γ.component ω).val.max) (hs : r < (Γ.component η).val.max) :
    potentialAn k E ((Γ.component ω).val.potential ⟨r, hr⟩) =
      potentialAn k E ((Γ.component η).val.potential ⟨r, hs⟩) := by
  let ζ := sourceKahlerFormCommonUpper ω η
  have hζ : r < (Γ.component ζ).val.max := by rwa [Γ.component_max_eq ζ ω]
  rw [potentialAn_eq_of_sourceIEquivalent k E (naComponent_potential_iEquivalent_of_le k Γ
      (sourceKahlerFormLE_commonUpper_left ω η) r hr hζ),
    potentialAn_eq_of_sourceIEquivalent k E (naComponent_potential_iEquivalent_of_le k Γ
      (sourceKahlerFormLE_commonUpper_right ω η) r hs hζ)]

/-- Source `def:Gammaana`: `Γ^An(v) = sup_{τ < Γ_max} (Γ^{θ+ω, An}_τ(v) + τ)` is independent of
the Kähler form `ω`, at every point `v ∈ X^An`. -/
theorem naPotentialAnAt_independent (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm k (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt k E Γ ω v = naPotentialAnAt k E Γ η v := by
  have hmax := Γ.component_max_eq ω η
  unfold naPotentialAnAt
  apply le_antisymm
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hs : r < (Γ.component η).val.max := by
      rw [← hmax]
      exact hr
    rw [potentialAn_naComponent_potential k E Γ ω η r hr hs]
    exact le_iSup (fun τ : Iio (Γ.component η).val.max =>
      potentialAn k E ((Γ.component η).val.potential τ) v + ((τ : ℝ) : EReal)) ⟨r, hs⟩
  · apply iSup_le
    rintro ⟨r, hr⟩
    have hs : r < (Γ.component ω).val.max := by
      rw [hmax]
      exact hr
    rw [potentialAn_naComponent_potential k E Γ η ω r hr hs]
    exact le_iSup (fun τ : Iio (Γ.component ω).val.max =>
      potentialAn k E ((Γ.component ω).val.potential τ) v + ((τ : ℝ) : EReal)) ⟨r, hs⟩

/-- Source `def:Gammaana`: the function `Γ^An : X^Div → [-∞, ∞)` (strict divisorial points)
does not depend on the Kähler form used to compute it. -/
theorem naPotentialAn_independent (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm k (SchemeComplexPoint f)) :
    naPotentialAn k E Γ ω = naPotentialAn k E Γ η :=
  funext fun v => naPotentialAnAt_independent k E Γ ω η v.1

/-- Source `def:Gammaana` on the revised source domain `X^Div` (the divisorial valuations
`t ord_E` together with the trivial valuation, `sourceDivisorialSet`):
`Γ^An(v) = sup_{τ < Γ_max} (Γ^{θ+ω, An}_τ(v) + τ)`. -/
def naPotentialAnDiv [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) : sourceDivisorialSet f → EReal :=
  fun v => naPotentialAnAt k E Γ ω v.1

/-- The revised `Γ^An` is independent of the Kähler form. -/
theorem naPotentialAnDiv_independent [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω η : SourceKahlerForm k (SchemeComplexPoint f)) :
    naPotentialAnDiv k E Γ ω = naPotentialAnDiv k E Γ η :=
  funext fun v => naPotentialAnAt_independent k E Γ ω η v.1

/-- On the strict divisorial points the revised `Γ^An` is the strict one. -/
theorem naPotentialAnDiv_divisorial [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) (v : divisorialSet f) :
    naPotentialAnDiv k E Γ ω ⟨v.1, divisorialSet_subset_sourceDivisorialSet f v.2⟩ =
      naPotentialAn k E Γ ω v := rfl

/-- The value of the revised `Γ^An` at the trivial valuation. -/
theorem naPotentialAnDiv_trivial [IrreducibleSpace X] (Γ : SourceNAPotential θ)
    (ω : SourceKahlerForm k (SchemeComplexPoint f)) :
    naPotentialAnDiv k E Γ ω ⟨BerkovichPoint.trivial f, trivial_mem_sourceDivisorialSet f⟩ =
      ⨆ τ : Iio (Γ.component ω).val.max,
        potentialAn k E ((Γ.component ω).val.potential τ) (BerkovichPoint.trivial f) +
          ((τ : ℝ) : EReal) := rfl

end SGPT.NAPotential.Berkovich

end
