import SGPT.NAPotential.NAGagaCoeffIdeal
import SGPT.NAPotential.NAGagaLimit
import SGPT.NAPotential.DivDict2Endpoint
import SGPT.NAPotential.AnTransIndependence
import SGPT.NAPotential.GAGAMult2Limit

/-!
# `prop:psiandPhi`: `Γ^An(v) = -σ(v)(Ψ)`

Source: `chapter_NApotential.tex`, `prop:psiandPhi` (lines 1008--1012): *Let
`Γ ∈ PSH^NA(X, θ)_{>0}` with `Γ_max ≤ 0` and let `Ψ` be the complexification of `Γ^*`. Then
`Γ^An(v) = -σ(v)(Ψ)` for all `v ∈ X^Div`.* Blueprint `claude-na-gaga.tex`, node
`claude-na-gaga:psiandPhi`.

## Formal setting

`X` is a smooth projective complex scheme of dimension `m + 1` with a closed projective embedding,
`X(ℂ) = SchemeComplexPoint f` its complex manifold, `X^An = BerkovichPoint f` and
`X^Div = divisorialSet f`, as for `def:Gammaana` (`naPotentialAnAt`, `naPotentialAn`).
`PSH^NA(X, θ)_{>0}` is `SourcePositiveIModelTestCurve θ`, embedded in `PSH^NA(X, θ)` by
`sourcePositiveTestCurveToNA` (`prop:NAposNAemb`). `Ψ` is any function on `X(ℂ) × Δ` equal to
`Γ^*_{-log|δ|²}(x)` for `δ ≠ 0` (`IsComplexificationOf`), so in particular its unique quasi-psh
extension across `X × {0}`.

**The value `σ(v)(Ψ)`.** As in `def:NApotential:L975` (`v(φ) = lim_k k⁻¹ v(𝓘(kφ))`) and in the
proof of `prop:PhiinducePSH`, `σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))`, where `σ(v)` is evaluated by
`eq:va` on the algebraic model of `𝓘(kΨ)`: by `lma:istab` (the `S¹`-invariance of `Ψ`) and
`lma:GAGA`, `𝓘(kΨ) = ∑_i 𝔞_{k,i} t^i` with the coefficient ideals `𝔞_{k,i}` (`coeffIdeal`) and,
by `eq:Gext`, `σ(v)(∑_i 𝔞_{k,i} t^i) = min_i (v(𝔞_{k,i}) + i)` (`BJModel.isGLB_gaussVal_flagStalk`
for flag ideals). Here `v(𝔞_{k,i})` is `v` on the algebraic model `algebraization 𝔞_{k,i}`
(as `multiplierIdealVal`); this is `gaussMultiplierVal`, and `gaussPotentialVal` is the limit.

## Main results

* `source_psiandPhi`: for every `v ∈ X^An` (not only `X^Div`) the limit defining `σ(v)(Ψ)`
  exists and `Γ^An(v) = -σ(v)(Ψ)`; `source_psiandPhi_div`: the statement on `X^Div`.

The proof is a direct multiplier-ideal computation (`NAGagaCoeffIdeal`):
`𝓘(kΓ_τ) ⊆ 𝔞_{k,i}` for `i + kτ > -1`, `𝔞_{k,i} ⊆ 𝓘(kΓ_{-(i+1)/k})`, `𝔞_{k,i} = 0` for
`i + 1 + kΓ_max ≤ 0`; hence `k⁻¹ σ(v)(𝓘(kΨ))` is squeezed between
`inf_τ (k⁻¹ v(𝓘(kΓ_τ)) - τ) - 1/k` and `inf_τ (k⁻¹ v(𝓘(kΓ_τ)) - τ)`, and `tendsto_div_of_bounds`
exchanges the limit with the infimum. (The source argues with Lelong numbers along the divisor
of `σ(v)` and `cor:supsLelong`; the multiplier-ideal route avoids realizing `σ(v)` analytically
on `X × Δ`.)
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.NAGaga

open Set Filter MeasureTheory
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open scoped ProductComplexManifold

/-- The coercion `[0, ∞] → [-∞, ∞]` commutes with infima. -/
theorem coe_ennreal_iInf {ι : Sort*} (u : ι → ℝ≥0∞) :
    ((⨅ i, u i : ℝ≥0∞) : EReal) = ⨅ i, (u i : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.coe_ennreal_le_coe_ennreal_iff.mpr (iInf_le _ i)
  · have h0 : (0 : EReal) ≤ ⨅ i, (u i : EReal) := le_iInf fun i => EReal.coe_ennreal_nonneg _
    rw [← EReal.coe_toENNReal h0]
    refine EReal.coe_ennreal_le_coe_ennreal_iff.mpr (le_iInf fun i => ?_)
    calc (⨅ i, (u i : EReal)).toENNReal ≤ (u i : EReal).toENNReal :=
          EReal.toENNReal_le_toENNReal (iInf_le _ i)
      _ = u i := EReal.toENNReal_coe

section Scheme

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance naGagaPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance naGagaPointCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance naGagaPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

variable (m) in
/-- **`σ(v)(𝓘(kΨ)) = min_i (v(𝔞_{k,i}) + i)`** (`eq:va`, `eq:Gext`) on the algebraic model
`∑_i 𝔞_{k,i} t^i` of `𝓘(kΨ)` (`lma:istab`, `lma:GAGA`, `eq:ImPhiexp`). -/
def gaussMultiplierVal (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal)
    (k : ℕ) : ℝ≥0∞ :=
  ⨅ i : ℕ, v.idealVal (algebraization f (m + 1) E (coeffIdeal (n := m + 1) Ψ k i)) + (i : ℝ≥0∞)

variable (m) in
/-- **`σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))`** (as `v(φ)` in `def:NApotential:L975`). -/
def gaussPotentialVal (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal) :
    ℝ≥0∞ :=
  limUnder atTop fun k : ℕ => gaussMultiplierVal m E v Ψ k / k

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel (m + 1) (SchemeComplexPoint f))}

/-- The algebraic model of `𝔞_{k,i}` is `0` when `i + 1 + kΓ_max ≤ 0`. -/
theorem algebraization_coeffIdeal_eq_bot {Γ : SourceTestCurvePredata θ}
    {Ψ : SchemeComplexPoint f × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k i : ℕ}
    (hki : (i : ℝ) + 1 + k * Γ.max ≤ 0) :
    algebraization f (m + 1) E (coeffIdeal (n := m + 1) Ψ k i) = ⊥ := by
  apply le_bot_iff.mp
  refine (algebraization_mono f (m + 1) E ?_).trans
    (algebraization_analytificationIdeal_le f (m + 1) E ⊥)
  intro x g hg
  refine ⟨hg.1, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  filter_upwards [eventuallyEq_zero_of_coeffIdeal hΨ hki hg] with y hy
  simpa using hy

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- `Γ^An` of an element of `PSH^NA(X, θ)_{>0}`, through its own slices:
`Γ^An(v) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)` (the `𝓘`-projections defining the components do not
change the analytification). -/
theorem naPotentialAnAt_sourcePositiveTestCurveToNA (Γ : SourcePositiveIModelTestCurve θ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt (m + 1) E (sourcePositiveTestCurveToNA Γ) ω v =
      ⨆ τ : Iio Γ.val.max, potentialAn (m + 1) E (Γ.val.potential τ) v + ((τ : ℝ) : EReal) := by
  have hmaxeq : ((sourcePositiveTestCurveToNA Γ).component ω).val.max = Γ.val.max :=
    sourcePositiveTestCurveToNA_max Γ ω
  have hslice : ∀ (r : ℝ) (hr : r < Γ.val.max)
      (hs : r < ((sourcePositiveTestCurveToNA Γ).component ω).val.max),
      potentialAn (m + 1) E (((sourcePositiveTestCurveToNA Γ).component ω).val.potential ⟨r, hs⟩) =
        potentialAn (m + 1) E (Γ.val.potential ⟨r, hr⟩) := by
    intro r hr hs
    rw [sourcePositiveTestCurveToNA_potential Γ ω r hr hs]
    exact potentialAn_sourceIEnvelope (m + 1) E
      (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ ω)
        (Γ.val.thetaPSH ⟨r, hr⟩))
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have hr : τ.1 < Γ.val.max := hmaxeq ▸ τ.2
    rw [show τ = ⟨τ.1, τ.2⟩ from rfl, hslice τ.1 hr τ.2]
    exact le_iSup (fun σ : Iio Γ.val.max =>
      potentialAn (m + 1) E (Γ.val.potential σ) v + ((σ : ℝ) : EReal)) ⟨τ.1, hr⟩
  · refine iSup_le fun τ => ?_
    have hs : τ.1 < ((sourcePositiveTestCurveToNA Γ).component ω).val.max := hmaxeq.symm ▸ τ.2
    have h := le_naPotentialAnAt (m + 1) E (sourcePositiveTestCurveToNA Γ) ω v ⟨τ.1, hs⟩
    rw [hslice τ.1 τ.2 hs] at h
    exact h

/-- **`prop:psiandPhi`** (at every point of `X^An`). Let `Γ ∈ PSH^NA(X, θ)_{>0}` with
`Γ_max ≤ 0` and let `Ψ` be the complexification of `Γ^*` (any extension across `X × {0}`). For
every `v ∈ X^An` the limit `σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))` exists and
`Γ^An(v) = -σ(v)(Ψ)`. -/
theorem source_psiandPhi (Γ : SourcePositiveIModelTestCurve θ) (hmax : Γ.val.max ≤ 0)
    {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ.val.toSourceTestCurvePredata Ψ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierVal m E v Ψ k / k) atTop
        (𝓝 (gaussPotentialVal m E v Ψ)) ∧
      naPotentialAnAt (m + 1) E (sourcePositiveTestCurveToNA Γ) ω v =
        -((gaussPotentialVal m E v Ψ : ℝ≥0∞) : EReal) := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set G := Γ.val.toSourceTestCurvePredata with hG
  set omega := sourceKahlerFormRepresentative ω with homega
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (m + 1)
  set a : ℕ → Iio Γ.val.max → ℝ≥0∞ := fun k τ =>
    v.multiplierIdealVal (m + 1) E (Γ.val.potential τ) k with ha
  set p : Iio Γ.val.max → ℝ≥0∞ := fun τ => v.potentialVal (m + 1) E (Γ.val.potential τ) with hp
  set b : ℕ → ℝ≥0∞ := fun k => gaussMultiplierVal m E v Ψ k with hb
  have hpsh : ∀ τ : Iio Γ.val.max,
      IsThetaPshPotential (atlasClosedFormToNative θ).val (Γ.val.potential τ) :=
    fun τ => G.native_thetaPSH τ
  have hlim : ∀ τ, Tendsto (fun k : ℕ => a k τ / k) atTop (𝓝 (p τ)) := fun τ =>
    BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic (m + 1) E hA (hpsh τ) v
  have hle : ∀ k : ℕ, 0 < k → ∀ τ, a k τ / k ≤ p τ := by
    intro k hk τ
    have h := BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic (m + 1) E hA
      (hpsh τ) v
    change a k τ / k ≤ v.potentialVal (m + 1) E (Γ.val.potential τ)
    rw [h]
    exact le_iSup₂ (f := fun k (_ : 0 < k) => a k τ / k) k hk
  have hmono : ∀ k : ℕ, 0 < k → ∀ τ τ' : Iio Γ.val.max, τ ≤ τ' → a k τ ≤ a k τ' := by
    intro k hk τ τ' h
    exact v.idealVal_antitone (algebraization_mono f (m + 1) E
      (multiplierIdeal_mono (hpsh τ).1 (fun x => G.antitone x h) (Nat.cast_pos.mpr hk)))
  have hup : ∀ k : ℕ, 0 < k → ∀ τ : Iio Γ.val.max,
      b k / k ≤ a k τ / k + ENNReal.ofReal (-τ.1) := by
    intro k hk τ
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hτneg : τ.1 < 0 := lt_of_lt_of_le τ.2 hmax
    have hnn : 0 ≤ (k : ℝ) * (-τ.1) := mul_nonneg hkpos.le (by linarith)
    set i := ⌊(k : ℝ) * (-τ.1)⌋₊ with hi
    have hi1 : -1 < (i : ℝ) + k * τ.1 := by
      have := Nat.lt_floor_add_one ((k : ℝ) * (-τ.1))
      linarith
    have hi2 : (i : ℝ) ≤ k * (-τ.1) := Nat.floor_le hnn
    have hbi : b k ≤ a k τ + (i : ℝ≥0∞) := by
      refine (iInf_le _ i).trans (add_le_add (v.idealVal_antitone
        (algebraization_mono f (m + 1) E ?_)) le_rfl)
      intro x g hg
      exact coeffIdeal_of_multiplierIdeal omega hΨ hk τ hi1 hg
    have hik : (i : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) * (-τ.1)) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hi2
    calc b k / k ≤ (a k τ + ENNReal.ofReal ((k : ℝ) * (-τ.1))) / k :=
          ENNReal.div_le_div_right (hbi.trans (add_le_add le_rfl hik)) _
      _ = a k τ / k + ENNReal.ofReal (-τ.1) := by
        rw [ENNReal.add_div, ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast,
          ← (ENNReal.eq_div_iff (Nat.cast_ne_zero.mpr hk.ne') (ENNReal.natCast_ne_top k)).mpr rfl]
  have hlow : ∀ k : ℕ, 0 < k → ∀ c : ℝ≥0∞,
      (∀ τ : Iio Γ.val.max, c ≤ a k τ / k + ENNReal.ofReal (-τ.1)) → c ≤ b k / k + 1 / k := by
    intro k hk c hc
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have hktop : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [← ENNReal.add_div, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
    change c * k ≤ (⨅ i : ℕ, v.idealVal (algebraization f (m + 1) E
      (coeffIdeal (n := m + 1) Ψ k i)) + (i : ℝ≥0∞)) + 1
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    by_cases hki : (i : ℝ) + 1 + k * Γ.val.max ≤ 0
    · rw [algebraization_coeffIdeal_eq_bot E hΨ hki, BJModel.idealVal_bot, top_add, top_add]
      exact le_top
    · have hτi : -((i : ℝ) + 1) / k < Γ.val.max := by
        rw [div_lt_iff₀ hkpos]
        rw [not_le] at hki
        linarith
      have hT : a k ⟨_, hτi⟩ ≤
          v.idealVal (algebraization f (m + 1) E (coeffIdeal (n := m + 1) Ψ k i)) :=
        v.idealVal_antitone (algebraization_mono f (m + 1) E
          (fun x g hg => multiplierIdeal_of_coeffIdeal hmax hΨ hk hτi hg))
      have hq : ENNReal.ofReal (-(-((i : ℝ) + 1) / k)) * k = (i : ℝ≥0∞) + 1 := by
        rw [neg_div, neg_neg, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ hkpos.ne', ENNReal.ofReal_add (by positivity) zero_le_one,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      calc c * k ≤ (a k ⟨_, hτi⟩ / k + ENNReal.ofReal (-(-((i : ℝ) + 1) / k))) * k :=
            mul_le_mul_of_nonneg_right (hc ⟨_, hτi⟩) bot_le
        _ = a k ⟨_, hτi⟩ + ((i : ℝ≥0∞) + 1) := by
            rw [add_mul, ENNReal.div_mul_cancel hk0 hktop, hq]
        _ ≤ v.idealVal (algebraization f (m + 1) E (coeffIdeal (n := m + 1) Ψ k i)) +
              (i : ℝ≥0∞) + 1 := by
            rw [add_assoc]; exact add_le_add hT le_rfl
  have hT := tendsto_div_of_bounds hmax a p b hmono hlim hle hup hlow
  have hval : gaussPotentialVal m E v Ψ = ⨅ τ : Iio Γ.val.max, p τ + ENNReal.ofReal (-τ.1) :=
    hT.limUnder_eq
  refine ⟨by rw [hval]; exact hT, ?_⟩
  rw [naPotentialAnAt_sourcePositiveTestCurveToNA E Γ ω v, hval, coe_ennreal_iInf]
  have hterm : ∀ τ : Iio Γ.val.max, potentialAn (m + 1) E (Γ.val.potential τ) v + ((τ : ℝ) : EReal) =
      -((p τ + ENNReal.ofReal (-τ.1) : ℝ≥0∞) : EReal) := by
    intro τ
    have hτneg : τ.1 < 0 := lt_of_lt_of_le τ.2 hmax
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left (by linarith),
      EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot _)) (Or.inr (EReal.coe_ne_bot _)),
      sub_eq_add_neg, ← EReal.coe_neg, neg_neg]
    rfl
  simp_rw [hterm]
  apply le_antisymm
  · exact iSup_le fun τ => EReal.neg_le_neg_iff.mpr (iInf_le _ τ)
  · rw [EReal.neg_le]
    refine le_iInf fun τ => ?_
    rw [EReal.neg_le]
    exact le_iSup (fun σ : Iio Γ.val.max => -((p σ + ENNReal.ofReal (-σ.1) : ℝ≥0∞) : EReal)) τ

/-- **`prop:psiandPhi`** as printed: `Γ^An(v) = -σ(v)(Ψ)` for all `v ∈ X^Div`. -/
theorem source_psiandPhi_div (Γ : SourcePositiveIModelTestCurve θ) (hmax : Γ.val.max ≤ 0)
    {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ.val.toSourceTestCurvePredata Ψ)
    (ω : SourceKahlerForm (m + 1) (SchemeComplexPoint f)) (v : divisorialSet f) :
    naPotentialAn (m + 1) E (sourcePositiveTestCurveToNA Γ) ω v =
      -((gaussPotentialVal m E v.1 Ψ : ℝ≥0∞) : EReal) :=
  (source_psiandPhi E Γ hmax hΨ ω v.1).2

end Scheme

end SGPT.NAPotential.NAGaga
