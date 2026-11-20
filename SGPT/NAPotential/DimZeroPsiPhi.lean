import SGPT.NAPotential.NAGagaPsiPhi
import SGPT.NAPotential.QwNANonTrivRestZero

/-!
# `prop:psiandPhi` in every dimension, including dimension zero

Source: `chapter_NApotential.tex`, `prop:psiandPhi` (lines 1008--1012): *Let
`Γ ∈ PSH^NA(X, θ)_{>0}` with `Γ_max ≤ 0` and let `Ψ` be the complexification of `Γ^*`. Then
`Γ^An(v) = -σ(v)(Ψ)` for all `v ∈ X^Div`.* The chapter's `X` is any connected projective
manifold; dimension `0` is not excluded. Blueprint `claude-dim-zero.tex`, node
`claude-dim-zero:psiandPhi`.

Lane NA-GAGA proved the statement (`SGPT.NAPotential.NAGaga.source_psiandPhi`) for `X` smooth of
relative dimension `m + 1 ≥ 1`; its value `σ(v)(Ψ)` (`NAGaga.gaussPotentialVal`) is only defined
in positive dimension. Here:

* `gaussMultiplierValDim`, `gaussPotentialValDim`: the same values
  `σ(v)(𝓘(kΨ)) = min_i (v(𝔞_{k,i}) + i)` and `σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))` for `X` of any
  relative dimension `n`; in dimension `m + 1` they are *definitionally* NA-GAGA's values
  (`gaussMultiplierValDim_succ`, `gaussPotentialValDim_succ`).
* `gaussPotentialValDim_of_isComplexificationOf`: for every test-curve predatum `Γ` with
  `Γ_max ≤ 0` and every `v ∈ X^An`, the limit defining `σ(v)(Ψ)` exists and
  `-σ(v)(Ψ) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`, in every dimension. The multiplier-ideal squeeze of
  NA-GAGA (`NAGaga.coeffIdeal_of_multiplierIdeal`, `NAGaga.multiplierIdeal_of_coeffIdeal`,
  `NAGaga.eventuallyEq_zero_of_coeffIdeal`, `NAGaga.tendsto_div_of_bounds`) is already stated for
  manifolds of any dimension; only its assembly was written for dimension `m + 1`.
* **`source_psiandPhi_dim`**, `source_psiandPhi_div_dim`: `prop:psiandPhi` for `X` of every
  relative dimension `n` (on `X^An` and, as printed, on `X^Div`).
* **`source_psiandPhi_dim_zero`**: the dimension-zero case made explicit: `X(ℂ)` is a point,
  `Γ^An ≡ Γ_max` (`NANS.naPotentialAnAt_eq_of_dim_zero`) and so `σ(v)(Ψ) = -Γ_max` for every
  `v ∈ X^An`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.DimZero

open Set Filter MeasureTheory
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.NAGaga (unitDisc coeffIdeal IsComplexificationOf)
open scoped ProductComplexManifold

section Scheme

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance dimZeroPsiPhiPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroPsiPhiPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance dimZeroPsiPhiPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- **`σ(v)(𝓘(kΨ)) = min_i (v(𝔞_{k,i}) + i)`** (`eq:va`, `eq:Gext`) on the algebraic model
`∑_i 𝔞_{k,i} t^i` of `𝓘(kΨ)` (`eq:ImPhiexp`), for `X` of relative dimension `n` (any `n`,
including `0`). For `n = m + 1` this is `NAGaga.gaussMultiplierVal` (`gaussMultiplierValDim_succ`). -/
def gaussMultiplierValDim (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal)
    (k : ℕ) : ℝ≥0∞ :=
  ⨅ i : ℕ, v.idealVal (algebraization f n E (coeffIdeal (n := n) Ψ k i)) + (i : ℝ≥0∞)

/-- **`σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))`** (as `v(φ)` in `def:NApotential:L975`), for `X` of relative
dimension `n` (any `n`, including `0`). For `n = m + 1` this is `NAGaga.gaussPotentialVal`
(`gaussPotentialValDim_succ`). -/
def gaussPotentialValDim (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal) :
    ℝ≥0∞ :=
  limUnder atTop fun k : ℕ => gaussMultiplierValDim n E v Ψ k / k

/-- In positive dimension `m + 1` the value is NA-GAGA's `σ(v)(𝓘(kΨ))`. -/
theorem gaussMultiplierValDim_succ (m : ℕ) [SmoothOfRelativeDimension (m + 1) f]
    (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal) (k : ℕ) :
    gaussMultiplierValDim (m + 1) E v Ψ k = NAGaga.gaussMultiplierVal m E v Ψ k :=
  rfl

/-- In positive dimension `m + 1` the value is NA-GAGA's `σ(v)(Ψ)`. -/
theorem gaussPotentialValDim_succ (m : ℕ) [SmoothOfRelativeDimension (m + 1) f]
    (v : BerkovichPoint f) (Ψ : SchemeComplexPoint f × unitDisc → EReal) :
    gaussPotentialValDim (m + 1) E v Ψ = NAGaga.gaussPotentialVal m E v Ψ :=
  rfl

variable {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}

/-- The algebraic model of `𝔞_{k,i}` is `0` when `i + 1 + kΓ_max ≤ 0` (any dimension). -/
theorem algebraization_coeffIdeal_eq_bot_dim {Γ : SourceTestCurvePredata θ}
    {Ψ : SchemeComplexPoint f × unitDisc → EReal} (hΨ : IsComplexificationOf Γ Ψ) {k i : ℕ}
    (hki : (i : ℝ) + 1 + k * Γ.max ≤ 0) :
    algebraization f n E (coeffIdeal (n := n) Ψ k i) = ⊥ := by
  apply le_bot_iff.mp
  refine (algebraization_mono f n E ?_).trans (algebraization_analytificationIdeal_le f n E ⊥)
  intro x g hg
  refine ⟨hg.1, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
  filter_upwards [NAGaga.eventuallyEq_zero_of_coeffIdeal hΨ hki hg] with y hy
  simpa using hy

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]

/-- **The squeeze of `prop:psiandPhi` for a test-curve predatum, in every dimension.** Let `Γ` be a
test-curve predatum with `Γ_max ≤ 0` and `Ψ` the complexification of `Γ^*` on `X × Δ^*`. For every
`v ∈ X^An` the limit `σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))` exists and
`-σ(v)(Ψ) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`. -/
theorem gaussPotentialValDim_of_isComplexificationOf (omega : KahlerBackground n (SchemeComplexPoint f))
    (Γ : SourceTestCurvePredata θ) (hmax : Γ.max ≤ 0) {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ Ψ) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierValDim n E v Ψ k / k) atTop
        (𝓝 (gaussPotentialValDim n E v Ψ)) ∧
      -((gaussPotentialValDim n E v Ψ : ℝ≥0∞) : EReal) =
        ⨆ τ : Iio Γ.max, potentialAn n E (Γ.potential τ) v + ((τ : ℝ) : EReal) := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E n
  set a : ℕ → Iio Γ.max → ℝ≥0∞ := fun k τ =>
    v.multiplierIdealVal n E (Γ.potential τ) k with ha
  set p : Iio Γ.max → ℝ≥0∞ := fun τ => v.potentialVal n E (Γ.potential τ) with hp
  set b : ℕ → ℝ≥0∞ := fun k => gaussMultiplierValDim n E v Ψ k with hb
  have hpsh : ∀ τ : Iio Γ.max,
      IsThetaPshPotential (atlasClosedFormToNative θ).val (Γ.potential τ) :=
    fun τ => Γ.native_thetaPSH τ
  have hlim : ∀ τ, Tendsto (fun k : ℕ => a k τ / k) atTop (𝓝 (p τ)) := fun τ =>
    BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic n E hA (hpsh τ) v
  have hle : ∀ k : ℕ, 0 < k → ∀ τ, a k τ / k ≤ p τ := by
    intro k hk τ
    have h := BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic n E hA (hpsh τ) v
    change a k τ / k ≤ v.potentialVal n E (Γ.potential τ)
    rw [h]
    exact le_iSup₂ (f := fun k (_ : 0 < k) => a k τ / k) k hk
  have hmono : ∀ k : ℕ, 0 < k → ∀ τ τ' : Iio Γ.max, τ ≤ τ' → a k τ ≤ a k τ' := by
    intro k hk τ τ' h
    exact v.idealVal_antitone (algebraization_mono f n E
      (multiplierIdeal_mono (hpsh τ).1 (fun x => Γ.antitone x h) (Nat.cast_pos.mpr hk)))
  have hup : ∀ k : ℕ, 0 < k → ∀ τ : Iio Γ.max,
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
        (algebraization_mono f n E ?_)) le_rfl)
      intro x g hg
      exact NAGaga.coeffIdeal_of_multiplierIdeal omega hΨ hk τ hi1 hg
    have hik : (i : ℝ≥0∞) ≤ ENNReal.ofReal ((k : ℝ) * (-τ.1)) := by
      rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hi2
    calc b k / k ≤ (a k τ + ENNReal.ofReal ((k : ℝ) * (-τ.1))) / k :=
          ENNReal.div_le_div_right (hbi.trans (add_le_add le_rfl hik)) _
      _ = a k τ / k + ENNReal.ofReal (-τ.1) := by
        rw [ENNReal.add_div, ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast,
          ← (ENNReal.eq_div_iff (Nat.cast_ne_zero.mpr hk.ne') (ENNReal.natCast_ne_top k)).mpr rfl]
  have hlow : ∀ k : ℕ, 0 < k → ∀ c : ℝ≥0∞,
      (∀ τ : Iio Γ.max, c ≤ a k τ / k + ENNReal.ofReal (-τ.1)) → c ≤ b k / k + 1 / k := by
    intro k hk c hc
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have hktop : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [← ENNReal.add_div, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
    change c * k ≤ (⨅ i : ℕ, v.idealVal (algebraization f n E
      (coeffIdeal (n := n) Ψ k i)) + (i : ℝ≥0∞)) + 1
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    by_cases hki : (i : ℝ) + 1 + k * Γ.max ≤ 0
    · rw [algebraization_coeffIdeal_eq_bot_dim n E hΨ hki, BJModel.idealVal_bot, top_add,
        top_add]
      exact le_top
    · have hτi : -((i : ℝ) + 1) / k < Γ.max := by
        rw [div_lt_iff₀ hkpos]
        rw [not_le] at hki
        linarith
      have hT : a k ⟨_, hτi⟩ ≤
          v.idealVal (algebraization f n E (coeffIdeal (n := n) Ψ k i)) :=
        v.idealVal_antitone (algebraization_mono f n E
          (fun x g hg => NAGaga.multiplierIdeal_of_coeffIdeal hmax hΨ hk hτi hg))
      have hq : ENNReal.ofReal (-(-((i : ℝ) + 1) / k)) * k = (i : ℝ≥0∞) + 1 := by
        rw [neg_div, neg_neg, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ hkpos.ne', ENNReal.ofReal_add (by positivity) zero_le_one,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      calc c * k ≤ (a k ⟨_, hτi⟩ / k + ENNReal.ofReal (-(-((i : ℝ) + 1) / k))) * k :=
            mul_le_mul_of_nonneg_right (hc ⟨_, hτi⟩) bot_le
        _ = a k ⟨_, hτi⟩ + ((i : ℝ≥0∞) + 1) := by
            rw [add_mul, ENNReal.div_mul_cancel hk0 hktop, hq]
        _ ≤ v.idealVal (algebraization f n E (coeffIdeal (n := n) Ψ k i)) +
              (i : ℝ≥0∞) + 1 := by
            rw [add_assoc]; exact add_le_add hT le_rfl
  have hT := NAGaga.tendsto_div_of_bounds hmax a p b hmono hlim hle hup hlow
  have hval : gaussPotentialValDim n E v Ψ = ⨅ τ : Iio Γ.max, p τ + ENNReal.ofReal (-τ.1) :=
    hT.limUnder_eq
  refine ⟨by rw [hval]; exact hT, ?_⟩
  rw [hval, NAGaga.coe_ennreal_iInf]
  have hterm : ∀ τ : Iio Γ.max, potentialAn n E (Γ.potential τ) v + ((τ : ℝ) : EReal) =
      -((p τ + ENNReal.ofReal (-τ.1) : ℝ≥0∞) : EReal) := by
    intro τ
    have hτneg : τ.1 < 0 := lt_of_lt_of_le τ.2 hmax
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left (by linarith),
      EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot _)) (Or.inr (EReal.coe_ne_bot _)),
      sub_eq_add_neg, ← EReal.coe_neg, neg_neg]
    rfl
  simp_rw [hterm]
  apply le_antisymm
  · rw [EReal.neg_le]
    refine le_iInf fun τ => ?_
    rw [EReal.neg_le]
    exact le_iSup (fun σ : Iio Γ.max => -((p σ + ENNReal.ofReal (-σ.1) : ℝ≥0∞) : EReal)) τ
  · exact iSup_le fun τ => EReal.neg_le_neg_iff.mpr (iInf_le _ τ)

/-- `Γ^An` of an element of `PSH^NA(X, θ)_{>0}` through its own slices, in every dimension:
`Γ^An(v) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`. -/
theorem naPotentialAnAt_sourcePositiveTestCurveToNA_dim (Γ : SourcePositiveIModelTestCurve θ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    naPotentialAnAt n E (sourcePositiveTestCurveToNA Γ) ω v =
      ⨆ τ : Iio Γ.val.max, potentialAn n E (Γ.val.potential τ) v + ((τ : ℝ) : EReal) := by
  have hmaxeq : ((sourcePositiveTestCurveToNA Γ).component ω).val.max = Γ.val.max :=
    sourcePositiveTestCurveToNA_max Γ ω
  have hslice : ∀ (r : ℝ) (hr : r < Γ.val.max)
      (hs : r < ((sourcePositiveTestCurveToNA Γ).component ω).val.max),
      potentialAn n E (((sourcePositiveTestCurveToNA Γ).component ω).val.potential ⟨r, hs⟩) =
        potentialAn n E (Γ.val.potential ⟨r, hr⟩) := by
    intro r hr hs
    rw [sourcePositiveTestCurveToNA_potential Γ ω r hr hs]
    exact potentialAn_sourceIEnvelope n E
      (sourceThetaPSH_of_semipositive_difference (sourceNAComponentBackground_positive θ ω)
        (Γ.val.thetaPSH ⟨r, hr⟩))
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have hr : τ.1 < Γ.val.max := hmaxeq ▸ τ.2
    rw [show τ = ⟨τ.1, τ.2⟩ from rfl, hslice τ.1 hr τ.2]
    exact le_iSup (fun σ : Iio Γ.val.max =>
      potentialAn n E (Γ.val.potential σ) v + ((σ : ℝ) : EReal)) ⟨τ.1, hr⟩
  · refine iSup_le fun τ => ?_
    have hs : τ.1 < ((sourcePositiveTestCurveToNA Γ).component ω).val.max := hmaxeq.symm ▸ τ.2
    have h := le_naPotentialAnAt n E (sourcePositiveTestCurveToNA Γ) ω v ⟨τ.1, hs⟩
    rw [hslice τ.1 τ.2 hs] at h
    exact h

/-- **`prop:psiandPhi`** for `X` of every relative dimension `n` (including `n = 0`), at every
point of `X^An`. Let `Γ ∈ PSH^NA(X, θ)_{>0}` with `Γ_max ≤ 0` and let `Ψ` be the complexification
of `Γ^*` (any extension across `X × {0}`). For every `v ∈ X^An` the limit
`σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))` exists and `Γ^An(v) = -σ(v)(Ψ)`. -/
theorem source_psiandPhi_dim (Γ : SourcePositiveIModelTestCurve θ) (hmax : Γ.val.max ≤ 0)
    {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ.val.toSourceTestCurvePredata Ψ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierValDim n E v Ψ k / k) atTop
        (𝓝 (gaussPotentialValDim n E v Ψ)) ∧
      naPotentialAnAt n E (sourcePositiveTestCurveToNA Γ) ω v =
        -((gaussPotentialValDim n E v Ψ : ℝ≥0∞) : EReal) := by
  have h := gaussPotentialValDim_of_isComplexificationOf n E (sourceKahlerFormRepresentative ω)
    Γ.val.toSourceTestCurvePredata hmax hΨ v
  exact ⟨h.1, by rw [naPotentialAnAt_sourcePositiveTestCurveToNA_dim n E Γ ω v, h.2]⟩

/-- **`prop:psiandPhi`** as printed, for `X` of every relative dimension `n` (including `n = 0`):
`Γ^An(v) = -σ(v)(Ψ)` for all `v ∈ X^Div`. -/
theorem source_psiandPhi_div_dim (Γ : SourcePositiveIModelTestCurve θ) (hmax : Γ.val.max ≤ 0)
    {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ.val.toSourceTestCurvePredata Ψ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (v : divisorialSet f) :
    naPotentialAn n E (sourcePositiveTestCurveToNA Γ) ω v =
      -((gaussPotentialValDim n E v.1 Ψ : ℝ≥0∞) : EReal) :=
  (source_psiandPhi_dim n E Γ hmax hΨ ω v.1).2

end Scheme

section DimZero

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 0 f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance dimZeroPsiPhiZeroTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance dimZeroPsiPhiZeroCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f 0
local instance dimZeroPsiPhiZeroManifold : IsComplexManifold 0 (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f 0

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 (SchemeComplexPoint f))}

/-- **`prop:psiandPhi` in dimension zero.** `X` smooth projective of relative dimension `0` with
`X(ℂ)` connected (a point). For `Γ ∈ PSH^NA(X, θ)_{>0}` with `Γ_max ≤ 0`, `Ψ` the complexification
of `Γ^*` and every `v ∈ X^An`: the limit defining `σ(v)(Ψ)` exists,
`Γ^An(v) = -σ(v)(Ψ)`, and both equal `Γ_max` (so `σ(v)(Ψ) = -Γ_max`). -/
theorem source_psiandPhi_dim_zero (Γ : SourcePositiveIModelTestCurve θ) (hmax : Γ.val.max ≤ 0)
    {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ.val.toSourceTestCurvePredata Ψ)
    (ω : SourceKahlerForm 0 (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierValDim 0 E v Ψ k / k) atTop
        (𝓝 (gaussPotentialValDim 0 E v Ψ)) ∧
      naPotentialAnAt 0 E (sourcePositiveTestCurveToNA Γ) ω v =
        -((gaussPotentialValDim 0 E v Ψ : ℝ≥0∞) : EReal) ∧
      -((gaussPotentialValDim 0 E v Ψ : ℝ≥0∞) : EReal) = (Γ.val.max : EReal) := by
  obtain ⟨h1, h2⟩ := source_psiandPhi_dim 0 E Γ hmax hΨ ω v
  refine ⟨h1, h2, ?_⟩
  rw [← h2, NANS.naPotentialAnAt_eq_of_dim_zero, sourcePositiveTestCurveToNA_max]

end DimZero

end SGPT.NAPotential.DimZero

end
