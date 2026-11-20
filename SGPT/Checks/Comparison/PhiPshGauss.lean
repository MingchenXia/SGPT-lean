import SGPT.NAPotential.NAGagaPsiPhi
import SGPT.PSH.SourceTestCurveLegendreCorrespondence
import SGPT.PSH.SourceTestCurveIEnvelope

/-!
# The Gauss values `σ(v)(Φ)` of the complexification of a geodesic ray

Infrastructure for `prop:PhiinducePSH` (`chapter_NApotential.tex`, *The algebraic setting*):
*let `φ ∈ PSH(X, θ)_{>0}` be a model potential, `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0` and `Φ` the
complexification of `ℓ`; then `v ↦ -σ(v)(Φ)` on `X^Div` admits a unique extension to
`PSH(L^An)`.*

Here we compute `-σ(v)(Φ)` at every point `v ∈ X^An`. The value `σ(v)(Φ)` is read as for
`prop:psiandPhi` (`SGPT.NAPotential.NAGaga.gaussPotentialVal`): `σ(v)(Φ) = lim_k k⁻¹ σ(v)(𝓘(kΦ))`
with `σ(v)(𝓘(kΦ)) = min_i (v(𝔞_{k,i}) + i)` on the coefficient ideals
`𝔞_{k,i} = {g : g(x) δ^i ∈ 𝓘(kΦ)_{(x,0)}}` of `𝓘(kΦ)` along `X × {0}` (`eq:ImPhiexp`).

## Main results

* `rayComplexification`, `IsRayComplexificationOf`: the complexification
  `Φ(x, δ) = ℓ_{-log|δ|²}(x)` of a ray on `X × Δ^*` (`def:subgeoray`, `rmk:complexify1`); any
  value is allowed on `X × {0}` (the multiplier ideals of `kΦ` do not see this null set).
* `gaussPotentialVal_of_isComplexificationOf`: `prop:psiandPhi` for an arbitrary test-curve
  predatum `Γ` with `Γ_max ≤ 0` (no `𝓘`-model or positivity hypothesis): for every `v ∈ X^An` the
  limit defining `σ(v)(Ψ)` exists and `-σ(v)(Ψ) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`. The proof of
  `SGPT.NAPotential.NAGaga.source_psiandPhi` uses only the predatum.
* `isComplexificationOf_rayLegendre`: the complexification of `ℓ ∈ 𝓡(X, θ; φ)` is the
  complexification of the Legendre transform `ℓ^*` (`lma:LegendsRtoTC`), by the Ross–Witt Nyström
  inversion `ℓ_t = sup_τ (ℓ^*_τ + tτ)`, `t > 0` (`sourceRayLegendre_right_inverse`).
* `neg_gaussPotentialVal_ray_eq_naPotentialAnAt`: for `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0` and
  every `v ∈ X^An`, `-σ(v)(Φ) = Γ_ℓ^An(v)`, where `Γ_ℓ = P_θ[ℓ^*]_𝓘 ∈ PSH^NA(X, θ)_{>0}`
  (`rayNAPotential`, `def:TCIenvelope`, `prop:transitionPI`) and `Γ^An` is the formula
  `eq:psiandef` (`naPotentialAnAt`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.NAPotential.PhiPsh

open Set Filter MeasureTheory
open scoped Topology ENNReal
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich SGPT.NAPotential.NAGaga
open scoped ProductComplexManifold

/-! ### The complexification of a ray -/

section Complexification

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The complexification** `Φ(x, δ) = ℓ_{-log|δ|²}(x)` of a ray `ℓ` on `X × Δ`
(`def:subgeoray` in the coordinate `t = -log|δ|²`, `rmk:complexify1`; at `δ = 0` the formula
gives the irrelevant value `ℓ_0(x)`). -/
def rayComplexification (ℓ : SourceRayFamily M) (p : M × unitDisc) : EReal :=
  sourceRayExtension ℓ (-Real.log (‖p.2.val‖ ^ 2)) p.1

/-- `Φ` is the complexification of the ray `ℓ` on `X × Δ^*` (any value on `X × {0}`). -/
def IsRayComplexificationOf (ℓ : SourceRayFamily M) (Φ : M × unitDisc → EReal) : Prop :=
  ∀ p : M × unitDisc, p.2.val ≠ 0 → Φ p = rayComplexification ℓ p

theorem isRayComplexificationOf_rayComplexification (ℓ : SourceRayFamily M) :
    IsRayComplexificationOf ℓ (rayComplexification ℓ) := fun _ _ => rfl

/-- For `δ ∈ Δ^*` the time `t = -log|δ|²` is positive. -/
theorem neg_log_norm_sq_pos {δ : unitDisc} (hδ : δ.val ≠ 0) : 0 < -Real.log (‖δ.val‖ ^ 2) := by
  have h0 : 0 < ‖δ.val‖ := norm_pos_iff.mpr hδ
  have h1 : ‖δ.val‖ < 1 := mem_unitDisc.mp δ.2
  have h2 : ‖δ.val‖ ^ 2 < 1 := by nlinarith
  have := Real.log_neg (by positivity) h2
  linarith

end Complexification

/-! ### Rays and their Legendre transforms -/

section Rays

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
  {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}

/-- **The complexification of `ℓ` is that of `ℓ^*`.** For `ℓ ∈ 𝓡(X, θ; φ)` and `t > 0`,
`ℓ_t = sup_τ (ℓ^*_τ + tτ)` pointwise (`sourceRayLegendre_right_inverse`), so the complexification
of `ℓ` is the complexification (`NAGaga.complexification`) of its Legendre transform `ℓ^*`. -/
theorem isComplexificationOf_rayLegendre (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) {Φ : M × unitDisc → EReal}
    (hΦ : IsRayComplexificationOf ℓ Φ) :
    IsComplexificationOf (sourceRayLegendreTestCurve omega h).toSourceTestCurvePredata Φ := by
  intro p hp
  have ht := neg_log_norm_sq_pos hp
  set t := -Real.log (‖p.2.val‖ ^ 2) with htdef
  rw [hΦ p hp, rayComplexification, ← htdef, sourceRayExtension_nonneg ℓ t ht.le]
  have hR := congrFun (congrFun (sourceRayLegendre_right_inverse omega h) ⟨t, ht.le⟩) p.1
  rw [← hR]
  change sourceTestCurveLegendreWithInitial _ _ t p.1 = _
  rw [sourceTestCurveLegendreWithInitial, if_neg ht.ne']
  rfl

/-- `sup_X ℓ₁ ≤ 0` means `ℓ^*_max ≤ 0` (`cor:reltestcursuplinear`). -/
theorem rayLegendreCutoff_nonpos (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ)
    (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0) : sourceRayLegendreCutoff omega h ≤ 0 := by
  have h1 := (sourceRayLegendre_normalized omega h).1 ⟨1, by norm_num⟩
  rw [h1, one_mul] at hsup
  exact_mod_cast hsup

/-- The Legendre transform `ℓ^*` of `ℓ ∈ 𝓡(X, θ; φ)` has positive mass; its `𝓘`-envelope
`P_θ[ℓ^*]_𝓘` (`def:TCIenvelope`) is a positive `𝓘`-model test curve (`prop:transitionPI`). -/
def rayIModelTestCurve (omega : KahlerBackground n M) (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    SourcePositiveIModelTestCurve θ :=
  ⟨(sourceRayLegendreTestCurve omega h).iEnvelope omega,
    (sourceIModelTestCurvesPositive_iff_slices omega _).mpr
      ((sourceRayLegendreTestCurve omega h).iEnvelope_isIModel omega)⟩

/-- **The non-Archimedean potential of a ray**: `Γ_ℓ = P_θ[ℓ^*]_𝓘 ∈ PSH^NA(X, θ)_{>0}`. -/
def rayNAPotential (omega : KahlerBackground n M) (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) :
    SourceNAPotential θ :=
  sourcePositiveTestCurveToNA (rayIModelTestCurve omega h)

end Rays

/-! ### `σ(v)(Ψ)` for test-curve predata -/

section Scheme

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {d : ℕ} [SmoothOfRelativeDimension (d + 1) f]
  (E : ClosedProjectiveEmbedding f) [IsProper f]

local instance phiPshPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance phiPshPointCharts : ChartedSpace (ComplexModel (d + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (d + 1)
local instance phiPshPointManifold : IsComplexManifold (d + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (d + 1)

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (d + 1) (SchemeComplexPoint f))}

/-- **`prop:psiandPhi` for an arbitrary test-curve predatum.** Let `Γ` be a test-curve predatum
(a concave decreasing family of `θ`-psh potentials fixed by `P_θ[·]`, with no mass condition) with
`Γ_max ≤ 0` and `Ψ` the complexification of `Γ^*` on `X × Δ^*`. For every `v ∈ X^An` the limit
`σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))` exists and `-σ(v)(Ψ) = sup_{τ < Γ_max} (Γ_τ^An(v) + τ)`. -/
theorem gaussPotentialVal_of_isComplexificationOf
    (omega : KahlerBackground (d + 1) (SchemeComplexPoint f)) (Γ : SourceTestCurvePredata θ)
    (hmax : Γ.max ≤ 0) {Ψ : SchemeComplexPoint f × unitDisc → EReal}
    (hΨ : IsComplexificationOf Γ Ψ) (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierVal d E v Ψ k / k) atTop
        (𝓝 (gaussPotentialVal d E v Ψ)) ∧
      -((gaussPotentialVal d E v Ψ : ℝ≥0∞) : EReal) =
        ⨆ τ : Iio Γ.max, potentialAn (d + 1) E (Γ.potential τ) v + ((τ : ℝ) : EReal) := by
  have := E.locallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hA := SGPT.GAGA.H0S.multiplierIdealAlgebraic f E (d + 1)
  set a : ℕ → Iio Γ.max → ℝ≥0∞ := fun k τ =>
    v.multiplierIdealVal (d + 1) E (Γ.potential τ) k with ha
  set p : Iio Γ.max → ℝ≥0∞ := fun τ => v.potentialVal (d + 1) E (Γ.potential τ) with hp
  set b : ℕ → ℝ≥0∞ := fun k => gaussMultiplierVal d E v Ψ k with hb
  have hpsh : ∀ τ : Iio Γ.max,
      IsThetaPshPotential (atlasClosedFormToNative θ).val (Γ.potential τ) :=
    fun τ => Γ.native_thetaPSH τ
  have hlim : ∀ τ, Tendsto (fun k : ℕ => a k τ / k) atTop (𝓝 (p τ)) := fun τ =>
    BerkovichPoint.tendsto_potentialVal_of_multiplierIdealAlgebraic (d + 1) E hA (hpsh τ) v
  have hle : ∀ k : ℕ, 0 < k → ∀ τ, a k τ / k ≤ p τ := by
    intro k hk τ
    have h := BerkovichPoint.potentialVal_eq_iSup_of_multiplierIdealAlgebraic (d + 1) E hA
      (hpsh τ) v
    change a k τ / k ≤ v.potentialVal (d + 1) E (Γ.potential τ)
    rw [h]
    exact le_iSup₂ (f := fun k (_ : 0 < k) => a k τ / k) k hk
  have hmono : ∀ k : ℕ, 0 < k → ∀ τ τ' : Iio Γ.max, τ ≤ τ' → a k τ ≤ a k τ' := by
    intro k hk τ τ' h
    exact v.idealVal_antitone (algebraization_mono f (d + 1) E
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
        (algebraization_mono f (d + 1) E ?_)) le_rfl)
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
      (∀ τ : Iio Γ.max, c ≤ a k τ / k + ENNReal.ofReal (-τ.1)) → c ≤ b k / k + 1 / k := by
    intro k hk c hc
    have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    have hktop : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
    rw [← ENNReal.add_div, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
    change c * k ≤ (⨅ i : ℕ, v.idealVal (algebraization f (d + 1) E
      (coeffIdeal (n := d + 1) Ψ k i)) + (i : ℝ≥0∞)) + 1
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    by_cases hki : (i : ℝ) + 1 + k * Γ.max ≤ 0
    · rw [algebraization_coeffIdeal_eq_bot E hΨ hki, BJModel.idealVal_bot, top_add, top_add]
      exact le_top
    · have hτi : -((i : ℝ) + 1) / k < Γ.max := by
        rw [div_lt_iff₀ hkpos]
        rw [not_le] at hki
        linarith
      have hT : a k ⟨_, hτi⟩ ≤
          v.idealVal (algebraization f (d + 1) E (coeffIdeal (n := d + 1) Ψ k i)) :=
        v.idealVal_antitone (algebraization_mono f (d + 1) E
          (fun x g hg => multiplierIdeal_of_coeffIdeal hmax hΨ hk hτi hg))
      have hq : ENNReal.ofReal (-(-((i : ℝ) + 1) / k)) * k = (i : ℝ≥0∞) + 1 := by
        rw [neg_div, neg_neg, ← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (by positivity),
          div_mul_cancel₀ _ hkpos.ne', ENNReal.ofReal_add (by positivity) zero_le_one,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
      calc c * k ≤ (a k ⟨_, hτi⟩ / k + ENNReal.ofReal (-(-((i : ℝ) + 1) / k))) * k :=
            mul_le_mul_of_nonneg_right (hc ⟨_, hτi⟩) bot_le
        _ = a k ⟨_, hτi⟩ + ((i : ℝ≥0∞) + 1) := by
            rw [add_mul, ENNReal.div_mul_cancel hk0 hktop, hq]
        _ ≤ v.idealVal (algebraization f (d + 1) E (coeffIdeal (n := d + 1) Ψ k i)) +
              (i : ℝ≥0∞) + 1 := by
            rw [add_assoc]; exact add_le_add hT le_rfl
  have hT := tendsto_div_of_bounds hmax a p b hmono hlim hle hup hlow
  have hval : gaussPotentialVal d E v Ψ = ⨅ τ : Iio Γ.max, p τ + ENNReal.ofReal (-τ.1) :=
    hT.limUnder_eq
  refine ⟨by rw [hval]; exact hT, ?_⟩
  rw [hval, coe_ennreal_iInf]
  have hterm : ∀ τ : Iio Γ.max, potentialAn (d + 1) E (Γ.potential τ) v + ((τ : ℝ) : EReal) =
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

variable {φ : SchemeComplexPoint f → EReal} {hφ : SourceModelPotential θ φ}
  {ℓ : SourceRayFamily (SchemeComplexPoint f)}

/-- **`-σ(v)(Φ)` for the complexification of a ray.** For `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`,
`Φ` its complexification and every `v ∈ X^An`, the limit `σ(v)(Φ) = lim_k k⁻¹ σ(v)(𝓘(kΦ))` exists
and `-σ(v)(Φ) = sup_{τ < ℓ^*_max} ((ℓ^*_τ)^An(v) + τ)`. -/
theorem gaussPotentialVal_ray (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (v : BerkovichPoint f) :
    Tendsto (fun k : ℕ => gaussMultiplierVal d E v Φ k / k) atTop
        (𝓝 (gaussPotentialVal d E v Φ)) ∧
      -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal) =
        ⨆ τ : Iio (sourceRayLegendreCutoff omega h),
          potentialAn (d + 1) E (sourcePositiveRayInverse ℓ τ.1) v + ((τ : ℝ) : EReal) :=
  gaussPotentialVal_of_isComplexificationOf E omega
    (sourceRayLegendreTestCurve omega h).toSourceTestCurvePredata
    (rayLegendreCutoff_nonpos omega h hsup) (isComplexificationOf_rayLegendre omega h hΦ) v

/-- **`-σ(v)(Φ) = Γ_ℓ^An(v)` on `X^An`.** For `ℓ ∈ 𝓡(X, θ; φ)` with `sup_X ℓ₁ ≤ 0`, `Φ` its
complexification, every Kähler index `ω` and every `v ∈ X^An`, `-σ(v)(Φ)` is the analytification
`eq:psiandef` of the non-Archimedean potential `Γ_ℓ = P_θ[ℓ^*]_𝓘` (`rayNAPotential`). -/
theorem neg_gaussPotentialVal_ray_eq_naPotentialAnAt
    (omega : KahlerBackground (d + 1) (SchemeComplexPoint f))
    (h : ℓ ∈ sourceGeodesicRays omega θ φ hφ) (hsup : (⨆ x, ℓ ⟨1, by norm_num⟩ x) ≤ 0)
    {Φ : SchemeComplexPoint f × unitDisc → EReal} (hΦ : IsRayComplexificationOf ℓ Φ)
    (ω : SourceKahlerForm (d + 1) (SchemeComplexPoint f)) (v : BerkovichPoint f) :
    -((gaussPotentialVal d E v Φ : ℝ≥0∞) : EReal) =
      naPotentialAnAt (d + 1) E (rayNAPotential omega h) ω v := by
  set Γ := sourceRayLegendreTestCurve omega h with hΓ
  set G := rayIModelTestCurve omega h with hG
  have hGval : G.val = Γ.iEnvelope omega := rfl
  have hmaxG : G.val.max = sourceRayLegendreCutoff omega h := by
    rw [hGval, SourceTestCurve.iEnvelope_max, hΓ, sourceRayLegendreTestCurve_max]
  have hpot : ∀ (τ : Iio (sourceRayLegendreCutoff omega h)) (τ' : Iio G.val.max), τ.1 = τ'.1 →
      potentialAn (d + 1) E (G.val.potential τ') =
        potentialAn (d + 1) E (sourcePositiveRayInverse ℓ τ.1) := by
    rintro ⟨τ, h1⟩ ⟨τ', h2⟩ (rfl : τ = τ')
    have hp1 : G.val.potential ⟨τ, h2⟩ = sourceIEnvelope θ (Γ.potential ⟨τ, h1⟩) :=
      SourceTestCurve.iEnvelope_potential omega Γ ⟨τ, h1⟩
    rw [hp1]
    exact potentialAn_sourceIEnvelope (d + 1) E (Γ.thetaPSH ⟨τ, h1⟩)
  rw [(gaussPotentialVal_ray E omega h hsup hΦ v).2, rayNAPotential,
    naPotentialAnAt_sourcePositiveTestCurveToNA E G ω v]
  apply le_antisymm
  · refine iSup_le fun τ => ?_
    have h2 : τ.1 ∈ Iio G.val.max := by rw [mem_Iio, hmaxG]; exact τ.2
    rw [← hpot τ ⟨τ.1, h2⟩ rfl]
    exact le_iSup (fun σ : Iio G.val.max =>
      potentialAn (d + 1) E (G.val.potential σ) v + ((σ : ℝ) : EReal)) ⟨τ.1, h2⟩
  · refine iSup_le fun τ => ?_
    have h1 : τ.1 ∈ Iio (sourceRayLegendreCutoff omega h) := by rw [mem_Iio, ← hmaxG]; exact τ.2
    rw [hpot ⟨τ.1, h1⟩ τ rfl]
    exact le_iSup (fun σ : Iio (sourceRayLegendreCutoff omega h) =>
      potentialAn (d + 1) E (sourcePositiveRayInverse ℓ σ.1) v + ((σ : ℝ) : EReal)) ⟨τ.1, h1⟩

end Scheme

end SGPT.NAPotential.PhiPsh
