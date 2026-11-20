import SGPT.TestCurve.RWNTwistedRays
import SGPT.PSH.SourceTestCurvePositiveMass

/-!
# From geodesic rays emanating from `Φ` to `Φ`-twisted test curves

Source `rmk:testcurve:L815` (chapter *Test curves*), the twisted version of
`lma:LegendsRtoTC`: for `Φ ∈ 𝓔(X, θ; φ)` and a geodesic ray `ℓ` in `𝓔(X, θ; φ)` emanating
from `Φ`, the inverse Legendre transform `ℓ*_τ = inf_{t > 0} (ℓ_t - tτ)` (`eq:invLeg`),
`τ < ℓ*_max`, is a `Φ`-twisted test curve whose Legendre transform is `ℓ`.

Two steps of the untwisted proof do not transfer verbatim.

* In the untwisted case `ℓ*_max = sup_X ℓ_1`, by the linearity `sup_X ℓ_t = t sup_X ℓ_1`
  (`prop:raysuplinear`), which uses that `ℓ_0 = φ` is a model potential. For a ray emanating
  from `Φ` the supremum is not linear in `t` (e.g. `ℓ_t = Φ + ct`), and it is not clear a priori
  that `ℓ*_τ ≡ -∞` for large `τ`. Here `ℓ*_max` is defined as the supremum of the slopes `τ`
  with `ℓ*_τ ≢ -∞` (`raySlopeSet`), and its finiteness (`raySlopeSet_bddAbove`) is proved as
  follows. If `ℓ*_τ` were `θ`-psh for every `τ ∈ ℝ`, then by concavity of `τ ↦ ℓ*_τ`,
  `ℓ*_τ ≥ t ℓ*_σ + (1 - t) ℓ*_{τ₁}` for `σ < τ < τ₁`, so
  `∫ θ_{ℓ*_τ}ⁿ ≥ tⁿ ∫ θ_{ℓ*_σ}ⁿ` (monotonicity and multilinearity of non-pluripolar masses);
  letting `τ₁ → ∞` (`t → 1`) the mass `τ ↦ ∫ θ_{ℓ*_τ}ⁿ` is constant, hence equal to its limit
  `∫ θ_Φⁿ = ∫ θ_φⁿ` at `-∞` (`cor:incseqnppcont`). So `ℓ*_τ ∈ 𝓔(X, θ; φ)` and
  `P_θ[ℓ*_τ](Φ) = Φ`; with the twisted fixed-point property this gives `ℓ*_τ = Φ` for all `τ`,
  i.e. `ℓ_1 ≥ Φ + τ` for all `τ`, which is absurd.
* The fixed-point property is `P_θ[ℓ*_τ](Φ) = ℓ*_τ` (`rayInverse_twistedFixedPoint`); its proof
  is the comparison of the geodesic `ℓ` on `[0, T]` with the subgeodesics
  `t ↦ η + t(Tτ - C)/T`, for a competitor `η ≤ Φ`, `η ≤ ℓ*_τ + C`, exactly as in the untwisted
  case, but without the reduction to the rooftop `(ℓ*_τ + C) ∧ V_θ`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.RWNTwisted

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.PSH.VariableComplexAtlas
open SGPT.TestCurve.TestConf

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Multiplication by a positive real preserves a real upper bound in `EReal`. -/
theorem coe_mul_le_coe {t : ℝ} (ht : 0 < t) {a : EReal} {r : ℝ} (h : a ≤ (r : EReal)) :
    (t : EReal) * a ≤ ((t * r : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ht]; exact bot_le
  | coe a =>
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) ht.le)
  | top => exact absurd h (by simp)

/-- Concavity of the inverse Legendre transform `τ ↦ ℓ*_τ` of any ray, as a convex
combination inequality. -/
theorem convexComb_rayInverse_le {X : Type*} (ℓ : SourceRayFamily X) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (σ τ₁ : ℝ) :
    convexComb t (sourcePositiveRayInverse ℓ σ) (sourcePositiveRayInverse ℓ τ₁) ≤
      sourcePositiveRayInverse ℓ (t * σ + (1 - t) * τ₁) := by
  intro x
  change (t : EReal) * sourcePositiveRayInverse ℓ σ x +
      ((1 - t : ℝ) : EReal) * sourcePositiveRayInverse ℓ τ₁ x ≤
    ⨅ s : Ioi (0 : ℝ), sourceRayExtension ℓ s.1 x -
      ((s.1 * (t * σ + (1 - t) * τ₁) : ℝ) : EReal)
  apply le_iInf
  intro s
  have hA : sourcePositiveRayInverse ℓ σ x ≤
      sourceRayExtension ℓ s.1 x - ((s.1 * σ : ℝ) : EReal) :=
    iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceRayExtension ℓ s.1 x - ((s.1 * σ : ℝ) : EReal)) s
  have hB : sourcePositiveRayInverse ℓ τ₁ x ≤
      sourceRayExtension ℓ s.1 x - ((s.1 * τ₁ : ℝ) : EReal) :=
    iInf_le (fun s : Ioi (0 : ℝ) ↦ sourceRayExtension ℓ s.1 x - ((s.1 * τ₁ : ℝ) : EReal)) s
  cases hv : sourceRayExtension ℓ s.1 x using EReal.rec with
  | bot =>
    rw [hv, EReal.bot_sub] at hA
    rw [le_bot_iff.mp hA, EReal.coe_mul_bot_of_pos ht0, EReal.bot_add]
    exact bot_le
  | top =>
    rw [EReal.top_sub_coe]
    exact le_top
  | coe v =>
    rw [hv, ← EReal.coe_sub] at hA hB
    have h1 := coe_mul_le_coe ht0 hA
    have h2 := coe_mul_le_coe (sub_pos.mpr ht1) hB
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    rw [← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    ring

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {φ Φ : M → EReal} {hφ : SourceModelPotential θ φ} {ℓ : SourceRayFamily M}
  {omega : KahlerBackground n M}

/-- **Twisted fixed points** (twisted version of `eq:Pellstartemp1` in `lma:LegendsRtoTC`):
for a geodesic ray `ℓ` emanating from `Φ`, every `θ`-psh inverse Legendre transform `ℓ*_τ`
satisfies `P_θ[ℓ*_τ](Φ) = ℓ*_τ`. -/
theorem rayInverse_twistedFixedPoint (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) (τ : ℝ)
    (hχ : (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ)) :
    sourceRelativeEnvelope θ (sourcePositiveRayInverse ℓ τ) Φ = sourcePositiveRayInverse ℓ τ := by
  let χ := sourcePositiveRayInverse ℓ τ
  have hsub := h.1.isSubgeodesicRay
  have hΦ : (ofFixedModel n M).IsThetaPSH θ Φ := h.2 ▸ hsub.thetaPSH ⟨0, by simp⟩
  have hχΦ : χ ≤ Φ := h.2 ▸ rayInverse_le_initial hsub τ
  apply le_antisymm
  · change uscRegularization
      (fun y ↦ ⨆ w : sourceRelativeEnvelopeCompetitors θ χ Φ, w.1 y) ≤ χ
    apply uscRegularization_le (sourceThetaPSH_upperSemicontinuous hχ)
    intro x
    apply iSup_le
    intro w
    obtain ⟨hw, hwΦ, hwχ⟩ := (sourceRelativeEnvelopeCompetitors_iff hΦ).mp w.2
    obtain ⟨K, hK⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp hwχ
    let D : ℝ := Max.max K 0
    have hwχ' (y : M) : w.1 y ≤ χ y + (D : EReal) :=
      (hK y).trans (add_le_add le_rfl (EReal.coe_le_coe (le_max_left K 0)))
    have htime (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (T : ℝ) (hT : 0 < T) (y : M) :
        w.1 y - ((D * s : ℝ) : EReal) ≤
          sourceRayExtension ℓ (s * T) y - (((s * T) * τ : ℝ) : EReal) := by
      have hterminal (y : M) : w.1 y + ((T * τ - D : ℝ) : EReal) ≤ ℓ ⟨T, hT.le⟩ y := by
        have hχT : χ y ≤ ℓ ⟨T, hT.le⟩ y - ((T * τ : ℝ) : EReal) := by
          have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
            sourceRayExtension ℓ t.1 y - ((t.1 * τ : ℝ) : EReal)) ⟨T, hT⟩
          simpa only [χ, sourcePositiveRayInverse, sourceRayExtension_nonneg ℓ T hT.le] using hh
        calc
          w.1 y + ((T * τ - D : ℝ) : EReal) ≤
              (χ y + (D : EReal)) + ((T * τ - D : ℝ) : EReal) := add_le_add (hwχ' y) le_rfl
          _ = χ y + ((T * τ : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            congr 2
            ring
          _ ≤ ℓ ⟨T, hT.le⟩ y := by
            simpa only [EReal.sub_add_cancel] using
              add_le_add hχT (le_rfl : ((T * τ : ℝ) : EReal) ≤ ((T * τ : ℝ) : EReal))
      have hq := sourceSubgeodesic_affine omega hw (T * τ - D)
      have hc : (fun s : ℝ ↦ fun y ↦ w.1 y + ((s * (T * τ - D) : ℝ) : EReal)) ∈
          sourcePerronCompetitors omega θ Φ (ℓ ⟨T, hT.le⟩) :=
        ⟨w.1, (fun y ↦ w.1 y + ((T * τ - D : ℝ) : EReal)), hw,
          sourceThetaPSH_add_const hw (T * τ - D), hwΦ, hterminal, hq⟩
      have hg := (h.1.2 0 T le_rfl hT.le).2.2.2.2.2 s hs
      simp only [mul_zero, add_zero] at hg
      rw [sourceRayExtension_nonneg ℓ 0 (by norm_num), h.2,
        sourceRayExtension_nonneg ℓ T hT.le] at hg
      have hdom := sourcePerron_competitor_le hc s y
      rw [← hg] at hdom
      apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mpr
      convert hdom using 1
      simp only [sub_eq_add_neg, ← EReal.coe_neg, add_assoc, ← EReal.coe_add]
      congr 2
      ring
    have hwhole (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (y : M) :
        w.1 y - ((D * s : ℝ) : EReal) ≤ χ y := by
      apply le_iInf
      intro t
      have ht : 0 < t.1 := t.2
      have heq : s * (t.1 / s) = t.1 := by field_simp [hs.1.ne']
      simpa only [heq] using htime s hs (t.1 / s) (div_pos ht hs.1) y
    have hDlim : Tendsto (fun s : ℝ ↦ ((D * s : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
      have hf : Continuous (fun s : ℝ ↦ ((D * s : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (continuous_const.mul continuous_id)
      simpa only [mul_zero, EReal.coe_zero] using
        (hf.tendsto (0 : ℝ)).mono_left
          (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpair : Tendsto (fun s : ℝ ↦ (χ x, ((D * s : ℝ) : EReal)))
        (𝓝[>] (0 : ℝ)) (𝓝 (χ x, (0 : EReal))) := tendsto_const_nhds.prodMk_nhds hDlim
    have hadd : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2) (χ x, (0 : EReal)) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    have hlim : Tendsto (fun s : ℝ ↦ χ x + ((D * s : ℝ) : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 (χ x)) := by
      simpa only [Function.comp_def, add_zero] using hadd.tendsto.comp hpair
    have hneg : -χ x ≤ -w.1 x := by
      apply le_of_tendsto
        ((continuous_neg : Continuous (fun z : EReal ↦ -z)).tendsto (χ x) |>.comp hlim)
      filter_upwards [sourceRay_endpoint_filters.1] with s hs
      exact EReal.neg_le_neg_iff.mpr ((EReal.sub_le_iff_le_add
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mp (hwhole s hs x))
    exact EReal.neg_le_neg_iff.mp hneg
  · exact le_sourceRelativeEnvelope hχ hχΦ (MoreSingularOn.refl _ univ)

/-- The slopes `τ` at which the inverse Legendre transform `ℓ*_τ` is not identically `-∞`. -/
def raySlopeSet {X : Type*} (ℓ : SourceRayFamily X) : Set ℝ :=
  {τ | ∃ x, sourcePositiveRayInverse ℓ τ x ≠ ⊥}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The slope set is a lower set. -/
theorem raySlopeSet_lower {τ τ' : ℝ} (hτ : τ ∈ raySlopeSet ℓ) (hle : τ' ≤ τ) :
    τ' ∈ raySlopeSet ℓ := by
  obtain ⟨x, hx⟩ := hτ
  exact ⟨x, ne_bot_of_le_ne_bot hx (sourceRayLegendre_inverse_antitone ℓ x hle)⟩

/-- The slope set of a subgeodesic ray is non-empty. -/
theorem raySlopeSet_nonempty (hsub : SourceIsSubgeodesicRay omega θ ℓ) :
    (raySlopeSet ℓ).Nonempty := by
  obtain ⟨x, hx⟩ := thetaPSH_exists_ne_bot (hsub.thetaPSH ⟨1, by norm_num⟩)
  by_contra hne
  have hall : ∀ τ, sourcePositiveRayInverse ℓ τ x = ⊥ := by
    intro τ
    by_contra hτ
    exact hne ⟨τ, x, hτ⟩
  have hinv := ray_positive_inversion hsub zero_lt_one x
  rw [sourceRayExtension_nonneg ℓ 1 zero_le_one] at hinv
  apply hx
  rw [hinv]
  simp [hall]

/-- **Finiteness of the cut-off**: for a geodesic ray emanating from `Φ ∈ 𝓔(X, θ; φ)`, the
inverse Legendre transform `ℓ*_τ` is identically `-∞` for `τ` large. -/
theorem raySlopeSet_bddAbove (hΦ : SourceRelativeFullMass θ φ Φ hφ)
    (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) : BddAbove (raySlopeSet ℓ) := by
  by_contra hunb
  have hsub := h.1.isSubgeodesicRay
  have hall : ∀ τ, τ ∈ raySlopeSet ℓ := by
    intro τ
    obtain ⟨τ', hτ', hlt⟩ := not_bddAbove_iff.mp hunb τ
    exact raySlopeSet_lower hτ' hlt.le
  have hpsh : ∀ τ, (ofFixedModel n M).IsThetaPSH θ (sourcePositiveRayInverse ℓ τ) :=
    fun τ ↦ rayInverse_thetaPSH_of_ne_bot hsub τ (hall τ)
  have hfix := fun τ ↦ rayInverse_twistedFixedPoint h τ (hpsh τ)
  obtain ⟨hray, rfl⟩ := h
  have hle : ∀ τ, sourcePositiveRayInverse ℓ τ ≤ ℓ ⟨0, by simp⟩ :=
    fun τ ↦ rayInverse_le_initial hsub τ
  -- the masses `τ ↦ ∫ θ_{ℓ*_τ}ⁿ` are decreasing
  have hanti : ∀ σ τ : ℝ, σ ≤ τ →
      sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ ≤
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ :=
    fun σ τ hστ ↦ sourcePotentialNonPluripolarMass_mono omega (hpsh τ) (hpsh σ)
      (MoreSingularOn.of_le (fun x _ ↦ sourceRayLegendre_inverse_antitone ℓ x hστ))
  -- and increasing, by concavity
  have hmono : ∀ σ τ : ℝ, σ < τ →
      sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ ≤
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ := by
    intro σ τ hστ
    have hstep : ∀ t ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ n) *
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ ≤
          sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ := by
      intro t ht
      have h1t : 0 < 1 - t := sub_pos.mpr ht.2
      let τ₁ : ℝ := (τ - t * σ) / (1 - t)
      have hpar : t * σ + (1 - t) * τ₁ = τ := by
        dsimp only [τ₁]
        field_simp
        ring
      have hcc : convexComb t (sourcePositiveRayInverse ℓ σ) (sourcePositiveRayInverse ℓ τ₁) ≤
          sourcePositiveRayInverse ℓ τ := by
        have hh := convexComb_rayInverse_le ℓ ht.1 ht.2 σ τ₁
        rwa [hpar] at hh
      let w := convexComb t (sourcePositiveRayInverse ℓ σ) (sourcePositiveRayInverse ℓ τ₁)
      have hwNative := isThetaPshPotential_convexComb
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh σ))
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh τ₁)) ht.1 ht.2
      have hw : (ofFixedModel n M).IsThetaPSH θ w :=
        (isThetaPSH_iff_nativeThetaPotential θ w).mpr hwNative
      have hmass := sourcePotentialNonPluripolarMass_mono omega hw (hpsh τ)
        (MoreSingularOn.of_le (fun x _ ↦ hcc x))
      have hscale := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
        (θ := atlasClosedFormToNative θ)
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh σ))
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hpsh τ₁)) ht.1 ht.2 univ
      change ENNReal.ofReal (t ^ n) *
          sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ ≤
            sourcePotentialNonPluripolarMeasure θ w hw univ at hscale
      exact hscale.trans hmass
    have hcont : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ n) *
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ)
        (𝓝[<] (1 : ℝ)) (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ n) *
          sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ)) := by
      apply ENNReal.Tendsto.mul_const _ (Or.inl (by simp))
      exact ((ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto (1 : ℝ)).mono_left
        nhdsWithin_le_nhds
    rw [one_pow, ENNReal.ofReal_one, one_mul] at hcont
    apply le_of_tendsto hcont
    filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
    exact hstep t ht
  have hconst : ∀ σ τ : ℝ,
      sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ σ) (hpsh σ) univ =
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ := by
    intro σ τ
    rcases lt_trichotomy σ τ with hlt | heq | hgt
    · exact le_antisymm (hmono σ τ hlt) (hanti σ τ hlt.le)
    · subst heq
      rfl
    · exact le_antisymm (hanti τ σ hgt.le) (hmono τ σ hgt)
  -- the limit of the masses at `-∞` is the mass of the initial potential
  have hΦpsh := hsub.thetaPSH ⟨0, by simp⟩
  obtain ⟨C, hC⟩ := thetaPSH_exists_upper hΦpsh
  have : Nonempty (OrderDual (Iio (0 : ℝ))) := ⟨⟨-1, by change (-1 : ℝ) < 0; norm_num⟩⟩
  have hm (j : Fin n) : Monotone
      (fun τ : OrderDual (Iio (0 : ℝ)) ↦ sourcePositiveRayInverse ℓ (τ : Iio (0 : ℝ)).1) := by
    intro a b hab x
    exact sourceRayLegendre_inverse_antitone ℓ x hab
  have hlim := sourceIncreasingMixed_mass_tendsto omega
    (θ := fun _ : Fin n ↦ θ)
    (u := fun τ : OrderDual (Iio (0 : ℝ)) ↦ fun _ : Fin n ↦
      sourcePositiveRayInverse ℓ (τ : Iio (0 : ℝ)).1)
    (fun τ _ ↦ hpsh _) hm (C := fun _ ↦ C)
    (fun _ τ x ↦ (hle _ x).trans (hC x))
  have hU : uscRegularization (⨆ τ : OrderDual (Iio (0 : ℝ)),
      sourcePositiveRayInverse ℓ (τ : Iio (0 : ℝ)).1) = ℓ ⟨0, by simp⟩ := by
    rw [← rayInverse_uscSup_eq_initial hsub 0 (fun τ ↦ hpsh τ.1)]
    apply congrArg uscRegularization
    funext x
    exact iSup_apply
  have hlim' : Tendsto (fun τ : OrderDual (Iio (0 : ℝ)) ↦
      sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ (τ : Iio (0 : ℝ)).1)
        (hpsh _) univ) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure θ (ℓ ⟨0, by simp⟩) hΦpsh univ)) := by
    simpa only [hU, sourceMixedNonPluripolarMass, sourceMixedNonPluripolarMeasure,
      sourcePotentialNonPluripolarMeasure, DiagonalMass.diagonalPotentialMeasure] using hlim
  have hmass0 : ∀ τ : ℝ,
      sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ =
        sourcePotentialNonPluripolarMeasure θ (ℓ ⟨0, by simp⟩) hΦpsh univ := by
    intro τ
    have hc : Tendsto (fun σ : OrderDual (Iio (0 : ℝ)) ↦
        sourcePotentialNonPluripolarMeasure θ (sourcePositiveRayInverse ℓ τ) (hpsh τ) univ) atTop
        (𝓝 (sourcePotentialNonPluripolarMeasure θ (ℓ ⟨0, by simp⟩) hΦpsh univ)) :=
      hlim'.congr (fun σ ↦ hconst _ τ)
    exact tendsto_nhds_unique tendsto_const_nhds hc
  -- hence every `ℓ*_τ` has full mass, and equals the initial potential
  have hfull : ∀ τ, SourceRelativeFullMass θ φ (sourcePositiveRayInverse ℓ τ) hφ := fun τ ↦
    ⟨hpsh τ, (MoreSingularOn.of_le (fun x _ ↦ hle τ x)).trans hΦ.choose_spec.1,
      (hmass0 τ).trans hΦ.choose_spec.2⟩
  have heq : ∀ τ, sourcePositiveRayInverse ℓ τ = ℓ ⟨0, by simp⟩ := by
    intro τ
    have hP := sourceRelativeEnvelope_fullMass omega (hfull τ) hΦ
    rw [← hfix τ]
    exact hP.1.trans hP.2
  -- which contradicts `ℓ*_τ ≤ ℓ_1 - τ`
  obtain ⟨x₀, hx₀⟩ := thetaPSH_exists_ne_bot hΦpsh
  obtain ⟨C₁, hC₁⟩ := thetaPSH_exists_upper (hsub.thetaPSH ⟨1, by norm_num⟩)
  obtain ⟨a, -, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hx₀)
  have hbound : sourcePositiveRayInverse ℓ (C₁ - a) x₀ ≤ (a : EReal) := by
    have hh := iInf_le (fun t : Ioi (0 : ℝ) ↦
      sourceRayExtension ℓ t.1 x₀ - ((t.1 * (C₁ - a) : ℝ) : EReal)) ⟨1, by norm_num⟩
    refine hh.trans ?_
    rw [sourceRayExtension_nonneg ℓ 1 zero_le_one]
    refine (EReal.sub_le_sub (hC₁ x₀) le_rfl).trans ?_
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe (by linarith)
  rw [heq (C₁ - a)] at hbound
  exact absurd hbound (not_le.mpr ha)

/-- The `Φ`-twisted test curve of a geodesic ray emanating from `Φ ∈ 𝓔(X, θ; φ)`: the inverse
Legendre transforms `ℓ*_τ = inf_{t > 0} (ℓ_t - tτ)` for `τ < ℓ*_max`, where `ℓ*_max` is the
supremum of the slopes `τ` with `ℓ*_τ ≢ -∞` (twisted version of `lma:LegendsRtoTC`). -/
def rayTwistedTestCurve (omega : KahlerBackground n M)
    (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) : SourceTwistedTestCurve θ Φ where
  max := sSup (raySlopeSet ℓ)
  potential := fun τ ↦ sourcePositiveRayInverse ℓ τ.1
  thetaPSH := fun τ ↦ by
    obtain ⟨τ', hτ', hlt⟩ := exists_lt_of_lt_csSup (raySlopeSet_nonempty h.1.isSubgeodesicRay)
      (show τ.1 < sSup (raySlopeSet ℓ) from τ.2)
    exact rayInverse_thetaPSH_of_ne_bot h.1.isSubgeodesicRay τ.1 (raySlopeSet_lower hτ' hlt.le)
  antitone := fun x _ _ hab ↦ sourceRayLegendre_inverse_antitone ℓ x hab
  concave := sourceRayLegendre_inverse_concave ℓ _
  twistedFixedPoint := fun τ ↦ by
    obtain ⟨τ', hτ', hlt⟩ := exists_lt_of_lt_csSup (raySlopeSet_nonempty h.1.isSubgeodesicRay)
      (show τ.1 < sSup (raySlopeSet ℓ) from τ.2)
    exact rayInverse_twistedFixedPoint h τ.1
      (rayInverse_thetaPSH_of_ne_bot h.1.isSubgeodesicRay τ.1 (raySlopeSet_lower hτ' hlt.le))
  limit_eq := by
    refine (rayInverse_uscSup_eq_initial h.1.isSubgeodesicRay _ (fun τ ↦ ?_)).trans h.2
    obtain ⟨τ', hτ', hlt⟩ := exists_lt_of_lt_csSup (raySlopeSet_nonempty h.1.isSubgeodesicRay)
      (show τ.1 < sSup (raySlopeSet ℓ) from τ.2)
    exact rayInverse_thetaPSH_of_ne_bot h.1.isSubgeodesicRay τ.1 (raySlopeSet_lower hτ' hlt.le)

/-- **Inversion** (twisted `thm:Legenbij`, surjectivity): the Legendre transform of the
twisted test curve of a geodesic ray `ℓ` emanating from `Φ` is `ℓ`. -/
theorem twistedLegendreRay_rayTwistedTestCurve (omega : KahlerBackground n M)
    (hΦ : SourceRelativeFullMass θ φ Φ hφ) (h : ℓ ∈ sourceGeodesicRaysFrom omega θ φ hφ Φ) :
    twistedLegendreRay (rayTwistedTestCurve omega h) = ℓ := by
  have hsub := h.1.isSubgeodesicRay
  have hbdd := raySlopeSet_bddAbove hΦ h
  have hbot : ∀ τ, sSup (raySlopeSet ℓ) < τ → sourcePositiveRayInverse ℓ τ = ⊥ := by
    intro τ hτ
    funext x
    by_contra hx
    exact notMem_of_csSup_lt hτ hbdd ⟨x, hx⟩
  funext t x
  by_cases ht : t.1 = 0
  · have ht0 : t = ⟨0, by simp⟩ := Subtype.ext ht
    simp only [twistedLegendreRay, if_pos ht]
    rw [ht0, h.2]
  · have hpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
    simp only [twistedLegendreRay, if_neg ht]
    have hinv := ray_positive_inversion_Iio hsub hbot hpos x
    rw [sourceRayExtension_nonneg ℓ t.1 t.2] at hinv
    exact hinv.symm

end SGPT.TestCurve.RWNTwisted
