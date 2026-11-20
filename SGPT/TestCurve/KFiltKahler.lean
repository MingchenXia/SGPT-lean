import SGPT.TestCurve.KFiltAnalytic
import SGPT.TestCurve.KFiltCurve

/-!
# `ex:RWN` and `rmk:max_filt` on compact Kähler manifolds

Sources `ex:RWN` and `rmk:max_filt` (chapter *Test curves*), in the book's setting: `X` a
connected compact Kähler manifold (not necessarily projective), `L` a big line bundle with a
smooth Hermitian metric `h`, `θ = c₁(L, h)`, `𝓕` a filtration of the analytic section ring
`R(X, L)` (`AnalyticSectionFiltration`). Blueprint `claude-k-filt`, nodes
`claude-k-filt:minimal`, `claude-k-filt:rwn`, `claude-k-filt:maxfilt`.

The bigness of `L` is the book's: `c₁(L, h)` contains a Kähler current (equivalently, by lane
K-BIG, `h⁰(X, L^k) ≥ c kⁿ` for large `k`, `SGPT.IGood.KBig.sectionGrowth_iff_exists_kahlerCurrent`).

* `minimalClause_of_kahlerCurrent` (**`eq:Gammatautheta`**): `Γ^𝓕_τ = V_θ` for `τ ≤ -C`. The
  book's proof: every `s ∈ H⁰(X, L^k)` lies in `H⁰(X, L^k ⊗ 𝓘(kψ))`, `ψ` the obstacle, so by
  `thm:DXmain1` (lane K-BIG, compact Kähler) and `cor:volbigL` `vol θ_ψ = vol L = ∫ θⁿ_{V_θ}`;
  `ψ` is `𝓘`-good, so `Γ^𝓕_τ = P_θ[ψ] = P_θ[ψ]_𝓘` is a model potential of full mass, `= V_θ`.
* `iModelClause_of_kahlerCurrent`: every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model.
* `filtrationTestCurve_mem_iModel_and_isBounded` (**conclusion of `ex:RWN`**):
  `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)` (an `𝓘`-model test curve based at `V_θ`, `Γ_max = τ(𝓕)`) and bounded.
* `filtrationRay_mem_maximal` (**`rmk:max_filt`**): the ray `Γ^{𝓕*}` is a maximal geodesic
  ray emanating from `V_θ`, for every Kähler background.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.KFilt

open Filter Set MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.Quant2
  SGPT.IGood.KBig
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

variable {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
/-- A Kähler current in `c₁(L, h)` makes the class `{θ}` big. -/
theorem isBigClass_of_kahlerCurrent
    (hbig : ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ) :
    IsBigClass (RealBottChern.ofRepresentative (analyticSectionMetric L hL).θ) := by
  obtain ⟨ψ, ω', hψ⟩ := hbig
  exact ⟨⟨_, rfl, ψ, ω', hψ⟩⟩

variable (F : AnalyticSectionFiltration L) (ωb : KahlerBackground n X)
  (hbig : ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ)

include ωb hbig in
/-- For `L` big, `τ(𝓕) > -C - 1` (some `H⁰(X, L^k) ≠ 0`, `k > 0`). -/
theorem neg_bound_sub_one_lt_slope_of_kahlerCurrent :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  obtain ⟨k, hk⟩ := ((AnalyticSectionFiltration.eventually_nontrivial_of_kahlerCurrent ωb hL
    hbig).and (eventually_gt_atTop 0)).exists
  exact GradedFiltration.neg_bound_sub_one_lt_slope_of_nontrivial F hk.2 hk.1

include ωb hbig in
/-- **Source `ex:RWN`, `eq:Gammatautheta`, compact Kähler setting**: for `L` big and every
filtration `𝓕` of `R(X, L)`, `Γ^𝓕_τ = V_θ` for every `τ ≤ -C` (`C` the constant of
`eq:Flinearlybdd`). -/
theorem minimalClause_of_kahlerCurrent :
    F.MinimalClause (analyticSectionMetric L hL) := by
  set D := analyticSectionMetric L hL with hD
  set θ := D.θ with hθ
  have hθL : θ = sourceNativeFirstChernForm L hL := rfl
  have hbigC := isBigClass_of_kahlerCurrent hL hbig
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  have hτ₀ := neg_bound_sub_one_lt_slope_of_kahlerCurrent hL F ωb hbig
  intro τ hτC
  rw [F.testCurvePotential_eq_of_le_neg_bound D hτC (show -(F.bound : ℝ) - 1 ≤ -(F.bound : ℝ)
    by linarith)]
  set τ₀ : ℝ := -(F.bound : ℝ) - 1 with hτ₀_def
  set ψ := F.obstacle D τ₀ with hψ_def
  have hψ : IsThetaPshPotential θ.val ψ := F.obstacle_isThetaPshPotential D hτ₀
  have hgood : IGood (n := n) ψ := F.obstacle_iGood_of_lt_slope D ωb hτ₀
  have hψA : (ofFixedModel n X).IsThetaPSH (chernForm L hL) ψ := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [chernForm, sourceNativeAtlasForm_roundTrip]
    exact hψ
  -- every section of `L^k` lies in `H⁰(X, L^k ⊗ 𝓘(kψ))`
  have hsing : ∀ k : ℕ, 0 < k → ∀ s : twistedSections L unit k,
      SGPT.PSH.SingularityLE (D.normalizedLog k s) ψ := by
    intro k hk s
    refine F.normalizedLog_singularityLE_obstacle D hk ?_
    rw [F.piece_eq_top_of_le_neg_bound (show τ₀ ≤ -(F.bound : ℝ) by linarith) hk]
    exact Submodule.mem_top
  have heq : ∀ᶠ k : ℕ in atTop, normalizedH0 L unit ψ k = normalizedFullH0 L unit k := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    unfold normalizedH0 normalizedFullH0
    rw [finrank_literal_eq_of_singularityLE L hL hk hψ.quasiPshPotential (hsing k hk)]
  -- `thm:DXmain1` and `cor:volbigL`: `vol θ_ψ = ∫ θⁿ_{V_θ}`
  have h1 := tendsto_normalizedH0 ωb hL sourceNativeUnit_smooth hψA
  have h2 := tendsto_normalizedH0_volume ωb hL hψA
  have hlim := tendsto_nhds_unique (h1.congr' heq) h2
  -- translation to the native masses
  have hw : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val ψ) :=
    iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2 hlocal _ hψ
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbigC
  have hrt : atlasClosedFormToNative (chernForm L hL) = θ := sourceNativeAtlasForm_roundTrip _
  have hmass : ∀ (θ₁ θ₂ : ClosedRealOneOneForm n X) (u₁ u₂ : X → EReal), θ₁ = θ₂ → u₁ = u₂ →
      ∀ (h₁ : IsThetaPshPotential θ₁.val u₁) (h₂ : IsThetaPshPotential θ₂.val u₂),
        diagonalPotentialMass θ₁ u₁ h₁ = diagonalPotentialMass θ₂ u₂ h₂ := by
    rintro θ₁ _ u₁ _ rfl rfl _ _
    rfl
  have hmw : sourceIVolume (chernForm L hL) ψ hψA = diagonalPotentialMass θ _ hw := by
    unfold sourceIVolume
    refine hmass _ _ _ _ hrt ?_ _ _
    rw [sourceIEnvelope_eq_native _ _ hψA, hrt]
  have hmV : sourcePotentialNonPluripolarMeasure (chernForm L hL)
      (sourceMinimalEnvelope (chernForm L hL)) (sourceMinimalEnvelope_thetaPSH_of_mem hψA) univ =
      diagonalPotentialMass θ _ hV := by
    refine hmass _ _ _ _ hrt ?_ _ _
    rw [sourceMinimalEnvelope_eq_native, hrt]
  rw [hmw, hmV] at hlim
  -- `Γ = P_θ[ψ] = P_θ[ψ]_𝓘 = V_θ`
  have hmodel := SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum ωb θ hbigC
  have hwpos : HasPositivePotentialMass θ (iSingularityEnvelope θ.val ψ) hw := by
    change 0 < diagonalPotentialMass θ _ hw
    rw [hlim]
    exact hmodel.positive_mass
  have hgw := SGPT.TestCurve.RWN.iGoodWith_of_iGood_of_iEnvelope_mass_pos ωb hψ hgood hw hwpos
  change singularityEnvelope θ.val ψ = _
  rw [hgw.envelope_eq]
  set w := iSingularityEnvelope θ.val ψ with hw_def
  have hwV : w ≤ thetaPshSupremum θ.val := fun x =>
    le_thetaPshSupremum hw (iSingularityEnvelope_le_zero θ.val _) x
  have hVle := equalMassLeSingularityEnvelope ωb θ w (thetaPshSupremum θ.val) hw hV hwpos
    (thetaPshSupremum_le_zero θ.val) (MoreSingularOn.of_le fun x _ => hwV x) hlim
  rw [hw_def, singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2 hlocal _
    hψ, ← hw_def] at hVle
  exact le_antisymm hwV hVle

include ωb hbig in
/-- **Source `ex:RWN`, compact Kähler setting**: every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model
(the obstacle is `𝓘`-good and the `P`- and `𝓘`-envelopes agree). -/
theorem iModelClause_of_kahlerCurrent : F.IModelClause (analyticSectionMetric L hL) :=
  GradedFiltration.iModelClause_of_minimalClause F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (minimalClause_of_kahlerCurrent hL F ωb hbig)

include ωb hbig in
/-- **The test curve `Γ^𝓕` of `ex:RWN`, compact Kähler setting**: the family
`(Γ^𝓕_τ)_{τ < τ(𝓕)}` as a test curve for `θ = c₁(L, h)` (`def:testcur`). -/
def kahlerFiltrationTestCurve : SourceTestCurve (analyticSectionMetric L hL).atlasForm :=
  GradedFiltration.filtrationTestCurve F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (iModelClause_of_kahlerCurrent hL F ωb hbig) (minimalClause_of_kahlerCurrent hL F ωb hbig)

theorem kahlerFiltrationTestCurve_potential (τ : Iio (kahlerFiltrationTestCurve hL F ωb hbig).max) :
    (kahlerFiltrationTestCurve hL F ωb hbig).potential τ =
      F.testCurvePotential (analyticSectionMetric L hL) τ.1 := rfl

/-- `Γ_max = τ(𝓕)`. -/
theorem coe_kahlerFiltrationTestCurve_max :
    (((kahlerFiltrationTestCurve hL F ωb hbig).max : ℝ) : EReal) = F.slope :=
  GradedFiltration.coe_filtrationTestCurve_max F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (iModelClause_of_kahlerCurrent hL F ωb hbig) (minimalClause_of_kahlerCurrent hL F ωb hbig)

/-- **Conclusion of source `ex:RWN`, compact Kähler setting**: for `L` big and every filtration
`𝓕` of `R(X, L)`, `Γ^𝓕 ∈ 𝓔^{NA}(X, θ)` (an `𝓘`-model test curve based at `V_θ`) and `Γ^𝓕`
is bounded. -/
theorem filtrationTestCurve_mem_iModel_and_isBounded :
    kahlerFiltrationTestCurve hL F ωb hbig ∈
        SourceIModelTestCurves (analyticSectionMetric L hL).atlasForm
          (sourceMinimalEnvelope (analyticSectionMetric L hL).atlasForm)
          ((analyticSectionMetric L hL).sourceMinimalEnvelope_atlasForm_model ωb
            (isBigClass_of_kahlerCurrent hL hbig)) ∧
      SourceTestCurveIsBounded (sourceMinimalEnvelope (analyticSectionMetric L hL).atlasForm)
        (kahlerFiltrationTestCurve hL F ωb hbig) :=
  ⟨GradedFiltration.filtrationTestCurve_mem_iModel F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (iModelClause_of_kahlerCurrent hL F ωb hbig) (minimalClause_of_kahlerCurrent hL F ωb hbig),
    GradedFiltration.filtrationTestCurve_isBounded F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (iModelClause_of_kahlerCurrent hL F ωb hbig) (minimalClause_of_kahlerCurrent hL F ωb hbig)⟩

/-- **Source `rmk:max_filt`, compact Kähler setting**: for `L` big and every filtration `𝓕` of
`R(X, L)`, the ray `Γ^{𝓕*}` induced by `𝓕` (the Legendre transform of the family
`(Γ^𝓕_τ)_{τ < τ(𝓕)}` of `ex:RWN`) is a maximal geodesic ray emanating from `V_θ`, for every
Kähler background `ω'` of `X`. -/
theorem filtrationRay_mem_maximal (ω' : KahlerBackground n X) :
    sourceTestCurveLegendreRay (kahlerFiltrationTestCurve hL F ωb hbig).toSourceTestCurvePredata ∈
      sourceMaximalGeodesicRays ω' (analyticSectionMetric L hL).atlasForm
        (sourceMinimalEnvelope (analyticSectionMetric L hL).atlasForm)
        ((analyticSectionMetric L hL).sourceMinimalEnvelope_atlasForm_model ωb
          (isBigClass_of_kahlerCurrent hL hbig)) :=
  GradedFiltration.filtrationRay_mem_maximal F _ ωb (isBigClass_of_kahlerCurrent hL hbig)
    (iModelClause_of_kahlerCurrent hL F ωb hbig) (minimalClause_of_kahlerCurrent hL F ωb hbig) ω'

end SGPT.TestCurve.KFilt
