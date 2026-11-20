import SGPT.TestCurve.RWNObstacleIGood
import SGPT.IGood.Misc2VolBigL
import SGPT.Foundations.Analysis.Pending.IGoodGlobalPStability
import SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshPositivePDomain
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

/-!
# Clause (a) of `ex:RWN` from positive mass, and from clause (b)

Source `ex:RWN` (chapter *Test curves*). With `ψ_τ = usc sup_{k>0} k⁻¹ Γ^{𝓕,k}_τ` and
`Γ^𝓕_τ = P_θ[ψ_τ]`, the book proves that `Γ^𝓕_τ` is `𝓘`-model (clause (a),
`SGPT.TestCurve.TestConf.RWNIModelClause`) from the `𝓘`-goodness of `ψ_τ`
(`SGPT.LineBundle.SectionFiltration.obstacle_iGood`): "hence the `P`- and `𝓘`-envelopes of this
obstacle agree". This step requires `∫_X θ_{ψ_τ}ⁿ > 0` in the background `θ` itself
(`def:Igoodpot` provides positive mass in *some* background; the zero-mass case is open, footnote of
`ex:ImodelIgood`). This file proves:

* `iGoodWith_of_iGood_of_iEnvelope_mass_pos` (general): an `𝓘`-good `u ∈ PSH(X, θ)` with
  `∫_X θ_{P_θ[u]_𝓘}ⁿ > 0` has positive mass and `P_θ[u] = P_θ[u]_𝓘`;
* `obstacle_hasPositiveMass_of_pos`: positivity of the mass of one `ψ_{τ₀}` propagates to every
  `ψ_τ`, `τ < τ(𝓕)` (monotonicity below `τ₀`, concavity of `τ ↦ ψ_τ` and
  `∫ θ_{tu+(1-t)v}ⁿ ≥ tⁿ ∫ θ_uⁿ` above);
* `rwnIModelClause_of_obstacle_mass_pos`: hence clause (a);
* **`rwnIModelClause_of_minimalClause`**: clause (b) (`eq:Gammatautheta`) and the bigness of `{θ}`
  imply clause (a), unconditionally: `∫ θ_{ψ_{-C-1}}ⁿ = ∫ θ_{P_θ[ψ_{-C-1}]}ⁿ = ∫ θ_{V_θ}ⁿ > 0`;
* **`filtrationRay_mem_maximal_of_minimalClause`** (`rmk:max_filt`): the ray of a filtration is
  maximal, conditional on clause (b) of `ex:RWN` alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.POrder SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.PSH.VariableComplexAtlas

namespace SGPT.TestCurve.RWN

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- **An `𝓘`-good potential with an `𝓘`-envelope of positive mass is `𝓘`-good in the given
background.** Let `u ∈ PSH(X, θ)` be `𝓘`-good (`def:Igoodpot`: in *some* background in which
it has positive mass) and suppose `∫_X θ_{P_θ[u]_𝓘}ⁿ > 0`. Then `∫_X θ_uⁿ > 0` and
`P_θ[u] = P_θ[u]_𝓘`.

Proof: `w = P_θ[u]_𝓘` is `𝓘`-model of positive mass, hence `𝓘`-good in `θ`. In a common
Kähler background `C ω` both `u` and `w` have positive mass and are `𝓘`-good, so
`P_{Cω}[u] = P_{Cω}[u]_𝓘 = P_{Cω}[w]_𝓘 = P_{Cω}[w]`: `u` and `w` are `P`-equivalent, and
`𝓘`-goodness in `θ` transfers from `w` to `u`. -/
theorem iGoodWith_of_iGood_of_iEnvelope_mass_pos (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgood : IGood (n := n) u) (hw : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u))
    (hpos : HasPositivePotentialMass θ (iSingularityEnvelope θ.val u) hw) :
    IGoodWith θ u hu := by
  set w := iSingularityEnvelope θ.val u with hw_def
  have hlocal := hu.1.hasSmoothLocalPotentials
  have hwgood : IGoodWith θ w hw := by
    refine ⟨hpos, ?_⟩
    rw [hw_def, singularityEnvelope_iSingularityEnvelope θ.val θ.property.1 θ.property.2
      hlocal u hu, iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2 hlocal u hu]
  obtain ⟨C, hC, hwC, huC, hwposC, huposC⟩ :=
    GlobalQuasiPshPositivePDomain.exists_pos_common_kahler_background omega
      hw.quasiPshPotential hu.quasiPshPotential
  have hwσ : IGoodWith (C • omega.form) w hwC :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential omega θ
      (C • omega.form) hw hwC hpos hwposC).mp hwgood
  obtain ⟨θ', hu', hg'⟩ := hgood
  have huσ : IGoodWith (C • omega.form) u huC :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential omega θ'
      (C • omega.form) hu' huC hg'.positiveMass huposC).mp hg'
  have hIeq : iSingularityEnvelope (C • omega.form).val w =
      iSingularityEnvelope (C • omega.form).val u :=
    iSingularityEnvelope_eq_of_iEquivalent
      (iEquivalent_iSingularityEnvelope θ.val θ.property.1 θ.property.2 hlocal u hu).symm
  have henv : singularityEnvelope (C • omega.form).val w =
      singularityEnvelope (C • omega.form).val u := by
    rw [hwσ.envelope_eq, huσ.envelope_eq, hIeq]
  have hPEq : SourcePEquivalent (n := n) w u :=
    ⟨⟨C • omega.form, hwC, huC, hwposC, huposC, henv.le⟩,
      ⟨C • omega.form, huC, hwC, huposC, hwposC, henv.ge⟩⟩
  exact IGoodGlobalPStability.iGoodWith_of_sourcePEquivalent omega hw hu hwgood hPEq

/-- An `𝓘`-good `u ∈ PSH(X, θ)` of positive mass satisfies `P_θ[u] = P_θ[u]_𝓘`, and
`P_θ[u]_𝓘` is `𝓘`-model. -/
theorem iModel_singularityEnvelope_of_iGood (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgood : IGood (n := n) u) (hpos : HasPositivePotentialMass θ u hu) :
    IsIModelPotential θ.val (singularityEnvelope θ.val u) := by
  obtain ⟨θ', hu', hg'⟩ := hgood
  have hgw : IGoodWith θ u hu :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential omega θ' θ hu'
      hu hg'.positiveMass hpos).mp hg'
  rw [hgw.envelope_eq]
  have hlocal := hu.1.hasSmoothLocalPotentials
  exact ⟨iSingularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2 hlocal _ hu,
    (iSingularityEnvelope_idempotent θ.val θ.property.1 θ.property.2 hlocal _ hu).symm⟩

end General

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance rwnRedTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance rwnRedCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance rwnRedManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

section Reduction

variable {L : X.Modules} {a : LineBundleAtlas L}
  (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)

/-- If `H⁰(X, L^k) ≠ 0` for some `k > 0`, then `τ(𝓕) ≥ -C > -C - 1`. -/
theorem neg_bound_sub_one_lt_slope_of_nontrivial {k : ℕ} (hk : 0 < k)
    (hnt : Nontrivial (SectionSpace f L k)) :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hj := F.neg_bound_le_jump hk
  have h1 : ((-(F.bound : ℝ) : ℝ) : EReal) ≤ F.jump k / ((k : ℝ) : EReal) := by
    rw [EReal.le_div_iff_mul_le (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _), ← EReal.coe_mul]
    refine le_trans (le_of_eq ?_) hj
    congr 1
    ring
  have h2 : F.jump k / ((k : ℝ) : EReal) ≤ F.slope :=
    le_iSup₂ (f := fun (k : ℕ) (_ : 0 < k) => F.jump k / ((k : ℝ) : EReal)) k hk
  refine lt_of_lt_of_le ?_ (h1.trans h2)
  exact EReal.coe_lt_coe_iff.mpr (by linarith)

/-- If `τ(𝓕) > -∞`, then `τ(𝓕) > -C - 1`. -/
theorem neg_bound_sub_one_lt_slope_of_ne_bot (hs : F.slope ≠ ⊥) :
    ((-(F.bound : ℝ) - 1 : ℝ) : EReal) < F.slope := by
  by_cases hex : ∃ k : ℕ, 0 < k ∧ Nontrivial (SectionSpace f L k)
  · obtain ⟨k, hk, hnt⟩ := hex
    exact neg_bound_sub_one_lt_slope_of_nontrivial F hk hnt
  · push Not at hex
    exfalso
    apply hs
    refine le_bot_iff.mp (iSup₂_le fun k hk => ?_)
    have hb : F.jump k = ⊥ := (F.jump_eq_bot_iff hk).mpr (not_nontrivial_iff_subsingleton.mpr
      (hex k hk))
    rw [hb, EReal.bot_div_of_pos_ne_top (EReal.coe_pos.mpr (by exact_mod_cast hk))
      (EReal.coe_ne_top _)]

variable [IsIntegral X] [ConnectedSpace (SchemeComplexPoint f)]

local instance rwnRedMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance rwnRedBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [ConnectedSpace (SchemeComplexPoint f)] in
/-- **Positivity of the mass of the obstacle propagates**: if `∫_X θ_{ψ_{τ₀}}ⁿ > 0` for one
`τ₀ < τ(𝓕)`, then `∫_X θ_{ψ_τ}ⁿ > 0` for every `τ < τ(𝓕)`. For `τ ≤ τ₀` by monotonicity
(`thm:mono`), otherwise by concavity of `τ ↦ ψ_τ` and `∫ θ_{tu+(1-t)v}ⁿ ≥ tⁿ ∫ θ_uⁿ`. -/
theorem obstacle_hasPositiveMass_of_pos {τ₀ : ℝ} (hτ₀ : (τ₀ : EReal) < F.slope)
    (hpos₀ : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) (F.obstacle H τ₀)
        (F.obstacle_isThetaPshPotential H hτ₀))
    {τ : ℝ} (hτ : (τ : EReal) < F.slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    HasPositivePotentialMass (H.curvature a) (F.obstacle H τ)
      (F.obstacle_isThetaPshPotential H hτ) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set θ := H.curvature a with hθ
  let omega := schemeProjectiveTNKahlerBackground f n E
  have hψ₀ := F.obstacle_isThetaPshPotential H hτ₀
  have hψ := F.obstacle_isThetaPshPotential H hτ
  rcases le_or_gt τ τ₀ with hle | hlt
  · exact hpos₀.trans_le (diagonalPotentialMass_mono_of_kahler omega hψ₀ hψ
      (MoreSingularOn.of_le fun x _ => F.obstacle_anti H hle x))
  · obtain ⟨τ₁, hττ₁, hτ₁⟩ := EReal.lt_iff_exists_real_btwn.mp hτ
    have hττ₁' : τ < τ₁ := EReal.coe_lt_coe_iff.mp hττ₁
    have hden : 0 < τ₁ - τ₀ := by linarith
    set t : ℝ := (τ - τ₀) / (τ₁ - τ₀) with ht_def
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
    have hpar : t * τ₁ + (1 - t) * τ₀ = τ := by
      rw [ht_def]
      field_simp
      ring
    have hψ₁ := F.obstacle_isThetaPshPotential H hτ₁
    have hcc := F.obstacle_concave H (show τ₀ < τ₁ by linarith) hτ₁ ht0 ht1
    rw [hpar] at hcc
    have hcomm : convexComb (1 - t) (F.obstacle H τ₀) (F.obstacle H τ₁) =
        convexComb t (F.obstacle H τ₁) (F.obstacle H τ₀) := by
      funext x
      rw [convexComb_apply, convexComb_apply, show 1 - (1 - t) = t by ring, add_comm]
    have h1t0 : 0 < 1 - t := by linarith
    have h1t1 : 1 - t < 1 := by linarith
    have hw := isThetaPshPotential_convexComb hψ₀ hψ₁ h1t0 h1t1
    have hscale := GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le
      (θ := θ) hψ₀ hψ₁ h1t0 h1t1 univ
    change ENNReal.ofReal ((1 - t) ^ n) * diagonalPotentialMass θ (F.obstacle H τ₀) hψ₀ ≤
      diagonalPotentialMass θ _ hw at hscale
    have hmono := diagonalPotentialMass_mono_of_kahler omega hw hψ
      (MoreSingularOn.of_le fun x _ => by rw [hcomm]; exact hcc x)
    exact (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (pow_pos h1t0 _)).ne' hpos₀.ne').trans_le
      (hscale.trans hmono)

/-- **Clause (a) of `ex:RWN` from the positive mass of one obstacle**: if
`∫_X θ_{ψ_{τ₀}}ⁿ > 0` for some `τ₀ < τ(𝓕)`, then every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model
(`ψ_τ` is `𝓘`-good, `SGPT.LineBundle.SectionFiltration.obstacle_iGood_of_lt_slope`, and has
positive mass, so `Γ^𝓕_τ = P_θ[ψ_τ] = P_θ[ψ_τ]_𝓘`). -/
theorem rwnIModelClause_of_obstacle_mass_pos {τ₀ : ℝ} (hτ₀ : (τ₀ : EReal) < F.slope)
    (hpos₀ : letI := E.isSeparated; letI := E.quasiCompact;
      haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
      HasPositivePotentialMass (H.curvature a) (F.obstacle H τ₀)
        (F.obstacle_isThetaPshPotential H hτ₀)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  intro τ hτ
  exact iModel_singularityEnvelope_of_iGood (schemeProjectiveTNKahlerBackground f n E)
    (F.obstacle_isThetaPshPotential H hτ) (F.obstacle_iGood_of_lt_slope H hτ)
    (obstacle_hasPositiveMass_of_pos F H hτ₀ hpos₀ hτ)

/-- **Clause (b) of `ex:RWN` implies clause (a)** (`{θ}` big, unconditionally): if
`Γ^𝓕_τ = V_θ` for `τ ≤ -C`, then every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is `𝓘`-model. Indeed
`τ(𝓕) > -C - 1` and `∫ θ_{ψ_{-C-1}}ⁿ = ∫ θ_{P_θ[ψ_{-C-1}]}ⁿ = ∫ θ_{V_θ}ⁿ > 0`
(`prop:Ppresmass`). -/
theorem rwnIModelClause_of_minimalClause
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hb : letI := E.isSeparated; letI := E.quasiCompact;
      SGPT.TestCurve.TestConf.RWNMinimalClause F H) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  set θ := H.curvature a with hθ
  let omega := schemeProjectiveTNKahlerBackground f n E
  have hτ₀ := neg_bound_sub_one_lt_slope_of_ne_bot F
    (SGPT.TestCurve.TestConf.slope_ne_bot_of_minimalClause F H hbig hb)
  apply rwnIModelClause_of_obstacle_mass_pos F H hτ₀
  have hψ₀ := F.obstacle_isThetaPshPotential H hτ₀
  have hlocal := LocalPotentials.closedRealOneOne_hasLocalPotentials θ
  have hP := Pending.singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
    hlocal _ hψ₀
  have hmass := singularityEnvelopeMassPreserving omega θ _ hψ₀ hP
  have hmodel := SingularMinimalCanonicalRay.isModelPotential_thetaPshSupremum omega θ hbig
  have hΓ : singularityEnvelope θ.val (F.obstacle H (-(F.bound : ℝ) - 1)) =
      thetaPshSupremum θ.val := hb _ (by linarith)
  change 0 < diagonalPotentialMass θ (F.obstacle H (-(F.bound : ℝ) - 1)) hψ₀
  rw [← hmass, SGPT.IGood.Misc2VolBigL.diagonalPotentialMass_congr θ hΓ hP
    hmodel.plurisubharmonic]
  exact hmodel.positive_mass

/-- **Source `rmk:max_filt`, conditional on clause (b) of `ex:RWN` alone** (clause (a) follows,
`rwnIModelClause_of_minimalClause`): the ray `Γ^{𝓕*}` induced by `𝓕` is a maximal geodesic ray
emanating from `V_θ`, for every Kähler background `ω`. -/
theorem filtrationRay_mem_maximal_of_minimalClause
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (hb : letI := E.isSeparated; letI := E.quasiCompact;
      SGPT.TestCurve.TestConf.RWNMinimalClause F H)
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    sourceTestCurveLegendreRay (SGPT.TestCurve.TestConf.filtrationTestCurvePredata F H hbig
        (rwnIModelClause_of_minimalClause F H hbig hb) hb) ∈
      sourceMaximalGeodesicRays omega (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact SGPT.TestCurve.TestConf.filtrationRay_mem_maximal_of_projective F H hbig _ _ omega

end Reduction

end SGPT.TestCurve.RWN
