import SGPT.Trace.RestVolIdeal
import SGPT.IGood.DXLow2Aux
import SGPT.IGood.LogVolume
import SGPT.PSH.SourceSingularityGeneralInterpolation
import SGPT.PSH.SourceGeneralMixedIVolumeContinuity
import SGPT.Okounkov.TranscendentalBodySingDecrease
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.ActualTraceFreeNormalizedReader
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.AmbientMassBackgroundMonotone
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

/-!
# The upper bound of `thm:rest_volume` for Kähler currents (Step 1)

Lane TRACE-RV, blueprint `claude-rest-vol.tex`, nodes `claude-rest-vol:scaled-volume`,
`claude-rest-vol:upper-kahler`.  Source: `chapter_trace.tex`, proof of `thm:rest_volume`,
Step 1: if `θ_φ` is a Kähler current, `ν(φ, Y) = 0` and `dim Y > 0`, then

`limsup_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) ≤ ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`.

## Proof (the book's Step 1)

Take a quasi-equisingular approximation `(φ_j)` of `φ` by potentials with analytic singularities
and `θ + dd^c φ_j ≥ κ/4` (`exists_gentle_kahler_qea`).  For `0 < c < 1` and `k` large,
`Res_Y 𝓘(kφ) ⊆ 𝓘(k · c φ_j|_Y)` (`eventually_restrictIdeal_le_scaled`, from `lma:IandIinf`), so by
the upper bound of `thm:DXmain1` on `Y` (`limsup_normalizedIdealH0_le`) the `limsup` is at most
`vol (c φ_j|_Y)`.  As `c → 1`, `vol (c φ_j|_Y) → vol (φ_j|_Y)` (`cor:lineardsconv`,
`thm:convdS`; `exists_scaled_sourceIVolume_lt`); `φ_j|_Y` has analytic singularities and is a
Kähler current, so it is `𝓘`-good and `vol (φ_j|_Y) = ∫_Y (θ|_Y + dd^c φ_j|_Y)^m ≤
∫_Y (θ|_Y + ε_j ω|_Y + dd^c φ_j|_Y)^m`; finally, the latter masses converge to the mass of the
trace (`TraceFreeLimit.tendsto_diagonalPotentialMass_traceFreeLimit` and
`ActualTraceFreeNormalizedReader.traceFreeLimit_eq_normalizedTraceAlong`, the definition of the
trace by `d_S`-limits).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Foundations.Analysis.Pending.SubmanifoldIdealRestriction
open SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

/-! ### Forms -/

section Forms

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V]

theorem geometricallyEq_add_right {a b : ClosedRealOneOneForm m V}
    (h : a.val.GeometricallyEq b.val) (c : ClosedRealOneOneForm m V) :
    (a + c).val.GeometricallyEq (b + c).val := by
  intro e z hz
  simp only [ClosedRealOneOneForm.coeff_add]
  rw [h e hz]

theorem geometricallyEq_sub_right {a b : ClosedRealOneOneForm m V}
    (h : a.val.GeometricallyEq b.val) (c : ClosedRealOneOneForm m V) :
    (a - c).val.GeometricallyEq (b - c).val := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact geometricallyEq_add_right h _

/-- A Kähler current for a form geometrically equal to the Chern form is a Kähler current for
the Chern form. -/
theorem isKahlerCurrentPotential_chern_of {L : HermitianHolomorphicLineBundle.{0, 0} m V}
    {hL : IsSourceSmoothHermitianMetric L} {η : ClosedRealOneOneForm m V}
    (hη : (sourceNativeFirstChernForm L hL).val.GeometricallyEq η.val)
    (κ : KahlerBackground m V) {u : V → EReal}
    (hu : IsThetaPshPotential (η - κ.form).val u) :
    IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) u :=
  ⟨κ, ((geometricallyEq_sub_right hη κ.form).thetaPshPotential_iff u).mpr hu⟩

variable [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- For an analytic Kähler current `u` the `𝓘`-volume for the Chern form is the mass of `u` in any
geometrically equal form `η`. -/
theorem sourceIVolume_chernForm_eq_mass_of_analytic (ωV : KahlerBackground m V)
    {L : HermitianHolomorphicLineBundle.{0, 0} m V}
    {hL : IsSourceSmoothHermitianMetric L} {η : ClosedRealOneOneForm m V}
    (hη : (sourceNativeFirstChernForm L hL).val.GeometricallyEq η.val)
    (κ : KahlerBackground m V) {u : V → EReal}
    (hu : IsThetaPshPotential (η - κ.form).val u)
    (hA : HasManifoldAnalyticSingularityType (n := m) u)
    (huθ : (ofFixedModel m V).IsThetaPSH (chernForm L hL) u) (huη : IsThetaPshPotential η.val u) :
    sourceIVolume (chernForm L hL) u huθ = diagonalPotentialMass η u huη := by
  have hcur := isKahlerCurrentPotential_chern_of hη κ hu
  obtain ⟨hu', hpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent ωV L hL hcur
  have hg := SGPT.IGood.LogVolume.sourceIGoodWith_of_analytic ωV hu' hA hpos
  have h := SGPT.IGood.LogVolume.sourceIVolume_eq_mass_of_iGoodWith ωV hu' hg
  have hu₀ : IsThetaPshPotential (sourceNativeFirstChernForm L hL).val u :=
    (hη.thetaPshPotential_iff u).mpr huη
  have key : ∀ (θ₁ : ClosedRealOneOneForm m V) (h₁ : θ₁ = sourceNativeFirstChernForm L hL)
      (hv : IsThetaPshPotential θ₁.val u),
      diagonalPotentialMass θ₁ u hv = diagonalPotentialMass (sourceNativeFirstChernForm L hL) u hu₀ := by
    rintro θ₁ rfl hv
    rfl
  calc sourceIVolume (chernForm L hL) u huθ = sourceIVolume (chernForm L hL) u hu' := rfl
    _ = sourcePotentialNonPluripolarMeasure (chernForm L hL) u hu' univ := h
    _ = diagonalPotentialMass (atlasClosedFormToNative (chernForm L hL)) u
          ((isThetaPSH_iff_nativeThetaPotential _ u).mp hu') := rfl
    _ = diagonalPotentialMass (sourceNativeFirstChernForm L hL) u hu₀ :=
          key _ (sourceNativeAtlasForm_roundTrip _) _
    _ = diagonalPotentialMass η u huη :=
          ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hη hu₀ huη

end Forms

/-! ### Continuity of the volume under scaling `c ↑ 1` -/

section Scaling

variable {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel m) V]
  [IsComplexManifold m V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- If `ψ` and `c₀ψ` (`0 < c₀ < 1`) are `θ`-psh and `θ` is big, then for every `M' > vol θ_ψ` there
is `c ∈ (c₀, 1)` with `cψ` `θ`-psh and `vol θ_{cψ} < M'` (`cor:lineardsconv`, `thm:convdS`). -/
theorem exists_scaled_sourceIVolume_lt (ωV : KahlerBackground m V)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel m V)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {ψ : V → EReal} (hψ : (ofFixedModel m V).IsThetaPSH θ ψ) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hc₀1 : c₀ < 1) (hc₀ψ : (ofFixedModel m V).IsThetaPSH θ (fun y => (c₀ : EReal) * ψ y))
    {M' : ℝ≥0∞} (hM' : sourceIVolume θ ψ hψ < M') :
    ∃ c : ℝ, c₀ < c ∧ c < 1 ∧ ∃ hc : (ofFixedModel m V).IsThetaPSH θ (fun y => (c : EReal) * ψ y),
      sourceIVolume θ _ hc < M' := by
  set u₀ : SourceThetaPotentialL1 θ := ⟨ψ, hψ⟩
  set u₁ : SourceThetaPotentialL1 θ := ⟨fun y => (c₀ : EReal) * ψ y, hc₀ψ⟩
  have ht01 : ∀ i : ℕ, (1 : ℝ) / ((i : ℝ) + 2) ∈ Ioo (0 : ℝ) 1 := fun i => by
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  let t : ℕ → Ioo (0 : ℝ) 1 := fun i => ⟨_, ht01 i⟩
  have ht : Tendsto (fun i => (t i).val) atTop (𝓝 0) := by
    change Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hconv := tendsto_sourceGeneralInterpolation_zero ωV θ hbig u₀ u₁ atTop t ht
  have hvol := (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology_all_mass ωV θ hbig
    atTop _ u₀ hconv).1
  obtain ⟨i, hi⟩ := (hvol.eventually (gt_mem_nhds hM')).exists
  set s := (t i).val with hs
  have hs0 : 0 < s := (t i).property.1
  have hs1 : s < 1 := (t i).property.2
  refine ⟨1 - s * (1 - c₀), by nlinarith, by nlinarith, ?_⟩
  have hinterp : (sourceGeneralInterpolation θ ⟨s, hs0.le, hs1.le⟩ u₀ u₁).val =
      fun y => ((1 - s * (1 - c₀) : ℝ) : EReal) * ψ y := by
    rw [sourceGeneralInterpolation_val]
    funext y
    have h1 : (0 : EReal) ≤ ((1 - s : ℝ) : EReal) := by exact_mod_cast (sub_nonneg.mpr hs1.le)
    have h2 : (0 : EReal) ≤ ((s * c₀ : ℝ) : EReal) := by exact_mod_cast (mul_pos hs0 hc₀).le
    change ((1 - s : ℝ) : EReal) * ψ y + ((s : ℝ) : EReal) * ((c₀ : EReal) * ψ y) = _
    rw [← mul_assoc, ← EReal.coe_mul, ← EReal.right_distrib_of_nonneg h1 h2, ← EReal.coe_add]
    congr 2
    ring
  refine ⟨hinterp ▸ (sourceGeneralInterpolation θ ⟨s, hs0.le, hs1.le⟩ u₀ u₁).property, ?_⟩
  refine lt_of_eq_of_lt ?_ hi
  exact SGPT.IGood.DXLow2.sourceIVolume_congr hinterp.symm _ _

end Scaling

/-! ### Step 1 -/

section Step1

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

/-- `f^*(θ - c ω) = f^*θ - c f^*ω`. -/
theorem pullback_sub_smul {m : ℕ} {V : Type} [TopologicalSpace V]
    [ChartedSpace (ComplexModel m) V] [IsComplexManifold m V] {f : V → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (a b : ClosedRealOneOneForm n X) (t : ℝ) :
    ClosedRealOneOneForm.pullback hf (a - t • b) =
      ClosedRealOneOneForm.pullback hf a - t • ClosedRealOneOneForm.pullback hf b := by
  rw [sub_eq_add_neg, ← neg_smul, NefCoreKahlerCurrent.pullback_add_smul, neg_smul,
    ← sub_eq_add_neg]

/-- **Step 1 of the proof of `thm:rest_volume`, the inequality `limsup ≤`**: if `θ_φ` is a Kähler
current (`θ = c₁(L, h₀)`, `θ + dd^c φ ≥ κ`), `ν(φ, Y) = 0` and `dim Y > 0`, then
`limsup_k m!/k^m h⁰(Y, T|_Y ⊗ L|_Y^k ⊗ Res_Y 𝓘(kφ)) ≤ ∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^m`. -/
theorem limsup_restrictedH0_le_of_kahlerCurrent (hn : n ≠ 0) (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {W : Set X} {m : ℕ} (hW : IsClosedConnectedSubmanifold n W m) (hm : 0 < m)
    {φ : X → EReal} {κ : KahlerBackground n X}
    (hφκ : IsThetaPshPotential (sourceNativeFirstChernForm L hL - κ.form).val φ)
    (hν : sourceGenericLelongNumber (n := n) (Subtype.val : W → X) φ = 0) :
    let hk := le_of_isClosedConnectedSubmanifold hW
    letI : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
    haveI : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
    haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    haveI : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
    letI : MeasurableSpace W := borel W
    haveI : BorelSpace W := ⟨rfl⟩
    limsup (fun k => normalizedIdealH0 (restrictBundle L (submanifoldInclusion hW))
        (restrictBundle T (submanifoldInclusion hW))
        (fun k => restrictIdeal (k := m) (W := W) (sourceDegreeMultiplierIdeal (n := n) k φ)) k)
        atTop ≤
      SGPT.Trace.sourceTraceMass ωb (SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb)
        (contMDiff_val hk hW.2.2) (sourceNativeFirstChernForm L hL) φ := by
  intro hk
  let : ChartedSpace (ComplexModel m) W := chartedSpace hk hW.2.2
  have : IsComplexManifold m W := isComplexManifold_chartedSpace hk hW.2.2
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  have : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  -- notation
  have hι : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) :=
    contMDiff_val hk hW.2.2
  let θ := sourceNativeFirstChernForm L hL
  let ωW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 ωb
  let κW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 κ
  have hωW : ωW.form = ClosedRealOneOneForm.pullback hι ωb.form := rfl
  have hκW : κW.form = ClosedRealOneOneForm.pullback hι κ.form := rfl
  let η := ClosedRealOneOneForm.pullback hι θ
  let ι := submanifoldInclusion hW
  have hLW := restrictBundle_smooth hL ι
  have hTW := restrictBundle_smooth hT ι
  have hgeo : (sourceNativeFirstChernForm (restrictBundle L ι) hLW).val.GeometricallyEq η.val :=
    restrictBundle_chern_geometricallyEq hL ι
  -- the gentle Kähler quasi-equisingular approximation `φ_j`, `θ + dd^c φ_j ≥ κ/4`
  obtain ⟨U, hQ, -, hU4⟩ := SGPT.IGood.DXLow2.exists_gentle_kahler_qea hφκ
  obtain ⟨ω', ε', happ'⟩ := native_of_sourceQuasiEquisingularApproximation hQ
  -- the same approximation with errors `ε_j = 1/(j+1)` for `ωb`
  set ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hεdef
  have hεpos : ∀ j, 0 < ε j := fun j => by positivity
  have hεanti : Antitone ε := fun i j hij => by
    simp only [hεdef]
    gcongr
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hUθ : ∀ j, IsThetaPshPotential θ.val (U j) := fun j =>
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hU4 j) (by
      have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num))
  have happ : IsQuasiEquisingularApproximation ωb θ φ ε U := by
    refine ⟨happ'.target, ⟨fun j => (hεpos j).le, hεanti, hεlim⟩, fun j => ?_,
      happ'.term_hasAnalyticSingularityType, happ'.decreasesPointwise,
      fun c d hc hcd => happ'.eventually_multiplierIdealIncluded hc hcd⟩
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hUθ j) ?_
    have heq : θ + ε j • ωb.form - θ = ε j • ωb.form := by abel
    rw [heq]
    exact KahlerDomination.isSemipositive_smul ωb.isSemipositive (hεpos j).le
  -- the trace is defined
  have hpullκ : (ClosedRealOneOneForm.pullback hι κ.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 κ.form κ.isKahler
  have hpull : (ClosedRealOneOneForm.pullback hι ωb.form).val.IsKahler :=
    SubmanifoldKahlerRestriction.isKahler_pullback hk hW.2.2 ωb.form ωb.isKahler
  have hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωW hι θ φ :=
    SGPT.Trace.hasPositiveSourceTraceAlong_of_kahlerCurrent hk ωb κ ωW hι hpullκ one_pos
      (by rwa [one_smul]) hν
  have hdefinedN := (SGPT.Trace.hasPositiveSourceTraceAlong_iff_native hn ωb ωW hι θ φ).mp hdefined
  -- the restricted stages `ψ_j = φ_j|_Y`
  have hgenN : (⨅ y : W, lelongNumber (n := n) φ y) = 0 :=
    (nativeGeneric_zero_iff_source hn Subtype.val φ).mpr hν
  let ψ : ℕ → W → EReal := fun j y => U j y
  have hψε : ∀ j, IsThetaPshPotential (η + ε j • ωW.form).val (ψ j) := fun j => by
    have h := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happ hι hgenN j
    rwa [NefCoreKahlerCurrent.pullback_add_smul] at h
  have hψanti : ∀ y : W, Antitone fun j => ψ j y := fun y => happ.term_antitone y
  have hψ4 : ∀ j, IsThetaPshPotential (η - (1 / 4 : ℝ) • κW.form).val (ψ j) := fun j => by
    have h := CompactAnalyticPoleLelongGap.isThetaPshPotential_comp_of_analytic_generic_inf_eq_zero
      hι (hU4 j).1 (fun x _ => happ.term_hasAnalyticSingularityType j (complexChartAt (n := n) x)
        ((complexChartAt (n := n) x).val x)
        ((complexChartAt (n := n) x).val.map_source (mem_complexChartAt_source x)))
      (AnalyticQuasiEquisingularRestriction.term_generic_lelong_inf_eq_zero happ Subtype.val hgenN j)
    rwa [pullback_sub_smul] at h
  have hψA : ∀ j, HasManifoldAnalyticSingularityType (n := m) (ψ j) := fun j =>
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι
      (happ.term_hasAnalyticSingularityType j)
  have hψη : ∀ j, IsThetaPshPotential η.val (ψ j) := fun j =>
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hψ4 j) (by
      have heq : η - (η - (1 / 4 : ℝ) • κW.form) = (1 / 4 : ℝ) • κW.form := by abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κW.isSemipositive (by norm_num))
  have hψθ' : ∀ j, (ofFixedModel m W).IsThetaPSH (chernForm (restrictBundle L ι) hLW) (ψ j) :=
    fun j => (isThetaPSH_chernForm_iff hgeo _).mpr (hψη j)
  -- the scaled stages `c ψ_j` are Kähler currents for `c ∈ [c₀, 1)`
  obtain ⟨A, hA0, hA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κW η
  set t₀ : ℝ := 1 / (2 * (1 + 4 * A)) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀small : t₀ * (1 + 4 * A) = 1 / 2 := by rw [ht₀]; field_simp
  set c₀ : ℝ := 1 - t₀ with hc₀
  have hc₀1 : c₀ < 1 := by linarith
  have hc₀0 : 0 < c₀ := by
    have : t₀ ≤ 1 / 2 := by nlinarith
    linarith
  have hscaled : ∀ j (c : ℝ), c₀ ≤ c → c < 1 →
      IsThetaPshPotential (η - (1 / 8 : ℝ) • κW.form).val (fun y => (c : EReal) * ψ j y) := by
    intro j c hc hc1
    have hc0 : 0 < c := lt_of_lt_of_le hc₀0 hc
    have hwc := RestrictedApproximantComparison.isThetaPshPotential_smul (hψ4 j) hc0
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hwc ?_
    have heq : η - (1 / 8 : ℝ) • κW.form - c • (η - (1 / 4 : ℝ) • κW.form) =
        (1 - c) • (η + A • κW.form) + (c / 4 - 1 / 8 - (1 - c) * A) • κW.form := by module
    rw [heq]
    refine UniformPerturbedKahlerLowerBound.isSemipositive_add
      (KahlerDomination.isSemipositive_smul hA (by linarith))
      (KahlerDomination.isSemipositive_smul κW.isSemipositive ?_)
    have h1 : 1 - c ≤ t₀ := by linarith
    nlinarith
  let κ8 : KahlerBackground m W := KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 8) κW
  have hψ₀ : IsKahlerCurrentPotential (sourceNativeFirstChernForm (restrictBundle L ι) hLW)
      (fun y => (c₀ : EReal) * ψ 0 y) :=
    isKahlerCurrentPotential_chern_of hgeo κ8 (hscaled 0 c₀ le_rfl hc₀1)
  -- bigness of `θ|_Y`
  obtain ⟨hψ₀θ', hψ₀pos⟩ := isThetaPSH_and_pos_of_kahlerCurrent ωW _ hLW hψ₀
  have hbig := sourcePositiveMass_isBig ωW hψ₀θ' hψ₀pos
  -- the masses of the stages converge to the mass of the trace
  have hlimit := TraceFreeLimit.tendsto_diagonalPotentialMass_traceFreeLimit hm ωW hεpos hεanti
    hεlim hψε hψanti
  have htf := ActualTraceFreeNormalizedReader.traceFreeLimit_eq_normalizedTraceAlong ωb ωW hι hpull
    θ hdefinedN happ hεpos
  have hmassTr : SGPT.Trace.sourceTraceMass ωb ωW hι θ φ =
      diagonalPotentialMass η (TraceFreeLimit.traceFreeLimit η ωW.form ε ψ)
        (TraceFreeLimit.isThetaPshPotential_traceFreeLimit ωW hεanti hεlim hψε hψanti) := by
    rw [SGPT.Trace.sourceTraceMass_eq_numericalTraceMass hk hn]
    unfold NumericalTraceMass.numericalTraceMass
    rw [dif_pos hdefinedN]
    have key : ∀ (a b : W → EReal) (_ : a = b) (ha : IsThetaPshPotential η.val a)
        (hb : IsThetaPshPotential η.val b),
        diagonalPotentialMass η a ha = diagonalPotentialMass η b hb := by
      rintro a b rfl ha hb
      rfl
    exact key _ _ htf.symm _ _
  rw [← hmassTr] at hlimit
  -- the core upper bound on `Y`
  refine limsup_normalizedIdealH0_le ωW hLW hTW hψ₀ (fun M' hM' => ?_)
  obtain ⟨j, hj⟩ := (hlimit.eventually (gt_mem_nhds hM')).exists
  have hvolj : sourceIVolume (chernForm (restrictBundle L ι) hLW) (ψ j) (hψθ' j) < M' := by
    let κ4 : KahlerBackground m W := KahlerBackground.smul (by norm_num : (0 : ℝ) < 1 / 4) κW
    rw [sourceIVolume_chernForm_eq_mass_of_analytic ωW hgeo κ4 (hψ4 j) (hψA j) (hψθ' j)
      (hψη j)]
    exact lt_of_le_of_lt (AmbientMassBackgroundMonotone.diagonalPotentialMass_le_add_smul ωW.isSemipositive
      (hεpos j) (hψη j) (hψε j)) hj
  have hc₀ψ : (ofFixedModel m W).IsThetaPSH (chernForm (restrictBundle L ι) hLW)
      (fun y => (c₀ : EReal) * ψ j y) :=
    (isThetaPSH_chernForm_iff hgeo _).mpr
      (SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hscaled j c₀ le_rfl hc₀1) (by
        have heq : η - (η - (1 / 8 : ℝ) • κW.form) = (1 / 8 : ℝ) • κW.form := by abel
        rw [heq]
        exact KahlerDomination.isSemipositive_smul κW.isSemipositive (by norm_num)))
  obtain ⟨c, hcc₀, hc1, hcψ, hvol⟩ :=
    exists_scaled_sourceIVolume_lt ωW hbig (hψθ' j) hc₀0 hc₀1 hc₀ψ hvolj
  refine ⟨_, hcψ, hvol, ?_⟩
  have hφU : φ ≤ U j := fun x => (happ.term_antitone x).le_of_tendsto (happ.term_tendsto x) j
  exact eventually_restrictIdeal_le_scaled hι hφU (hUθ j).1.quasiPlurisubharmonic
    (happ.term_hasAnalyticSingularityType j) (hψη j).1.quasiPlurisubharmonic
    (lt_trans hc₀0 hcc₀) hc1

end Step1

end SGPT.Trace.RestVol
