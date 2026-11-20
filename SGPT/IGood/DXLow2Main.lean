import SGPT.IGood.DXLow2Count
import SGPT.IGood.DXLow2Aux
import SGPT.IGood.DXLowBridge
import SGPT.Bergman.Quant3MainKahcurr
import SGPT.PSH.GlobalL2SectionsPosMass
import SGPT.PSH.SourceSingularityGeneralInterpolation
import SGPT.PSH.SourceGeneralMixedIVolumeContinuity
import SGPT.NAPotential.Homogeneous

/-!
# The lower bound of the asymptotic Riemann–Roch formula for every Kähler current

Blueprint `claude-dx-low2`, nodes `claude-dx-low2:scaled` and `claude-dx-low2:main`. Source
`thm:DXmain1` (chapter *`𝓘`-good singularities*), Step 1 of the book's proof, the inequality `≥`:
for a Hermitian holomorphic line bundle `(L, h)` with smooth metric on a connected compact Kähler
manifold `X` of dimension `n > 0`, `θ = c₁(L, h)`, a Hermitian holomorphic line bundle `(T, h_T)`
and `φ ∈ PSH(X, θ)` such that `θ_φ` is a Kähler current,

`vol θ_φ ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`

(`riemannRochLowerBound_of_kahlerCurrent`; its type is literally
`SGPT.Bergman.Quant2.RiemannRochLowerBound (chernForm L hL) L T φ`).

## Proof (the book's Step 1, with the potential `c φ_j`, `c = N/(N-1)`, in place of the bundle
`L^{N-1}` with weight `N φ_j`)

Let `P = P_θ[φ]_𝓘`, so `vol θ_φ = ∫ θ_Pⁿ > 0` and `𝓘(kP) = 𝓘(kφ)`. Fix `N` large and put
`c = N/(N-1)`. Take a quasi-equisingular approximation `(φ_j)` of `φ` by potentials with gentle
analytic singularities and `θ_{φ_j} ≥ κ/4` (`exists_gentle_kahler_qea`); with
`V_j = P_θ[φ_j]_𝓘`, `∫ θ_{V_j}ⁿ = vol θ_{φ_j} → vol θ_φ`. For `j` large, `lma:pathoenvelope`
gives `η ∈ PSH(X, θ)_{>0}` with `N⁻¹ η + (1 - N⁻¹) V_j ≤ P` and `η ≤ P`. Write `k = m + b`
with `m = ⌊k(N-1)/N⌋`. By `lma:existsecposmass` there is `0 ≠ s ∈ H⁰(X, L^b ⊗ 𝓘(bη))`, by
`lma:IandIinf` every `t ∈ H⁰(X, L^m ⊗ T ⊗ 𝓘(m c φ_j))` satisfies `|t|² ≲ e^{m φ_j}`, and
`m φ_j + b η ≤ k P + const`; multiplication by `s` gives (`finrank_le_of_mul`)

`h⁰(L^m ⊗ T ⊗ 𝓘(m c φ_j)) ≤ h⁰(L^k ⊗ T ⊗ 𝓘(kP)) ≤ h⁰(L^k ⊗ T ⊗ 𝓘(kφ))`.

The potential `c φ_j` is smooth off its poles and `θ_{cφ_j}` is a Kähler current, so lane
DX-LOW's `diagonalPotentialMass_le_liminf_finrank` gives
`liminf_m n!/mⁿ h⁰(L^m ⊗ T ⊗ 𝓘(m c φ_j)) ≥ ∫ θ_{cφ_j}ⁿ = vol θ_{cφ_j} ≥ vol θ_{cφ}`. Hence

`liminf_k n!/kⁿ h⁰(L^k ⊗ T ⊗ 𝓘(kφ)) ≥ ((N-2)/N)ⁿ vol θ_{cφ}` (`le_liminf_normalizedH0_scaled`).

Finally `cφ = (1 - t) φ + t (Rφ)` with `t → 0` as `N → ∞`, so `vol θ_{cφ} → vol θ_φ`
(`cor:lineardsconv`, `thm:contvolu`). The book instead applies `prop:DXmainanalytic` to
`L^{N-1}` with the weight `N φ_j` and bounds `∫((1-N⁻¹)θ + dd^c φ_j)ⁿ ≥ ∫ θ_{φ_j}ⁿ - C/N`; the
rescaled potential `c φ_j` avoids both the powers of `L` and the mixed-mass estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.DXLow2

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.IGood.LogVolume
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-- `vol θ_u` depends only on the function `u`. -/
theorem sourceIVolume_congr {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u v : X → EReal}
    (h : u = v) (hu : (ofFixedModel n X).IsThetaPSH θ u) (hv : (ofFixedModel n X).IsThetaPSH θ v) :
    sourceIVolume θ u hu = sourceIVolume θ v hv := by
  subst h; rfl

/-- The rational scaling factor `c_N = (N₂ + 2)/(N₂ + 1)`, i.e. `N/(N-1)` for `N = N₂ + 2`. -/
def scaleFactor (N₂ : ℕ) : ℚ := ((N₂ : ℚ) + 2) / ((N₂ : ℚ) + 1)

theorem scaleFactor_real (N₂ : ℕ) :
    ((scaleFactor N₂ : ℚ) : ℝ) = ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) := by
  simp [scaleFactor]

theorem one_lt_scaleFactor (N₂ : ℕ) : (1 : ℝ) < ((scaleFactor N₂ : ℚ) : ℝ) := by
  rw [scaleFactor_real, one_lt_div (by positivity)]
  linarith

/-- The `c`-multiple `c · u` of a potential. -/
abbrev scaled (c : ℝ) (u : X → EReal) : X → EReal := fun x => (c : EReal) * u x

/-- The elementary counting inequality:
`(N₂/(N₂+2))ⁿ · n!/mⁿ · h ≤ n!/kⁿ · H` when `N₂ k ≤ (N₂+2) m` and `h ≤ H`. -/
theorem ofReal_ratio_mul_le {m k h H N₂ : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmk : N₂ * k ≤ (N₂ + 2) * m) (hhH : h ≤ H) :
    ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ n) *
        (ENNReal.ofReal ((n.factorial : ℝ) / (m : ℝ) ^ n) * (h : ℝ≥0∞)) ≤
      ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n * H) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmk' : (N₂ : ℝ) * k ≤ ((N₂ : ℝ) + 2) * m := by exact_mod_cast hmk
  have hhH' : (h : ℝ) ≤ H := by exact_mod_cast hhH
  have hratio : (N₂ : ℝ) / ((N₂ + 2) * m) ≤ 1 / k := by
    rw [div_le_div_iff₀ (by positivity) hk']
    linarith
  have hpow : ((N₂ : ℝ) / ((N₂ + 2) * m)) ^ n ≤ (1 / (k : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hratio n
  have e1 : ((N₂ : ℝ) / (N₂ + 2)) ^ n * ((n.factorial : ℝ) / (m : ℝ) ^ n * h) =
      (n.factorial : ℝ) * h * ((N₂ : ℝ) / ((N₂ + 2) * m)) ^ n := by
    rw [div_pow, div_pow, mul_pow]; field_simp
  have e2 : (n.factorial : ℝ) / (k : ℝ) ^ n * H = (n.factorial : ℝ) * H * (1 / (k : ℝ)) ^ n := by
    rw [div_pow, one_pow]; field_simp
  rw [e1, e2]
  have hf : (0 : ℝ) ≤ n.factorial := by positivity
  calc (n.factorial : ℝ) * h * ((N₂ : ℝ) / ((N₂ + 2) * m)) ^ n
      ≤ (n.factorial : ℝ) * H * ((N₂ : ℝ) / ((N₂ + 2) * m)) ^ n := by gcongr
    _ ≤ (n.factorial : ℝ) * H * (1 / (k : ℝ)) ^ n := by gcongr

/-- The degree `m(k) = ⌊k (N₂+1)/(N₂+2)⌋` tends to infinity. -/
theorem tendsto_degree (N₂ : ℕ) :
    Tendsto (fun k : ℕ => k * (N₂ + 1) / (N₂ + 2)) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun B => ⟨B * (N₂ + 2), fun k hk => ?_⟩
  rw [Nat.le_div_iff_mul_le (by positivity)]
  nlinarith

/-- **The scaled lower bound** (blueprint `claude-dx-low2:scaled`): for a Kähler current
`θ + dd^c φ ≥ κ`, `θ ≤ A κ`, `N₂ > 4A` and `c = (N₂+2)/(N₂+1)`,
`(N₂/(N₂+2))ⁿ · vol θ_{cφ} ≤ liminf_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
theorem le_liminf_normalizedH0_scaled (hn : 0 < n)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (κ : KahlerBackground n X) {φ : X → EReal}
    (hφκ : IsThetaPshPotential (sourceNativeFirstChernForm L hL - κ.form).val φ)
    {A : ℝ} (hA : (-sourceNativeFirstChernForm L hL + A • κ.form).val.IsSemipositive)
    {N₂ : ℕ} (hN : 4 * A < N₂)
    (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ)
    (hcφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (scaled (scaleFactor N₂) φ)) :
    ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ n) *
        sourceIVolume (chernForm L hL) (scaled (scaleFactor N₂) φ) hcφ ≤
      liminf (fun k => normalizedH0 L T φ k) atTop := by
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set θ' := chernForm L hL with hθ'def
  have hrt : atlasClosedFormToNative θ' = θ := sourceNativeAtlasForm_roundTrip θ
  set c : ℝ := ((scaleFactor N₂ : ℚ) : ℝ) with hcdef
  have hc1 : 1 < c := one_lt_scaleFactor N₂
  have hc0 : 0 < c := by linarith
  have hcR : c = ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) := scaleFactor_real N₂
  have hN0 : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
  have hNR : (1 : ℝ) < (N₂ : ℝ) + 2 := by linarith
  -- positivity of the mass
  have hcur : IsKahlerCurrentPotential θ φ := ⟨κ, hφκ⟩
  obtain ⟨hφ0, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent κ L hL hcur
  -- native/atlas conversions
  have toNative : ∀ {u : X → EReal}, (ofFixedModel n X).IsThetaPSH θ' u →
      IsThetaPshPotential θ.val u := fun h => by
    have := (isThetaPSH_iff_nativeThetaPotential θ' _).mp h
    rwa [hrt] at this
  have toAtlas : ∀ {u : X → EReal}, IsThetaPshPotential θ.val u →
      (ofFixedModel n X).IsThetaPSH θ' u := fun h =>
    (isThetaPSH_iff_nativeThetaPotential θ' _).mpr (by rw [hrt]; exact h)
  -- the gentle Kähler quasi-equisingular approximation
  obtain ⟨U, hQ, hgentle, hU4⟩ := exists_gentle_kahler_qea hφκ
  have hUθ : ∀ j, IsThetaPshPotential θ.val (U j) := fun j =>
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le (hU4 j) (by
      have heq : θ - (θ - (1 / 4 : ℝ) • κ.form) = (1 / 4 : ℝ) • κ.form := by abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive (by norm_num))
  have hU' : ∀ j, (ofFixedModel n X).IsThetaPSH θ' (U j) := fun j => toAtlas (hUθ j)
  have hQ' : SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ') φ U := by
    rw [hrt]; exact hQ
  -- the envelopes `P = P_θ[φ]_𝓘` and `V_j = P_θ[φ_j]_𝓘`
  set P := sourceIEnvelope θ' φ with hPdef
  have hP : (ofFixedModel n X).IsThetaPSH θ' P := isThetaPSH_sourceIEnvelope hφ
  have hPpos : 0 < sourcePotentialNonPluripolarMeasure θ' P hP univ :=
    SGPT.Bergman.Quant3.sourceIEnvelope_pos κ hφ hφpos
  have hV : ∀ j, (ofFixedModel n X).IsThetaPSH θ' (sourceIEnvelope θ' (U j)) := fun j =>
    isThetaPSH_sourceIEnvelope (hU' j)
  have hPV : ∀ j, P ≤ sourceIEnvelope θ' (U j) := fun j =>
    sourceIEnvelope_mono_of_singularityLE hφ (hU' j)
      (SGPT.Okounkov.PartialBody.le_of_sourceQuasiEquisingularApproximation hQ j)
  have hPVs : ∀ j, SingularityLE P (sourceIEnvelope θ' (U j)) := fun j =>
    (singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by simpa using hPV j x⟩
  -- `vol θ_{φ_j} → vol θ_φ`; choose `j` with an admissible coefficient `N₂ + 2`
  have hlim := SGPT.Bergman.Quant3.qea_sourceIVolume_tendsto κ hφ hφpos hQ' hU'
  have hfinP : sourcePotentialNonPluripolarMeasure θ' P hP univ ≠ ⊤ :=
    (@measure_lt_top _ _ _ (SGPT.Bergman.PartialEnergyDifferentiability.sourcePotentialMeasure_finite κ hP)
      univ).ne
  have hfinV : ∀ j, sourcePotentialNonPluripolarMeasure θ' (sourceIEnvelope θ' (U j)) (hV j) univ
      ≠ ⊤ := fun j =>
    (@measure_lt_top _ _ _
      (SGPT.Bergman.PartialEnergyDifferentiability.sourcePotentialMeasure_finite κ (hV j)) univ).ne
  have hreal := (ENNReal.tendsto_toReal hfinP).comp hlim
  have hgap : 0 < (sourcePotentialNonPluripolarMeasure θ' P hP univ).toReal /
      ((N₂ : ℝ) + 2) ^ n :=
    div_pos (ENNReal.toReal_pos hPpos.ne' hfinP) (by positivity)
  obtain ⟨j, hj⟩ := (hreal.eventually (gt_mem_nhds (lt_add_of_pos_right _ hgap))).exists
  have hmono : sourcePotentialNonPluripolarMeasure θ' P hP univ ≤
      sourcePotentialNonPluripolarMeasure θ' (sourceIEnvelope θ' (U j)) (hV j) univ :=
    sourcePotentialNonPluripolarMass_mono κ hP (hV j) (hPVs j)
  have ha : SourceAffineCoefficient n (sourcePotentialNonPluripolarMeasure θ' P hP univ)
      (sourcePotentialNonPluripolarMeasure θ' (sourceIEnvelope θ' (U j)) (hV j) univ)
      ((N₂ : ℝ) + 2) := by
    refine sourceAffineCoefficient_of_close hNR hPpos hmono (hfinV j) ?_
    have : (sourcePotentialNonPluripolarMeasure θ' (sourceIEnvelope θ' (U j)) (hV j) univ).toReal <
        (sourcePotentialNonPluripolarMeasure θ' P hP univ).toReal +
          (sourcePotentialNonPluripolarMeasure θ' P hP univ).toReal / ((N₂ : ℝ) + 2) ^ n := hj
    linarith
  -- `lma:pathoenvelope`: `η` with `N⁻¹ η + (1 - N⁻¹) V_j ≤ P` and `η ≤ P`
  obtain ⟨hE, hEpos, hbar, -⟩ := sourcePositiveAffineEnvelope κ hP (hV j) (hPVs j) hPpos ha
  set η := sourceRelativeEnvelope θ' (fun _ => ⊤)
    (convexComb ((N₂ : ℝ) + 2) P (sourceIEnvelope θ' (U j))) with hηdef
  have hηP : η ≤ P := sourceAffineBarrier_le_left hP hE (hPV j)
    (inv_pos.mpr (by linarith)) (inv_lt_one_of_one_lt₀ hNR) hbar
  -- `lma:existsecposmass` for `η`
  obtain ⟨k₀, hk₀, hsec⟩ := SGPT.PSH.GlobalL2.existsecposmass κ L hL θ'
    ⟨θ, sourceNativeFirstChernForm_isOwn L hL, by rw [hrt]⟩ hE hEpos
  -- the analytic type of `φ_j` and `lma:IandIinf`
  obtain ⟨cg, 𝔞, hg⟩ := hgentle j
  have hman : HasManifoldAnalyticSingularityType (n := n) (U j) :=
    hg.2.1.hasManifoldAnalyticSingularityType
  have hUan : (ofFixedModel n X).HasRationalAnalyticChartType (U j) := hman
  obtain ⟨s₀, -, hIinf⟩ :=
    SGPT.PSH.MultiplierIdealInf.exists_multiplierIdeal_le_inftyIdeal hUan
      (show (0 : ℝ) < c - 1 by linarith)
  -- `φ_j ≤ V_j + C`
  obtain ⟨C₁, hC₁⟩ := (singularityLE_iff_exists_real _ _).mp
    (sourceSingularityLE_sourceIEnvelope (hU' j))
  set C : ℝ := max C₁ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hC : ∀ x, U j x ≤ sourceIEnvelope θ' (U j) x + (C : EReal) := fun x =>
    (hC₁ x).trans (add_le_add_right (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) _)
  -- the potential `w = c φ_j`: smooth off its poles, `θ_w ≥ δ' κ`
  set w : X → EReal := scaled c (U j) with hwdef
  set δ' : ℝ := c / 4 - (c - 1) * A with hδ'def
  have hδ' : 0 < δ' := by
    have hN1 : (0 : ℝ) < N₂ + 1 := by positivity
    have : c - 1 = 1 / ((N₂ : ℝ) + 1) := by rw [hcR]; field_simp; ring
    rw [hδ'def, this, hcR]
    rw [show ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) / 4 - 1 / ((N₂ : ℝ) + 1) * A =
      ((N₂ : ℝ) + 2 - 4 * A) / (4 * ((N₂ : ℝ) + 1)) by field_simp]
    apply div_pos <;> linarith
  have hwc : IsThetaPshPotential (c • (θ - (1 / 4 : ℝ) • κ.form)).val w :=
    RestrictedApproximantComparison.isThetaPshPotential_smul (hU4 j) hc0
  have hwδ : IsThetaPshPotential (θ - δ' • κ.form).val w := by
    refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hwc ?_
    have heq : θ - δ' • κ.form - c • (θ - (1 / 4 : ℝ) • κ.form) =
        (c - 1) • (-θ + A • κ.form) := by rw [hδ'def]; module
    rw [heq]
    exact KahlerDomination.isSemipositive_smul hA (by linarith)
  have hwθ : IsThetaPshPotential θ.val w :=
    SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le hwδ (by
      have heq : θ - (θ - δ' • κ.form) = δ' • κ.form := by abel
      rw [heq]
      exact KahlerDomination.isSemipositive_smul κ.isSemipositive hδ'.le)
  have hw' : (ofFixedModel n X).IsThetaPSH θ' w := toAtlas hwθ
  have hsm : SmoothOffPoleSet (n := n) w := smoothOffPoleSet_const_mul (smoothOffPoleSet_of_gentle hg) hc0
  -- the lower bound for `w`
  have hDX := SGPT.IGood.DXLow.diagonalPotentialMass_le_liminf_finrank hn κ
    (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume κ) hL hT
    (sourceNativeFirstChernForm_isOwn L hL) hδ' hwδ hwθ hsm
  -- `vol θ_{cφ} ≤ vol θ_w = ∫ θ_wⁿ`
  have hwmass : sourcePotentialNonPluripolarMeasure θ' w hw' univ = diagonalPotentialMass θ w hwθ := by
    change diagonalPotentialMass (atlasClosedFormToNative θ') w _ = _
    exact SGPT.Okounkov.TranscendentalVolumeConcavity.diagonalPotentialMass_congr hrt rfl _ _
  have hwcur : IsKahlerCurrentPotential θ w :=
    ⟨KahlerBackground.smul hδ' κ, by rw [KahlerBackground.smul_form]; exact hwδ⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  have hwpos : 0 < sourcePotentialNonPluripolarMeasure θ' w hw' univ := by
    rw [hwmass]
    exact SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hwcur hwθ
  have hAw : HasManifoldAnalyticSingularityType (n := m' + 1) w :=
    SGPT.Okounkov.TranscendentalCore.hasManifoldAnalyticSingularityType_nonneg_rat_smul hman
      (show (0 : ℚ) ≤ scaleFactor N₂ by unfold scaleFactor; positivity)
  have hvolw : sourceIVolume θ' w hw' = diagonalPotentialMass θ w hwθ := by
    rw [sourceIVolume_eq_mass_of_iGoodWith κ hw' (sourceIGoodWith_of_analytic κ hw' hAw hwpos),
      hwmass]
  have hsing : SingularityLE (scaled c φ) w := by
    obtain ⟨C₀, hC₀⟩ := (singularityLE_iff_exists_real _ _).mp
      (SGPT.Okounkov.PartialBody.le_of_sourceQuasiEquisingularApproximation hQ j)
    refine (singularityLE_iff_exists_real _ _).mpr ⟨c * C₀, fun x => ?_⟩
    calc (c : EReal) * φ x ≤ (c : EReal) * (U j x + (C₀ : EReal)) :=
          mul_le_mul_of_nonneg_left (hC₀ x) (by exact_mod_cast hc0.le)
      _ = (c : EReal) * U j x + ((c * C₀ : ℝ) : EReal) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hc0.le)
            (EReal.coe_ne_top _), EReal.coe_mul]
  have hvolle : sourceIVolume θ' (scaled c φ) hcφ ≤ diagonalPotentialMass θ w hwθ := by
    rw [← hvolw]
    exact sourcePotentialNonPluripolarMass_mono κ (isThetaPSH_sourceIEnvelope hcφ)
      (isThetaPSH_sourceIEnvelope hw')
      ((singularityLE_iff_exists_real _ _).mpr ⟨0, fun x => by
        simpa using sourceIEnvelope_mono_of_singularityLE hcφ hw' hsing x⟩)
  -- the counting `h⁰(L^m ⊗ T ⊗ 𝓘(m w)) ≤ h⁰(L^k ⊗ T ⊗ 𝓘(kP)) ≤ h⁰(L^k ⊗ T ⊗ 𝓘(kφ))`
  set M : ℕ → ℕ := fun k => k * (N₂ + 1) / (N₂ + 2) with hMdef
  have hM : Tendsto M atTop atTop := tendsto_degree N₂
  have hηq : IsGlobalQuasiPshPotential (n := m' + 1) η := (toNative hE).quasiPshPotential
  have hPq : IsGlobalQuasiPshPotential (n := m' + 1) P := (toNative hP).quasiPshPotential
  have hwq : IsGlobalQuasiPshPotential (n := m' + 1) (fun x => (c : EReal) * U j x) :=
    hwθ.quasiPshPotential
  have hUtop : ∀ x, U j x ≠ ⊤ := fun x => (hUθ j).quasiPshPotential.1.ne_top x
  have hIord : sourceIOrder (ofFixedModel (m' + 1) X) P φ := (sourceIEquivalent_iEnvelope hφ).2
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume κ
  have hev : ∀ᶠ k in atTop, ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) *
      (ENNReal.ofReal (((m' + 1).factorial : ℝ) / (M k : ℝ) ^ (m' + 1)) *
        (Module.finrank ℂ (LiteralTwistedMultiplierSections L T (M k) w) : ℝ≥0∞)) ≤
      normalizedH0 L T φ k := by
    have h1 : ∀ᶠ k in atTop, s₀ ≤ (M k : ℝ) :=
      (tendsto_natCast_atTop_atTop.comp hM).eventually_ge_atTop s₀
    have h2 : ∀ᶠ k in atTop, 1 ≤ M k := hM.eventually_ge_atTop 1
    have h3 : ∀ᶠ k in atTop, (k₀ + 1) * (N₂ + 2) ≤ k := eventually_ge_atTop _
    filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
    have hMk : M k * (N₂ + 2) ≤ k * (N₂ + 1) := Nat.div_mul_le_self _ _
    have hMk' : k * (N₂ + 1) < M k * (N₂ + 2) + (N₂ + 2) := Nat.lt_div_mul_add (by positivity)
    have hsum : M k + k₀ + 1 ≤ k := by
      have : (M k + k₀ + 1) * (N₂ + 2) ≤ k * (N₂ + 2) := by nlinarith
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    set p : ℕ := k - M k - 1 with hpdef
    have hkp : M k + p + 1 = k := by omega
    have hpk : k₀ ≤ p + 1 := by omega
    have hk0 : 0 < k := by omega
    -- a non-zero section `s ∈ H⁰(X, L^{p+1} ⊗ 𝓘((p+1)η))`
    have := hsec (p + 1) hpk
    obtain ⟨s', hs'⟩ := exists_ne (0 : LiteralTwistedMultiplierSections L unit (p + 1) η)
    set s := (literalTwistedMultiplierSectionEquiv L unit (p + 1) η s').val with hsdef
    have hsmem := (literalTwistedMultiplierSectionEquiv L unit (p + 1) η s').property
    have hs0 : s ≠ 0 := by
      intro h0
      apply hs'
      apply (literalTwistedMultiplierSectionEquiv L unit (p + 1) η).injective
      rw [map_zero]
      exact Subtype.ext h0
    -- `𝓘(m c φ_j) ⊆ 𝓘_∞(m φ_j)`
    have hle : (multiplierIdeal (n := m' + 1) 1
        (fun x => (((M k : ℝ) * c : ℝ) : EReal) * U j x)).Le
        (SGPT.PSH.inftyIdeal (n := m' + 1) (fun x => ((M k : ℝ) : EReal) * U j x)) := by
      have := hIinf (M k) hk1
      rwa [add_sub_cancel] at this
    -- `m φ_j + (p+1) η ≤ k P + m C`
    have hineq : ∀ x, ((M k : ℝ) : EReal) * U j x + (((p + 1 : ℕ) : ℝ) : EReal) * η x ≤
        (((M k + p + 1 : ℕ) : ℝ) : EReal) * P x + (((M k : ℝ) * C : ℝ) : EReal) := by
      intro x
      have hbc : (M k : ℝ) / ((N₂ : ℝ) + 2 - 1) ≤ ((p + 1 : ℕ) : ℝ) := by
        have hc1 : ((M k : ℕ) : ℝ) * ((N₂ : ℝ) + 2) ≤ (k : ℝ) * ((N₂ : ℝ) + 1) := by
          exact_mod_cast hMk
        have hc2 : (((p + 1 : ℕ) : ℝ)) + (M k : ℝ) = (k : ℝ) := by
          have : p + 1 + M k = k := by omega
          exact_mod_cast this
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have hconv := ereal_convex_ineq hNR (hbar x) (hηP x) (Nat.cast_nonneg (M k)) hbc
      have hU : ((M k : ℝ) : EReal) * U j x ≤ ((M k : ℝ) : EReal) * sourceIEnvelope θ' (U j) x +
          (((M k : ℝ) * C : ℝ) : EReal) := by
        calc ((M k : ℝ) : EReal) * U j x
            ≤ ((M k : ℝ) : EReal) * (sourceIEnvelope θ' (U j) x + (C : EReal)) :=
              mul_le_mul_of_nonneg_left (hC x) (by exact_mod_cast (Nat.cast_nonneg (M k)))
          _ = _ := by
              rw [EReal.left_distrib_of_nonneg_of_ne_top
                (by exact_mod_cast (Nat.cast_nonneg (M k))) (EReal.coe_ne_top _), EReal.coe_mul]
      calc ((M k : ℝ) : EReal) * U j x + (((p + 1 : ℕ) : ℝ) : EReal) * η x
          ≤ (((M k : ℝ) : EReal) * sourceIEnvelope θ' (U j) x + (((M k : ℝ) * C : ℝ) : EReal)) +
              (((p + 1 : ℕ) : ℝ) : EReal) * η x := add_le_add_left hU _
        _ = (((M k : ℝ) : EReal) * sourceIEnvelope θ' (U j) x +
              (((p + 1 : ℕ) : ℝ) : EReal) * η x) + (((M k : ℝ) * C : ℝ) : EReal) :=
              add_right_comm _ _ _
        _ ≤ (((M k : ℝ) + ((p + 1 : ℕ) : ℝ) : ℝ) : EReal) * P x + (((M k : ℝ) * C : ℝ) : EReal) :=
              add_le_add_left hconv _
        _ = _ := by
              rw [show ((M k : ℝ) + ((p + 1 : ℕ) : ℝ)) = ((M k + p + 1 : ℕ) : ℝ) by push_cast; ring]
    have hcount := finrank_le_of_mul (L := L) (T := T) hμ (p := p) (m := M k) hwq hUtop hηq hPq hle
      hineq hs0 hsmem
    rw [hkp] at hcount
    have hIfin : Module.finrank ℂ (LiteralTwistedMultiplierSections L T k P) ≤
        Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) := by
      let := literalTwistedMultiplierSections_finiteDimensional L T k φ
      exact LinearMap.finrank_le_finrank_of_injective
        (SGPT.Bergman.IdealOrderMonotonicity.originalGammaIOrderInclusion_injective L T hIord k hk0)
    have hmk : N₂ * k ≤ (N₂ + 2) * M k := by nlinarith
    exact ofReal_ratio_mul_le (by omega) hk0 hmk (hcount.trans hIfin)
  -- the `liminf`
  calc ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) * sourceIVolume θ' (scaled c φ) hcφ
      ≤ ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) * diagonalPotentialMass θ w hwθ := by
        gcongr
    _ ≤ ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) *
          liminf (fun k : ℕ => ENNReal.ofReal (((m' + 1).factorial : ℝ) / (k : ℝ) ^ (m' + 1)) *
            (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k w) : ℝ≥0∞)) atTop := by
        gcongr
    _ ≤ ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) *
          liminf (fun k : ℕ => ENNReal.ofReal (((m' + 1).factorial : ℝ) / (M k : ℝ) ^ (m' + 1)) *
            (Module.finrank ℂ (LiteralTwistedMultiplierSections L T (M k) w) : ℝ≥0∞)) atTop := by
        gcongr
        exact hM.liminf_le_liminf_comp (u := fun k : ℕ =>
          ENNReal.ofReal (((m' + 1).factorial : ℝ) / (k : ℝ) ^ (m' + 1)) *
            (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k w) : ℝ≥0∞))
    _ = liminf (fun k => ENNReal.ofReal (((N₂ : ℝ) / (N₂ + 2)) ^ (m' + 1)) *
          (ENNReal.ofReal (((m' + 1).factorial : ℝ) / (M k : ℝ) ^ (m' + 1)) *
            (Module.finrank ℂ (LiteralTwistedMultiplierSections L T (M k) w) : ℝ≥0∞))) atTop :=
        (ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top).symm
    _ ≤ liminf (fun k => normalizedH0 L T φ k) atTop := liminf_le_liminf hev

/-- `c φ` is `θ`-psh for `c = (N₂+2)/(N₂+1)` when `θ + dd^c φ ≥ κ`, `θ ≤ A κ` and `A ≤ N₂ + 2`. -/
theorem isThetaPshPotential_scaled {θ : ClosedRealOneOneForm n X} {κ : KahlerBackground n X}
    {φ : X → EReal} (hφκ : IsThetaPshPotential (θ - κ.form).val φ) {A : ℝ}
    (hA : (-θ + A • κ.form).val.IsSemipositive) {N₂ : ℕ} (hN : A ≤ N₂ + 2) :
    IsThetaPshPotential θ.val (scaled (scaleFactor N₂) φ) := by
  set c : ℝ := ((scaleFactor N₂ : ℚ) : ℝ) with hcdef
  have hc1 : 1 < c := one_lt_scaleFactor N₂
  have hcR : c = ((N₂ : ℝ) + 2) / ((N₂ : ℝ) + 1) := scaleFactor_real N₂
  have h := RestrictedApproximantComparison.isThetaPshPotential_smul hφκ (by linarith : 0 < c)
  refine SGPT.Okounkov.TranscendentalBody.isThetaPshPotential_of_le h ?_
  have heq : θ - c • (θ - κ.form) = (c - 1) • (-θ + A • κ.form) + (c - (c - 1) * A) • κ.form := by
    module
  rw [heq]
  refine UniformPerturbedKahlerLowerBound.isSemipositive_add
    (KahlerDomination.isSemipositive_smul hA (by linarith))
    (KahlerDomination.isSemipositive_smul κ.isSemipositive ?_)
  have hN1 : (0 : ℝ) < N₂ + 1 := by positivity
  have : c - (c - 1) * A = ((N₂ : ℝ) + 2 - A) / ((N₂ : ℝ) + 1) := by rw [hcR]; field_simp; ring
  rw [this]
  apply div_nonneg <;> linarith

/-- **The lower bound of `thm:DXmain1` for every Kähler current** (blueprint
`claude-dx-low2:main`; source `thm:DXmain1`, Step 1 of the proof, `≥`): if `θ_φ` is a Kähler
current (`θ = c₁(L, h)`), then for every Hermitian holomorphic line bundle `(T, h_T)` with smooth
metric `vol θ_φ ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. This is
`SGPT.Bergman.Quant2.RiemannRochLowerBound (chernForm L hL) L T φ`. -/
theorem riemannRochLowerBound_of_kahlerCurrent (hn : 0 < n)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ) :
    RiemannRochLowerBound (chernForm L hL) L T φ := by
  obtain ⟨κ, hφκ⟩ := hcurrent
  obtain ⟨hφ, hφpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent κ L hL ⟨κ, hφκ⟩
  refine ⟨hφ, ?_⟩
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set θ' := chernForm L hL with hθ'def
  have hrt : atlasClosedFormToNative θ' = θ := sourceNativeAtlasForm_roundTrip θ
  have toAtlas : ∀ {u : X → EReal}, IsThetaPshPotential θ.val u →
      (ofFixedModel n X).IsThetaPSH θ' u := fun h =>
    (isThetaPSH_iff_nativeThetaPotential θ' _).mpr (by rw [hrt]; exact h)
  obtain ⟨A, hA0, hA⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul κ (-θ)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * A)
  have hsc : ∀ N₂ : ℕ, 4 * A < N₂ →
      (ofFixedModel n X).IsThetaPSH θ' (scaled (scaleFactor N₂) φ) := fun N₂ hN =>
    toAtlas (isThetaPshPotential_scaled hφκ hA (by linarith))
  -- the indices `N₂ = i + N₀ + 1`
  have hNi : ∀ i : ℕ, 4 * A < ((i + N₀ + 1 : ℕ) : ℝ) := fun i => by push_cast; linarith
  -- the interpolation `c_i φ = (1 - tᵢ) φ + tᵢ (c_{N₀} φ)`, `tᵢ = (N₀+1)/(i+N₀+2) → 0`
  set R : ℝ := ((scaleFactor N₀ : ℚ) : ℝ) with hRdef
  have hRR : R = ((N₀ : ℝ) + 2) / ((N₀ : ℝ) + 1) := scaleFactor_real N₀
  set u₀ : SourceThetaPotentialL1 θ' := ⟨φ, hφ⟩
  set u₁ : SourceThetaPotentialL1 θ' := ⟨scaled R φ, hsc N₀ hN₀⟩
  have ht01 : ∀ i : ℕ, ((N₀ : ℝ) + 1) / ((i : ℝ) + N₀ + 2) ∈ Ioo (0 : ℝ) 1 := fun i => by
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  let t : ℕ → Ioo (0 : ℝ) 1 := fun i => ⟨_, ht01 i⟩
  have ht : Tendsto (fun i => (t i).val) atTop (𝓝 0) := by
    change Tendsto (fun i : ℕ => ((N₀ : ℝ) + 1) / ((i : ℝ) + N₀ + 2)) atTop (𝓝 0)
    refine tendsto_const_nhds.div_atTop ?_
    have := tendsto_atTop_add_const_right atTop ((N₀ : ℝ) + 2) tendsto_natCast_atTop_atTop
    refine this.congr fun i => ?_
    ring
  have hbig := sourcePositiveMass_isBig κ hφ hφpos
  have hconv := tendsto_sourceGeneralInterpolation_zero κ θ' hbig u₀ u₁ atTop t ht
  have hvol := (tendsto_sourceIVolume_and_mass_of_sourceSingularityTopology_all_mass κ θ' hbig
    atTop _ u₀ hconv).1
  have hinterp : ∀ i : ℕ, (sourceGeneralInterpolation θ' ⟨(t i).val, (t i).property.1.le,
      (t i).property.2.le⟩ u₀ u₁).val = scaled (scaleFactor (i + N₀ + 1)) φ := by
    intro i
    rw [sourceGeneralInterpolation_val]
    funext x
    have hti : (t i).val = ((N₀ : ℝ) + 1) / ((i : ℝ) + N₀ + 2) := rfl
    have hc : ((scaleFactor (i + N₀ + 1) : ℚ) : ℝ) = 1 - (t i).val + (t i).val * R := by
      rw [scaleFactor_real, hti, hRR]; push_cast; field_simp; ring
    have h1 : (0 : EReal) ≤ ((1 - (t i).val : ℝ) : EReal) := by
      exact_mod_cast (sub_nonneg.mpr (t i).property.2.le)
    have h2 : (0 : EReal) ≤ (((t i).val * R : ℝ) : EReal) := by
      have : 0 ≤ R := by rw [hRR]; positivity
      exact_mod_cast mul_nonneg (t i).property.1.le this
    change ((1 - (t i).val : ℝ) : EReal) * φ x + ((t i).val : EReal) * ((R : EReal) * φ x) =
      (((scaleFactor (i + N₀ + 1) : ℚ) : ℝ) : EReal) * φ x
    rw [← mul_assoc, ← EReal.coe_mul, ← EReal.right_distrib_of_nonneg h1 h2, ← EReal.coe_add, hc]
  have hvol' : Tendsto (fun i : ℕ => sourceIVolume θ' (scaled (scaleFactor (i + N₀ + 1)) φ)
      (hsc _ (hNi i))) atTop (𝓝 (sourceIVolume θ' φ hφ)) := by
    refine hvol.congr fun i => ?_
    exact sourceIVolume_congr (hinterp i) _ _
  -- the factors `((N₂)/(N₂+2))ⁿ → 1`
  have hfac : Tendsto (fun i : ℕ => ENNReal.ofReal
      ((((i + N₀ + 1 : ℕ) : ℝ) / (((i + N₀ + 1 : ℕ) : ℝ) + 2)) ^ n)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun i : ℕ => (2 : ℝ) / (((i + N₀ + 1 : ℕ) : ℝ) + 2)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      have := tendsto_atTop_add_const_right atTop ((N₀ : ℝ) + 3) tendsto_natCast_atTop_atTop
      refine this.congr fun i => ?_
      push_cast; ring
    have h1 : Tendsto (fun i : ℕ => (((i + N₀ + 1 : ℕ) : ℝ) / (((i + N₀ + 1 : ℕ) : ℝ) + 2)) ^ n)
        atTop (𝓝 ((1 - 0) ^ n)) := by
      refine ((tendsto_const_nhds.sub h0).pow n).congr fun i => ?_
      congr 1
      field_simp
      ring
    rw [sub_zero, one_pow] at h1
    have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h1
    rw [ENNReal.ofReal_one] at h2
    exact h2
  have hprod := ENNReal.Tendsto.mul hfac (Or.inl one_ne_zero) hvol' (Or.inr ENNReal.one_ne_top)
  rw [one_mul] at hprod
  refine le_of_tendsto' hprod fun i => ?_
  exact le_liminf_normalizedH0_scaled hn hL hT κ hφκ hA (hNi i) hφ (hsc _ (hNi i))

end SGPT.IGood.DXLow2
