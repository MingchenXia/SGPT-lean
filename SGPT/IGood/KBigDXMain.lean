import SGPT.Bergman.KBigUpper
import SGPT.IGood.DXLow2DXMain
import SGPT.IGood.DXLow2Upper
import SGPT.Envelopes.SourceClassVolume
import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Bergman.SourceNativeTensorSmoothMetric

/-!
# The asymptotic Riemann–Roch formula and the volume on compact Kähler manifolds

Blueprint `claude-k-big`, nodes `claude-k-big:dxmain1`, `claude-k-big:volbigL` and
`claude-k-big:big-iff`. Sources `thm:DXmain1` and `cor:volbigL` (chapter *`𝓘`-good
singularities*) in the book's setting of a connected compact Kähler manifold `X` (not necessarily
projective), and the bigness notion of `def:testcurve:L1134`.

* `tendsto_normalizedH0` (**`thm:DXmain1`**): for `(L, h₀)` and `T` holomorphic line bundles with
  smooth metrics, `θ = c₁(L, h₀)`, every `φ ∈ PSH(X, θ)`:
  `n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ)) → vol θ_φ`; in particular the limit exists. The book's Step 3
  (`vol θ_φ = 0`, `L` not big) used the projectivity of `X`; here it is the bigness criterion
  `SGPT.Bergman.KBig.tendsto_normalizedH0_zero_of_not_big`.
* `tendsto_normalizedH0_volume` (**`cor:volbigL`**): for pseudo-effective `L` with a smooth metric,
  `n!/kⁿ h⁰(X, L^k) → ∫_X θⁿ_{V_θ}` (and `= vol c₁(L)`, `eq:volL_volc1L`:
  `tendsto_normalizedH0_classVolume`).
* `limsup_pos_iff_exists_kahlerCurrent`: `L` is big in the sense of section growth
  (`limsup h⁰(X, L^k)/kⁿ > 0`) iff `c₁(L)` contains a Kähler current.

Here `h⁰(X, L^k) = dim H⁰(X, L^{⊗k} ⊗ 𝒪_X)` is the dimension of ALL holomorphic sections
(`twistedSections L unit k`), and `h⁰(X, T ⊗ L^k ⊗ 𝓘(kφ))` is `LiteralTwistedMultiplierSections`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.IGood.KBig

open Set Filter MeasureTheory CategoryTheory Opposite
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf
open IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.Quant2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-! ### The zero weight: `H⁰(X, L^k ⊗ T ⊗ 𝓘(k·0)) = H⁰(X, L^k ⊗ T)` -/

/-- The multiplier ideal of the zero weight is `𝒪_X` in every degree. -/
theorem sourceDegreeMultiplierIdeal_zeroWeight (k : ℕ) :
    sourceDegreeMultiplierIdeal (n := n) k (fun _ : X => (0 : EReal)) =
      originalUnitGermIdeal (n := n) (X := X) := by
  unfold sourceDegreeMultiplierIdeal
  simp only [mul_zero]
  exact zeroPotentialMultiplier_eq_unit (n := n) one_pos

/-- Every holomorphic section of `L^k ⊗ T` lies in `H⁰(X, L^k ⊗ T ⊗ 𝓘(k·0))`. -/
theorem fullHolomorphicIdealSections_zeroWeight_eq_top (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) :
    fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
      (sourceDegreeMultiplierIdeal (n := n) k (fun _ : X => (0 : EReal))) = ⊤ := by
  rw [sourceDegreeMultiplierIdeal_zeroWeight]
  apply Submodule.eq_top_iff'.mpr
  intro s
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) (twistedPower L T k).Fiber
    _ originalUnitGermIdeal_isCoherent s]
  intro x
  exact originalSectionCoefficient_holomorphicAt (n := n) (twistedPower L T k).Fiber
    (preferredOriginalFrame (twistedPower L T k).Fiber x) s
    (mem_baseSet_trivializationAt ℂ (twistedPower L T k).Fiber x)

/-- `H⁰(X, L^k ⊗ T ⊗ 𝓘(k·0)) ≃ H⁰(X, L^k ⊗ T)`. -/
def literalZeroWeightEquiv (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) :
    LiteralTwistedMultiplierSections L T k (fun _ => 0) ≃ₗ[ℂ] twistedSections L T k :=
  (literalTwistedMultiplierSectionEquiv L T k (fun _ => 0)).trans
    ((LinearEquiv.ofEq _ _ (fullHolomorphicIdealSections_zeroWeight_eq_top L T k)).trans
      Submodule.topEquiv)

/-- `h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ h⁰(X, L^k ⊗ T)` for every weight `φ`. -/
theorem finrank_literal_le [CompactSpace X] (L T : HermitianHolomorphicLineBundle n X) (k : ℕ)
    (φ : X → EReal) :
    Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) ≤
      Module.finrank ℂ (twistedSections L T k) := by
  have := twistedSections_finiteDimensional L T k
  rw [(literalTwistedMultiplierSectionEquiv L T k φ).finrank_eq]
  exact Submodule.finrank_le _

/-- The normalized dimension `n!/kⁿ h⁰(X, L^k ⊗ T)` of all holomorphic sections. -/
def normalizedFullH0 (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n * Module.finrank ℂ (twistedSections L T k))

theorem normalizedH0_zeroWeight (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) :
    normalizedH0 L T (fun _ => 0) k = normalizedFullH0 L T k := by
  rw [normalizedH0, normalizedFullH0, (literalZeroWeightEquiv L T k).finrank_eq]

theorem normalizedH0_le_normalizedFullH0 [CompactSpace X] (L T : HermitianHolomorphicLineBundle n X)
    (k : ℕ) (φ : X → EReal) : normalizedH0 L T φ k ≤ normalizedFullH0 L T k := by
  rw [normalizedH0, normalizedFullH0]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  exact_mod_cast finrank_literal_le L T k φ

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

/-! ### `thm:DXmain1` on compact Kähler manifolds -/

/-- **The upper half of `thm:DXmain1`, compact Kähler setting** (blueprint `claude-k-big:dxmain1`):
for every `φ ∈ PSH(X, θ)`, `θ = c₁(L, h₀)`, and every twist `T`,
`limsup_k n!/kⁿ h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ)) ≤ vol θ_φ`. If `θ` carries a Kähler current this is lane
DX-LOW2's bound; otherwise the left-hand side is `0` by the bigness criterion. -/
theorem riemannRochUpperBound (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    SGPT.Bergman.Quant3.RiemannRochUpperBound (chernForm L hL) L T φ := by
  obtain ⟨ω, hω⟩ := SGPT.IGood.DXLow2.exists_normalized_kahlerBackground ωb
  by_cases hbig : ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ
  · obtain ⟨ψ, hψ⟩ := hbig
    exact SGPT.IGood.DXLow2.riemannRochUpperBound_of_kahlerCurrent ω hω hL hT hψ hφ
  · refine ⟨hφ, ?_⟩
    rw [(SGPT.Bergman.KBig.tendsto_normalizedH0_zero_of_not_big ω hω L T hL hT φ hbig).limsup_eq]
    exact bot_le

/-- **Source `thm:DXmain1` (asymptotic Riemann–Roch formula), compact Kähler setting**
(blueprint `claude-k-big:dxmain1`): `X` a connected compact Kähler manifold of dimension `n`,
`(L, h₀)` and `T` holomorphic line bundles with smooth metrics, `θ = c₁(L, h₀)`,
`φ ∈ PSH(X, θ)` (`h = h₀ e^{-φ}`). Then
`lim_k n!/kⁿ h⁰(X, T ⊗ L^k ⊗ 𝓘(h^k)) = vol(dd^c h) = vol θ_φ`; in particular the limit exists. -/
theorem tendsto_normalizedH0 (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hφ : (ofFixedModel n X).IsThetaPSH (chernForm L hL) φ) :
    Tendsto (fun k => normalizedH0 L T φ k) atTop (𝓝 (sourceIVolume (chernForm L hL) φ hφ)) := by
  obtain ⟨_, hlow⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωb hL hT hφ
  obtain ⟨_, hup⟩ := riemannRochUpperBound ωb hL hT hφ
  exact tendsto_of_le_liminf_of_limsup_le hlow hup

/-! ### `cor:volbigL` on compact Kähler manifolds -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- The obstacle envelope `P_θ(0)` is the minimal envelope `V_θ`. -/
theorem obstacleEnvelope_eq_sourceMinimalEnvelope (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hL : IsSourceSmoothHermitianMetric L)
    (hP : (ofFixedModel n X).IsThetaPSH (chernForm L hL) (SGPT.Bergman.KBig.obstacleEnvelope L hL)) :
    SGPT.Bergman.KBig.obstacleEnvelope L hL = sourceMinimalEnvelope (chernForm L hL) := by
  have hP0 : SGPT.Bergman.KBig.obstacleEnvelope L hL ≤ 0 := fun x => by
    have h : SGPT.Bergman.KBig.obstacleEnvelope L hL x ≤ ((0 : C(X, ℝ)) x : EReal) :=
      SGPT.Envelopes.DNT.sourceObstacleEnvelope_le (0 : C(X, ℝ)).continuous hP x
    simpa using h
  funext x
  apply le_antisymm
  · exact le_iSup (fun v : {v : X → EReal // (ofFixedModel n X).IsThetaPSH (chernForm L hL) v ∧
      v ≤ 0} => v.1 x) ⟨_, hP, hP0⟩
  · refine iSup_le fun v => ?_
    refine SGPT.Bergman.KBig.le_obstacleEnvelope L hL ?_ v.2.2 x
    simpa only [chernForm, sourceNativeAtlasForm_roundTrip] using
      (isThetaPSH_iff_nativeThetaPotential _ _).mp v.2.1

/-- `vol θ_{V_θ} = ∫_X θⁿ_{V_θ}` (`V_θ` is `𝓘`-model). -/
theorem sourceIVolume_sourceMinimalEnvelope (ωb : KahlerBackground n X)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    sourceIVolume θ (sourceMinimalEnvelope θ) (sourceMinimalEnvelope_thetaPSH_of_mem hu) =
      sourcePotentialNonPluripolarMeasure θ (sourceMinimalEnvelope θ)
        (sourceMinimalEnvelope_thetaPSH_of_mem hu) univ := by
  rw [← sourceClassVolume_eq ωb (sourceMinimalEnvelope_minimalSingularities hu),
    sourceClassVolume_eq_minimalEnvelope_mass ωb hu]

/-- **Source `cor:volbigL`, compact Kähler setting** (blueprint `claude-k-big:volbigL`): for a
pseudo-effective line bundle `L` (`PSH(X, θ) ≠ ∅`) with a smooth metric `h`, `θ = c₁(L, h)`, on a
connected compact Kähler manifold, `lim_k n!/kⁿ h⁰(X, L^k) = ∫_X θⁿ_{V_θ}`. -/
theorem tendsto_normalizedH0_volume (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L)
    {u : X → EReal} (hu : (ofFixedModel n X).IsThetaPSH (chernForm L hL) u) :
    Tendsto (fun k => normalizedFullH0 L unit k) atTop
      (𝓝 (sourcePotentialNonPluripolarMeasure (chernForm L hL)
        (sourceMinimalEnvelope (chernForm L hL)) (sourceMinimalEnvelope_thetaPSH_of_mem hu) univ)) := by
  obtain ⟨ω, hω⟩ := SGPT.IGood.DXLow2.exists_normalized_kahlerBackground ωb
  have hV := sourceMinimalEnvelope_thetaPSH_of_mem hu
  -- lower bound: `thm:DXmain1` at `V_θ` and `H⁰(L^k ⊗ 𝓘(kV_θ)) ⊆ H⁰(L^k)`
  obtain ⟨_, hlow⟩ := SGPT.IGood.DXLow2.riemannRochLowerBound_of_kahler ωb hL sourceNativeUnit_smooth
    hV
  rw [sourceIVolume_sourceMinimalEnvelope ωb hu] at hlow
  have hlow' : sourcePotentialNonPluripolarMeasure (chernForm L hL)
      (sourceMinimalEnvelope (chernForm L hL)) hV univ ≤
      liminf (fun k => normalizedFullH0 L unit k) atTop :=
    hlow.trans (liminf_le_liminf (Eventually.of_forall fun k =>
      normalizedH0_le_normalizedFullH0 L unit k _))
  -- upper bound: Berman's bound for the zero weight
  obtain ⟨hP, hup⟩ := SGPT.Bergman.KBig.limsup_normalizedH0_le_envelopeMass ω hω L unit hL
    sourceNativeUnit_smooth (fun _ => 0) ⟨u, hu⟩
  have heq := obstacleEnvelope_eq_sourceMinimalEnvelope L hL hP
  have hup' : limsup (fun k => normalizedFullH0 L unit k) atTop ≤
      sourcePotentialNonPluripolarMeasure (chernForm L hL)
        (sourceMinimalEnvelope (chernForm L hL)) hV univ := by
    have h1 : (fun k => normalizedFullH0 L unit k) = fun k => normalizedH0 L unit (fun _ => 0) k :=
      funext fun k => (normalizedH0_zeroWeight L unit k).symm
    rw [h1]
    refine hup.trans_eq ?_
    rw [SGPT.Envelopes.DNT.sourcePotentialNonPluripolarMeasure_congr hP hV heq]
  exact tendsto_of_le_liminf_of_limsup_le hlow' hup'

/-- **`eq:volL_volc1L`, compact Kähler setting**: `vol L = lim_k n!/kⁿ h⁰(X, L^k) = vol c₁(L)`
(`def:volcohclass`). -/
theorem tendsto_normalizedH0_classVolume (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L)
    {u : X → EReal} (hu : (ofFixedModel n X).IsThetaPSH (chernForm L hL) u) :
    Tendsto (fun k => normalizedFullH0 L unit k) atTop
      (𝓝 (sourceClassVolume (RealBottChern.ofRepresentative (sourceNativeFirstChernForm L hL)))) := by
  have h := sourceClassVolume_eq_minimalEnvelope_mass ωb hu
  rw [show atlasClosedFormToNative (chernForm L hL) = sourceNativeFirstChernForm L hL from
    sourceNativeAtlasForm_roundTrip _] at h
  rw [h]
  exact tendsto_normalizedH0_volume ωb hL hu

/-! ### The two bigness notions -/

/-- **Bigness by section growth vs. Kähler currents** (blueprint `claude-k-big:big-iff`; the two
bigness notions of `def:testcurve:L1134`): on a connected compact Kähler manifold, for `L` with a
smooth metric, `limsup_k n!/kⁿ h⁰(X, L^k) > 0` iff `c₁(L, h)` contains a Kähler current. -/
theorem limsup_pos_iff_exists_kahlerCurrent (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L) :
    0 < limsup (fun k => normalizedFullH0 L unit k) atTop ↔
      ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ := by
  obtain ⟨ω, hω⟩ := SGPT.IGood.DXLow2.exists_normalized_kahlerBackground ωb
  constructor
  · intro hpos
    apply SGPT.Bergman.KBig.exists_kahlerCurrent_of_limsup_pos ω hω L unit hL
      sourceNativeUnit_smooth (fun _ => 0)
    simpa only [normalizedH0_zeroWeight] using hpos
  · rintro ⟨ψ, hψ⟩
    obtain ⟨hψA, hψpos⟩ := isThetaPSH_and_pos_of_kahlerCurrent ω L hL hψ
    have hV := sourceMinimalEnvelope_thetaPSH_of_mem hψA
    rw [(tendsto_normalizedH0_volume ωb hL hψA).limsup_eq]
    exact hψpos.trans_le (sourcePotentialNonPluripolarMass_mono ω hψA hV
      ((sourceMinimalEnvelope_minimalSingularities hψA).2 ψ hψA))

/-- **The two bigness notions agree on compact Kähler manifolds** (blueprint
`claude-k-big:big-iff`; `def:testcurve:L1134`): `L` is big in the sense of section growth,
`h⁰(X, L^k) ≥ c kⁿ` for some `c > 0` and all large `k` (the shape of `SGPT.LineBundle.IsBig`), iff
`c₁(L, h)` contains a Kähler current. -/
theorem sectionGrowth_iff_exists_kahlerCurrent (ωb : KahlerBackground n X)
    {L : HermitianHolomorphicLineBundle.{0, 0} n X} (hL : IsSourceSmoothHermitianMetric L) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
        c * (k : ℝ) ^ n ≤ (Module.finrank ℂ (twistedSections L unit k) : ℝ)) ↔
      ∃ ψ : X → EReal, IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) ψ := by
  have hfac : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  constructor
  · rintro ⟨c, hc, hev⟩
    rw [← limsup_pos_iff_exists_kahlerCurrent ωb hL]
    have hb : ∀ᶠ k in atTop, ENNReal.ofReal ((n.factorial : ℝ) * c) ≤ normalizedFullH0 L unit k := by
      filter_upwards [hev, eventually_gt_atTop 0] with k hk hk0
      unfold normalizedFullH0
      apply ENNReal.ofReal_le_ofReal
      have hkn : (0 : ℝ) < (k : ℝ) ^ n := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hkn]
      nlinarith
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity))
      (le_limsup_of_frequently_le hb.frequently)
  · rintro ⟨ψ, hψ⟩
    obtain ⟨ω, hω⟩ := SGPT.IGood.DXLow2.exists_normalized_kahlerBackground ωb
    have hpos := (limsup_pos_iff_exists_kahlerCurrent ωb hL).mpr ⟨ψ, hψ⟩
    obtain ⟨hψA, -⟩ := isThetaPSH_and_pos_of_kahlerCurrent ω L hL hψ
    have hlim := tendsto_normalizedH0_volume ωb hL hψA
    rw [hlim.limsup_eq] at hpos
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
    have hr : 0 < r := ENNReal.ofReal_pos.mp hr1
    refine ⟨r / n.factorial, by positivity, ?_⟩
    filter_upwards [hlim.eventually (lt_mem_nhds hr2), eventually_gt_atTop 0] with k hk hk0
    unfold normalizedFullH0 at hk
    have hkn : (0 : ℝ) < (k : ℝ) ^ n := by positivity
    have h1 := (ENNReal.ofReal_lt_ofReal_iff'.mp hk).1
    rw [div_mul_eq_mul_div, lt_div_iff₀ hkn] at h1
    rw [div_mul_eq_mul_div, div_le_iff₀ hfac]
    linarith

end SGPT.IGood.KBig
