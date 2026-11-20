import SGPT.IGood.DXLowMain
import SGPT.IGood.LogVolume
import SGPT.PSH.SourceIVolumeGoodness
import SGPT.Envelopes.SourceRelativeEnergyClosure
import SGPT.Bergman.SourceNativeFirstChernForm
import SGPT.Okounkov.PartialBodyVolume
import SGPT.Okounkov.TranscendentalVolumeConcavity
import SGPT.PSH.GlobalL2BergmanLower
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import SGPT.Bergman.Quant2SmoothWeakConv

/-!
# The lower bound of `thm:DXmain1` in the source (Bergman-chapter) form

Blueprint `claude-dx-low`, node `claude-dx-low:bridge`. Source `prop:DXmainanalytic` (`≥`) in the
form used by the Bergman chapter: for a Hermitian holomorphic line bundle `(L, h)` with smooth
metric, `θ = c₁(L, h)` (`sourceNativeFirstChernForm`), a holomorphic line bundle `(T, h_T)` and a
potential `φ` with analytic singularities (`HasManifoldAnalyticSingularityType`), smooth off its
pole set (`SmoothOffPoleSet`; e.g. neat analytic singularities) and with `θ_φ` a Kähler current,

`vol θ_φ ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`,

with `vol θ_φ = sourceIVolume θ φ = ∫_X θ_{P_θ[φ]_𝓘}ⁿ` (`def:volqpsh`) and `h⁰` the dimension of
the literal section space `LiteralTwistedMultiplierSections L T k φ` (`def:Bergman:L778`).

The conclusion of `sourceIVolume_le_liminf_normalizedH0` is literally the proposition
`SGPT.Bergman.Quant2.RiemannRochLowerBound (chernForm L hL) L T φ` of lane BERGMAN2
(`chernForm L hL = nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)`,
`normalizedH0 L T φ k = ofReal (n!/kⁿ · h⁰)`): `riemannRochLowerBound_of_smoothOffPoleSet`.

Proof: `diagonalPotentialMass_le_liminf_finrank` and `vol θ_φ = ∫_X θ_φⁿ` for analytic
singularities of positive mass (`sourceIGoodWith_of_analytic`, `sourceIVolume_eq_mass_of_iGoodWith`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.AdmissibleCurrentFormPositivity
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
  SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.PSH.VariableComplexAtlas SGPT.IGood.LogVolume
open SGPT.PSH.GlobalL2
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

namespace SGPT.IGood.DXLow

/-- **`prop:DXmainanalytic`, the inequality `≥`, in the Bergman-chapter form** (blueprint
`claude-dx-low:bridge`): for `φ` with analytic singularities, smooth off its pole set, and
`θ_φ` a Kähler current (`θ = c₁(L, h)`),
`vol θ_φ ≤ liminf_k n!/kⁿ · h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. This is
`RiemannRochLowerBound (chernForm L hL) L T φ`. -/
theorem sourceIVolume_le_liminf_normalizedH0 (hn : 0 < n) (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) φ) (hsm : SmoothOffPoleSet (n := n) φ) :
    ∃ hφ : (ofFixedModel n X).IsThetaPSH
        (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)) φ,
      sourceIVolume (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL)) φ hφ ≤
        liminf (fun k : ℕ => ENNReal.ofReal ((n.factorial : ℝ) / (k : ℝ) ^ n *
          Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ))) atTop := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  set θ := sourceNativeFirstChernForm L hL with hθdef
  set θ' := nativeClosedFormToAtlas θ with hθ'
  have hrt : atlasClosedFormToNative θ' = θ := sourceNativeAtlasForm_roundTrip θ
  obtain ⟨δ, hδ, hφδ⟩ := exists_isThetaPshPotential_sub_smul_of_kahlerCurrent ωb hcurrent
  have hφθ : IsThetaPshPotential θ.val φ := by
    have h := Pending.LocalPotentials.isThetaPshPotential_add_of_semipositive hφδ
      (Pending.KahlerDomination.isSemipositive_smul ωb.isSemipositive hδ.le)
    have hform : θ - δ • ωb.form + δ • ωb.form = θ := by module
    rwa [hform] at h
  have hφ' : (ofFixedModel (m + 1) X).IsThetaPSH θ' φ :=
    (isThetaPSH_iff_nativeThetaPotential θ' φ).mpr (by rw [hrt]; exact hφθ)
  refine ⟨hφ', ?_⟩
  have : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact absurd (SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hcurrent hφθ) (by
      simp [diagonalPotentialMass, Set.univ_eq_empty_iff.mpr h])
  have hmass : sourcePotentialNonPluripolarMeasure θ' φ hφ' univ =
      diagonalPotentialMass θ φ hφθ := by
    change diagonalPotentialMass (atlasClosedFormToNative θ') φ _ = _
    exact SGPT.Okounkov.TranscendentalVolumeConcavity.diagonalPotentialMass_congr hrt rfl _ _
  have hpos : 0 < sourcePotentialNonPluripolarMeasure θ' φ hφ' univ := by
    rw [hmass]; exact SGPT.Okounkov.PartialBody.diagonalPotentialMass_pos_of_isKahlerCurrentPotential hcurrent hφθ
  have hvol : sourceIVolume θ' φ hφ' = diagonalPotentialMass θ φ hφθ := by
    rw [sourceIVolume_eq_mass_of_iGoodWith ωb hφ' (sourceIGoodWith_of_analytic ωb hφ' hA hpos),
      hmass]
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume ωb
  have hmain := diagonalPotentialMass_le_liminf_finrank (Nat.succ_pos m) ωb hμ hL hT
    (sourceNativeFirstChernForm_isOwn L hL) hδ hφδ hφθ hsm
  rw [hvol]
  refine hmain.trans_eq ?_
  congr 1
  funext k
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-- **`RiemannRochLowerBound` for analytic Kähler currents smooth off their poles**: the hypothesis
of the `smooth_weak_conv` and of the `Quant2*`/`Quant3*` consumers, for
`φ` with analytic singularities that is smooth off its pole set (e.g. neat analytic singularities). -/
theorem riemannRochLowerBound_of_smoothOffPoleSet (hn : 0 < n) (ωb : KahlerBackground n X)
    {L T : HermitianHolomorphicLineBundle.{0, 0} n X}
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    {φ : X → EReal} (hcurrent : IsKahlerCurrentPotential (sourceNativeFirstChernForm L hL) φ)
    (hA : HasManifoldAnalyticSingularityType (n := n) φ) (hsm : SmoothOffPoleSet (n := n) φ) :
    SGPT.Bergman.Quant2.RiemannRochLowerBound (SGPT.Bergman.Quant2.chernForm L hL) L T φ :=
  sourceIVolume_le_liminf_normalizedH0 hn ωb hL hT hcurrent hA hsm

end SGPT.IGood.DXLow
