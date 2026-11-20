import SGPT.Foundations.Analysis.Pending.VaryingIModelNativeGlobalClass
import SGPT.Foundations.Analysis.Pending.AnalyticTypeHolomorphicPullback
import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.AnalyticPotentialsIGood
import SGPT.Foundations.Analysis.Pending.NefCoreKahlerCurrent

set_option autoImplicit false

/-! # A positive varying I-model chain from a genuine normalized ordinary restriction -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionVaryingModelChain

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass IEnvelopeVaryingBackgroundModelInfimum

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Every stage field and the original positive infimum mass are internally
produced from a full QEA and natural positive normalized ordinary restriction. -/
theorem exists_positive_varying_iModel_chain_of_ordinary_restriction
    (omega : KahlerBackground n M) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {a : ℕ → ℝ} {U : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u a U)
    (hu0 : u ≤ 0)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0)
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hι θ).val (fun y => u (ι y)))
    (hwpos : HasPositivePotentialMass (ClosedRealOneOneForm.pullback hι θ)
      (fun y => u (ι y)) hw) :
    let η := ClosedRealOneOneForm.pullback hι θ
    let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
    ∃ b : ℕ → ℝ, (∀ j, 0 < b j) ∧
      ∃ hbanti : Antitone b, ∃ hblim : Tendsto b atTop (𝓝 0),
      IsQuasiEquisingularApproximation omega θ u b U ∧
      let P : ℕ → V → EReal := fun j => singularityEnvelope (η + b j • ρ.form).val (fun y => U j (ι y))
      ∃ hP : ∀ j, IsModelPotential (η + b j • ρ.form) (P j),
      ∃ hanti : Antitone P,
        (∀ j, IsIModelPotential (η + b j • ρ.form).val (P j)) ∧
        HasPositivePotentialMass η (⨅ j, P j)
          (isThetaPshPotential_iInf_varying_models ρ η hbanti hblim hP hanti) := by
  let η := ClosedRealOneOneForm.pullback hι θ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let r : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hrpos (j : ℕ) : 0 < r j := by dsimp only [r]; positivity
  have hranti : Antitone r := by
    intro i j hij
    have hden : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    simpa only [r, one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < (i : ℝ) + 1) hden
  have hrlim : Tendsto r atTop (𝓝 0) := by
    simpa only [r, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let b : ℕ → ℝ := fun j => a j + r j
  have hbpos (j : ℕ) : 0 < b j := add_pos_of_nonneg_of_pos (happ.error_nonneg j) (hrpos j)
  have hbanti : Antitone b := fun i j hij => add_le_add (happ.error_antitone hij) (hranti hij)
  have hblim : Tendsto b atTop (𝓝 0) := by
    simpa only [zero_add] using happ.error_tendsto.add hrlim
  have happb : IsQuasiEquisingularApproximation omega θ u b U := by
    refine ⟨happ.target, ⟨fun j => (hbpos j).le, hbanti, hblim⟩, ?_,
      happ.term_hasAnalyticSingularityType, ⟨happ.term_antitone, happ.term_tendsto⟩, ?_⟩
    · intro j
      have hform : θ + a j • omega.form + r j • omega.form = θ + b j • omega.form := by
        dsimp only [b]
        module
      simpa only [hform] using LocalPotentials.isThetaPshPotential_add_of_semipositive
        (happ.term j) (KahlerDomination.isSemipositive_smul omega.isSemipositive (hrpos j).le)
    · intro c d hc hcd
      exact happ.eventually_multiplierIdealIncluded hc hcd
  let R : ℕ → V → EReal := fun j y => U j (ι y)
  have hR (j : ℕ) : IsThetaPshPotential (η + b j • ρ.form).val (R j) := by
    have hh := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happb hι hgeneric j
    simpa only [NefCoreKahlerCurrent.pullback_add_smul] using hh
  have hA (j : ℕ) : HasManifoldAnalyticSingularityType (n := k) (R j) :=
    AnalyticTypeHolomorphicPullback.hasManifoldAnalyticSingularityType_comp hι
      (happ.term_hasAnalyticSingularityType j)
  have hwR (j : ℕ) : (fun y => u (ι y)) ≤ R j := by
    intro y
    apply le_of_tendsto (happ.term_tendsto (ι y))
    filter_upwards [eventually_ge_atTop j] with l hl
    exact happ.term_antitone (ι y) hl
  have hRpos (j : ℕ) : HasPositivePotentialMass (η + b j • ρ.form) (R j) (hR j) :=
    hwpos.trans_le (DivisorialDomination.diagonalPotentialMass_le_of_le_add_smul
      ρ (hbpos j) hw (hR j) (hwR j))
  let P : ℕ → V → EReal := fun j => singularityEnvelope (η + b j • ρ.form).val (R j)
  have hP (j : ℕ) : IsModelPotential (η + b j • ρ.form) (P j) := by
    have hp := singularityEnvelope_isThetaPshPotential (η + b j • ρ.form).val
      (η + b j • ρ.form).property.1 (η + b j • ρ.form).property.2
      (hR j).1.hasSmoothLocalPotentials (R j) (hR j)
    exact ⟨hp, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      ρ (η + b j • ρ.form) (R j) (hR j) (hRpos j)).symm,
      (singularityEnvelopeMassPreserving ρ (η + b j • ρ.form) (R j) (hR j) hp).symm ▸ hRpos j⟩
  have hPanti : Antitone P := fun i j hij => TraceFreeLimit.singularityEnvelope_antitone
    ρ.isSemipositive hbanti (fun y l m hlm => happ.term_antitone (ι y) hlm) hij
  have hPI (j : ℕ) : IsIModelPotential (η + b j • ρ.form).val (P j) := by
    have he := (AnalyticPotentialsIGood.iGoodWith_of_analytic_type_of_positive_mass
      ρ (hR j) (hA j) (hRpos j)).envelope_eq
    change IsIModelPotential (η + b j • ρ.form).val
      (singularityEnvelope (η + b j • ρ.form).val (R j))
    rw [he]
    exact iSingularityEnvelope_isIModelPotential (η + b j • ρ.form).val
      (η + b j • ρ.form).property.1 (η + b j • ρ.form).property.2
      (hR j).1.hasSmoothLocalPotentials (R j) (hR j)
  have hwP (j : ℕ) : (fun y => u (ι y)) ≤ P j := by
    have hwj : IsThetaPshPotential (η + b j • ρ.form).val (fun y => u (ι y)) :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hw
        (KahlerDomination.isSemipositive_smul ρ.isSemipositive (hbpos j).le)
    exact le_singularityEnvelope hwj (fun y => hu0 (ι y))
      (MoreSingularOn.of_le fun y _ => hwR j y)
  have hInf := isThetaPshPotential_iInf_varying_models ρ η hbanti hblim hP hPanti
  have hposInf : HasPositivePotentialMass η (⨅ j, P j) hInf := hwpos.trans_le
    (diagonalPotentialMass_mono_of_kahler ρ hw hInf
      (MoreSingularOn.of_le fun y _ => (le_iInf hwP) y))
  exact ⟨b, hbpos, hbanti, hblim, happb, hP, hPanti, hPI, hposInf⟩

end
end SGPT.Foundations.Analysis.Pending.PositiveOrdinaryRestrictionVaryingModelChain
