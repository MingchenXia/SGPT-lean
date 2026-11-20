import SGPT.NPP.LogConcavityGeneralIGood
import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeRelativeMAExistence
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeIdempotencePositive
import SGPT.Foundations.Analysis.Pending.KahlerLaplacianSolvability

/-!
# Log-concavity of non-pluripolar masses: reduction of the general case to Dinew's inequality

Source `thm:logconc` (second assertion), general case. This file is a **reduction**, not a proof:
it isolates the one missing analytic input as the proposition `KahlerVolumeMixedLowerBound` and
proves that it implies the general mixed-mass inequality
`∫_X ⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ ∏ᵢ (∫_X ⟨Tᵢⁿ⟩)^{1/n}` for arbitrary closed positive `(1,1)`-currents.

`KahlerVolumeMixedLowerBound` is the special case `ν = ωⁿ` (the Kähler volume), `fᵢ = cᵢ`
(constants) of Dinew's inequality for non-pluripolar products against a common measure
(Xia, *Foundations of pluripotential theory*, `prop:nonpluripolar-multifactor-common-measure`):
if `⟨Tᵢⁿ⟩ ≥ cᵢ ωⁿ` for all `i`, then `⟨T₁ ∧ ⋯ ∧ Tₙ⟩ ≥ (∏ᵢ cᵢ^{1/n}) ωⁿ`. It is **not** proved
here.

The reduction follows FPT `thm:ordinary-mixed-mass-geometric-mean`: replace `uᵢ` by its model
envelope `φᵢ = P_{θᵢ}[uᵢ]` (same masses, `prop:mono2`), solve
`⟨(θᵢ + ddᶜχᵢ)ⁿ⟩ = (∫θ_{φᵢ}ⁿ / ∫ωⁿ) ωⁿ` with `χᵢ ≤ φᵢ` (TN
`ActualSmoothVolumeRelativeMAExistence.exists_normalized_relative_smooth_volume_solution`; this TN
module and its ten TN dependencies are not in the built TN library), and use the monotonicity
`∫⟨⋀θᵢ,χᵢ⟩ ≤ ∫⟨⋀θᵢ,φᵢ⟩` (`thm:mono`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u

namespace SGPT.NPP.LogConcavity

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.PSH.VariableComplexAtlas

/-- **Dinew's mixed inequality against the Kähler volume, constant densities** (the missing
input; FPT `prop:nonpluripolar-multifactor-common-measure` with `ν = ωⁿ`, `fᵢ = cᵢ`): if
`⟨(θᵢ + ddᶜwᵢ)ⁿ⟩ ≥ cᵢ ωⁿ` for all `i`, then `⟨⋀ᵢ (θᵢ + ddᶜwᵢ)⟩ ≥ (∏ᵢ cᵢ^{1/k}) ωⁿ`.
A statement, not an assumption of this project: it is only used as an explicit hypothesis. -/
def KahlerVolumeMixedLowerBound (k : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M] [MeasurableSpace M]
    [BorelSpace M] [CompactSpace M] : Prop :=
  ∀ (ω : KahlerBackground k M) (θ : Fin k → ClosedRealOneOneForm k M) (w : Fin k → M → EReal)
    (hw : ∀ i, ThetaPlurisubharmonic (θ i).val (w i)) (c : Fin k → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ i, ENNReal.ofReal (c i) • IntegrationCurrent.kahlerVolume ω ≤
      globalMixedMeasure (fun _ => θ i) (fun _ => w i) (fun _ => hw i)) →
    ENNReal.ofReal (∏ i, c i ^ ((k : ℝ)⁻¹)) • IntegrationCurrent.kahlerVolume ω ≤
      globalMixedMeasure θ w hw

variable {q : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel (q + 1)) M]
  [IsComplexManifold (q + 1) M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M]

/-- **Reduction of `thm:logconc` (second assertion) to Dinew's inequality.** Assuming
`KahlerVolumeMixedLowerBound`, for arbitrary closed real `(1,1)`-forms `θᵢ` and `θᵢ`-psh `uᵢ` on a
compact connected Kähler manifold of dimension `n = q + 1`,
`∏ᵢ (∫ ⟨(θᵢ + ddᶜuᵢ)ⁿ⟩)^{1/n} ≤ ∫ ⟨(θ₁ + ddᶜu₁) ∧ ⋯ ∧ (θₙ + ddᶜuₙ)⟩`. -/
theorem prod_sourceMass_rpow_le_sourceMixedMass_of_kahlerVolumeMixedLowerBound
    (hD : KahlerVolumeMixedLowerBound (q + 1) M) (ω : KahlerBackground (q + 1) M)
    (θ : Fin (q + 1) → AtlasClosedRealOneOneForm (ofFixedModel (q + 1) M))
    (u : Fin (q + 1) → M → EReal) (hu : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (u i)) :
    ∏ i, ((sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal) ^
        (((q + 1 : ℕ) : ℝ)⁻¹) ≤
      (sourceMixedNonPluripolarMass θ u hu).toReal := by
  classical
  by_cases hpos : ∀ i, 0 < sourcePotentialNonPluripolarMeasure (θ i) (u i) (hu i) univ
  swap
  · push Not at hpos
    obtain ⟨i, hi⟩ := hpos
    have h0 : sourcePotentialNonPluripolarMeasure (θ i) (u i) (hu i) univ = 0 :=
      le_antisymm hi zero_le
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [sourceMixedNonPluripolarMass_diagonal, h0, ENNReal.toReal_zero,
        Real.zero_rpow (by positivity)])]
    exact ENNReal.toReal_nonneg
  set θn : Fin (q + 1) → ClosedRealOneOneForm (q + 1) M := fun i => atlasClosedFormToNative (θ i)
    with hθn
  have hun : ∀ i, IsThetaPshPotential (θn i).val (u i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (θ i) (u i)).mp (hu i)
  have hposn : ∀ i, DiagonalMass.HasPositivePotentialMass (θn i) (u i) (hun i) := fun i => by
    have h := hpos i
    simpa only [sourcePotentialNonPluripolarMeasure, DiagonalMass.HasPositivePotentialMass,
      DiagonalMass.diagonalPotentialMass] using h
  -- the model envelopes
  set φ : Fin (q + 1) → M → EReal := fun i => singularityEnvelope (θn i).val (u i) with hφdef
  have hP : ∀ i, IsThetaPshPotential (θn i).val (φ i) := fun i =>
    SGPT.Foundations.Analysis.Pending.singularityEnvelope_isThetaPshPotential (θn i).val (θn i).property.1 (θn i).property.2
      (hun i).1.hasSmoothLocalPotentials (u i) (hun i)
  have hmassφ : ∀ i, DiagonalMass.diagonalPotentialMass (θn i) (φ i) (hP i) =
      DiagonalMass.diagonalPotentialMass (θn i) (u i) (hun i) := fun i =>
    singularityEnvelopeMassPreserving ω (θn i) (u i) (hun i) (hP i)
  have hmodel : ∀ i, IsModelPotential (θn i) (φ i) := fun i =>
    ⟨hP i, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass ω
      (θn i) (u i) (hun i) (hposn i)).symm, (hmassφ i).symm ▸ hposn i⟩
  have hbig : ∀ i, IsBigClass (RealBottChern.ofRepresentative (θn i)) := fun i =>
    sourcePositiveMassClass_isBig ω ⟨u i, hu i, hpos i⟩
  -- Monge–Ampère solutions with prescribed singularities and smooth right-hand side
  choose χ hχ _ hle hMA using fun i =>
    ActualSmoothVolumeRelativeMAExistence.exists_normalized_relative_smooth_volume_solution
      (hφ := hmodel i) ω (Nat.succ_pos q) (hbig i)
  have hχn : ∀ i, IsThetaPshPotential (θn i).val (χ i) := fun i => (hχ i).1.plurisubharmonic
  have hχs : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (χ i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (θ i) (χ i)).mpr (hχn i)
  have hφs : ∀ i, (ofFixedModel (q + 1) M).IsThetaPSH (θ i) (φ i) := fun i =>
    (isThetaPSH_iff_nativeThetaPotential (θ i) (φ i)).mpr (hP i)
  -- the mixed masses
  have h1 : sourceMixedNonPluripolarMass θ χ hχs ≤ sourceMixedNonPluripolarMass θ φ hφs :=
    sourceMixedNonPluripolarMass_mono ω hχs hφs (fun i => MoreSingularOn.of_le fun x _ => hle i x)
  have h2 : sourceMixedNonPluripolarMass θ φ hφs = sourceMixedNonPluripolarMass θ u hu :=
    (sourceMixedNonPluripolarMass_eq_of_sourcePEquivalent ω hu hφs (fun i =>
      SingularGlobalPEnvelopeBridge.sourcePEquivalent_singularityEnvelope ω (θn i) (hun i))).symm
  set V : ℝ := (IntegrationCurrent.kahlerVolume ω).real univ with hV
  have hVpos : 0 < V := KahlerLaplacianSolvability.kahlerVolume_real_univ_pos ω
  set c : Fin (q + 1) → ℝ := fun i =>
    ActualSmoothVolumeVariationalFoundation.smoothVolumeCoefficient ω (θn i) (φ i) (hmodel i)
    with hc
  set m : Fin (q + 1) → ℝ := fun i =>
    (sourceMixedNonPluripolarMass (fun _ => θ i) (fun _ => u i) (fun _ => hu i)).toReal with hm
  have hm0 : ∀ i, 0 ≤ m i := fun i => ENNReal.toReal_nonneg
  have hcm : ∀ i, c i = m i / V := by
    intro i
    simp only [hc, hm, ActualSmoothVolumeVariationalFoundation.smoothVolumeCoefficient,
      RelativePreceqClasses.modelVolume, hV]
    congr 1
    rw [sourceMixedNonPluripolarMass_diagonal, measureReal_def]
    exact congrArg ENNReal.toReal (hmassφ i)
  have hc0 : ∀ i, 0 ≤ c i := fun i => by rw [hcm i]; exact div_nonneg (hm0 i) hVpos.le
  have h3 := hD ω θn χ (fun i => (hχn i).1) c hc0 (fun i => (hMA i).symm.le)
  have h4 : ENNReal.ofReal (∏ i, c i ^ (((q + 1 : ℕ) : ℝ)⁻¹)) *
      IntegrationCurrent.kahlerVolume ω univ ≤ sourceMixedNonPluripolarMass θ χ hχs := h3 univ
  -- real arithmetic
  have hprod : (∏ i, c i ^ (((q + 1 : ℕ) : ℝ)⁻¹)) * V = ∏ i, m i ^ (((q + 1 : ℕ) : ℝ)⁻¹) := by
    have hdiv : ∀ i, c i ^ (((q + 1 : ℕ) : ℝ)⁻¹) =
        m i ^ (((q + 1 : ℕ) : ℝ)⁻¹) / V ^ (((q + 1 : ℕ) : ℝ)⁻¹) := fun i => by
      rw [hcm i, Real.div_rpow (hm0 i) hVpos.le]
    simp_rw [hdiv]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.rpow_inv_natCast_pow hVpos.le (Nat.succ_ne_zero q)]
    field_simp
  have hfin : sourceMixedNonPluripolarMass θ χ hχs ≠ ⊤ :=
    (sourceMixedNonPluripolarMass_lt_top ω θ χ hχs).ne
  have h5 : (∏ i, c i ^ (((q + 1 : ℕ) : ℝ)⁻¹)) * V ≤
      (sourceMixedNonPluripolarMass θ χ hχs).toReal := by
    have hprodnn : 0 ≤ ∏ i, c i ^ (((q + 1 : ℕ) : ℝ)⁻¹) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hc0 i) _
    have := ENNReal.toReal_mono hfin h4
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hprodnn, ← measureReal_def] at this
  rw [← hprod]
  refine h5.trans ?_
  rw [← h2]
  exact ENNReal.toReal_mono (sourceMixedNonPluripolarMass_lt_top ω θ φ hφs).ne h1

end SGPT.NPP.LogConcavity
