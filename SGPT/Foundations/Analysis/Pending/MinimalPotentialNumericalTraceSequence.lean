import SGPT.Foundations.Analysis.Pending.MinimalPotentialPositiveTraceDomain
import SGPT.Foundations.Analysis.Pending.MinimalPotentialCommonBackgroundNativeLimit
import SGPT.Foundations.Analysis.Pending.TraceNativeDecreasingNetAllReaders
import SGPT.Foundations.Analysis.Pending.NormalizedTraceIdealOrderComparison
import SGPT.Foundations.Analysis.Pending.NormalizedTraceFixedPotentialPerturbation

set_option autoImplicit false

/-! # Actual moving-minimal numerical trace sequence, including original undefined zero -/

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceSequence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass MixedMass
  PositiveNormalizedTrace NumericalTraceMass TraceRepresentativeConstruction
  SingularGlobalPOrder ThetaPshL1Topology SingularCanonicalSingularityDistance
  PluripolarCapacityDichotomy IEnvelopeVaryingBackgroundModelInfimum

noncomputable section

variable {n k : ℕ} {M V : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]

/-- Every moving positive domain and the original positive/undefined-zero
branch is supplied internally; no numerical trace limit is an input. -/
theorem tendsto_numericalTraceMass_minimal_reciprocal
    (omega : KahlerBackground n M) (omegaV : KahlerBackground k V) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hpull : (ClosedRealOneOneForm.pullback hι omega.form).val.IsKahler)
    (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hgeneric : (⨅ y : V, lelongNumber (n := n) (thetaPshSupremum θ.val) (ι y)) = 0) :
    Tendsto (fun j : ℕ => numericalTraceMass omega omegaV hι
        (θ + ((j : ℝ) + 1)⁻¹ • omega.form)
        (thetaPshSupremum (θ + ((j : ℝ) + 1)⁻¹ • omega.form).val))
      atTop (𝓝 (numericalTraceMass omega omegaV hι θ (thetaPshSupremum θ.val))) := by
  classical
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hε1 (j : ℕ) : ε j ≤ 1 := by
    dsimp only [ε]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))] : (1 : ℝ) ≤ (j : ℝ) + 1)
  have hεzero : ε 0 = 1 := by norm_num [ε]
  have hεanti : Antitone ε := by
    intro i j hij
    have hden : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    simpa only [ε, one_div] using
      one_div_le_one_div_of_le (by positivity : 0 < (i : ℝ) + 1) hden
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let η := ClosedRealOneOneForm.pullback hι θ
  let ρ : KahlerBackground k V := ⟨ClosedRealOneOneForm.pullback hι omega.form, hpull⟩
  let W : ℕ → M → EReal := fun j => thetaPshSupremum (θ + ε j • omega.form).val
  have hV := MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum θ hbig
  have hW (j : ℕ) : IsThetaPshPotential (θ + ε j • omega.form).val (W j) :=
    MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum _
      (PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV (hεpos j))
  have hVW (j : ℕ) : thetaPshSupremum θ.val ≤ W j :=
    le_thetaPshSupremum
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hV
        (KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos j).le))
      (thetaPshSupremum_le_zero θ.val)
  have hWanti : Antitone W := by
    intro i j hij
    have hc : 0 ≤ ε i - ε j := sub_nonneg.mpr (hεanti hij)
    have hf : θ + ε j • omega.form + (ε i - ε j) • omega.form = θ + ε i • omega.form := by module
    have hp : IsThetaPshPotential (θ + ε i • omega.form).val (W j) := by
      simpa only [hf] using LocalPotentials.isThetaPshPotential_add_of_semipositive
        (hW j) (KahlerDomination.isSemipositive_smul omega.isSemipositive hc)
    exact le_thetaPshSupremum hp (thetaPshSupremum_le_zero _)
  have hdefined (j : ℕ) : HasPositiveTraceRepresentativeAlong
      omega omegaV hι (θ + ε j • omega.form) (W j) :=
    MinimalPotentialPositiveTraceDomain.hasPositiveTraceRepresentativeAlong_minimal_add_smul
      omega omegaV hι hpull θ hbig hgeneric (hεpos j)
  let v : ℕ → V → EReal := fun j =>
    normalizedTraceAlong omega omegaV hι (θ + ε j • omega.form) (W j) (hdefined j)
  have hpullform (j : ℕ) : ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) =
      η + ε j • ρ.form := NefCoreKahlerCurrent.pullback_add_smul hι θ omega.form (ε j)
  have hv (j : ℕ) : IsModelPotential (η + ε j • ρ.form) (v j) := by
    simpa only [hpullform j] using
      (normalizedTraceAlong_models omega omegaV hι (θ + ε j • omega.form) (W j) (hdefined j)).1
  have hIv (j : ℕ) : IsIModelPotential (η + ε j • ρ.form).val (v j) := by
    simpa only [hpullform j] using
      (normalizedTraceAlong_models omega omegaV hι (θ + ε j • omega.form) (W j) (hdefined j)).2
  have hTi (j : ℕ) : IsTraceRepresentativeAlong omega omegaV hι (W j) (v j) :=
    NormalizedTraceBackgroundMonotonicity.isTraceRepresentativeAlong_normalizedTraceAlong omega omegaV hι
      (θ + ε j • omega.form) (W j) (hdefined j)
  have hvanti : Antitone v := by
    intro i j hij
    have hc : 0 ≤ ε i - ε j := sub_nonneg.mpr (hεanti hij)
    have hdiff : θ + ε i • omega.form - (θ + ε j • omega.form) =
        (ε i - ε j) • omega.form := by module
    have hsemi : (θ + ε i • omega.form - (θ + ε j • omega.form)).val.IsSemipositive := by
      rw [hdiff]
      exact KahlerDomination.isSemipositive_smul omega.isSemipositive hc
    exact NormalizedTraceIdealOrderComparison.normalizedTraceAlong_le_of_iOrder_of_semipositive_difference
      omega omega omegaV omegaV hι (θ + ε j • omega.form) (θ + ε i • omega.form)
      (iOrderOnManifold_of_le (hW i).1.quasiPlurisubharmonic (hWanti hij))
      hsemi (hdefined j) (hdefined i)
  let H : V → EReal := ⨅ j, v j
  have hH : IsThetaPshPotential η.val H :=
    isThetaPshPotential_iInf_varying_models ρ η hεanti hεlim hv hvanti
  let L : ℝ≥0∞ := diagonalPotentialMass η H hH
  have hm : Tendsto (fun j => diagonalPotentialMass (η + ε j • ρ.form)
      (v j) (hv j).plurisubharmonic) atTop (𝓝 L) :=
    tendsto_diagonalPotentialMass_iInf_varying_models ρ η hεpos hεanti hεlim hv hvanti
  obtain ⟨τ, hT, β, hτmodel⟩ :=
    GlobalQuasiPshTraceExistence.exists_of_isThetaPshPotential omega omegaV hV hι hgeneric
  obtain ⟨c, hc, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul ρ (η - β.form)
  let Γ : ClosedRealOneOneForm k V := η + (1 + c) • ρ.form
  have hsmallform : β.form + (η - β.form + c • ρ.form) = Γ - ρ.form := by
    dsimp only [Γ]
    module
  have hτsmall : IsThetaPshPotential (Γ - ρ.form).val τ := by
    simpa only [hsmallform] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hτmodel.plurisubharmonic hsemi
  have hτΓ : IsThetaPshPotential Γ.val τ := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hτsmall ρ.isSemipositive
  have hτpos : HasPositivePotentialMass Γ τ hτΓ := by
    change 0 < diagonalPotentialMass Γ τ hτΓ
    exact RestrictedApproximantMass.diagonalPotentialMass_pos_of_sub_smul
      ρ zero_lt_one (by simpa only [one_smul] using hτsmall) hτΓ
  have hΓ : IsBigClass (RealBottChern.ofRepresentative Γ) := by
    simpa only [one_smul, sub_add_cancel] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential ρ (Γ - ρ.form) hτsmall zero_lt_one
  have hGv (j : ℕ) : IsThetaPshPotential Γ.val (v j) := by
    have hcoeff : 0 ≤ 1 + c - ε j := by linarith [hε1 j]
    have heq : η + ε j • ρ.form + (1 + c - ε j) • ρ.form = Γ := by
      dsimp only [Γ]
      module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hv j).plurisubharmonic (KahlerDomination.isSemipositive_smul ρ.isSemipositive hcoeff)
  obtain ⟨ζ, hζ, hgoodζ⟩ := TraceRepresentativeIGood.iGood_of_isTraceRepresentativeAlong omegaV hι hT
  have hgoodτ : IGoodWith Γ τ hτΓ :=
    (IGoodPositiveBackgroundIndependence.iGoodWith_iff_positive_common_potential
      ρ ζ Γ hζ hτΓ hgoodζ.positiveMass hτpos).mp hgoodζ
  let B : ClosedRealOneOneForm n M := θ + omega.form
  have hB : IsBigClass (RealBottChern.ofRepresentative B) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hV zero_lt_one
  have hVB : IsThetaPshPotential B.val (thetaPshSupremum θ.val) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hV omega.isSemipositive
  have hWB (j : ℕ) : IsThetaPshPotential B.val (W j) := by
    have heq : θ + ε j • omega.form + (1 - ε j) • omega.form = B := by
      dsimp only [B]
      module
    simpa only [heq] using LocalPotentials.isThetaPshPotential_add_of_semipositive
      (hW j) (KahlerDomination.isSemipositive_smul omega.isSemipositive (sub_nonneg.mpr (hε1 j)))
  have hWlim := MinimalPotentialCommonBackgroundNativeLimit.tendsto_native_minimal_add_smul_in_common_background
    omega θ hbig B hB atTop ε hεpos hε1 hεlim hVB hWB
  have hvlim := TraceNativeDecreasingNetAllReaders.tendsto_native_trace_readers_of_antitone_net
    omega ρ B hB (fun j => (⟨W j, hWB j⟩ : ThetaPshL1 B.val)) ⟨thetaPshSupremum θ.val, hVB⟩
      (fun x i j hij => hWanti hij x) hWlim hι Γ hΓ
        (fun j => (⟨v j, hGv j⟩ : ThetaPshL1 Γ.val)) ⟨τ, hτΓ⟩ hTi hT
  let Ω : KahlerBackground k V := KahlerBackground.smul hc ρ
  let b : ℕ → ℝ := fun j => ε j / c
  have hbpos (j : ℕ) : 0 < b j := div_pos (hεpos j) hc
  have hbanti : Antitone b := fun i j hij => div_le_div_of_nonneg_right (hεanti hij) hc.le
  have hblim : Tendsto b atTop (𝓝 0) := by
    simpa only [zero_div] using hεlim.div_const c
  have hbform (j : ℕ) : η + b j • Ω.form = η + ε j • ρ.form := by
    dsimp only [b, Ω, KahlerBackground.smul_form]
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']
  have hΓform : η + (b 0 + 1) • Ω.form = Γ := by
    have hcoeff : (ε 0 / c + 1) * c = 1 + c := by
      rw [hεzero]
      field_simp
    dsimp only [b, Ω, KahlerBackground.smul_form, Γ]
    rw [smul_smul, hcoeff]
  have hvb (j : ℕ) : IsModelPotential (η + b j • Ω.form) (v j) := by
    simpa only [hbform j] using hv j
  have hIb (j : ℕ) : IsIModelPotential (η + b j • Ω.form).val (v j) := by
    simpa only [hbform j] using hIv j
  have hvlimΩ := (TraceTargetAuxiliaryIndependence.tendsto_native_iff_auxiliary_choices
    ρ Ω Γ hΓ atTop (fun j => (⟨v j, hGv j⟩ : ThetaPshL1 Γ.val)) ⟨τ, hτΓ⟩).mp hvlim
  have hΓb : IsBigClass (RealBottChern.ofRepresentative (η + (b 0 + 1) • Ω.form)) := by
    simpa only [hΓform] using hΓ
  have hGvb (j : ℕ) : IsThetaPshPotential (η + (b 0 + 1) • Ω.form).val (v j) := by
    simpa only [hΓform] using hGv j
  have hτb : IsThetaPshPotential (η + (b 0 + 1) • Ω.form).val τ := by
    simpa only [hΓform] using hτΓ
  have hgoodτb : IGoodWith (η + (b 0 + 1) • Ω.form) τ hτb := by
    simpa only [hΓform] using hgoodτ
  have hvlimb : Tendsto (fun j => (⟨v j, hGvb j⟩ : ThetaPshL1 (η + (b 0 + 1) • Ω.form).val)) atTop
      (@nhds (ThetaPshL1 (η + (b 0 + 1) • Ω.form).val)
        (singularityPseudoMetricSpace Ω (η + (b 0 + 1) • Ω.form) hΓb).toUniformSpace.toTopologicalSpace
        ⟨τ, hτb⟩) := by
    exact (SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
      Ω Γ (η + (b 0 + 1) • Ω.form) hΓ hΓb atTop hGv hτΓ hGvb hτb).mp hvlimΩ
  have hnum (j : ℕ) : numericalTraceMass omega omegaV hι (θ + ε j • omega.form) (W j) =
      diagonalPotentialMass (η + ε j • ρ.form) (v j) (hv j).plurisubharmonic := by
    simp only [numericalTraceMass, dif_pos (hdefined j), hpullform j]
    rfl
  have horiginal : numericalTraceMass omega omegaV hι θ (thetaPshSupremum θ.val) = L := by
    by_cases hpos : 0 < L
    · have hclass : SourcePEquivalent (n := k) H τ :=
        VaryingIModelNativeGlobalClass.sourcePEquivalent_iInf_of_native_varying_iModels
          Ω η hbpos hbanti hblim hvb hIb hvanti hpos hΓb hGvb hτb hgoodτb hvlimb
      have hTH : IsTraceRepresentativeAlong omega omegaV hι (thetaPshSupremum θ.val) H :=
        TraceRepresentativeGlobalPClass.isTraceRepresentativeAlong_of_sourcePEquivalent
          omegaV hι hT hclass.symm
      have hd : HasPositiveTraceRepresentativeAlong omega omegaV hι θ (thetaPshSupremum θ.val) :=
        ⟨H, hTH, hH, hpos⟩
      exact numericalTraceMass_eq_of_positive_reader omegaV omegaV hι θ
        (thetaPshSupremum θ.val) hd hTH hH hpos
    · have hzero : L = 0 := le_antisymm (not_lt.mp hpos) zero_le
      have hundefined : ¬ HasPositiveTraceRepresentativeAlong omega omegaV hι θ (thetaPshSupremum θ.val) := by
        intro hd
        let A := normalizedTraceAlong omega omegaV hι θ (thetaPshSupremum θ.val) hd
        have hA : IsModelPotential η A :=
          (normalizedTraceAlong_models omega omegaV hι θ (thetaPshSupremum θ.val) hd).1
        have hAv (j : ℕ) : A ≤ v j := by
          have hdiff : θ + ε j • omega.form - θ = ε j • omega.form := by module
          have hsemi' : (θ + ε j • omega.form - θ).val.IsSemipositive := by
            rw [hdiff]
            exact KahlerDomination.isSemipositive_smul omega.isSemipositive (hεpos j).le
          exact NormalizedTraceIdealOrderComparison.normalizedTraceAlong_le_of_iOrder_of_semipositive_difference
            omega omega omegaV omegaV hι θ (θ + ε j • omega.form)
            (iOrderOnManifold_of_le (hW j).1.quasiPlurisubharmonic (hVW j)) hsemi' hd (hdefined j)
        have hAH : A ≤ H := le_iInf hAv
        have hmass : diagonalPotentialMass η A hA.plurisubharmonic ≤ L :=
          diagonalPotentialMass_mono_of_kahler ρ hA.plurisubharmonic hH
            (MoreSingularOn.of_le fun y _ => hAH y)
        exact (hA.positive_mass.trans_le hmass).ne' hzero
      exact (numericalTraceMass_eq_zero_of_undefined omega omegaV hι θ
        (thetaPshSupremum θ.val) hundefined).trans hzero.symm
  rw [horiginal]
  exact hm.congr (fun j => (hnum j).symm)

end
end SGPT.Foundations.Analysis.Pending.MinimalPotentialNumericalTraceSequence
