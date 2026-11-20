import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergy
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-!
# Actual full mass from uniform singular truncation bounds

An independent singular-truncation adaptation of the actual Markov/locality
mass argument on Xia SGPT PDF0132. Actual own-gap integral bounds on genuine
same-type truncations produce full mass; their actual energy lower bounds
then produce finite-energy membership. The full-mass source domain of the
existing Proposition 3.1.17 characterization is kept unchanged and is used
only after full mass has been produced. No bounded model is assumed.
-/

open Set Filter MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelUniformTruncationFullMass

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeEnergyIntegrability
  SingularModelEnergyTruncation SingularModelEnergyTruncationGap
  SingularModelEnergyEndpointBounds DiagonalMass MongeAmpereEnergyDecreasing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual uniform own-gap bounds on genuine singular max truncations produce full mass. -/
theorem relativeFullMass_of_uniform_truncation_gap_bound (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hule : u ≤ φ) {K : ℝ}
    (hK : ∀ j : ℕ, (∫ x, canonicalERealDiffToReal (φ x) (truncation φ u j x)
      ∂diagonalPotentialMeasure θ (truncation φ u j)
        (relativeEInfinity_truncation hφ.plurisubharmonic hu
          (MoreSingularOn.of_le fun x _ => hule x) j).1) ≤ K) :
    RelativeFullMass θ φ u hφ := by
  let huφ : MoreSingularOn u φ univ := MoreSingularOn.of_le fun x _ => hule x
  let htj := fun j => relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j
  let μ := diagonalPotentialMeasure θ u hu
  let μj := fun j => diagonalPotentialMeasure θ (truncation φ u j) (htj j).1
  let A := fun j : ℕ => {x | φ x - ((j : ℝ) : EReal) < u x}
  let g := fun j x => canonicalERealDiffToReal (φ x) (truncation φ u j x)
  let m := diagonalPotentialMass θ φ hφ.plurisubharmonic
  let : IsFiniteMeasure μ :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hu
  have hmfin : m ≠ ⊤ :=
    GlobalNonPluripolar.globalMixedMeasure_apply_lt_top omega (fun _ => hφ.plurisubharmonic.1) univ |>.ne
  have hμjfin (j : ℕ) : IsFiniteMeasure (μj j) :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ (htj j).1
  have hAm (j : ℕ) : MeasurableSet (A j) :=
    FiniteEnergyCharacterization.measurableSet_lt_truncation hφ.plurisubharmonic.1 hu.1 j
  have hgnn (j : ℕ) (x : M) : 0 ≤ g j x := by
    have h := canonicalDiff_nonpos_of_le_of_sameType
      (htj j).1.1.quasiPlurisubharmonic.ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top
      (htj j).2 (FiniteEnergyCharacterization.truncation_le hule j) x
    dsimp only [g]
    rw [canonicalERealDiffToReal_swap]
    linarith
  have hint (j : ℕ) : Integrable (g j) (μj j) :=
    integrable_canonicalDiff_globalMixedMeasure omega hφ.plurisubharmonic.1 (htj j).1.1
      (htj j).2.symm (fun _ => (htj j).1.1)
  have hKnn : 0 ≤ K := (integral_nonneg (hgnn 0)).trans (hK 0)
  have htail (j : ℕ) : (j : ℝ) * (μj j).real (A j)ᶜ ≤ K := by
    let := hμjfin j
    have hpole : ∀ᵐ x ∂μj j, φ x ≠ ⊥ := by
      have hz : μj j {x | φ x = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n => (htj j).1.1) hφ.plurisubharmonic
      exact ae_iff.mpr (by simpa only [not_not] using hz)
    have heq : g j =ᵐ[(μj j).restrict (A j)ᶜ] fun _ => (j : ℝ) := by
      filter_upwards [ae_restrict_of_ae hpole, ae_restrict_mem (hAm j).compl] with x hx hxA
      exact canonicalDiff_truncation_tail (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
        hx j (not_lt.mp hxA)
    have hIA : 0 ≤ ∫ x in A j, g j x ∂μj j := integral_nonneg (hgnn j)
    have hIc : (∫ x in (A j)ᶜ, g j x ∂μj j) = (j : ℝ) * (μj j).real (A j)ᶜ := by
      rw [integral_congr_ae heq, setIntegral_const, smul_eq_mul, mul_comm]
    have hsplit := integral_add_compl (hAm j) (hint j)
    have hbound := hK j
    change (∫ x, g j x ∂μj j) ≤ K at hbound
    linarith
  have hloc (j : ℕ) : μ (A j) = μj j (A j) := by
    have h := FiniteEnergyCharacterization.diagonalPotentialMeasure_truncation_restrict
      θ hφ.plurisubharmonic hu j (htj j).1
    rw [← Measure.restrict_apply_self, ← Measure.restrict_apply_self (μj j)]
    exact congrArg (fun ν : Measure M => ν (A j)) h.symm
  have huniv (j : ℕ) : μj j univ = m :=
    diagonalPotentialMeasure_truncation_univ omega θ hφ.plurisubharmonic hu huφ j
  have hAmass (j : ℕ) : μ.real (A j) = m.toReal - (μj j).real (A j)ᶜ := by
    let := hμjfin j
    have h3 := measureReal_add_measureReal_compl (μ := μj j) (hAm j)
    have h4 : (μj j).real univ = m.toReal := congrArg ENNReal.toReal (huniv j)
    have h5 : μ.real (A j) = (μj j).real (A j) := congrArg ENNReal.toReal (hloc j)
    linarith
  have hle : μ univ ≤ m :=
    GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
      (fun _ : Fin n => hu) (fun _ => hφ.plurisubharmonic) (fun _ => huφ)
  have hge : m.toReal ≤ μ.real univ := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hKnn hε.le) hN
    have hcompl : (μj N).real (A N)ᶜ < ε := by
      have hm : (μj N).real (A N)ᶜ ≤ K / N := by
        apply (le_div_iff₀ hNpos).mpr
        nlinarith [htail N]
      have hKN : K / N < ε := by
        apply (div_lt_iff₀ hNpos).mpr
        have h := (div_lt_iff₀ hε).mp hN
        nlinarith
      exact hm.trans_lt hKN
    have h2 : μ.real (A N) ≤ μ.real univ := measureReal_mono (subset_univ _)
    have h3 := hAmass N
    linarith
  refine ⟨hu, hule, le_antisymm hle ?_⟩
  exact (ENNReal.toReal_le_toReal hmfin (measure_ne_top _ _)).mp hge

/-- Actual uniform finite same-type truncation energy lower bounds produce actual E1 membership. -/
theorem relativeFiniteEnergy_of_uniform_truncation_energy_lower (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hule : u ≤ φ) {L : ℝ}
    (hL : ∀ j : ℕ, L ≤ relativeEnergyOfMinimalType θ φ (truncation φ u j)
      hφ.plurisubharmonic (relativeEInfinity_truncation hφ.plurisubharmonic hu
        (MoreSingularOn.of_le fun x _ => hule x) j).1) :
    RelativeFiniteEnergy θ φ u hφ := by
  have hfull := relativeFullMass_of_uniform_truncation_gap_bound (hφ := hφ) omega hu hule
    (K := -(((n : ℝ) + 1) * L)) (fun j => by
      have h := (SingularModelFiniteEnergy.neg_energy_le_integral_gap_le
        omega θ hφ.plurisubharmonic hu hule j).2
      have hm := mul_le_mul_of_nonneg_left (hL j) (by positivity : 0 ≤ (n : ℝ) + 1)
      linarith)
  apply (SingularModelFiniteEnergy.relativeFiniteEnergy_iff_bot_lt_energy omega θ hφ hfull).mpr
  refine lt_of_lt_of_le (EReal.bot_lt_coe L) ?_
  rw [energy_eq_iInf_truncation omega θ hφ hu (MoreSingularOn.of_le fun x _ => hule x)]
  exact le_iInf fun j => EReal.coe_le_coe_iff.mpr (hL j)

end

end SGPT.Foundations.Analysis.Pending.SingularModelUniformTruncationFullMass
