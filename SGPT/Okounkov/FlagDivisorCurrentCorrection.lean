import SGPT.Okounkov.DivisorMetricPullback
import SGPT.Okounkov.DivisorMetricAddition
import SGPT.Okounkov.FlagCorrectionRow
import SGPT.Okounkov.UnitDivisorCurrent

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff NNReal ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending IdealWeightPowers GermIdealTotalTransform
open GlobalCurrents CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

private theorem effectiveDivisor_ext_ideal_current {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {D E : EffectiveDivisor n M} (h : D.ideal = E.ideal) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- The actual canonical Cartier current of the reduced unit ideal is the
same whole unit current already used by the original residual recursion. -/
theorem effectiveDivisorIntegrationCurrent_unit_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))) :
    effectiveDivisorIntegrationCurrent F D = smoothDivisorIntegrationCurrent F.firstDivisor := by
  obtain ⟨E, _hsup, hE⟩ := DivisorMetric.exists_divisorMetric D
  exact (effectiveDivisorIntegrationCurrent_eq_of_metric F D E hE).trans
    (smoothDivisorIntegrationCurrent_eq_of_unit_metric F.firstDivisor D hDI E hE).symm

/-- An actual head-one Cartier step produces its same effective residual
as a literal complete current difference, with the actual restricted ideal. -/
theorem exists_current_residual_of_headOne_cartier_step {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier)
    (Dtail : EffectiveDivisor m F.tail.carrier)
    (hstep : OriginalCartierFlagStep F D 1 Dtail) :
    letI : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
    ∃ R : EffectiveDivisor (m + 1) F.carrier,
      ¬ F.flag (1 : Fin (m + 2)) ⊆ R.support ∧
      Dtail.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : F.tail.carrier → F.carrier) R.ideal ∧
      effectiveDivisorIntegrationCurrent F D - smoothDivisorIntegrationCurrent F.firstDivisor =
        effectiveDivisorIntegrationCurrent F R := by
  let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  obtain ⟨R, _ha, hDR, hnot, htail⟩ := hstep
  obtain ⟨L, hLI, _E, _hsup, _hE, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms F.firstDivisor
  have hpow : idealPow (vanishingIdeal (n := m + 1)
      (F.flag (1 : Fin (m + 2)))) 1 = L.ideal := by
    rw [idealPow_succ, idealPow_zero, ← hLI]
    exact BlowupControlledTransform.unitIdeal_mul
      (DivisorMetric.isCoherent_of_isInvertible L.isInvertible)
  have hsum : D = GermIdealTotalTransform.EffectiveDivisor.add L R := by
    apply effectiveDivisor_ext_ideal_current
    change D.ideal = L.ideal.mul R.ideal
    rw [hDR, hpow]
  refine ⟨R, hnot, htail, ?_⟩
  rw [hsum, effectiveDivisorIntegrationCurrent_add_eq,
    effectiveDivisorIntegrationCurrent_unit_eq F L hLI]
  exact add_sub_cancel_left (smoothDivisorIntegrationCurrent F.firstDivisor)
    (effectiveDivisorIntegrationCurrent F R)

/-- Original lifting data manufacture the whole effective unit-current
residual and its literal Cartier restriction and independent integer tail. -/
theorem IsFlagLifting.exists_totalTransform_unit_current_decomposition {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π)
    (D : EffectiveDivisor (m + 1) F.carrier)
    (hDI : D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2)))) :
    letI : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
    ∃ (R : EffectiveDivisor (m + 1) W.carrier)
      (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ),
      OriginalCartierFlagStep W
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
      OriginalCartierFlagValuation m W.tail Dtail ν ∧
      ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support ∧
      Dtail.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : W.tail.carrier → W.carrier) R.ideal ∧
      effectiveDivisorIntegrationCurrent W
          (GermIdealTotalTransform.EffectiveDivisor.totalTransform
            hπ.1.1 hπ.interior_exceptional_eq_empty D) -
        smoothDivisorIntegrationCurrent W.firstDivisor = effectiveDivisorIntegrationCurrent W R := by
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  obtain ⟨Dtail, ν, hstep, hν⟩ := hπ.exists_effective_exceptional_divisor D hDI
  obtain ⟨R, hnot, htail, hcur⟩ := exists_current_residual_of_headOne_cartier_step W _ Dtail hstep
  exact ⟨R, Dtail, ν, hstep, hν, hnot, htail, hcur⟩

/-- Genuine Cartier/current compatibility and independent vector uniqueness
read the complete total-transform current as its actual head and integer tail. -/
theorem currentFlagValuation_totalTransform_eq_of_cartier_step {m : ℕ}
    (W : OriginalFlagGeometry.{u} (m + 1))
    (DA : EffectiveDivisor (m + 1) W.carrier)
    (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ)
    (hstep : OriginalCartierFlagStep W DA 1 Dtail)
    (hν : OriginalCartierFlagValuation m W.tail Dtail ν) :
    currentFlagValuation W (effectiveDivisorIntegrationCurrent W DA)
      (effectiveDivisorIntegrationCurrent_closed_type_positive W DA).1
      (effectiveDivisorIntegrationCurrent_closed_type_positive W DA).2.1
      (effectiveDivisorIntegrationCurrent_closed_type_positive W DA).2.2 =
      (fun i => ((Fin.cons (1 : ℕ) ν : Fin (m + 1) → ℕ) i : ℝ≥0)) := by
  have hcons : OriginalCartierFlagValuation (m + 1) W DA (Fin.cons (1 : ℕ) ν) := by
    refine ⟨Dtail, ?_, ?_⟩
    · simpa only [Fin.cons_zero] using hstep
    · simpa only [Fin.cons_succ] using hν
  obtain ⟨μ, hμ, hcur⟩ := exists_currentFlagValuation_effectiveDivisor_eq_integer_vector W DA
  have hμν : μ = Fin.cons (1 : ℕ) ν := originalCartierFlagValuation_unique W DA hμ hcons
  rwa [hμν] at hcur

/-- The lifting alone supplies an actual whole-current realization of
the selected row, with its effective residual and literal restricted tail. -/
theorem IsFlagLifting.exists_unit_current_correction_row {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) :
    letI : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
    ∃ (D : EffectiveDivisor (m + 1) F.carrier)
      (R : EffectiveDivisor (m + 1) W.carrier)
      (Dtail : EffectiveDivisor m W.tail.carrier) (ν : Fin m → ℕ),
      D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
      OriginalCartierFlagStep W
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
      OriginalCartierFlagValuation m W.tail Dtail ν ∧
      ¬ W.flag (1 : Fin (m + 2)) ⊆ R.support ∧
      Dtail.ideal = GermIdeal.pullback (m := m)
        (Subtype.val : W.tail.carrier → W.carrier) R.ideal ∧
      effectiveDivisorIntegrationCurrent W
          (GermIdealTotalTransform.EffectiveDivisor.totalTransform
            hπ.1.1 hπ.interior_exceptional_eq_empty D) -
        smoothDivisorIntegrationCurrent W.firstDivisor = effectiveDivisorIntegrationCurrent W R ∧
      flagLiftingCorrectionRow hπ = (fun i => (ν i : ℤ)) ∧
      currentFlagValuation W
          (effectiveDivisorIntegrationCurrent W (GermIdealTotalTransform.EffectiveDivisor.totalTransform
            hπ.1.1 hπ.interior_exceptional_eq_empty D))
          (effectiveDivisorIntegrationCurrent_closed_type_positive W _).1
          (effectiveDivisorIntegrationCurrent_closed_type_positive W _).2.1
          (effectiveDivisorIntegrationCurrent_closed_type_positive W _).2.2 =
        (fun i => ((Fin.cons (1 : ℕ) ν : Fin (m + 1) → ℕ) i : ℝ≥0)) := by
  let : ChartedSpace (ComplexModel m) (W.flag (1 : Fin (m + 2))) := W.tail.charts
  obtain ⟨D, hDI, _E, _hsup, _hE, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms F.firstDivisor
  obtain ⟨R, Dtail, ν, hstep, hν, hnot, htail, hcur⟩ :=
    hπ.exists_totalTransform_unit_current_decomposition D hDI
  refine ⟨D, R, Dtail, ν, hDI, hstep, hν, hnot, htail, hcur, ?_, ?_⟩
  · exact flagLiftingCorrectionRow_eq_of_spec hπ ⟨D, hDI, Dtail, hstep, ν, hν, rfl⟩
  · exact currentFlagValuation_totalTransform_eq_of_cartier_step W _ Dtail ν hstep hν

end SGPT.Okounkov
