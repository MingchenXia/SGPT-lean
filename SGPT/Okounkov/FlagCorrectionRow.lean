import SGPT.Okounkov.FlagLiftingExceptionalDivisor
import SGPT.Okounkov.EffectiveDivisorPotentialCompatibility
import SGPT.Foundations.Analysis.Pending.BlowupControlledTransform

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov

open Set
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending IdealWeightPowers
open AnalyticModificationLocalDiscrepancy InvertibleIdealQuotient

private theorem effectiveDivisor_ext_ideal {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    {D E : EffectiveDivisor n M} (h : D.ideal = E.ideal) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- Actual invertible-ideal colon cancellation identifies any two literal
tail divisors in the same source Cartier step. -/
theorem originalCartierFlagStep_tail_unique {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier) (a : ℕ)
    {Dtail E : EffectiveDivisor m F.tail.carrier}
    (hD : OriginalCartierFlagStep F D a Dtail) (hE : OriginalCartierFlagStep F D a E) :
    Dtail = E := by
  let : ChartedSpace (ComplexModel m) (F.flag (1 : Fin (m + 2))) := F.tail.charts
  obtain ⟨R, _ha, hDR, _hnotR, hDtail⟩ := hD
  obtain ⟨S, _haS, hDS, _hnotS, hEtail⟩ := hE
  obtain ⟨L, hLI, _EL, _hELsup, _hEL, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms F.firstDivisor
  have hLIpow : (idealPow (vanishingIdeal (n := m + 1)
      (F.flag (1 : Fin (m + 2)))) a).IsInvertible := by
    rw [← hLI]
    exact BlowupExceptionalDivisor.isInvertible_idealPow L.isInvertible a
  have hR : colon D.ideal (idealPow (vanishingIdeal (n := m + 1)
      (F.flag (1 : Fin (m + 2)))) a) = R.ideal := by
    rw [hDR]
    exact BlowupControlledTransform.colon_mul_eq hLIpow
      (DivisorMetric.isCoherent_of_isInvertible R.isInvertible)
  have hS : colon D.ideal (idealPow (vanishingIdeal (n := m + 1)
      (F.flag (1 : Fin (m + 2)))) a) = S.ideal := by
    rw [hDS]
    exact BlowupControlledTransform.colon_mul_eq hLIpow
      (DivisorMetric.isCoherent_of_isInvertible S.isInvertible)
  apply effectiveDivisor_ext_ideal
  rw [hDtail, hEtail, hR.symm.trans hS]

/-- Independent actual Cartier data for the source row: the reduced original
unit divisor, its actual total transform, head one, and literal tail vector. -/
def OriginalFlagCorrectionRow {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) (c : Fin m → ℤ) : Prop :=
  ∃ D : EffectiveDivisor (m + 1) F.carrier,
    D.ideal = vanishingIdeal (n := m + 1) (F.flag (1 : Fin (m + 2))) ∧
    ∃ Dtail : EffectiveDivisor m W.tail.carrier,
      OriginalCartierFlagStep W
        (GermIdealTotalTransform.EffectiveDivisor.totalTransform
          hπ.1.1 hπ.interior_exceptional_eq_empty D) 1 Dtail ∧
      ∃ ν : Fin m → ℕ, OriginalCartierFlagValuation m W.tail Dtail ν ∧
        c = fun i => (ν i : ℤ)

/-- The original geometry manufactures every actual correction row datum,
without an assumed residual, integer vector, or matrix certificate. -/
theorem exists_originalFlagCorrectionRow {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    ∃ c : Fin m → ℤ, OriginalFlagCorrectionRow hπ c := by
  obtain ⟨D, hDI, _E, _hEsup, _hE, _hnormal⟩ :=
    exists_normalized_smooth_divisor_metric_normal_forms F.firstDivisor
  obtain ⟨Dtail, ν, hstep, hν⟩ := hπ.exists_effective_exceptional_divisor D hDI
  exact ⟨fun i => (ν i : ℤ), D, hDI, Dtail, hstep, ν, hν, rfl⟩

/-- Reduced unit ideals and true Cartier cancellation identify all possible
rows from the same original lifting. -/
theorem originalFlagCorrectionRow_unique {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π)
    {c d : Fin m → ℤ} (hc : OriginalFlagCorrectionRow hπ c)
    (hd : OriginalFlagCorrectionRow hπ d) : c = d := by
  obtain ⟨D, hDI, Dtail, hstep, ν, hν, rfl⟩ := hc
  obtain ⟨E, hEI, Etail, hEstep, μ, hμ, rfl⟩ := hd
  have hDE : D = E := effectiveDivisor_ext_ideal (hDI.trans hEI.symm)
  subst E
  have htail : Dtail = Etail := originalCartierFlagStep_tail_unique W _ 1 hstep hEstep
  subst Etail
  have hνμ : ν = μ := originalCartierFlagValuation_unique W.tail Dtail hν hμ
  rw [hνμ]

/-- The actual integer row selected from proved original geometric existence. -/
def flagLiftingCorrectionRow {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) : Fin m → ℤ :=
  Classical.choose (exists_originalFlagCorrectionRow hπ)

theorem flagLiftingCorrectionRow_spec {m : ℕ} {F W : OriginalFlagGeometry.{u} (m + 1)}
    {π : W.carrier → F.carrier} (hπ : IsFlagLifting F W π) :
    OriginalFlagCorrectionRow hπ (flagLiftingCorrectionRow hπ) :=
  Classical.choose_spec (exists_originalFlagCorrectionRow hπ)

/-- Every true Cartier realization gives this same selected source row. -/
theorem flagLiftingCorrectionRow_eq_of_spec {m : ℕ}
    {F W : OriginalFlagGeometry.{u} (m + 1)} {π : W.carrier → F.carrier}
    (hπ : IsFlagLifting F W π) {c : Fin m → ℤ}
    (hc : OriginalFlagCorrectionRow hπ c) : flagLiftingCorrectionRow hπ = c :=
  originalFlagCorrectionRow_unique hπ (flagLiftingCorrectionRow_spec hπ) hc

end SGPT.Okounkov
