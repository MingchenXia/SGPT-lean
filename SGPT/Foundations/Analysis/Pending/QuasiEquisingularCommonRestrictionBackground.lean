import SGPT.Foundations.Analysis.Pending.QuasiEquisingularMaximum
import SGPT.Foundations.Analysis.Pending.AnalyticRestrictedApproximantUniformMass

set_option autoImplicit false

/-! # One internally produced positive background for two restricted QEA families -/

open Set MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularCommonRestrictionBackground

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  DiagonalMass GlobalNonPluripolar PluripolarCapacityDichotomy

noncomputable section

/-- The actual two approximation families produce one common sufficiently
positive target background and one positive mass floor for all three families. -/
theorem exists_common_background_uniform_positive_mass
    {n k : ℕ} {M V : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]
    [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
    [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε δ : ℕ → ℝ} {uSeq vSeq : ℕ → M → EReal}
    (hu : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    (hv : IsQuasiEquisingularApproximation omega θ u δ vSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ C : ℝ, 0 < C ∧
      IsAdmissibleTraceBackground hι omega θ (fun j => max (ε j) (δ j))
        (C • omegaV.form) ∧
      ∃ hU : ∀ j, IsThetaPshPotential (C • omegaV.form).val (fun y => uSeq j (ι y)),
      ∃ hV : ∀ j, IsThetaPshPotential (C • omegaV.form).val (fun y => vSeq j (ι y)),
      ∃ hW : ∀ j, IsThetaPshPotential (C • omegaV.form).val
        (fun y => max (uSeq j (ι y)) (vSeq j (ι y))),
      ∃ b : ℝ, 0 < b ∧ ∀ j,
        ENNReal.ofReal b ≤ diagonalPotentialMass (C • omegaV.form)
          (fun y => uSeq j (ι y)) (hU j) ∧
        ENNReal.ofReal b ≤ diagonalPotentialMass (C • omegaV.form)
          (fun y => vSeq j (ι y)) (hV j) ∧
        ENNReal.ofReal b ≤ diagonalPotentialMass (C • omegaV.form)
          (fun y => max (uSeq j (ι y)) (vSeq j (ι y))) (hW j) := by
  have hm := QuasiEquisingularMaximum.isQuasiEquisingularApproximation_max hu hv
  have hu' := QuasiEquisingularComparison.IsQuasiEquisingularApproximation.mono_error
    hu hm.2.1 fun j => le_max_left _ _
  have hv' := QuasiEquisingularComparison.IsQuasiEquisingularApproximation.mono_error
    hv hm.2.1 fun j => le_max_right _ _
  obtain ⟨C, hC, hadm, hmargin⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega omegaV θ hm.error_antitone
  have hγ (j : ℕ) {v : V → EReal}
      (hp : IsThetaPshPotential
        (ClosedRealOneOneForm.pullback hι (θ + max (ε j) (δ j) • omega.form)).val v) :
      IsThetaPshPotential (C • omegaV.form - omegaV.form).val v := by
    have hplus := LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hmargin j)
    have hforms : ClosedRealOneOneForm.pullback hι (θ + max (ε j) (δ j) • omega.form) +
        (C • omegaV.form -
          ClosedRealOneOneForm.pullback hι (θ + max (ε j) (δ j) • omega.form) -
            omegaV.form) = C • omegaV.form - omegaV.form := by module
    simpa only [hforms] using hplus
  have hγU (j : ℕ) : IsThetaPshPotential (C • omegaV.form - omegaV.form).val
      (fun y => uSeq j (ι y)) := hγ j
    (AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      hu' hι hgeneric j)
  have hγV (j : ℕ) : IsThetaPshPotential (C • omegaV.form - omegaV.form).val
      (fun y => vSeq j (ι y)) := hγ j
    (AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      hv' hι hgeneric j)
  have hγW (j : ℕ) : IsThetaPshPotential (C • omegaV.form - omegaV.form).val
      (fun y => max (uSeq j (ι y)) (vSeq j (ι y))) :=
    IsThetaPshPotential.max (hγU j) (hγV j)
  have henlarge {v : V → EReal}
      (hp : IsThetaPshPotential (C • omegaV.form - omegaV.form).val v) :
      IsThetaPshPotential (C • omegaV.form).val v := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hp omegaV.isSemipositive
  let hU := fun j => henlarge (hγU j)
  let hV := fun j => henlarge (hγV j)
  let hW := fun j => henlarge (hγW j)
  let hzero := isThetaPshPotential_zero omegaV
  let b : ℝ := (diagonalPotentialMass omegaV.form (fun _ => 0) hzero).toReal
  have hb : 0 < b := ENNReal.toReal_pos
    (KahlerVolumePositive.diagonalPotentialMass_zero_pos omegaV).ne'
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => hzero.1) univ).ne
  have hfloor {v : V → EReal}
      (hp : IsThetaPshPotential (C • omegaV.form - omegaV.form).val v)
      (hvβ : IsThetaPshPotential (C • omegaV.form).val v) :
      ENNReal.ofReal b ≤ diagonalPotentialMass (C • omegaV.form) v hvβ := by
    have hmass : diagonalPotentialMass omegaV.form (fun _ => 0) hzero ≤
        diagonalPotentialMass (C • omegaV.form) v hvβ := by
      simpa only [sub_add_cancel] using
        AnalyticRestrictedApproximantUniformMass.diagonalPotentialMass_zero_le_add_unit
          omegaV hp
    exact ENNReal.ofReal_toReal_le.trans hmass
  exact ⟨C, hC, hadm, hU, hV, hW, b, hb,
    fun j => ⟨hfloor (hγU j) (hU j), hfloor (hγV j) (hV j), hfloor (hγW j) (hW j)⟩⟩

end

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularCommonRestrictionBackground
