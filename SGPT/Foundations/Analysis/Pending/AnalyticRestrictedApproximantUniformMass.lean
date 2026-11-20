import SGPT.Foundations.Analysis.Pending.AnalyticQuasiEquisingularRestriction
import SGPT.Foundations.Analysis.Pending.AdmissibleTraceBackgroundMargin
import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

set_option autoImplicit false

/-! # Actual restricted analytic approximants have a uniform positive mass floor -/

open Set MeasureTheory
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.AnalyticRestrictedApproximantUniformMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.QuasiEquisingularApproximation FirstPass.TraceBackground
  DiagonalMass MixedMass GlobalNonPluripolar MixedMassBoundedDifference
  CanonicalBackgroundPolynomial SingularPBackgroundMassPolynomial
  PluripolarCapacityDichotomy

noncomputable section

variable {k : ℕ} {V : Type*} [TopologicalSpace V]
  [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [MeasurableSpace V] [BorelSpace V] [CompactSpace V]

/-- A typed real coefficient estimate keeps the actual diagonal expansion
separate from finite extended-mass realification. -/
private theorem unit_floor_real (omega : KahlerBackground k V)
    {θ : ClosedRealOneOneForm k V} {u : V → EReal}
    (hu : IsThetaPshPotential θ.val u) {a : ℝ} (ha : 0 < a) :
    a ^ k * (diagonalPotentialMass omega.form (fun _ => 0)
      (isThetaPshPotential_zero omega)).toReal ≤
      (diagonalPotentialMass (θ + a • omega.form) u
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hu
          (KahlerDomination.isSemipositive_smul omega.isSemipositive ha.le))).toReal := by
  classical
  let p : ∀ i : Fin k, IsThetaPshPotential θ.val u := fun _ => hu
  have hexp := globalMixedMass_add_background_toReal_eq_sum omega p ha
  have hnone : (fun _ : Fin k => (none : Option (Fin k))) ∈
      Fintype.piFinset (backgroundChoices (n := k)) := by
    simp [Fintype.mem_piFinset, backgroundChoices]
  have hle : a ^ backgroundDegree (fun _ : Fin k => (none : Option (Fin k))) *
      (globalMixedMass (fun i => optForm omega (fun _ => θ) ((fun _ => none) i))
        (fun i => optPot (fun _ => u) ((fun _ => none) i))
        (fun i => optPot_psh omega p ((fun _ => none) i))).toReal ≤
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := k)), a ^ backgroundDegree g *
        (globalMixedMass (fun i => optForm omega (fun _ => θ) (g i))
          (fun i => optPot (fun _ => u) (g i)) (fun i => optPot_psh omega p (g i))).toReal := by
    exact Finset.single_le_sum
      (f := fun g => a ^ backgroundDegree g *
        (globalMixedMass (fun i => optForm omega (fun _ => θ) (g i))
          (fun i => optPot (fun _ => u) (g i)) (fun i => optPot_psh omega p (g i))).toReal)
      (fun g _ => mul_nonneg (pow_nonneg ha.le (backgroundDegree g)) ENNReal.toReal_nonneg)
      hnone
  have hdegree : backgroundDegree (fun _ : Fin k => (none : Option (Fin k))) = k := by
    simp [backgroundDegree]
  have hcoeff : globalMixedMass
      (fun i : Fin k => optForm omega (fun _ => θ) ((fun _ => none) i))
      (fun i => optPot (fun _ => u) ((fun _ => none) i))
      (fun i => optPot_psh omega p ((fun _ => none) i)) =
      diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega) := rfl
  rw [hdegree, hcoeff, ← hexp] at hle
  exact hle

/-- The actual all-Kähler coefficient is a uniform extended mass floor. -/
theorem diagonalPotentialMass_zero_le_add_unit (omegaV : KahlerBackground k V)
    {γ : ClosedRealOneOneForm k V} {v : V → EReal}
    (hv : IsThetaPshPotential γ.val v) :
    diagonalPotentialMass omegaV.form (fun _ => 0) (isThetaPshPotential_zero omegaV) ≤
      diagonalPotentialMass (γ + omegaV.form) v
        (LocalPotentials.isThetaPshPotential_add_of_semipositive hv omegaV.isSemipositive) := by
  let hzero := isThetaPshPotential_zero omegaV
  let henlarged :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv omegaV.isSemipositive
  have hfinite0 : diagonalPotentialMass omegaV.form (fun _ => 0) hzero ≠ ⊤ :=
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => hzero.1) univ).ne
  have hfinite1 : diagonalPotentialMass (γ + omegaV.form) v henlarged ≠ ⊤ :=
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => henlarged.1) univ).ne
  have hreal : (diagonalPotentialMass omegaV.form (fun _ => 0) hzero).toReal ≤
      (diagonalPotentialMass (γ + omegaV.form) v henlarged).toReal := by
    simpa only [one_pow, one_mul, one_smul] using unit_floor_real omegaV hv zero_lt_one
  exact (ENNReal.toReal_le_toReal hfinite0 hfinite1).mp hreal

/-- All target geometry, genuine restrictions, and the single positive
mass constant are internally produced from the actual approximation. -/
theorem exists_admissible_background_uniform_positive_restricted_mass
    [ConnectedSpace V] {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {omega : KahlerBackground n M} (omegaV : KahlerBackground k V)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (happ : IsQuasiEquisingularApproximation omega θ u ε uSeq)
    {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (hgeneric : (⨅ y : V, lelongNumber (n := n) u (ι y)) = 0) :
    ∃ C : ℝ, 0 < C ∧
      IsAdmissibleTraceBackground hι omega θ ε (C • omegaV.form) ∧
      ∃ hterms : ∀ j, IsThetaPshPotential (C • omegaV.form).val (fun y => uSeq j (ι y)),
        ∃ δ : ℝ, 0 < δ ∧ ∀ j,
          ENNReal.ofReal δ ≤ diagonalPotentialMass (C • omegaV.form)
            (fun y => uSeq j (ι y)) (hterms j) := by
  obtain ⟨C, hC, hadm, hmargin⟩ :=
    AdmissibleTraceBackgroundMargin.exists_admissible_background_with_uniform_margin
      hι omega omegaV θ happ.error_antitone
  have hgamma (j : ℕ) : IsThetaPshPotential (C • omegaV.form - omegaV.form).val
      (fun y => uSeq j (ι y)) := by
    have hp := AnalyticQuasiEquisingularRestriction.isThetaPshPotential_ordinaryRestriction_term
      happ hι hgeneric j
    have hplus := LocalPotentials.isThetaPshPotential_add_of_semipositive hp (hmargin j)
    have hforms : ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) +
        (C • omegaV.form - ClosedRealOneOneForm.pullback hι (θ + ε j • omega.form) -
          omegaV.form) = C • omegaV.form - omegaV.form := by module
    simpa only [hforms] using hplus
  have hterms (j : ℕ) : IsThetaPshPotential (C • omegaV.form).val
      (fun y => uSeq j (ι y)) := by
    simpa only [sub_add_cancel] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive (hgamma j) omegaV.isSemipositive
  let hzero := isThetaPshPotential_zero omegaV
  let δ : ℝ := (diagonalPotentialMass omegaV.form (fun _ => 0) hzero).toReal
  have hvolpos : 0 < δ := ENNReal.toReal_pos
    (KahlerVolumePositive.diagonalPotentialMass_zero_pos omegaV).ne'
    (globalMixedMeasure_apply_lt_top omegaV (fun _ : Fin k => hzero.1) univ).ne
  refine ⟨C, hC, hadm, hterms, δ, hvolpos, ?_⟩
  intro j
  have hfloor : diagonalPotentialMass omegaV.form (fun _ => 0) hzero ≤
      diagonalPotentialMass (C • omegaV.form) (fun y => uSeq j (ι y)) (hterms j) := by
    simpa only [sub_add_cancel] using diagonalPotentialMass_zero_le_add_unit omegaV (hgamma j)
  exact ENNReal.ofReal_toReal_le.trans hfloor

end

end SGPT.Foundations.Analysis.Pending.AnalyticRestrictedApproximantUniformMass
