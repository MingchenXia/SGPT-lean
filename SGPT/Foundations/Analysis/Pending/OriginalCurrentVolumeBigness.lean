import SGPT.Foundations.Analysis.Pending.OriginalCurrentACVolume
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.ThetaCurrentGlobalACDomination
import SGPT.Foundations.Analysis.Pending.OriginalCurrentAnalyticACMajorization
import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMonotonicity

set_option autoImplicit false

/-!
# The original-current Grauert--Riemenschneider criterion

Complete blueprint statements and ENTIRE proofs precede this source.
Positive volume internally chooses an original current, its actual potential
and its positive NP mass; the genuine proved mass-bigness theorem constructs
the Kähler current. Conversely its actual smooth lower bound contributes a
positive original AC mass. No calibration or uniform bound is an input.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeBigness

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold CurrentBottChernClass CanonicalCurrentFrame
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  NaturalThetaPshGeometricCurrent ThetaPotentialCurrentBottChernClass
  OriginalCurrentACVolume DiagonalMass IntegrationCurrent

private theorem zero_has_analytic_type
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] :
    HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) (fun _ : X => 0) := by
  intro e z _
  let one : Fin 1 → ComplexModel n → ℂ := fun _ _ => 1
  have hlog (y : ComplexModel n) : generatorLog one y = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  refine ⟨1, 1, one, one_pos, ⟨univ, isOpen_univ, mem_univ _,
    fun _ => differentiableOn_const 1⟩, fun _ => 0,
    boundedRealGermAt_of_continuousAt continuousAt_const,
    Eventually.of_forall fun _ _ => contDiffAt_const,
    Eventually.of_forall fun y => ?_⟩
  simp only [chartFunction, hlog, mul_zero, EReal.coe_zero, add_zero]

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]

private theorem fullPositive_add
    {S T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hT : IsFullPositive T) : IsFullPositive (S + T) := by
  intro e ψ hψ
  exact add_nonneg (hS e ψ hψ) (hT e ψ hψ)

private theorem global_ac_congr [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    {T S : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hT : IsFullPositive T) (hS : IsFullPositive S) (heq : T = S) :
    globalACtopMeasure T hT = globalACtopMeasure S hS := by
  subst S
  rfl

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
private theorem class_add
    (S T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (S + T) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S +
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T :=
  (bottChernClassLinearMap (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_add S T

/-- Positive original-current volume internally supplies an actual Kähler
current in the SAME original smooth Bott--Chern class. -/
theorem isBigClass_of_originalCurrentACVolume_pos [ConnectedSpace X] [Nonempty X]
    (ω : KahlerBackground (m + 1) X) {α : RealBottChern (m + 1) X}
    (hvol : 0 < originalCurrentACVolume α) : IsBigClass α := by
  obtain ⟨T, hT, hclass, hmass⟩ := exists_current_mass_gt α hvol
  obtain ⟨θ, v, hv, heq, _hreader⟩ :=
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      T.val T.property.1 T.property.2 hT
  have hTc : T = thetaClosedCurrent θ v hv := Subtype.ext heq
  have hθ : RealBottChern.ofRepresentative θ = α := by
    rw [← bottChernClass_thetaClosedCurrent θ v hv, ← hTc]
    exact hclass
  let hpos : IsFullPositive (thetaPotentialCurrent θ.val v hv) :=
    thetaPotentialCurrent_full_positive θ.val v hv
  have hmass' : 0 < globalACtopMeasure (thetaPotentialCurrent θ.val v hv) hpos univ := by
    rw [← global_ac_congr hT hpos heq]
    exact hmass
  have hAC := ThetaCurrentGlobalACDomination.globalACtopMeasure_le_globalMixedMeasure ω θ hv
  have hNP : 0 < diagonalPotentialMass θ v hv :=
    hmass'.trans_le (Measure.le_iff'.mp hAC univ)
  have hbig := BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos
    (Nat.succ_pos m) ω θ hv hNP
  simpa only [hθ] using hbig

/-- The genuine Kähler lower bound itself supplies a strictly positive AC
benchmark for the original volume; no specified background is required. -/
theorem originalCurrentACVolume_pos_of_isBigClass [Nonempty X]
    {α : RealBottChern (m + 1) X} (hbig : IsBigClass α) :
    0 < originalCurrentACVolume α := by
  obtain ⟨K⟩ := hbig
  let S := thetaClosedCurrent (K.representative - K.lowerBound.form) K.potential K.strictlyPsh
  have hS : IsFullPositive S.val :=
    thetaPotentialCurrent_full_positive _ _ K.strictlyPsh
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff K.lowerBound.form).mpr
    K.lowerBound.isSemipositive
  let D := thetaClosedCurrent K.lowerBound.form (fun _ => 0) hu
  have hD : IsFullPositive D.val := thetaPotentialCurrent_full_positive _ _ hu
  have hsum : IsFullPositive (D + S).val := fullPositive_add hD hS
  have hclass : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (D + S) = α := by
    rw [class_add, bottChernClass_thetaClosedCurrent, bottChernClass_thetaClosedCurrent,
      sub_eq_add_neg, RealBottChern.ofRepresentative_add, RealBottChern.ofRepresentative_neg]
    calc
      RealBottChern.ofRepresentative K.lowerBound.form +
          (RealBottChern.ofRepresentative K.representative +
            -RealBottChern.ofRepresentative K.lowerBound.form) =
          RealBottChern.ofRepresentative K.representative := by abel
      _ = α := K.represents
  have hmeasure : globalACtopMeasure D.val hD = kahlerVolume K.lowerBound :=
    OriginalCurrentAnalyticACMajorization.globalACtopMeasure_theta_analytic_eq
      K.lowerBound.form hu zero_has_analytic_type
  have hΩ : 0 < kahlerVolume K.lowerBound univ := by
    have hreal := NefCoreKahlerCurrent.kahlerVolume_real_univ_pos K.lowerBound
    exact ENNReal.toReal_pos_iff.mp hreal |>.1
  calc
    0 < globalACtopMeasure D.val hD univ := by rw [hmeasure]; exact hΩ
    _ ≤ globalACtopMeasure (D + S).val hsum univ := Measure.le_iff'.mp
      (PositiveCurrentACTopMonotonicity.globalACtopMeasure_le_add D.val S.val hD hS) univ
    _ ≤ originalCurrentACVolume α := ac_top_mass_le_volume (D + S) hsum hclass

/-- The literal two-way criterion for the original-current volume. -/
theorem isBigClass_iff_originalCurrentACVolume_pos [ConnectedSpace X] [Nonempty X]
    (ω : KahlerBackground (m + 1) X) (α : RealBottChern (m + 1) X) :
    IsBigClass α ↔ 0 < originalCurrentACVolume α :=
  ⟨originalCurrentACVolume_pos_of_isBigClass, isBigClass_of_originalCurrentACVolume_pos ω⟩

end SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeBigness
