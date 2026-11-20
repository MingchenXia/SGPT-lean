import SGPT.Foundations.Analysis.Pending.PositiveCurrentACTopMonotonicity
import SGPT.Foundations.Analysis.Pending.PseudoeffectiveOriginalCurrentEquivalence
import SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeUpperSemicontinuity

set_option autoImplicit false

/-!
# The genuine Kähler right limit of original-current volume

The complete blueprint statements and ENTIRE proofs precede this source.
Semipositive addition internally produces the original positive sum and its
actual class. The internally chosen reciprocal path and actual quotient
continuity identify the entire right-neighborhood limit. No incoming volume
limit, class path, calibration or maximizing current is a hypothesis.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions
universe u
namespace SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeRightLimit

open FirstPass FirstPass.PositiveClasses CurrentBottChernClass CanonicalCurrentFrame
  ThetaPotentialCurrentBottChernClass NaturalThetaPshGeometricCurrent
  GlobalPositiveCurrentACRestriction GlobalPositiveCurrentACTopMeasure
  OriginalCurrentACVolume PseudoeffectiveOriginalCurrentEquivalence
  XiaoPureSmoothTopology XiaoPureSmoothBottChernClosure

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [CompactSpace X]

omit [CompactSpace X] in
private theorem fullPositive_add
    {S T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m))}
    (hS : IsFullPositive S) (hT : IsFullPositive T) : IsFullPositive (S + T) := by
  intro e ψ hψ
  exact add_nonneg (hS e ψ hψ) (hT e ψ hψ)

private theorem class_add
    (S T : ClosedOneOneCurrent (M := X) (canonicalBasis (m + 1)) (Nat.succ_pos m)) :
    bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (S + T) =
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) S +
      bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) T :=
  (bottChernClassLinearMap (canonicalBasis (m + 1)) (Nat.succ_pos m)).map_add S T

/-- Natural original pseudoeffectivity survives a genuine smooth semipositive
addition. The positive current and its actual class are produced internally. -/
theorem classPseudoeffective_add_semipositive
    {α : RealBottChern (m + 1) X} (hα : ClassPseudoeffectiveViaPotentials α)
    (η : ClosedRealOneOneForm (m + 1) X) (hη : η.val.IsSemipositive) :
    ClassPseudoeffectiveViaPotentials (α + RealBottChern.ofRepresentative η) := by
  obtain ⟨T, hT, hclass⟩ :=
    (classPseudoeffectiveViaPotentials_iff_exists_original_current α).mp hα
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη
  let D := thetaClosedCurrent η (fun _ => 0) hu
  have hD : IsFullPositive D.val := thetaPotentialCurrent_full_positive η.val (fun _ => 0) hu
  apply (classPseudoeffectiveViaPotentials_iff_exists_original_current _).mpr
  refine ⟨T + D, fullPositive_add hT hD, ?_⟩
  rw [class_add, hclass, bottChernClass_thetaClosedCurrent]

variable [MeasurableSpace X] [BorelSpace X]

/-- The supremum of ALL original-current AC masses increases under genuine
semipositive addition. No pseudoeffectivity or finiteness is assumed. -/
theorem originalCurrentACVolume_le_add_semipositive
    (α : RealBottChern (m + 1) X) (η : ClosedRealOneOneForm (m + 1) X)
    (hη : η.val.IsSemipositive) :
    originalCurrentACVolume α ≤
      originalCurrentACVolume (α + RealBottChern.ofRepresentative η) := by
  have hu := (LocalPotentials.isThetaPshPotential_zero_iff η).mpr hη
  let D := thetaClosedCurrent η (fun _ => 0) hu
  have hD : IsFullPositive D.val := thetaPotentialCurrent_full_positive η.val (fun _ => 0) hu
  unfold originalCurrentACVolume
  refine iSup_le fun T => iSup_le fun hT => iSup_le fun hclass => ?_
  have hTD : IsFullPositive (T + D).val := fullPositive_add hT hD
  have hc : bottChernClass (canonicalBasis (m + 1)) (Nat.succ_pos m) (T + D) =
      α + RealBottChern.ofRepresentative η := by
    rw [class_add, hclass, bottChernClass_thetaClosedCurrent]
  calc
    globalACtopMeasure T.val hT univ ≤ globalACtopMeasure (T + D).val hTD univ :=
      Measure.le_iff'.mp
        (PositiveCurrentACTopMonotonicity.globalACtopMeasure_le_add T.val D.val hT hD) univ
    _ ≤ originalCurrentACVolume (α + RealBottChern.ofRepresentative η) :=
      ac_top_mass_le_volume (T + D) hTD hc

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem semipositive_smul
    (ω : KahlerBackground (m + 1) X) {c : ℝ} (hc : 0 ≤ c) :
    (c • ω.form).val.IsSemipositive := by
  intro e z hz v
  simpa [ClosedRealOneOneForm.coeff_smul] using
    mul_nonneg hc (ω.isSemipositive e z hz v)

private theorem perturbation_monotone
    (ω : KahlerBackground (m + 1) X) (α : RealBottChern (m + 1) X) :
    Monotone (fun ε : ℝ =>
      originalCurrentACVolume (α + ε • RealBottChern.ofRepresentative ω.form)) := by
  intro s t hst
  have h := originalCurrentACVolume_le_add_semipositive
    (α + s • RealBottChern.ofRepresentative ω.form) ((t - s) • ω.form)
    (semipositive_smul ω (sub_nonneg.mpr hst))
  have heq : α + s • RealBottChern.ofRepresentative ω.form +
      (t - s) • RealBottChern.ofRepresentative ω.form =
      α + t • RealBottChern.ofRepresentative ω.form := by module
  simpa only [RealBottChern.ofRepresentative_smul, heq] using h

variable [ConnectedSpace X]

/-- The original volume converges along the ENTIRE right-neighborhood filter,
with reciprocal classes, their natural pseudoeffectivity and their true
quotient convergence all constructed inside. Zero volume is allowed. -/
theorem tendsto_originalCurrentACVolume_add_smul_right
    (ω : KahlerBackground (m + 1) X) (α : RealBottChern (m + 1) X)
    (hα : ClassPseudoeffectiveViaPotentials α) :
    Tendsto (fun ε : ℝ =>
      originalCurrentACVolume (α + ε • RealBottChern.ofRepresentative ω.form))
      (𝓝[>] 0) (𝓝 (originalCurrentACVolume α)) := by
  let f : ℝ → ℝ≥0∞ := fun ε =>
    originalCurrentACVolume (α + ε • RealBottChern.ofRepresentative ω.form)
  have hmono : Monotone f := perturbation_monotone ω α
  have hright : Tendsto f (𝓝[>] 0) (𝓝 (sInf (f '' Ioi 0))) := hmono.tendsto_nhdsGT 0
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hpath : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Eventually.of_forall hεpos⟩
  have hpsef (j : ℕ) : ClassPseudoeffectiveViaPotentials
      (α + ε j • RealBottChern.ofRepresentative ω.form) := by
    simpa only [RealBottChern.ofRepresentative_smul] using
      classPseudoeffective_add_semipositive hα (ε j • ω.form)
        (semipositive_smul ω (hεpos j).le)
  have hclasses : Tendsto (fun j => α + ε j • RealBottChern.ofRepresentative ω.form)
      atTop (@nhds (RealBottChern (m + 1) X) classPureSmoothTopology α) := by
    refine Quotient.inductionOn α ?_
    intro θ
    change Tendsto (fun j => RealBottChern.ofRepresentative θ +
      ε j • RealBottChern.ofRepresentative ω.form) atTop
      (@nhds (RealBottChern (m + 1) X) classPureSmoothTopology
        (RealBottChern.ofRepresentative θ))
    let : TopologicalSpace (ClosedRealOneOneForm (m + 1) X) := formPureSmoothTopology
    let : TopologicalSpace (RealBottChern (m + 1) X) := classPureSmoothTopology
    let : IsTopologicalAddGroup (ClosedRealOneOneForm (m + 1) X) :=
      formPureSmoothTopology_isTopologicalAddGroup
    let : ContinuousSMul ℝ (ClosedRealOneOneForm (m + 1) X) :=
      formPureSmoothTopology_continuousSMul
    have hform : Tendsto (fun j => θ + ε j • ω.form) atTop (𝓝 θ) := by
      simpa only [zero_smul, add_zero] using
        tendsto_const_nhds.add (hεlim.smul_const ω.form)
    have h := (isOpenQuotientMap_ofRepresentative ω).continuous.tendsto θ |>.comp hform
    have hf : (fun j => RealBottChern.ofRepresentative θ +
        ε j • RealBottChern.ofRepresentative ω.form) =
        RealBottChern.ofRepresentative ∘ (fun j => θ + ε j • ω.form) := by
      funext j
      simp only [Function.comp_apply, RealBottChern.ofRepresentative_add,
        RealBottChern.ofRepresentative_smul]
    rw [hf]
    exact h
  have hsup : limsup (fun j => f (ε j)) atTop ≤ originalCurrentACVolume α :=
    OriginalCurrentVolumeUpperSemicontinuity.limsup_originalCurrentACVolume_le
      ω _ α hpsef hclasses
  have hinf : originalCurrentACVolume α ≤ liminf (fun j => f (ε j)) atTop := by
    apply le_liminf_of_le (by isBoundedDefault)
    exact Eventually.of_forall fun j => by
      simpa only [f, zero_smul, add_zero] using hmono (hεpos j).le
  have hseq : Tendsto (fun j => f (ε j)) atTop (𝓝 (originalCurrentACVolume α)) :=
    tendsto_of_le_liminf_of_limsup_le hinf hsup
  have heq := tendsto_nhds_unique (hright.comp hpath) hseq
  rwa [heq] at hright

end SGPT.Foundations.Analysis.Pending.OriginalCurrentVolumeRightLimit
