import SGPT.Projective.SimplexFubiniStudy
import SGPT.Hodge.SourceSmoothMixedCohomology
import SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling
import SGPT.Toric.SmoothMongeAmpereMass
import SGPT.Convex.UnitCubeSupport
import SGPT.Toric.Toric4Examples
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Lean.Elab.Command

section FsBlowdownCanonicalFragmentSimplexOriginalMassTransportDraft
/- BEGIN SimplexOriginalMassTransportDraft; original frozen source SHA256 add67eed7553e9cf014b577a8efe8e530e41843eb2acb6019295816bfd0f903b -/
/-! Actual SAME native simplex/projective smooth mass transport. The only
map is the original genuine biholomorphism, with EMPTY exceptional sets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext

open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open SGPT.Foundations.Analysis.Pending.AnalyticModificationMixedMass
open SGPT.Foundations.Analysis.Pending.ModificationMassInvariance
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
open SGPT.Foundations.Analysis.Pending.MixedMassClassInvariance
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped BigOperators Manifold ContDiff Topology

variable {N : ℕ} (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- The actual full-lattice curvature supplies its own genuine native Kähler background. -/
def simplexFullLatticeBackground : KahlerBackground N (PolytopeToricVariety (simplexGenerator N) hs) :=
  ⟨(toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)).form,
    toricFullLatticeMetric_isKahler (γ := simplexGenerator N) (hs := hs)⟩

/-- The SAME original biholomorphism manufactures mass-transport geometry with EMPTY sets. -/
theorem simplexOriginalFs_actualModification :
    IsAnalyticModification (n := N) (simplexProjectiveHomeomorph hs) :=
  ⟨contMDiff_simplexProjectiveHomeomorph hs, (simplexProjectiveHomeomorph hs).isProperMap,
    ∅, ∅, (simplexProjectiveHomeomorph hs).symm, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, isClosed_empty,
    isComplexAnalyticSubset_empty, interior_empty, preimage_empty,
    (contMDiff_simplexProjectiveHomeomorph_symm hs).contMDiffOn,
    (fun x _ => (simplexProjectiveHomeomorph hs).apply_symm_apply x),
    (fun y _ => (simplexProjectiveHomeomorph hs).symm_apply_apply y)⟩

/-- Actual smooth integrals agree for the SAME full-lattice and original projective FS forms.
All dimension-zero tuples are retained; no integration-comparison field is assumed. -/
theorem simplexOriginalFs_integral_eq :
    slotIntegral (simplexFullLatticeBackground hs)
      (fun _ : Fin N => (toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)).form) =
      slotIntegral (ComplexProjectiveSpace.fsBackground (N := N))
        (fun _ : Fin N => ComplexProjectiveSpace.fsClosedForm (N := N)) := by
  let h := toricFullLatticeMetric (γ := simplexGenerator N) (hs := hs)
  have hX : ∀ _ : Fin N, ThetaPlurisubharmonic
      (ComplexProjectiveSpace.fsClosedForm (N := N)).val (fun _ => (0 : EReal)) :=
    fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
      (ComplexProjectiveSpace.fsBackground (N := N)).isSemipositive).1
  have hY : ∀ _ : Fin N, ThetaPlurisubharmonic h.form.val (fun _ => (0 : EReal)) :=
    fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff _).mpr
      (simplexFullLatticeBackground hs).isSemipositive).1
  have hmass := globalMixedMeasure_univ_pullback_of_isAnalyticModification
    (simplexOriginalFs_actualModification hs) hX
  have hforms : pullbackTuple (simplexOriginalFs_actualModification hs).1
      (fun _ : Fin N => ComplexProjectiveSpace.fsClosedForm (N := N)) =
      (fun _ : Fin N => h.form) := by
    funext i
    exact (simplexFullLatticeMetric_form_eq_original_fs_pullback hs).symm
  have hread := GlobalDiagonalScaling.globalMixedMeasure_congr hforms rfl
    (fun i => thetaPlurisubharmonic_comp (simplexOriginalFs_actualModification hs).1 (hX i)) hY
  rw [hread] at hmass
  calc
    slotIntegral (simplexFullLatticeBackground hs) (fun _ : Fin N => h.form) =
        (globalMixedMeasure (fun _ : Fin N => h.form) (fun _ _ => 0) hY).real univ :=
      (globalMixedMeasure_real_univ_eq_integral (simplexFullLatticeBackground hs)
        (fun _ : Fin N => h.form) hY).symm
    _ = (globalMixedMeasure (fun _ : Fin N => ComplexProjectiveSpace.fsClosedForm (N := N))
        (fun _ _ => 0) hX).real univ := congrArg ENNReal.toReal hmass
    _ = slotIntegral (ComplexProjectiveSpace.fsBackground (N := N))
        (fun _ : Fin N => ComplexProjectiveSpace.fsClosedForm (N := N)) :=
      globalMixedMeasure_real_univ_eq_integral (ComplexProjectiveSpace.fsBackground (N := N))
        (fun _ : Fin N => ComplexProjectiveSpace.fsClosedForm (N := N)) hX

end SGPT.Projective.FsNormalizationNext

end
/- END SimplexOriginalMassTransportDraft -/
end FsBlowdownCanonicalFragmentSimplexOriginalMassTransportDraft

section FsBlowdownCanonicalFragmentOriginalCp1FsNormalizationDraft
/- BEGIN OriginalCp1FsNormalizationDraft; original frozen source SHA256 b73b4612634e62c074d13c0cd3c92503412fc232c39d8beed63e360106908f9c -/
/-! The exact genuine original projective-line FS integral equals one.
No rescaled integration label, arbitrary mass premise or polar integral is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext

open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped BigOperators Manifold ContDiff Topology

/-- Literal accepted original CP1 Bott--Chern smooth integral, with its actual FS background. -/
theorem originalCP1_fs_classSlotIntegral_eq_one :
    classSlotIntegral (ComplexProjectiveSpace.fsBackground (N := 1))
      (fun _ : Fin 1 => RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 1))) = 1 := by
  let hs : latticePolytopeEdgeSmooth (simplexGenerator 1) := simplex_edgeSmooth
  let h := toricFullLatticeMetric (γ := simplexGenerator 1) (hs := hs)
  let κ := simplexFullLatticeBackground hs
  have hpoly : toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs) =
      SGPT.Convex.euclideanUnitCube 1 := by
    rw [← simplexHyperplaneDivisor_eq_ample hs, P1toric_polytope hs]
    ext m
    simp only [SGPT.Convex.euclideanUnitCube, mem_ofPred_eq, Fin.forall_fin_one, mem_Icc]
  have hP : (toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs)).Nonempty := by
    rw [hpoly]
    exact SGPT.Convex.nonempty_euclideanUnitCube 1
  have hma : h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive) univ = 1 := by
    calc
      _ = ((1 : ℕ).factorial : ENNReal) * volume
          (toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs)) :=
        toricSmoothMetric_zero_MA_univ h κ.isSemipositive hP
      _ = 1 := by rw [hpoly, SGPT.Convex.volume_euclideanUnitCube]; norm_num
  calc
    classSlotIntegral (ComplexProjectiveSpace.fsBackground (N := 1))
        (fun _ : Fin 1 => RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 1))) =
        slotIntegral (ComplexProjectiveSpace.fsBackground (N := 1))
          (fun _ : Fin 1 => ComplexProjectiveSpace.fsClosedForm (N := 1)) :=
      classSlotIntegral_ofRepresentative _ _
    _ = slotIntegral κ (fun _ : Fin 1 => h.form) := (simplexOriginalFs_integral_eq hs).symm
    _ = (h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive)).real univ :=
      (toricSmoothMetric_zero_MA_eq_nativeIntegral h κ.isSemipositive κ).symm
    _ = 1 := by
      change (h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive) univ).toReal = 1
      rw [hma]
      rfl

end SGPT.Projective.FsNormalizationNext

end
/- END OriginalCp1FsNormalizationDraft -/
end FsBlowdownCanonicalFragmentOriginalCp1FsNormalizationDraft

section FsBlowdownCanonicalFragmentOriginalCp2FsNormalizationDraft
/- BEGIN OriginalCp2FsNormalizationDraft; original frozen source SHA256 037e5bb7ecb4ac0b250bf266a53978e7c63a9d1e3e0661d103037147af725073 -/
/-! The genuine original CP2 FS class integral, through actual triangle area.
The accepted CP1 cohort's all-dimensional geometry is reused unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.Projective.FsNormalizationNext
open Set Filter MeasureTheory
open SGPT.Toric
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open scoped BigOperators Manifold ContDiff Topology

/-- Actual Fin2-coordinate product Lebesgue volume of the standard triangle. -/
theorem volume_actual_standardTriangle :
    volume {m : Fin 2 → ℝ | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} = (1 / 2 : ENNReal) := by
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}
  have hS : MeasurableSet S := measurableSet_region_between_cc measurable_const
    (measurable_const.sub measurable_id) measurableSet_Icc
  have hpre : {m : Fin 2 → ℝ | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} =
      MeasurableEquiv.finTwoArrow ⁻¹' S := by
    ext m
    change (m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1) ↔
      ((0 ≤ m 0 ∧ m 0 ≤ 1) ∧ 0 ≤ m 1 ∧ m 1 ≤ 1 - m 0)
    constructor <;> intro h <;> constructor
    · exact ⟨h.2.1, by linarith [h.1, h.2.2]⟩
    · exact ⟨h.2.2, by linarith [h.1]⟩
    · linarith [h.2.2]
    · exact ⟨h.1.1, h.2.1⟩
  have hclosed : (volume.prod volume) S =
      (volume.prod volume) (regionBetween (fun _ : ℝ => 0) (fun x => 1 - x) (Icc 0 1)) := by
    have hopen : MeasurableSet (regionBetween (fun _ : ℝ => 0) (fun x => 1 - x) (Icc 0 1)) :=
      measurableSet_regionBetween measurable_const (measurable_const.sub measurable_id) measurableSet_Icc
    rw [Measure.prod_apply hS, Measure.prod_apply hopen]
    apply lintegral_congr
    intro x
    change volume {a : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ a ∈ Icc 0 (1 - x)} =
      volume {a : ℝ | x ∈ Icc (0 : ℝ) 1 ∧ a ∈ Ioo 0 (1 - x)}
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp only [hx, true_and]
      change volume (Icc (0 : ℝ) (1 - x)) = volume (Ioo (0 : ℝ) (1 - x))
      rw [Real.volume_Icc, Real.volume_Ioo]
    · simp only [hx, false_and]
  have harea : (volume.prod volume)
      (regionBetween (fun _ : ℝ => 0) (fun x => 1 - x) (Icc 0 1)) =
      ENNReal.ofReal (∫ x in Icc (0 : ℝ) 1, 1 - x) := by
    simpa using volume_regionBetween_eq_integral
      ((show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const).continuousOn.integrableOn_Icc)
      ((show Continuous (fun x : ℝ => (1 : ℝ) - x) from continuous_const.sub continuous_id).continuousOn.integrableOn_Icc)
      measurableSet_Icc (fun x hx => sub_nonneg.mpr hx.2)
  have hint : (∫ x in Icc (0 : ℝ) 1, 1 - x) = (1 / 2 : ℝ) := by
    have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
    have hi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 := continuous_id.intervalIntegrable 0 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_sub hc hi]
    norm_num
  rw [hpre, (volume_preserving_finTwoArrow ℝ).measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) S = (1 / 2 : ENNReal)
  rw [hclosed, harea, hint]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The SAME triangle's genuine Euclidean-space volume, with its original
orthonormal-coordinate normalization, rather than a new product measure. -/
theorem volume_actual_euclideanStandardTriangle :
    volume {m : EuclideanSpace ℝ (Fin 2) | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} = (1 / 2 : ENNReal) := by
  have hT : MeasurableSet {m : Fin 2 → ℝ | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} := by
    measurability
  change volume ((WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) ⁻¹'
    {m : Fin 2 → ℝ | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1}) = (1 / 2 : ENNReal)
  rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage hT.nullMeasurableSet,
    volume_actual_standardTriangle]

/-- The literal ORIGINAL ordinary-atlas CP2 FS Bott--Chern integral equals one. -/
theorem originalCP2_fs_classSlotIntegral_eq_one :
    classSlotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
      (fun _ : Fin 2 => RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) = 1 := by
  let hs : latticePolytopeEdgeSmooth (simplexGenerator 2) := simplex_edgeSmooth
  let h := toricFullLatticeMetric (γ := simplexGenerator 2) (hs := hs)
  let κ := simplexFullLatticeBackground hs
  have hpoly : toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 2) hs) =
      {m : EuclideanSpace ℝ (Fin 2) | m 0 + m 1 ≤ 1 ∧ 0 ≤ m 0 ∧ 0 ≤ m 1} := by
    rw [← simplexHyperplaneDivisor_eq_ample hs]
    exact (P2_divisor hs).2.2.2
  have hP : (toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 2) hs)).Nonempty := by
    rw [hpoly]
    exact ⟨0, by simp⟩
  have hma : h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive) univ = 1 := by
    calc
      _ = ((2 : ℕ).factorial : ENNReal) * volume
          (toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 2) hs)) :=
        toricSmoothMetric_zero_MA_univ h κ.isSemipositive hP
      _ = 1 := by
        rw [hpoly, volume_actual_euclideanStandardTriangle]
        norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, mul_one, one_div]
        exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  calc
    classSlotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
        (fun _ : Fin 2 => RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) =
        slotIntegral (ComplexProjectiveSpace.fsBackground (N := 2))
          (fun _ : Fin 2 => ComplexProjectiveSpace.fsClosedForm (N := 2)) :=
      classSlotIntegral_ofRepresentative _ _
    _ = slotIntegral κ (fun _ : Fin 2 => h.form) := (simplexOriginalFs_integral_eq hs).symm
    _ = (h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive)).real univ :=
      (toricSmoothMetric_zero_MA_eq_nativeIntegral h κ.isSemipositive κ).symm
    _ = 1 := by
      change (h.MA (toricSmoothMetric_zero_mem h κ.isSemipositive) univ).toReal = 1
      rw [hma]
      rfl

end SGPT.Projective.FsNormalizationNext

end
/- END OriginalCp2FsNormalizationDraft -/
end FsBlowdownCanonicalFragmentOriginalCp2FsNormalizationDraft


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`SimplexOriginalFsWeightsDraft, `SimplexOriginalFsFormDraft, `ToricOriginalSmoothMassDraft, `SimplexOriginalMassTransportDraft, `OriginalCp1FsNormalizationDraft, `OriginalCp2FsNormalizationDraft, `OriginalBlowdownMassDraft, `OriginalBlowdownLocusDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden original private module in actual proper FS/blowdown provider: {m}"
