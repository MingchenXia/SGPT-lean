import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyDiagonalGap

set_option autoImplicit false

/-!
# Actual maximum decomposition of singular finite-energy diagonal gaps

Genuine full-mass order closure and actual finite-energy characterization
produce E1 maximum closure. Actual plurifine max locality decomposes the
canonical diagonal gap without assuming its finiteness.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass SingularModelFiniteEnergyDiagonalGap

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine full-mass order closure and the actual energy characterization
produce E1 upward closure for arbitrary singular models in every dimension. -/
theorem relativeFiniteEnergyPreceq_of_le (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativePSHPreceq θ φ v)
    (huv : u ≤ v) : RelativeFiniteEnergyPreceq θ φ v hφ := by
  obtain ⟨c, hcu, hcv⟩ := exists_common_add_le hu.1.relativePSHPreceq hv
  have huN := hu.relativeFiniteEnergy_add omega hcu
  have horder : (fun x => u x + (c : EReal)) ≤ fun x => v x + (c : EReal) :=
    fun x => add_le_add (huv x) le_rfl
  have hvF := FiniteGeodesicsFullMassAnyDim.relativeFullMass_of_between omega
    huN.1 (hv.1.add_const c) horder hcv
  have hE : ⊥ < energy θ φ hφ (fun x => v x + (c : EReal)) :=
    (SingularModelFiniteEnergyPreceq.bot_lt_energy omega
      (preceq_of_relativeFiniteEnergy huN)).trans_le (energy_mono_of_le horder)
  have hvN := (SingularModelFiniteEnergy.relativeFiniteEnergy_iff_bot_lt_energy
    omega θ hφ hvF).mpr hE
  exact relativeFiniteEnergyPreceq_of_add omega (preceq_of_relativeFiniteEnergy hvN)

/-- The actual genuine maximum of two singularity-order E1 endpoints is E1. -/
theorem relativeFiniteEnergyPreceq_max (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    RelativeFiniteEnergyPreceq θ φ (fun x => max (u x) (v x)) hφ :=
  relativeFiniteEnergyPreceq_of_le omega hu
    ⟨IsThetaPshPotential.max hu.1.plurisubharmonic hv.1.plurisubharmonic,
      DominationPrincipleReduction.moreSingularOn_max hu.1.relativePSHPreceq.2 hv.1.relativePSHPreceq.2⟩
    (fun _ => le_max_left _ _)

private theorem canonicalAbs_symm (a b : EReal) :
    canonicalERealAbsDiff a b = canonicalERealAbsDiff b a := by
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff, ← EReal.coe_sub,
      EReal.abs_def, abs_sub_comm]

private theorem canonicalAbs_max_left {X : Type*} {u v : X → EReal}
    (hu : ∀ x, u x ≠ ⊤) (x : X) :
    canonicalERealAbsDiff (max (u x) (v x)) (u x) =
      {x | u x < v x}.indicator (fun x => canonicalERealAbsDiff (u x) (v x)) x := by
  by_cases hx : u x < v x
  · rw [max_eq_right (le_of_lt hx), indicator_of_mem (show x ∈ {x | u x < v x} from hx)]
    exact canonicalAbs_symm _ _
  · rw [max_eq_left (not_lt.mp hx), indicator_of_notMem (show x ∉ {x | u x < v x} from hx)]
    exact canonicalERealAbsDiff_self_of_ne_top (hu x)

private theorem gap_max_left_eq_restrict (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    diagonalGapIntegral θ (fun x => max (u x) (v x)) u (IsThetaPshPotential.max hu hv) hu =
      ∫⁻ x in {x | u x < v x}, canonicalERealAbsDiff (u x) (v x)
        ∂(diagonalPotentialMeasure θ u hu + diagonalPotentialMeasure θ v hv) := by
  let S := {x | u x < v x}
  let R := {x | ∀ _i : Fin n, u x < v x}
  let μu := diagonalPotentialMeasure θ u hu
  let μv := diagonalPotentialMeasure θ v hv
  let μm := diagonalPotentialMeasure θ (fun x => max (u x) (v x)) (IsThetaPshPotential.max hu hv)
  let f := fun x => canonicalERealAbsDiff (u x) (v x)
  have hSm : MeasurableSet S := measurableSet_lt
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1)
  have hR : μm.restrict R = μv.restrict R := by
    have h := GlobalMaxLocality.globalMixedMeasure_restrict_max_eq
      (fun _ : Fin n => hv.1) (fun _ => hu.1) (fun _ => (IsThetaPshPotential.max hv hu).1)
    simpa only [μm, μv, R, diagonalPotentialMeasure, max_comm] using h
  have hsub : S ⊆ R := fun _ hx _ => hx
  have hS : μm.restrict S = μv.restrict S := by
    rw [← Measure.restrict_restrict_of_subset hsub, hR, Measure.restrict_restrict_of_subset hsub]
  have heq : (fun x => canonicalERealAbsDiff (max (u x) (v x)) (u x)) = S.indicator f :=
    funext fun x => canonicalAbs_max_left hu.1.quasiPlurisubharmonic.ne_top x
  change (∫⁻ x, canonicalERealAbsDiff (max (u x) (v x)) (u x) ∂(μm + μu)) =
    ∫⁻ x in S, f x ∂(μu + μv)
  rw [heq, lintegral_add_measure, lintegral_indicator hSm,
    lintegral_indicator hSm, hS, Measure.restrict_add, lintegral_add_measure]
  exact add_comm _ _

/-- Actual plurifine maximum locality decomposes the actual absolute
diagonal gap, including all infinite strata and without finiteness premises. -/
theorem diagonalGapIntegral_max_decomposition (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) :
    diagonalGapIntegral θ u v hu hv =
      diagonalGapIntegral θ (fun x => max (u x) (v x)) u (IsThetaPshPotential.max hu hv) hu +
      diagonalGapIntegral θ (fun x => max (u x) (v x)) v (IsThetaPshPotential.max hu hv) hv := by
  classical
  let S := {x | u x < v x}
  let T := {x | v x < u x}
  let μ := diagonalPotentialMeasure θ u hu + diagonalPotentialMeasure θ v hv
  let f := fun x => canonicalERealAbsDiff (u x) (v x)
  have hSm : MeasurableSet S := measurableSet_lt
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1)
  have hTm : MeasurableSet T := measurableSet_lt
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1)
  have hfm : Measurable f := measurable_canonicalERealAbsDiff.comp
    ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1).prodMk
      (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1))
  have hsplit : f = fun x => S.indicator f x + T.indicator f x := by
    funext x
    by_cases hxS : x ∈ S
    · have hxT : x ∉ T := by
        change ¬v x < u x
        exact not_lt.mpr (le_of_lt hxS)
      rw [indicator_of_mem hxS, indicator_of_notMem hxT, add_zero]
    · by_cases hxT : x ∈ T
      · rw [indicator_of_notMem hxS, indicator_of_mem hxT, zero_add]
      · have heq : u x = v x := le_antisymm (not_lt.mp hxT) (not_lt.mp hxS)
        rw [indicator_of_notMem hxS, indicator_of_notMem hxT, zero_add]
        change canonicalERealAbsDiff (u x) (v x) = 0
        rw [heq]
        exact canonicalERealAbsDiff_self_of_ne_top (hv.1.quasiPlurisubharmonic.ne_top x)
  have hleft := gap_max_left_eq_restrict hu hv
  have hright : diagonalGapIntegral θ (fun x => max (u x) (v x)) v
      (IsThetaPshPotential.max hu hv) hv = ∫⁻ x in T, f x ∂μ := by
    simpa only [T, f, μ, max_comm, canonicalAbs_symm, add_comm] using gap_max_left_eq_restrict hv hu
  rw [hleft, hright]
  change (∫⁻ x, f x ∂μ) = (∫⁻ x in S, f x ∂μ) + ∫⁻ x in T, f x ∂μ
  calc (∫⁻ x, f x ∂μ) = ∫⁻ x, S.indicator f x + T.indicator f x ∂μ := by rw [← hsplit]
    _ = (∫⁻ x, S.indicator f x ∂μ) + ∫⁻ x, T.indicator f x ∂μ :=
      lintegral_add_left (hfm.indicator hSm) _
    _ = _ := by rw [lintegral_indicator hSm, lintegral_indicator hTm]

/-- The actual maximum decomposition and produced E1 maximum closure make
the canonical diagonal gap finite for every genuine E1 pair. -/
theorem diagonalGapIntegral_lt_top (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic < ⊤ := by
  have hm := relativeFiniteEnergyPreceq_max omega hu hv
  rw [diagonalGapIntegral_max_decomposition]
  exact ENNReal.add_lt_top.mpr
    ⟨(diagonalGapIntegral_le_mul_energy_sub_of_preceq omega hm hu (fun _ => le_max_left _ _)).trans_lt
        ENNReal.ofReal_lt_top,
      (diagonalGapIntegral_le_mul_energy_sub_of_preceq omega hm hv (fun _ => le_max_right _ _)).trans_lt
        ENNReal.ofReal_lt_top⟩

/-- Every genuine singularity-order E1 pair has actual canonical signed
cross-measure integrability against the sum of its diagonal measures. -/
theorem integrable_canonicalDiff_diagonal_add (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (diagonalPotentialMeasure θ u hu.1.plurisubharmonic +
        diagonalPotentialMeasure θ v hv.1.plurisubharmonic) := by
  let μ := diagonalPotentialMeasure θ u hu.1.plurisubharmonic +
    diagonalPotentialMeasure θ v hv.1.plurisubharmonic
  have hfin : (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ) < ⊤ :=
    diagonalGapIntegral_lt_top omega hu hv
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) :
      ∀ᵐ x ∂μ, w x ≠ ⊥ := by
    apply ae_iff.mpr
    have hzero : μ {x | w x = ⊥} = 0 := by
      change (diagonalPotentialMeasure θ u hu.1.plurisubharmonic +
        diagonalPotentialMeasure θ v hv.1.plurisubharmonic) {x | w x = ⊥} = 0
      have hzu : diagonalPotentialMeasure θ u hu.1.plurisubharmonic {x | w x = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n => hu.1.plurisubharmonic.1) hw
      have hzv : diagonalPotentialMeasure θ v hv.1.plurisubharmonic {x | w x = ⊥} = 0 :=
        GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
          (fun _ : Fin n => hv.1.plurisubharmonic.1) hw
      rw [Measure.add_apply, hzu, hzv, add_zero]
    simpa only [not_not] using hzero
  have heq : ∀ᵐ x ∂μ, ‖canonicalERealDiffToReal (u x) (v x)‖ₑ =
      canonicalERealAbsDiff (u x) (v x) := by
    filter_upwards [hpole u hu.1.plurisubharmonic, hpole v hv.1.plurisubharmonic] with x hubot hvbot
    have hpole : u x = ⊥ ↔ v x = ⊥ := ⟨fun h => (hubot h).elim, fun h => (hvbot h).elim⟩
    rw [Real.enorm_eq_ofReal_abs, canonicalERealAbsDiff_eq_ofReal_abs_diff
      (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
      (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpole]
  have hm : Measurable (fun x => canonicalERealDiffToReal (u x) (v x)) :=
    measurable_canonicalERealDiffToReal.comp
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1.plurisubharmonic.1).prodMk
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1.plurisubharmonic.1))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖canonicalERealDiffToReal (u x) (v x)‖ₑ ∂μ) < ⊤
  rw [lintegral_congr_ae heq]
  exact hfin

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyGapMax
