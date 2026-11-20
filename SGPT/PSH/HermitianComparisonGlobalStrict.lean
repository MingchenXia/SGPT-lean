import SGPT.PSH.HermitianComparisonCompactPartition
import SGPT.PSH.HermitianConstantComparison

/-!
# Actual global strict one-factor inequality after cutoff cancellation

The compact inner domains and both scalar cutoffs are produced from the
original chart partition. Genuine radial mollifiers prove every local
strict inequality, and the actual native global derivative identity cancels
all partition derivatives before the final torsion-density sum.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts
open Hermitian HermitianGlobalProducts HermitianComparisonOneFactor HermitianComparisonStrict
  HermitianComparisonMollifier HermitianComparisonCutoff
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

/-- The actual sum of signed strict-set weighted distinguished factors.
Each factor is an existing bounded Bedford--Taylor current and smooth
residual wedge on its original inner coordinate domain. -/
def strictDifference (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (a b : M → EReal) : ℝ :=
  ∑ i, weightedDifference (patchResidual (C.patch i) u hu hb)
    ((C.patch i).correctedReal a) ((C.patch i).correctedReal b)
    strictIndicator scalarUnit (C.weight i)

/-- The actual derivative-density sum after partition cancellation. The
residuals are the original ones, with no derivatives of partition weights. -/
def torsionDifference (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (a b : M → EReal) : ℝ :=
  ∑ i, derivativeWeight (patchResidual (C.patch i) u hu hb) (C.weight i)
    (fun z => max ((b ((C.patch i).geometry.chart.val.symm z)).toReal -
      (a ((C.patch i).geometry.chart.val.symm z)).toReal) 0)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Genuine global one-factor comparison for the actual original bounded
Hermitian potentials, with the complete cutoff cancellation proved before
the torsion bound. No global inequality or covariance certificate is assumed. -/
theorem strict_onefactor (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a b : M → EReal} (ha : IsHermitianPSH omega a) (hbb : IsHermitianPSH omega b)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (hbbound : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ b x ∧ b x ≤ (d : EReal))
    {δ : ℝ} (hδ : 0 ≤ δ) (hgap : ∀ x, max ((b x).toReal - (a x).toReal) 0 ≤ δ) :
    strictDifference C u hu hb a b ≤ torsionDifference C u hu hb a b := by
  have hlocal (i : Fin C.outer.count) :
      weightedDifference (patchResidual (C.patch i) u hu hb)
        ((C.patch i).correctedReal a) ((C.patch i).correctedReal b)
        strictIndicator scalarUnit (C.weight i) ≤
      localizedDerivativeWeight (patchResidual (C.patch i) u hu hb) (C.weight i) (C.auxiliary i)
        (fun z => max ((b ((C.patch i).geometry.chart.val.symm z)).toReal -
          (a ((C.patch i).geometry.chart.val.symm z)).toReal) 0) := by
    have hS : IsPositive (mixedCurrent (patchResidual (C.patch i) u hu hb)) := by
      rw [mixedCurrent_patchResidual]
      exact (C.patch i).bidimensionOneCurrent_isPositive u hu hb
    have haP : IsLocallyBoundedPshOn (C.outer.patch i).geometry.domain ((C.patch i).correctedReal a) :=
      (C.outer.patch i).correctedReal_isLocallyBoundedPshOn ha hab
    have hbP : IsLocallyBoundedPshOn (C.outer.patch i).geometry.domain ((C.patch i).correctedReal b) :=
      (C.outer.patch i).correctedReal_isLocallyBoundedPshOn hbb hbbound
    have h := strict_local_onefactor_of_locallyBoundedPsh (patchResidual (C.patch i) u hu hb)
      hS (C.relativelyCompact i) haP hbP (C.weight i) (C.weight_nonneg i) (C.auxiliary i) (C.auxiliary_one i)
    apply h.trans_eq
    apply localizedDerivativeWeight_congr_on
    intro z _
    apply congrArg (fun t : ℝ => max t 0)
    dsimp only [BackgroundPatch.correctedReal, chartFunction]
    ring
  have hcancel := bounded_partition_derivative_cancellation C.partition u hu hb ha hbb hab hbbound
    hδ hgap C.weight C.auxiliary C.weight_eq_partition C.auxiliary_one
  exact (Finset.sum_le_sum (fun i _ => hlocal i)).trans_eq hcancel

/-- The constant-competitor specialization needed by the pure-trace
recurrence and positive bounded Monge--Ampère mass argument. The genuine
Hermitian PSH class and bounds of the constant are produced internally. -/
theorem strict_onefactor_const (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a : M → EReal} (ha : IsHermitianPSH omega a)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hgap : ∀ x, max (c - (a x).toReal) 0 ≤ δ) :
    strictDifference C u hu hb a (fun _ => (c : EReal)) ≤
      torsionDifference C u hu hb a (fun _ => (c : EReal)) := by
  apply strict_onefactor C u hu hb ha
    (HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c)
    hab ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩ hδ
  simpa only [EReal.toReal_coe] using hgap

end SGPT.PSH.HermitianComparisonGlobalOneFactor
