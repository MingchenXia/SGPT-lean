import SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion

set_option autoImplicit false

/-!
# Reducing a closed-current Stokes argument to a common exhaustion limit

The regular-piece formalism already proves that every monotone family which
absorbs compact subsets of the regular locus computes the global supremum of
the mass of any smooth real two-form.  Consequently, the analytic part of a
closed-integration-current argument need not assert an equality of those two
global suprema.  It is enough to provide one such exhaustion and prove that
the two sequences of finite regular-piece masses have a common limit.

For the intended application the common-limit assertion is exactly where the
form-valued integration current is used: local chart reconstruction and scalar
Stokes give cancellation away from the singular locus, while the singular
collar estimate shows that the remaining error tends to zero.  The theorem
below turns that analytic convergence statement into the global equality using
only the already verified regular-piece exhaustion theorem.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ClosedCurrentMassLimitReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- Two smooth forms have a common regular-piece mass limit along one family.
This is the exact numerical output of the closed-current plus singular-collar
argument; it does not mention a global supremum. -/
structure FormPieceMassCommonLimit (a b : SmoothRealForm n M 2)
    (H : ℕ → RegularPieceFamily V (∅ : Set M)) where
  /-- The common limiting mass. -/
  limit : ℝ≥0∞
  /-- The first form's finite-piece masses approach that mass. -/
  tendsto_left : Tendsto (fun m : ℕ => PatchFormMass.formPieceMass a (H m)) atTop
    (𝓝 limit)
  /-- The second form's finite-piece masses approach the same mass. -/
  tendsto_right : Tendsto (fun m : ℕ => PatchFormMass.formPieceMass b (H m)) atTop
    (𝓝 limit)

/-- A common mass limit on a monotone compact-absorbing exhaustion identifies
the two global regular-piece suprema.  No positivity or finiteness assumption
is needed: the target is `ℝ≥0∞`, and each individual global supremum is already
the limit of its own mass sequence. -/
theorem iSup_formPieceMass_eq_of_commonLimit
    (a b : SmoothRealForm n M 2) {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (hmono : ∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m, K ⊆ coveredRegion (H m))
    (hlimit : FormPieceMassCommonLimit a b H) :
    (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass a F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass b F := by
  have hleft := tendsto_formPieceMass_of_exhaustion (V := V) isClosed_empty hmono
    (fun K hK hKreg _ => hexh K hK hKreg) a
  have hright := tendsto_formPieceMass_of_exhaustion (V := V) isClosed_empty hmono
    (fun K hK hKreg _ => hexh K hK hKreg) b
  exact (tendsto_nhds_unique hleft hlimit.tendsto_left).trans
    (tendsto_nhds_unique hlimit.tendsto_right hright)

end

end SGPT.Foundations.Analysis.Pending.ClosedCurrentMassLimitReduction
