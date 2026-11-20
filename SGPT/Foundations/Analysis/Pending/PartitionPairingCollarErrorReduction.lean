import SGPT.Foundations.Analysis.Pending.FiniteTelescopeLocalWeightedPairing
import SGPT.Foundations.Analysis.Pending.PatchFormMassSignedBridge
import SGPT.Foundations.Analysis.Pending.SingularCollarMassErrorReduction

set_option autoImplicit false

/-!
# From finite partition pairings to a singular-collar mass error

`FiniteTelescopeLocalWeightedPairing` proves the exact finite identity between
one regular-piece family's signed form-density defect and the sum of its local
weighted Borel pairings. A partition-of-unity current construction need not
annihilate that sum exactly at a finite cutoff: after inserting a collar cutoff,
it may leave a signed real remainder which tends to zero along an exhaustion.

This module makes the numerical consequence precise. It assumes the two
finite-piece masses are finite and their densities nonnegative, so that their
`ENNReal` values can be converted faithfully to signed real integrals. It then
turns a bound for the finite sum of local pairings into
`FormPieceMassCollarError`, and hence into the existing common-limit and global
supremum reductions. No finite mass equality is asserted unless the supplied
remainder is actually zero.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold
open PatchFormMassSignedBridge
open FormPieceMassCurrentPairingBridge
open FormPieceMassCurrentPairingBridge.FormPieceTelescopeData
open FiniteTelescopeLocalWeightedPairing
open FiniteTelescopeLocalWeightedPairing.FiniteTelescopeLocalWeightedPairingData
open SingularCollarMassErrorReduction
open RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

variable {beta : KahlerBackground n M}
  {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
  {avoid : Set M} {G : RegularPieceFamily V avoid}

/-- Under nonnegativity and finiteness, the signed real difference of the two
finite-piece masses is exactly the sum of their signed density defects. This
is the `toReal` version of the existing signed-to-`ENNReal` bridge. -/
theorem current_toReal_sub_background_eq_sum_densityDefectIntegral
    (hcurrent_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
        (G.patch i) w)
    (hbackground_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)
    (hcurrent_finite : PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) G ≠ ⊤)
    (hbackground_finite : PatchFormMass.formPieceMass beta.form.val G ≠ ⊤) :
    (PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) G).toReal -
        (PatchFormMass.formPieceMass beta.form.val G).toReal =
      ∑ i, ∫ w in G.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (G.patch i) w) := by
  have hcurrent_integrable : ∀ i,
      IntegrableOn (fun w => PatchFormMass.patchFormDensity
        (ACTopMassComparison.currentForm q hvs) (G.patch i) w) (G.piece i) := by
    intro i
    exact integrableOn_patchFormDensity (ACTopMassComparison.currentForm q hvs)
      (G.patch i) (G.measurableSet_piece i) (G.piece_subset i) (hcurrent_nonneg i)
      (setLIntegral_piece_ne_top G hcurrent_finite i)
  have hbackground_integrable : ∀ i,
      IntegrableOn (fun w => PatchFormMass.patchFormDensity beta.form.val
        (G.patch i) w) (G.piece i) := by
    intro i
    exact integrableOn_patchFormDensity beta.form.val (G.patch i)
      (G.measurableSet_piece i) (G.piece_subset i) (hbackground_nonneg i)
      (setLIntegral_piece_ne_top G hbackground_finite i)
  have hcurrent_integral_nonneg : ∀ i,
      0 ≤ ∫ w in G.piece i,
        PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w := by
    intro i
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (G.measurableSet_piece i)] with w hw
    exact hcurrent_nonneg i w hw
  have hbackground_integral_nonneg : ∀ i,
      0 ≤ ∫ w in G.piece i,
        PatchFormMass.patchFormDensity beta.form.val (G.patch i) w := by
    intro i
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (G.measurableSet_piece i)] with w hw
    exact hbackground_nonneg i w hw
  have hcurrent_toReal_sum :
      (∑ i, ENNReal.ofReal (∫ w in G.piece i,
        PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w)).toReal =
        ∑ i, ∫ w in G.piece i,
          PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
            (G.patch i) w := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro i _hi
    exact ENNReal.toReal_ofReal (hcurrent_integral_nonneg i)
  have hbackground_toReal_sum :
      (∑ i, ENNReal.ofReal (∫ w in G.piece i,
        PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)).toReal =
        ∑ i, ∫ w in G.piece i,
          PatchFormMass.patchFormDensity beta.form.val (G.patch i) w := by
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro i _hi
    exact ENNReal.toReal_ofReal (hbackground_integral_nonneg i)
  rw [formPieceMass_eq_sum_ofReal_setIntegral
      (ACTopMassComparison.currentForm q hvs) G hcurrent_nonneg hcurrent_finite,
    formPieceMass_eq_sum_ofReal_setIntegral beta.form.val G hbackground_nonneg
      hbackground_finite, hcurrent_toReal_sum, hbackground_toReal_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (integral_sub (hcurrent_integrable i) (hbackground_integrable i)).symm

/-- The finite local weighted-patch data for one family, together with the
remaining real collar remainder controlling its sum of pairings. -/
structure FiniteTelescopePairingRemainderData
    (T : FormPieceTelescopeData beta q hvs G) where
  /-- The exact local weighted-pushforward and density reconstruction data. -/
  weightedPairing : FiniteTelescopeLocalWeightedPairingData T
  /-- The signed finite-cutoff remainder. -/
  remainder : ℝ
  /-- The finite partition pairing is controlled by that remainder. -/
  abs_sum_pairing_le :
    |∑ i, (weightedPairing.localMeasure i).pairing (weightedPairing.test i)| ≤ remainder

namespace FiniteTelescopePairingRemainderData

/-- The finite signed mass difference is controlled by the stipulated finite
partition remainder. This does not force equality of the masses. -/
theorem abs_toReal_sub_le_remainder
    {T : FormPieceTelescopeData beta q hvs G}
    (D : FiniteTelescopePairingRemainderData T)
    (hcurrent_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
        (G.patch i) w)
    (hbackground_nonneg : ∀ i, ∀ w ∈ G.piece i,
      0 ≤ PatchFormMass.patchFormDensity beta.form.val (G.patch i) w)
    (hcurrent_finite : PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) G ≠ ⊤)
    (hbackground_finite : PatchFormMass.formPieceMass beta.form.val G ≠ ⊤) :
    |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) G).toReal -
        (PatchFormMass.formPieceMass beta.form.val G).toReal| ≤ D.remainder := by
  rw [current_toReal_sub_background_eq_sum_densityDefectIntegral
    hcurrent_nonneg hbackground_nonneg hcurrent_finite hbackground_finite,
    D.weightedPairing.sum_densityDefectIntegral_eq_sum_pairing]
  exact D.abs_sum_pairing_le

end FiniteTelescopePairingRemainderData

/-- Data along one exhaustion. The individual finite-family pairing remainders
are allowed to be nonzero; only their common real control sequence is required
to converge to zero. Both finite-mass premises are retained because the proof
passes through `ENNReal.toReal`. -/
structure ExhaustionPartitionPairingRemainderData
    (H : ℕ → RegularPieceFamily V (∅ : Set M)) where
  telescope : ∀ m, FormPieceTelescopeData beta q hvs (H m)
  pairingRemainder : ∀ m, FiniteTelescopePairingRemainderData (telescope m)
  current_nonneg : ∀ m i, ∀ w ∈ (H m).piece i,
    0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
      ((H m).patch i) w
  background_nonneg : ∀ m i, ∀ w ∈ (H m).piece i,
    0 ≤ PatchFormMass.patchFormDensity beta.form.val ((H m).patch i) w
  current_ne_top : ∀ m, PatchFormMass.formPieceMass
    (ACTopMassComparison.currentForm q hvs) (H m) ≠ ⊤
  background_ne_top : ∀ m, PatchFormMass.formPieceMass beta.form.val (H m) ≠ ⊤
  error : ℕ → ℝ
  tendsto_error : Tendsto error atTop (𝓝 0)
  remainder_le_error : ∀ m, (pairingRemainder m).remainder ≤ error m

namespace ExhaustionPartitionPairingRemainderData

/-- The finite partition pairing estimates assemble exactly into the collar
error record used by the existing mass-limit reduction. -/
def toFormPieceMassCollarError
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (D : ExhaustionPartitionPairingRemainderData (beta := beta) (q := q) (hvs := hvs) H) :
    FormPieceMassCollarError (ACTopMassComparison.currentForm q hvs) beta.form.val H where
  left_ne_top := D.current_ne_top
  error := D.error
  tendsto_error := D.tendsto_error
  abs_toReal_sub_le := by
    intro m
    calc
      |(PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) (H m)).toReal -
          (PatchFormMass.formPieceMass beta.form.val (H m)).toReal| ≤
          (D.pairingRemainder m).remainder :=
        (D.pairingRemainder m).abs_toReal_sub_le_remainder
          (D.current_nonneg m) (D.background_nonneg m)
          (D.current_ne_top m) (D.background_ne_top m)
      _ ≤ D.error m := D.remainder_le_error m

/-- Combining the constructed collar error with a finite limiting background
mass gives the common `ENNReal` limit used by the closed-current reduction. -/
noncomputable def commonLimit
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (D : ExhaustionPartitionPairingRemainderData (beta := beta) (q := q) (hvs := hvs) H)
    {L : ℝ≥0∞}
    (hbackground_limit : Tendsto
      (fun m : ℕ => PatchFormMass.formPieceMass beta.form.val (H m)) atTop (𝓝 L))
    (hLfinite : L ≠ ⊤) :
    ClosedCurrentMassLimitReduction.FormPieceMassCommonLimit
      (ACTopMassComparison.currentForm q hvs) beta.form.val H :=
  FormPieceMassCollarError.commonLimit_of_collarError
    D.toFormPieceMassCollarError hbackground_limit hLfinite

/-- With the already formalized compact-absorbing exhaustion, a vanishing
finite partition remainder identifies the global regular-piece masses. -/
theorem iSup_formPieceMass_eq
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (D : ExhaustionPartitionPairingRemainderData (beta := beta) (q := q) (hvs := hvs) H)
    (hmono : ∀ m, coveredRegion (H m) ⊆ coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m, K ⊆ coveredRegion (H m))
    (hbackground_global_ne_top : (⨆ F : RegularPieceFamily V (∅ : Set M),
      PatchFormMass.formPieceMass beta.form.val F) ≠ ⊤) :
    (⨆ F : RegularPieceFamily V (∅ : Set M),
      PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F :=
  iSup_formPieceMass_eq_of_collarError
    (ACTopMassComparison.currentForm q hvs) beta.form.val hmono hexh
    hbackground_global_ne_top D.toFormPieceMassCollarError

end ExhaustionPartitionPairingRemainderData

end

end SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction
