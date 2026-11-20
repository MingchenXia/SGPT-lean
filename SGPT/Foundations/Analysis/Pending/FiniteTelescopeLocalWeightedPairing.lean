import SGPT.Foundations.Analysis.Pending.LocalPatchWeightedMeasure
import SGPT.Foundations.Analysis.Pending.FormPieceMassCurrentPairingBridge

set_option autoImplicit false

/-!
# Finite telescope pairings from local weighted patch measures

For a finite regular-piece family, the area/Jacobian statement belongs to each
piece separately.  It should therefore produce a separate ambient Borel measure
for each piece, rather than identifying one global countable-cover measure with
every piece.  This module packages exactly those local weighted pushforwards
and their coefficient reconstruction for the telescope already supplied by
`FormPieceTelescopeData`.

The conclusion is a finite equality between the signed form-density defect and
a sum of genuine local scalar pairings.  A subsequent partition-of-unity
current construction need only prove that this finite sum of pairings vanishes;
no individual local measure is claimed to be closed, and no global covering or
limit assertion is made here.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.FiniteTelescopeLocalWeightedPairing

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold
open LocalPatchWeightedMeasure
open FormPieceMassCurrentPairingBridge
open FormPieceMassCurrentPairingBridge.FormPieceTelescopeData

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The local area/Jacobian and coefficient data for every member of one finite
regular-piece family.  Each `localMeasure i` already records an explicit finite
Borel measure equal to the weighted pushforward `ρᵢ dvol`; the final field is
the remaining pointwise density identification for the actual telescope
integrand. -/
structure FiniteTelescopeLocalWeightedPairingData
    {beta : KahlerBackground n M}
    {q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
    {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
    {avoid : Set M} {G : RegularPieceFamily V avoid}
    (T : FormPieceTelescopeData beta q hvs G) where
  localMeasure : ∀ i, LocalWeightedPatchMeasure V (G.patch i)
  parameterSet_eq_piece : ∀ i, (localMeasure i).parameterSet = G.piece i
  test : ∀ _i, C_c(M, ℝ)
  telescope_eq_weightedTest : ∀ i,
    ∀ᵐ w ∂volume.restrict (G.piece i),
      T.telescopeIntegrand i w = ((localMeasure i).density w).toReal *
        (test i) ((G.patch i).toManifold w)

namespace FiniteTelescopeLocalWeightedPairingData

variable {beta : KahlerBackground n M}
  {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
  {avoid : Set M} {G : RegularPieceFamily V avoid}
  {T : FormPieceTelescopeData beta q hvs G}

/-- The telescope integral on one parameter piece is its local ambient
weighted-pushforward pairing. -/
theorem telescopeIntegral_eq_pairing
    (S : FiniteTelescopeLocalWeightedPairingData T) (i : Fin G.size) :
    ∫ w in G.piece i, T.telescopeIntegrand i w =
      (S.localMeasure i).pairing (S.test i) := by
  have hpair := (S.localMeasure i).pairing_eq_weightedParameterIntegral (S.test i)
  rw [S.parameterSet_eq_piece i] at hpair
  calc
    ∫ w in G.piece i, T.telescopeIntegrand i w =
        ∫ w in G.piece i, ((S.localMeasure i).density w).toReal *
          (S.test i) ((G.patch i).toManifold w) :=
      integral_congr_ae (S.telescope_eq_weightedTest i)
    _ = (S.localMeasure i).pairing (S.test i) := hpair.symm

/-- Sum the local weighted-pushforward pairings over the finite regular-piece
family.  This is the exact pairing expression a partition-of-unity Stokes
argument has to cancel. -/
theorem sum_telescopeIntegral_eq_sum_pairing
    (S : FiniteTelescopeLocalWeightedPairingData T) :
    ∑ i, ∫ w in G.piece i, T.telescopeIntegrand i w =
      ∑ i, (S.localMeasure i).pairing (S.test i) := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact S.telescopeIntegral_eq_pairing i

/-- The finite signed density defect reduces directly to the finite sum of
local pairings.  No integrability hypothesis is hidden here: the first rewrite
is pointwise on each measurable regular piece, and the second is the supplied
finite weighted-pushforward identity. -/
theorem sum_densityDefectIntegral_eq_sum_pairing
    (S : FiniteTelescopeLocalWeightedPairingData T) :
    ∑ i, ∫ w in G.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (G.patch i) w) =
      ∑ i, (S.localMeasure i).pairing (S.test i) := by
  calc
    ∑ i, ∫ w in G.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (G.patch i) w) =
        ∑ i, ∫ w in G.piece i, T.telescopeIntegrand i w := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (G.measurableSet_piece i)] with w hw
      exact T.density_defect_eq_telescopeIntegrand i hw
    _ = ∑ i, (S.localMeasure i).pairing (S.test i) :=
      S.sum_telescopeIntegral_eq_sum_pairing

/-- Once a partition-of-unity current construction proves that the finite sum
of local pairings vanishes, the corresponding finite signed form-density defect
vanishes as well. -/
theorem sum_densityDefectIntegral_eq_zero_of_sum_pairing_eq_zero
    (S : FiniteTelescopeLocalWeightedPairingData T)
    (hsum : ∑ i, (S.localMeasure i).pairing (S.test i) = 0) :
    ∑ i, ∫ w in G.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs)
          (G.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (G.patch i) w) = 0 :=
  S.sum_densityDefectIntegral_eq_sum_pairing.trans hsum

end FiniteTelescopeLocalWeightedPairingData

end

end SGPT.Foundations.Analysis.Pending.FiniteTelescopeLocalWeightedPairing
