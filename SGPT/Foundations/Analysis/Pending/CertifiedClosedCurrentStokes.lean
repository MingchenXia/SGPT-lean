import SGPT.Foundations.Analysis.Pending.PositiveTelescopeExhaustion
import SGPT.Foundations.Analysis.Pending.PositiveDimensionalClosedCurrentStokes
import SGPT.Foundations.Analysis.Pending.StokesRegularLocusIdentity

set_option autoImplicit false

/-!
# The closed-current Stokes datum, with plurisubharmonic local potentials

Blueprint `ana:stokes-certified-input`.  `certifiedFinitePairingRemainderData_of_closed_integrationCurrent`
supplies, along a monotone compact-absorbing exhaustion of `V_reg` by finite regular-piece families
whose local telescope potentials carry the two Hessian certificates
(`Pending.PositiveTelescopeExhaustion`), local weighted-pushforward measures whose finite pairing sum
is bounded by a remainder tending to zero.  It is PROVED: the exhaustion hypotheses `hmono`, `hexh`
were added by human decision I-0902 (inbox I-0839 showed the statement false without them), and the
remainder `|mass_{H m}(β + ddᶜv) − mass_{H m}(β)|` tends to zero because both masses converge to the
masses on `V_reg`, which are equal by Stokes on the regular locus
(`Pending.StokesRegularLocusIdentity`).

* `closedCurrentFinitePairingRemainderData_of_certified`: the certified datum gives the datum of
  `PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData` for the same
  family (proved transport of `Pending.PositiveTelescopeExhaustion`).  The older named input stated
  with that structure along arbitrary sequences of families was retired.
* `formPieceMassCollarError_of_certified`, `formPieceMassCommonLimit_of_certified`,
  `iSup_formPieceMass_global_eq_of_certified`: the collar error, the common limit and the global
  regular-piece supremum equality, along the exhaustion of
  `PositiveTelescopeExhaustion.exists_exhaustion_positiveLocalTelescopePotential`.

Source: Lelong, *Intégration sur un ensemble analytique complexe* (1957), and Demailly, *Complex
Analytic and Differential Geometry*, III, Theorem 2.7 (`demailly-cadg:III.2.7`).
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.CertifiedClosedCurrentStokes

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.SingularCollarMassErrorReduction
open SGPT.Foundations.Analysis.Pending.ClosedCurrentMassLimitReduction
open SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction
open SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction.ExhaustionPartitionPairingRemainderData
open SGPT.Foundations.Analysis.Pending.ClosedCurrentMassFinitenessReduction
open SGPT.Foundations.Analysis.Pending.PositiveTelescopeExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The finite-cutoff datum supplied by the closed-current argument, along an
exhaustion whose local telescope potentials are PLURISUBHARMONIC.  Identical to
`PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData`
except that `hgood` carries the two Hessian certificates, so the telescope data
the pairing remainder is stated for are the certified ones. -/
structure CertifiedFinitePairingRemainderData
    [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i))
    (hV : V.dim ≠ 0) where
  pairingRemainder : ∀ m,
    FiniteTelescopePairingRemainderData
      (FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential
        (hgood m)).toFormPieceTelescopeData
  tendsto_remainder : Tendsto
    (fun m => (pairingRemainder m).remainder) atTop (𝓝 0)

/-- **The closed-integration-current datum along an exhaustion with plurisubharmonic local
potentials** (blueprint `ana:stokes-certified-input`), PROVED.  The exhaustion hypotheses `hmono`
and `hexh` were added by human decision I-0902 (inbox I-0839: without them the statement is false,
a fixed family has unequal masses).  With them the remainder
`|mass_{H m}(β + ddᶜv) − mass_{H m}(β)|` tends to `0`: both masses converge along the exhaustion to
the masses on `V_reg`, which are equal by Stokes on the regular locus
(`StokesRegularLocusIdentity.tendsto_pairingRemainder_of_exhaustion`). -/
noncomputable def certifiedFinitePairingRemainderData_of_closed_integrationCurrent
    [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (H : ℕ → RegularPieceFamily V (∅ : Set M))
    (hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i))
    (hmono : ∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
      RegularPieceExhaustion.coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ RegularPieceExhaustion.coveredRegion (H m))
    (hV : V.dim ≠ 0) :
    CertifiedFinitePairingRemainderData beta V q hq hvs hpot H hgood hV :=
  ⟨StokesRegularLocusIdentity.pairingRemainder_of_exhaustion beta V q hvs hpot H hgood,
    StokesRegularLocusIdentity.tendsto_pairingRemainder_of_exhaustion beta V q hq hvs hpot H hgood
      hmono hexh⟩

/-- The certified input implies the input the existing interface is stated with:
the local measures, the test functions and the remainder transport verbatim
between the certified and the `Classical.choose`-selected telescope data of the
same family.  So no obligation has been weakened by adding the certificates. -/
def closedCurrentFinitePairingRemainderData_of_certified
    [CompactSpace M] {beta : KahlerBackground n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
    {hq : q.representative = 0} {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
    {hpot : q.potential = fun x => ((v x : ℝ) : EReal)}
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    {hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i)}
    {hV : V.dim ≠ 0}
    (D : CertifiedFinitePairingRemainderData beta V q hq hvs hpot H hgood hV) :
    PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData
      beta V q hq hvs hpot H
      (fun m i => hasLocalTelescopePotential_of_positive (hgood m i)) hV where
  pairingRemainder := fun m =>
    finitePairingRemainderData_of_positive (hgood m) (D.pairingRemainder m)
  tendsto_remainder := by simpa using D.tendsto_remainder

/-- The certified source datum produces the signed singular-collar error used by
the existing common-limit reduction.  The nonnegativity, finiteness and
background-mass facts are the same proved ones as in the uncertified assembly;
only the telescope data are the certified ones. -/
noncomputable def formPieceMassCollarError_of_certified
    [CompactSpace M] {beta : KahlerBackground n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
    {hq : q.representative = 0} {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
    {hpot : q.potential = fun x => ((v x : ℝ) : EReal)}
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    {hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i)}
    {hV : V.dim ≠ 0}
    (D : CertifiedFinitePairingRemainderData beta V q hq hvs hpot H hgood hV) :
    FormPieceMassCollarError (ACTopMassComparison.currentForm q hvs) beta.form.val H := by
  apply toFormPieceMassCollarError
  refine
    { telescope := fun m =>
        (FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential
          (hgood m)).toFormPieceTelescopeData
      pairingRemainder := D.pairingRemainder
      current_nonneg := ?_
      background_nonneg := ?_
      current_ne_top := fun m =>
        formPieceMass_currentForm_ne_top (q := q) (hvs := hvs) (beta := beta) hpot (H m)
      background_ne_top := ?_
      error := fun m => (D.pairingRemainder m).remainder
      tendsto_error := D.tendsto_remainder
      remainder_le_error := fun _ => le_rfl }
  · intro m i w hw
    exact PatchDensityTelescope.patchFormDensity_currentForm_nonneg q hvs hpot
      ((H m).patch i) ((H m).piece_subset i hw)
  · intro m i w hw
    exact PatchDensityTelescope.patchFormDensity_kahler_nonneg beta ((H m).patch i)
      ((H m).piece_subset i hw)
  · intro m
    have hglobal : (⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F) ≠ ⊤ :=
      SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V
    exact ne_top_of_le_ne_top hglobal
      (le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
        PatchFormMass.formPieceMass beta.form.val F) (H m))

/-- The certified collar estimate has a common finite-piece mass limit, the
background mass being finite by the proved local Lelong bound. -/
noncomputable def formPieceMassCommonLimit_of_certified
    [CompactSpace M] {beta : KahlerBackground n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
    {hq : q.representative = 0} {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
    {hpot : q.potential = fun x => ((v x : ℝ) : EReal)}
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    {hgood : ∀ m i, HasPositiveLocalTelescopePotential q hvs
      ((H m).patch i) ((H m).piece i)}
    {hV : V.dim ≠ 0}
    (D : CertifiedFinitePairingRemainderData beta V q hq hvs hpot H hgood hV)
    (hmono : ∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
      RegularPieceExhaustion.coveredRegion (H (m + 1)))
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ RegularPieceExhaustion.coveredRegion (H m)) :
    FormPieceMassCommonLimit (ACTopMassComparison.currentForm q hvs) beta.form.val H := by
  apply FormPieceMassCollarError.commonLimit_of_collarError
    (formPieceMassCollarError_of_certified D)
  · exact RegularPieceExhaustion.tendsto_formPieceMass_of_exhaustion isClosed_empty hmono
      (fun K hK hKreg _ => hexh K hK hKreg) beta.form.val
  · exact SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V

/-- **The global regular-piece supremum equality from the certified datum**, along the exhaustion
with plurisubharmonic local telescope potentials. -/
theorem iSup_formPieceMass_global_eq_of_certified
    [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (hV : V.dim ≠ 0) :
    (⨆ F : RegularPieceFamily V (∅ : Set M), PatchFormMass.formPieceMass
      (ACTopMassComparison.currentForm q hvs) F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F := by
  obtain ⟨H, hmono, hgood, hexh⟩ :=
    exists_exhaustion_positiveLocalTelescopePotential q hq hvs hpot
  exact iSup_formPieceMass_eq_of_commonLimit
    (ACTopMassComparison.currentForm q hvs) beta.form.val hmono hexh
    (formPieceMassCommonLimit_of_certified
      (certifiedFinitePairingRemainderData_of_closed_integrationCurrent beta V q hq hvs hpot H
        hgood hmono hexh hV) hmono hexh)

end

end SGPT.Foundations.Analysis.Pending.CertifiedClosedCurrentStokes
