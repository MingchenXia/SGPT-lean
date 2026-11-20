import SGPT.Foundations.Analysis.Pending.TelescopeDefectCutoffSum
import SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction

set_option autoImplicit false

/-!
# A good exhaustion of `V_reg` whose local telescope potentials are plurisubharmonic

`Pending.RegularPieceGoodExhaustion.HasLocalTelescopePotential` records that a
parameter piece lies in one open set carrying a smooth local potential `φ` of the
background together with the density telescope identity — and NOTHING about `φ`
beyond smoothness.  In particular it does not record that `ddᶜφ` is the pulled-back
Kähler background, so it does not imply `(complexHessian φ).PosSemidef`; at
`dim V = 1` the density identity reads `(a + b) - a = b` and constrains the Hessian
of `φ` not at all.  That is why the Chern--Levine--Nirenberg cutoff estimate of
`Pending.TelescopeCutoffEstimate`, whose fixed slots must be plurisubharmonic,
could not be composed with the Stokes obligation: the potential selected for a
piece is an arbitrary `Classical.choose` with no Hessian certificate.

This module closes that gap without touching any existing statement.

* `HasPositiveLocalTelescopePotential` is the same property with the two Hessian
  certificates added.  It is a `LocalPieceProperty` — the `nhds` clause is exactly
  `Pending.TelescopeSlotPositivity.exists_localPotential_telescope_posSemidef`,
  which already produces one `φ` carrying smoothness, both semidefiniteness
  statements and the density identity — so the Lindelöf refinement of
  `Pending.RegularPieceGoodExhaustion` yields an exhaustion of `V_reg` all of whose
  pieces carry a PLURISUBHARMONIC local potential, and forgetting the two
  certificates recovers the old exhaustion.
* `FormPiecePositiveTelescopeData` bundles the selected potentials of a finite
  family with their certificates;
  `abs_integral_mul_mixedDensity_telescope_piece_le` is the cutoff estimate read on
  one slot of one piece of one such family, and
  `abs_integral_mul_telescopeIntegrand_piece_le` is the same estimate on that
  piece's whole telescope integrand, which on the piece is the signed density
  defect.  This is the composition that was missing: the certificates are consumed
  in a proof term, not cited in prose.
* The obligation left at the Stokes interface is INDEPENDENT of which potential was
  selected.  `pairingData_transport` and `remainderData_transport` move a local
  weighted-pairing datum, and the collar-remainder datum built on it, between any
  two telescope data of the SAME finite family: on a piece both telescope
  integrands equal the signed density defect, so the local measures, the test
  functions and hence the remainder can be carried over verbatim.  Consequently
  `finitePairingRemainderData_of_positive` discharges the obligation as
  `Pending.PositiveDimensionalClosedCurrentStokes` states it — with the arbitrary
  chosen potential — from the same obligation for the plurisubharmonic potential.

What is still owed by the Stokes collar step is NOT supplied here: a family of cutoffs
along the exhaustion whose squeeze constants `A_m` times the flat comparison mass of
the collar tend to zero.  (The integrability needed to sum the per-slot bounds over
`j` is proved, in `Pending.TelescopeDefectCutoffSum`.)
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.PositiveTelescopeExhaustion

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.MixedHessian
open SGPT.Foundations.Analysis.Pending.PatchDensityLocalPotential
open SGPT.Foundations.Analysis.Pending.TelescopeSlotPositivity
open SGPT.Foundations.Analysis.Pending.TelescopeFlatSlotCutoff
open SGPT.Foundations.Analysis.Pending.TelescopeDefectCutoffSum
open SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion
open SGPT.Foundations.Analysis.Pending.FormPieceMassCurrentPairingBridge
open SGPT.Foundations.Analysis.Pending.FiniteTelescopeLocalWeightedPairing
open SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}
  {beta : KahlerBackground n M}

/-! ## The strengthened local piece property -/

/-- **Carrying a PLURISUBHARMONIC local telescope potential.**
`RegularPieceGoodExhaustion.HasLocalTelescopePotential`, with the two Hessian
certificates the Chern--Levine--Nirenberg cutoff estimate needs of its fixed
slots: the complex Hessian of `φ` (a local potential of the Kähler background)
and of `φ + v ∘ P` (a local potential of `β + ddᶜv`) are positive semidefinite
on the whole neighbourhood. -/
def HasPositiveLocalTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (P : RegularPatch V) (S : Set (ComplexModel V.dim)) : Prop :=
  ∃ (Omega : Set (ComplexModel V.dim)) (phi : ComplexModel V.dim → ℝ),
    S ⊆ Omega ∧ IsOpen Omega ∧ Omega ⊆ P.parameterDomain ∧
      ContDiffOn ℝ ∞ phi Omega ∧
      ContDiffOn ℝ ∞ (fun y => v (P.toManifold y)) Omega ∧
      (∀ w' ∈ Omega, (complexHessian phi w').PosSemidef) ∧
      (∀ w' ∈ Omega,
        (complexHessian (fun y => phi y + v (P.toManifold y)) w').PosSemidef) ∧
      ∀ w' ∈ Omega,
        PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w' -
            PatchFormMass.patchFormDensity beta.form.val P w' =
          ∑ j : Fin V.dim, mixedDensity
            (telescopeFunctions phi (fun y => v (P.toManifold y)) j) w'

/-- Forgetting the two Hessian certificates recovers the property the existing
Stokes obligation is stated with. -/
theorem hasLocalTelescopePotential_of_positive
    {q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
    {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
    {P : RegularPatch V} {S : Set (ComplexModel V.dim)}
    (h : HasPositiveLocalTelescopePotential q hvs P S) :
    HasLocalTelescopePotential q hvs P S := by
  obtain ⟨Omega, phi, hS, hO, hsub, hphi, hpsi, -, -, hdens⟩ := h
  exact ⟨Omega, phi, hS, hO, hsub, hphi, hpsi, hdens⟩

/-- `HasPositiveLocalTelescopePotential` is a local piece property: it is inherited
by subsets, and `TelescopeSlotPositivity.exists_localPotential_telescope_posSemidef`
supplies it near every parameter of every regular patch. -/
def positiveLocalTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    LocalPieceProperty V where
  good := HasPositiveLocalTelescopePotential q hvs
  mono := by
    rintro P S S' ⟨Omega, phi, hSO, hrest⟩ hS'
    exact ⟨Omega, phi, hS'.trans hSO, hrest⟩
  nhds := by
    intro P w hw
    obtain ⟨Omega, phi, hwO, hOopen, hOsub, hphi, hpsi, hP1, hP2, heq⟩ :=
      exists_localPotential_telescope_posSemidef beta q hq hvs hpot P hw
    exact ⟨Omega, hOopen, hwO, hOsub,
      ⟨Omega, phi, subset_rfl, hOopen, hOsub, hphi, hpsi, hP1, hP2, heq⟩⟩

/-- **The exhaustion of `V_reg` by pieces with a plurisubharmonic local telescope
potential.**  Same shape as
`RegularPieceGoodExhaustion.exists_exhaustion_localTelescopePotential`, with the two
Hessian certificates carried along. -/
theorem exists_exhaustion_positiveLocalTelescopePotential
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    ∃ H : ℕ → RegularPieceFamily V (∅ : Set M),
      (∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
        RegularPieceExhaustion.coveredRegion (H (m + 1))) ∧
      (∀ m i, HasPositiveLocalTelescopePotential q hvs ((H m).patch i) ((H m).piece i)) ∧
      ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        ∃ m, K ⊆ RegularPieceExhaustion.coveredRegion (H m) := by
  obtain ⟨H, hmono, hgood, hexh⟩ :=
    exists_exhaustion_good (positiveLocalTelescopePotential q hq hvs hpot) (V := V)
      isClosed_empty
  exact ⟨H, hmono, fun m i => hgood m i,
    fun K hK hKreg => hexh K hK hKreg (Set.disjoint_empty K)⟩

/-! ## Telescope data of a finite family, with the certificates -/

/-- `FormPieceTelescopeData` with the two Hessian certificates of every selected
potential, on the whole neighbourhood it was selected on. -/
structure FormPiecePositiveTelescopeData
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    {avoid : Set M} (F : RegularPieceFamily V avoid)
    extends FormPieceTelescopeData beta q hvs F where
  potential_posSemidef : ∀ i, ∀ w ∈ omega i, (complexHessian (potential i) w).PosSemidef
  sum_posSemidef : ∀ i, ∀ w ∈ omega i,
    (complexHessian (fun y => potential i y + v ((F.patch i).toManifold y)) w).PosSemidef

variable {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
  {avoid : Set M} {F : RegularPieceFamily V avoid}

/-- A family all of whose pieces carry a plurisubharmonic local telescope potential
supplies one certified datum per piece. -/
def FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential
    (hgood : ∀ i, HasPositiveLocalTelescopePotential q hvs (F.patch i) (F.piece i)) :
    FormPiecePositiveTelescopeData beta q hvs F := by
  choose omega potential hpiece hopen hsub hpotential hrestricted hP1 hP2 hdensity using hgood
  exact
    { omega := omega
      potential := potential
      piece_subset := hpiece
      omega_open := hopen
      omega_subset_domain := hsub
      potential_smooth := hpotential
      restricted_potential_smooth := hrestricted
      density_telescope := hdensity
      potential_posSemidef := hP1
      sum_posSemidef := hP2 }

/-! ## The cutoff estimate on one piece -/

/-- **The Chern--Levine--Nirenberg cutoff bound on one piece of a certified
family.**  For a cutoff `χ` compactly supported in the neighbourhood selected for
the piece `i`, whose complex Hessian is squeezed between `-A` and `A` times the flat
Kähler form, and with `|v ∘ P| ≤ C` on `supp χ`,
\[
  \Bigl|\int\chi\,D_{u_j}\Bigr|\le C\,A\int_{\operatorname{supp}\chi}D_{\text{flat slot }j},
\]
`u_j` being the telescope family of the selected potential with signed index `j`.
The two plurisubharmonicity hypotheses of the estimate are discharged by the
certificates of the datum; nothing is assumed here beyond them. -/
theorem abs_integral_mul_mixedDensity_telescope_piece_le
    (T : FormPiecePositiveTelescopeData beta q hvs F) (i : Fin F.size) (j : Fin V.dim)
    {chi : ComplexModel V.dim → ℝ} (hchi : ContDiffOn ℝ ∞ chi (T.omega i))
    (hchic : HasCompactSupport chi) (hchiO : tsupport chi ⊆ T.omega i)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) -
      complexHessian chi z).PosSemidef)
    (hadd : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) +
      complexHessian chi z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |v ((F.patch i).toManifold z)| ≤ C) :
    |∫ z, chi z * mixedDensity
        (telescopeFunctions (T.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) z| ≤
      C * A * ∫ z in tsupport chi, mixedDensity
        (flatTelescopeSlot (T.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) z :=
  abs_integral_mul_mixedDensity_telescope_le_flat (T.omega_open i) (T.potential_smooth i)
    (T.restricted_potential_smooth i) hchi hchic hchiO
    (fun z hz => T.potential_posSemidef i z (hchiO hz))
    (fun z hz => T.sum_posSemidef i z (hchiO hz)) hsub hadd hC j

/-- **The cutoff bound on the Stokes defect of one piece.**  The same estimate summed over
the `dim V` telescope slots, so the left-hand side is the cutoff against the piece's whole
telescope integrand — which on the piece IS the signed density defect
`ρ_{β+ddᶜv}(P,·) - ρ_β(P,·)` (`density_defect_eq_telescopeIntegrand`).  This is the shape
the Stokes collar step has to make small; what it still owes is the CHOICE of the cutoffs
`χ_m` along the exhaustion. -/
theorem abs_integral_mul_telescopeIntegrand_piece_le
    (T : FormPiecePositiveTelescopeData beta q hvs F) (i : Fin F.size)
    {chi : ComplexModel V.dim → ℝ} (hchi : ContDiffOn ℝ ∞ chi (T.omega i))
    (hchic : HasCompactSupport chi) (hchiO : tsupport chi ⊆ T.omega i)
    {A : ℝ}
    (hsub : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) -
      complexHessian chi z).PosSemidef)
    (hadd : ∀ z ∈ tsupport chi, (((A : ℂ) • (1 : Matrix (Fin V.dim) (Fin V.dim) ℂ)) +
      complexHessian chi z).PosSemidef)
    {C : ℝ} (hC : ∀ z ∈ tsupport chi, |v ((F.patch i).toManifold z)| ≤ C) :
    |∫ z, chi z * T.telescopeIntegrand i z| ≤
      C * A * ∑ j : Fin V.dim, ∫ z in tsupport chi, mixedDensity
        (flatTelescopeSlot (T.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) z :=
  abs_integral_mul_telescopeDefect_le (T.omega_open i) (T.potential_smooth i)
    (T.restricted_potential_smooth i) hchi hchic hchiO
    (fun z hz => T.potential_posSemidef i z (hchiO hz))
    (fun z hz => T.sum_posSemidef i z (hchiO hz)) hsub hadd hC

/-! ## The Stokes obligation is independent of the selected potential -/

/-- On a piece, the telescope integrands of ANY two telescope data of the same
family agree: both are the signed density defect there. -/
theorem telescopeIntegrand_congr (T T' : FormPieceTelescopeData beta q hvs F)
    (i : Fin F.size) {w : ComplexModel V.dim} (hw : w ∈ F.piece i) :
    T.telescopeIntegrand i w = T'.telescopeIntegrand i w :=
  (T.density_defect_eq_telescopeIntegrand i hw).symm.trans
    (T'.density_defect_eq_telescopeIntegrand i hw)

/-- **Local weighted-pairing data transport between telescope data.**  The local
measures, the parameter sets and the test functions are carried over verbatim; only
the density identification has to be moved, and on a piece the two telescope
integrands are equal. -/
def pairingData_transport {T T' : FormPieceTelescopeData beta q hvs F}
    (S : FiniteTelescopeLocalWeightedPairingData T') :
    FiniteTelescopeLocalWeightedPairingData T where
  localMeasure := S.localMeasure
  parameterSet_eq_piece := S.parameterSet_eq_piece
  test := S.test
  telescope_eq_weightedTest := by
    intro i
    filter_upwards [S.telescope_eq_weightedTest i,
      ae_restrict_mem (F.measurableSet_piece i)] with w hw hwmem
    rw [telescopeIntegrand_congr T T' i hwmem]
    exact hw

/-- **The collar-remainder datum transports with the same remainder.**  The pairing
sum it bounds is literally the same finite sum, because `pairingData_transport`
keeps the local measures and test functions. -/
def remainderData_transport {T T' : FormPieceTelescopeData beta q hvs F}
    (D : FiniteTelescopePairingRemainderData T') :
    FiniteTelescopePairingRemainderData T where
  weightedPairing := pairingData_transport D.weightedPairing
  remainder := D.remainder
  abs_sum_pairing_le := D.abs_sum_pairing_le

@[simp] theorem remainderData_transport_remainder
    {T T' : FormPieceTelescopeData beta q hvs F}
    (D : FiniteTelescopePairingRemainderData T') :
    (remainderData_transport (T := T) D).remainder = D.remainder := rfl

/-- **The Stokes collar obligation may be discharged with a PLURISUBHARMONIC
potential.**  The obligation of
`Pending.PositiveDimensionalClosedCurrentStokes.ClosedCurrentFinitePairingRemainderData`
is stated for the potential `of_localTelescopePotential` selects by
`Classical.choose`, which carries no Hessian certificate.  This says the two
obligations are the same: a remainder datum for the certified potentials of the
family yields one for the selected potentials, with the same remainder. -/
def finitePairingRemainderData_of_positive
    (hgood : ∀ i, HasPositiveLocalTelescopePotential q hvs (F.patch i) (F.piece i))
    (D : FiniteTelescopePairingRemainderData
      (FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential
        hgood).toFormPieceTelescopeData) :
    FiniteTelescopePairingRemainderData
      (FormPieceTelescopeData.of_localTelescopePotential
        (fun i => hasLocalTelescopePotential_of_positive (hgood i))) :=
  remainderData_transport D

@[simp] theorem finitePairingRemainderData_of_positive_remainder
    (hgood : ∀ i, HasPositiveLocalTelescopePotential q hvs (F.patch i) (F.piece i))
    (D : FiniteTelescopePairingRemainderData
      (FormPiecePositiveTelescopeData.of_positiveLocalTelescopePotential
        hgood).toFormPieceTelescopeData) :
    (finitePairingRemainderData_of_positive hgood D).remainder = D.remainder := rfl

end

end SGPT.Foundations.Analysis.Pending.PositiveTelescopeExhaustion
