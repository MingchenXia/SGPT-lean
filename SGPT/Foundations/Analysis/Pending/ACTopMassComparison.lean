import SGPT.Foundations.Analysis.Pending.PatchFormMass
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm

set_option autoImplicit false

/-!
# The restricted mass of a smooth-potential presentation, patch by patch

`Pending.RegularPieceMassComparison` compares two regular-piece families for the
BACKGROUND Kähler form, and the docstring of
`SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass` records why the same
comparison was not available for `acTopMass`:

> the change of variables ... is stated for a `SmoothRealForm n M 2`, whereas
> `patchDensity` is built from `coordinateCurrentForm`, which adds a `smoothDDC`
> term read in the chart at the centre of the patch.  Two patches have different
> centres, so the transfer needs the chart-change law for that `smoothDDC` term
> as well.

That law is not missing.  `Pending.SmoothDDCForm.ddcForm` already bundles `ddᶜv`
of a CHART-SMOOTH REAL function `v` as a genuine `SmoothRealForm n M 2`, and the
`compatible` field of that bundle *is* the chart-change law (it rests on
`FirstPass.HolomorphicDDC.smoothDc_comp`, the naturality of the normalized `dᶜ`
under a holomorphic map, and on mathlib's `extDeriv_pullback`).

So for a presentation whose potential is a chart-smooth real function the
coordinate current form is the coefficient family of ONE bundled smooth
two-form,

  `coordinateCurrentForm q e = (θ + εω + ddᶜv).coeff e`  (`coordinateCurrentForm_eq`),

and the whole patch-change apparatus of `Pending.PatchFormMass` applies to
`acTopMass` unchanged: a family is dominated by any family covering more of
`V_reg` (`acPieceMass_mono_of_image_subset`), two families covering the same
region compute the same mass, and the supremum defining `acTopMass` is directed.

For such a potential the pole set is empty (`poleSet_eq_empty`), so the families
occurring in `acTopMass` are literally the families occurring in
`backgroundMass`, and `acTopMass_eq_iSup_formPieceMass` writes both sides of the
Stokes obligation as suprema of `formPieceMass` over the SAME index type — the
left-hand side for `β + ddᶜv` and the right-hand side for `β`.

**What this does not do.**  It does not prove Stokes.  The remaining content of
`acTopMass_eq_backgroundMass` is exactly the classical part: a sequence of finite
regular-piece families exhausting `V_reg` in measure (an analytic-geometry
statement about `V_sing`), and the vanishing of `∫_{V_reg} ((β + ddᶜv)^k - β^k)`,
which is Stokes against the closed integration current `[V]`.  What is removed is
the bookkeeping obstruction that made the two sides incomparable family by
family.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ACTopMassComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open PatchFormMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- **The perturbed current of a smooth-potential presentation, as one bundled
smooth two-form** `θ + εω + ddᶜv`.  The overlap law is the overlap law of the
representative together with that of `Pending.SmoothDDCForm.ddcForm`. -/
def currentForm (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v) : SmoothRealForm n M 2 where
  coeff e z :=
    (perturbedRepresentative q).val.coeff e z + (SmoothDDCForm.ddcForm v hv).coeff e z
  smooth e :=
    ((perturbedRepresentative q).val.smooth e).add ((SmoothDDCForm.ddcForm v hv).smooth e)
  compatible e f z hz w :=
    congrArg₂ (· + ·) ((perturbedRepresentative q).val.compatible e f z hz w)
      ((SmoothDDCForm.ddcForm v hv).compatible e f z hz w)

@[simp] theorem currentForm_coeff
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v) (e : ComplexChart n M) (z : ComplexModel n) :
    (currentForm q hv).coeff e z =
      (perturbedRepresentative q).val.coeff e z + smoothDDC (fun y => v (e.val.symm y)) z := rfl

/-- **The coordinate current form of a smooth-potential presentation is the
coefficient family of a single bundled smooth two-form.** -/
theorem coordinateCurrentForm_eq
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (e : ComplexChart n M) (z : ComplexModel n) :
    coordinateCurrentForm q e z = (currentForm q hv).coeff e z := by
  simp [coordinateCurrentForm, hpot]

/-- The parameter density of a smooth-potential presentation is the parameter
density of that bundled form. -/
theorem patchDensity_eq_patchFormDensity
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    patchDensity q P w = patchFormDensity (currentForm q hv) P w := by
  simp only [patchDensity, patchFormDensity, RegularPatchTransition.patchCoordinateForm,
    coordinateCurrentForm_eq q hv hpot]

/-- A real-valued potential has no poles. -/
theorem poleSet_eq_empty
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    poleSet q.potential = (∅ : Set M) := by
  ext x
  simp [hpot]

/-- The finite sum attached to one regular-piece family by a presentation.
`acTopMass` is its supremum over the families avoiding the pole set. -/
def acPieceMass (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {avoid : Set M} (F : RegularPieceFamily V avoid) : ℝ≥0∞ :=
  ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity q (F.patch i) w)

theorem acTopMass_eq_iSup
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon) :
    acTopMass q = ⨆ F : RegularPieceFamily V (poleSet q.potential), acPieceMass q F := rfl

theorem acPieceMass_le_acTopMass
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (F : RegularPieceFamily V (poleSet q.potential)) :
    acPieceMass q F ≤ acTopMass q :=
  le_iSup (fun F : RegularPieceFamily V (poleSet q.potential) => acPieceMass q F) F

theorem acPieceMass_eq_formPieceMass
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    {avoid : Set M} (F : RegularPieceFamily V avoid) :
    acPieceMass q F = formPieceMass (currentForm q hv) F :=
  Finset.sum_congr rfl fun i _ => lintegral_congr fun w =>
    congrArg ENNReal.ofReal (patchDensity_eq_patchFormDensity q hv hpot (F.patch i) w)

/-- **The restricted mass of a smooth-potential presentation is monotone in the
region of `V_reg` that is covered.**  This is the left-hand-side comparison that
`SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass` records as missing. -/
theorem acPieceMass_mono_of_image_subset
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    {avoidF avoidG : Set M} {F : RegularPieceFamily V avoidF} {G : RegularPieceFamily V avoidG}
    (hcov : ∀ i, (F.patch i).toManifold '' F.piece i ⊆
      ⋃ j, (G.patch j).toManifold '' G.piece j) :
    acPieceMass q F ≤ acPieceMass q G := by
  rw [acPieceMass_eq_formPieceMass q hv hpot, acPieceMass_eq_formPieceMass q hv hpot]
  exact formPieceMass_mono_of_image_subset _ hcov

/-- Two families covering the same part of `V_reg` compute the same restricted
mass. -/
theorem acPieceMass_congr_of_iUnion_image_eq
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    {avoidF avoidG : Set M} {F : RegularPieceFamily V avoidF} {G : RegularPieceFamily V avoidG}
    (h : (⋃ i, (F.patch i).toManifold '' F.piece i) =
      ⋃ j, (G.patch j).toManifold '' G.piece j) :
    acPieceMass q F = acPieceMass q G := by
  rw [acPieceMass_eq_formPieceMass q hv hpot, acPieceMass_eq_formPieceMass q hv hpot]
  exact formPieceMass_congr_of_iUnion_image_eq _ h

/-- **The supremum defining `acTopMass` is directed** for a smooth-potential
presentation: two families are dominated by their union family. -/
theorem directed_acPieceMass
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) (avoid : Set M) :
    Directed (· ≤ ·) (fun F : RegularPieceFamily V avoid => acPieceMass q F) := by
  intro F G
  refine ⟨unionFamily F G, ?_, ?_⟩
  · show acPieceMass q F ≤ acPieceMass q (unionFamily F G)
    rw [acPieceMass_eq_formPieceMass q hv hpot, acPieceMass_eq_formPieceMass q hv hpot]
    exact le_formPieceMass_unionFamily_left _ F G
  · show acPieceMass q G ≤ acPieceMass q (unionFamily F G)
    rw [acPieceMass_eq_formPieceMass q hv hpot, acPieceMass_eq_formPieceMass q hv hpot]
    exact le_formPieceMass_unionFamily_right _ F G

/-- Re-labelling the set a family avoids, along an equality of sets. -/
def retagFamily {A B : Set M} (h : A = B) (F : RegularPieceFamily V A) :
    RegularPieceFamily V B where
  size := F.size
  patch := F.patch
  piece := F.piece
  measurableSet_piece := F.measurableSet_piece
  piece_subset := F.piece_subset
  image_subset_regularLocus := F.image_subset_regularLocus
  image_disjoint_avoid := fun i => h ▸ F.image_disjoint_avoid i
  pairwise_disjoint_image := F.pairwise_disjoint_image

@[simp] theorem retagFamily_patch {A B : Set M} (h : A = B) (F : RegularPieceFamily V A) :
    (retagFamily h F).patch = F.patch := rfl

@[simp] theorem retagFamily_piece {A B : Set M} (h : A = B) (F : RegularPieceFamily V A) :
    (retagFamily h F).piece = F.piece := rfl

/-- **Both sides of the Stokes obligation are suprema over the SAME index type.**
For a chart-smooth real potential the pole set is empty, so the families
occurring in `acTopMass q` are the families occurring in `backgroundMass`, and
the left-hand side is the `formPieceMass` supremum of the single smooth form
`θ + εω + ddᶜv`. -/
theorem acTopMass_eq_iSup_formPieceMass
    (q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    {v : M → ℝ} (hv : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    acTopMass q =
      ⨆ F : RegularPieceFamily V (∅ : Set M), formPieceMass (currentForm q hv) F := by
  have hpole : poleSet q.potential = (∅ : Set M) := poleSet_eq_empty q hpot
  refine le_antisymm (iSup_le fun F => ?_) (iSup_le fun F => ?_)
  · refine le_trans (le_of_eq ?_)
      (le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
        formPieceMass (currentForm q hv) F) (retagFamily hpole F))
    exact acPieceMass_eq_formPieceMass q hv hpot F
  · refine le_trans (le_of_eq ?_) (acPieceMass_le_acTopMass q (retagFamily hpole.symm F))
    exact (acPieceMass_eq_formPieceMass q hv hpot (retagFamily hpole.symm F)).symm

end

end SGPT.Foundations.Analysis.Pending.ACTopMassComparison
