import SGPT.Foundations.Analysis.Pending.SubvarietyBackgroundMass
import SGPT.Foundations.Analysis.Pending.ACTopMassComparison
import SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion
import SGPT.Foundations.Analysis.Pending.PatchDensityTelescope
import SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion
import SGPT.Foundations.Analysis.Pending.PositiveDimensionalClosedCurrentStokes
import SGPT.Foundations.Analysis.Pending.CertifiedClosedCurrentStokes

set_option autoImplicit false

/-!
# The two named classical inputs behind subvariety Stokes mass

`Pending.SubvarietyStokesMass` states two obligations about SMOOTH `β`-psh
potentials on an irreducible analytic subvariety `V` of a compact Kähler
manifold: independence of the top mass of the potential (Stokes against the
closed integration current `[V]`), and finiteness of that mass (Lelong's local
finite volume of `V_reg`).  The code audit
`docs/stokes_formalization_audit_20260920.md` found no Mathlib or public Lean
source for either.

This module isolates them as two *named* interfaces about a single object each,
so that the two obligations become corollaries rather than bare `sorry`s.

* `backgroundMass beta V` (defined in `Pending.SubvarietyBackgroundMass`) is the
  finite-regular-piece supremum of the parameter densities of the **background
  Kähler form alone** — no class, no admissible presentation, no potential, no
  pole set.
* `backgroundMass_ne_top` (LELONG) says that number is finite.  This is exactly
  `k! vol_β(V_reg) < ∞`, phrased in the project's regular-patch parametrization.
  It is now DERIVED in `Pending.SubvarietyBackgroundMass` from the strictly
  local bound `exists_localBackgroundBound`, which is the one classical input
  left on this side.
* `acTopMass_eq_backgroundMass` (STOKES) says that the mass of *any* admissible
  presentation of the zero class with zero representative and a chart-smooth
  real potential equals that same number.  This is the one-potential form
  `∫_{V_reg}(β + ddᶜv)^k = ∫_{V_reg} β^k`; the two-potential statement of
  `SubvarietyStokesMass.acTopMass_eq_of_smooth` follows by comparing both sides
  with the fixed quantity `backgroundMass beta V`.

Naming them this way also records the exact shape a future formalization must
produce: a proper finite branched projection with a uniform sheet bound near
every point of `V` (for the first) and closedness of the integration current of
`V_reg` against compactly supported smooth forms (for the second).
-/

open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SubvarietyStokesMassInterfaces

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open MeasureTheory

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- With zero representative and zero potential, the parameter density of a
presentation is the parameter density of the background K\"ahler form itself. -/
theorem patchDensity_eq_formPatchDensity_of_zero
    {beta : KahlerBackground n M} {V : ClosedIrreducibleAnalyticSubvariety n M}
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    patchDensity q P w = formPatchDensity beta.form P w := by
  have hrep : perturbedRepresentative q = beta.form := by
    simp [perturbedRepresentative, hq]
  simp [patchDensity, formPatchDensity, coordinateCurrentForm, hv, hrep]

/-- A zero-potential presentation of the zero class with zero representative has
exactly the background mass.  This is an unconditional computation: it does NOT
use the Stokes interface below, because there is no potential to move. -/
theorem acTopMass_eq_backgroundMass_of_potential_eq_zero
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0) :
    acTopMass q = backgroundMass beta V := by
  have hpole : poleSet q.potential = (∅ : Set M) := by
    rw [hv]
    ext x
    simp [poleSet]
  unfold acTopMass backgroundMass
  rw [hpole]
  refine iSup_congr fun F => Finset.sum_congr rfl fun i _ => lintegral_congr fun w => ?_
  exact congrArg ENNReal.ofReal (patchDensity_eq_formPatchDensity_of_zero q hq hv (F.patch i) w)

/-- **Lelong finiteness of the background mass.**  The regular locus of an
irreducible analytic subvariety of a compact Kähler manifold has finite volume,
so the background regular-piece mass is finite.

This is no longer an assumption of this module.  `Pending.SubvarietyBackgroundMass`
proves the whole passage from the LOCAL finite-volume bound to this global
statement (`backgroundMass_ne_top_of_localBounds`: compactness of the carrier, a
finite subcover, and subadditivity of the parameter integral over the induced
finite cover of every piece).  What remains is the local bound
`exists_localBackgroundBound`, the single named classical input. -/
theorem backgroundMass_ne_top [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    backgroundMass beta V ≠ ⊤ :=
  backgroundMass_ne_top' beta V

/-- The background regular-piece mass of a family is the `PatchFormMass` mass of
the background form: the two densities are the same expression. -/
theorem backgroundPieceMass_eq_formPieceMass (beta : KahlerBackground n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (F : RegularPieceFamily V (∅ : Set M)) :
    backgroundPieceMass beta F = PatchFormMass.formPieceMass beta.form.val F := rfl

/-- `backgroundMass` is the `PatchFormMass` supremum of the background form. -/
theorem backgroundMass_eq_iSup_formPieceMass (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    backgroundMass beta V =
      ⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F := rfl

/-- **The Stokes obligation, read along an exhaustion.**  The regular-piece
supremum identity for the two smooth two-forms `β + ddᶜv` and `β` follows from
the same identity along ANY monotone sequence of finite regular-piece families
that absorbs every compact subset of `V_reg`.

This is the whole content of the exhaustion step, and it is PROVED: by
`Pending.RegularPieceExhaustion.exists_exhaustion` such a sequence exists, and by
`Pending.RegularPieceExhaustion.iSup_formPieceMass_eq_iSup_of_exhaustion` it
computes the regular-piece supremum of every smooth real two-form -- the SAME
sequence for both forms, which a two-form comparison needs and which no finite
family supplies.  Only Stokes itself is left to the hypothesis. -/
theorem iSup_formPieceMass_currentForm_eq_of_exhaustion (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hstokes : ∀ H : ℕ → RegularPieceFamily V (∅ : Set M),
      (∀ m, RegularPieceExhaustion.coveredRegion (H m) ⊆
        RegularPieceExhaustion.coveredRegion (H (m + 1))) →
      (∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
        ∃ m, K ⊆ RegularPieceExhaustion.coveredRegion (H m)) →
      (⨆ m : ℕ, PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) (H m)) =
        ⨆ m : ℕ, PatchFormMass.formPieceMass beta.form.val (H m)) :
    (⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F := by
  obtain ⟨H, hmono, hexh⟩ :=
    RegularPieceExhaustion.exists_exhaustion (V := V) (avoid := (∅ : Set M)) isClosed_empty
  have hexh' : ∀ K : Set M, IsCompact K → K ⊆ regularLocus (n := n) V.carrier V.dim →
      ∃ m, K ⊆ RegularPieceExhaustion.coveredRegion (H m) :=
    fun K hK hKreg => hexh K hK hKreg (Set.disjoint_empty K)
  rw [← RegularPieceExhaustion.iSup_formPieceMass_eq_iSup_of_exhaustion isClosed_empty hexh
      (ACTopMassComparison.currentForm q hvs),
    ← RegularPieceExhaustion.iSup_formPieceMass_eq_iSup_of_exhaustion isClosed_empty hexh
      beta.form.val]
  exact hstokes H hmono hexh'

/-- **NAMED CLASSICAL INPUT (Stokes against the closed current `[V]`), in its
bare form.**  For a presentation of the zero class with zero representative,
unit error and a chart-smooth real potential `v`, the regular-piece suprema of
the two smooth two-forms `β + ddᶜv` and `β` agree.

This is `∫_{V_reg}(β + ddᶜv)^k = ∫_{V_reg}β^k` with every trace of the
presentation removed: two smooth real two-forms on `X`, one parameter density
each, one supremum each, over the same finite regular-piece families.  A
family-by-family identity is FALSE, so a proof needs the exhaustion of `V_reg`
by finite regular pieces near `V_sing` as well as Stokes for the closed current
`[V]`.  The exhaustion is now PROVED, in
`Pending.RegularPieceExhaustion.exists_exhaustion_iSup_formPieceMass`: one
monotone sequence of finite families, depending on `V` alone and not on any form,
absorbs every compact subset of `V_reg` and therefore computes the regular-piece
supremum of EVERY smooth real two-form.  The reduction
`iSup_formPieceMass_currentForm_eq_of_exhaustion` above consumes it, so what is
left here is Stokes itself, read along such a sequence: nothing in the exhaustion
compares two different forms.

The ZERO-DIMENSIONAL case is proved below and no longer part of the hypothesis: for
`dim V = 0` every parameter density is the empty wedge `1`, so the two masses agree family
by family (`Pending.PatchDensityTelescope.formPieceMass_eq_of_dim_eq_zero`).  The `sorry`
is therefore confined to `dim V ≠ 0`.

The ALGEBRA of the remaining branch is discharged in `Pending.PatchDensityTelescope` and
`Pending.PatchDensityLocalPotential`: the difference of the two parameter densities is a
sum of `dim V` mixed densities each carrying `ddᶜv` once, both densities are nonnegative,
and locally the difference is the mixed Monge--Ampère density of `dim V` smooth real
functions of `dim V` complex variables.  Three things still separate that from this
statement -- the passage from those signed real densities to the `ENNReal` suprema here,
the cut-off against the exhaustion, and the collar estimate near `V_sing` -- and they are
recorded on this declaration's hgraph node.

The exhaustion is now read through `Pending.RegularPieceGoodExhaustion`, so the residue is
strictly smaller than the bare supremum identity: the sequence of families supplied at the
`sorry` has the extra property that EVERY piece of EVERY family lies inside one open
parameter set carrying a smooth local potential of `β` (and on which `v` restricted to the
branch is smooth), on which the difference of the two parameter densities is the sum of the
`dim V` mixed Monge--Ampère densities of the telescope families.  That is the shape for
which integration by parts against a compactly supported test function is proved in
`Pending.MixedHessian`.  What is left is the partition of unity subordinate to the pieces,
the extension of the local potentials to globally smooth functions, and the collar estimate
near `V_sing`.

The route now goes through `Pending.CertifiedClosedCurrentStokes`, whose input is asked for
along an exhaustion carrying MORE: on every piece, the selected local potential `φ` also
comes with positive semidefiniteness of the complex Hessians of `φ` and of `φ + v ∘ P`.
That strengthened exhaustion exists (`Pending.PositiveTelescopeExhaustion`), the certified
input implies the older one of `Pending.PositiveDimensionalClosedCurrentStokes`, and the
certificates are exactly what the Chern--Levine--Nirenberg cutoff estimate consumes of the
fixed telescope slots — which `HasLocalTelescopePotential` alone does not supply.  That move
discharges NO part of the obligation: the certified input follows from the older one by
instantiation and inherits its load-bearing fields verbatim.  It narrowed the domain of the
then-remaining `sorry` so that a proof of it may use the plurisubharmonicity.  STATUS:
the certified input is now PROVED (`Pending.StokesRegularLocusIdentity`; its exhaustion hypotheses
were added by human decision), and the older input was retired. -/
theorem iSup_formPieceMass_currentForm_eq [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (_hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    (⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) F) =
      ⨆ F : RegularPieceFamily V (∅ : Set M),
        PatchFormMass.formPieceMass beta.form.val F := by
  by_cases hV : V.dim = 0
  · -- In complex dimension zero every parameter density is the empty wedge `1`, so the two
    -- masses coincide family by family and no analysis is needed.
    exact iSup_congr fun F =>
      PatchDensityTelescope.formPieceMass_eq_of_dim_eq_zero _ _ hV F
  · -- The exhaustion is built so that every piece lies in ONE open parameter set on which
    -- the Stokes defect is a sum of `dim V` mixed Monge--Ampère densities of smooth real
    -- functions of `dim V` complex variables AND the two fixed telescope slots are
    -- plurisubharmonic.  The remaining closed-current cut-off/collar argument is the
    -- source-anchored interface of `Pending.CertifiedClosedCurrentStokes`.
    exact _root_.SGPT.Foundations.Analysis.Pending.CertifiedClosedCurrentStokes.iSup_formPieceMass_global_eq_of_certified
      beta V q hq hvs _hpot hV

/-- **NAMED CLASSICAL INPUT (Stokes against the closed current `[V]`).**  The
top mass of a smooth `β`-psh potential on `V_reg` does not depend on the
potential: it is the background mass.

Missing ingredient, per `docs/stokes_formalization_audit_20260920.md`:
differential forms and the exterior derivative on the regular analytic locus,
an integration current `[V]` with closedness, a cut-off/exhaustion argument near
`V_sing`, and the bridge from `acTopMass` coordinate-density sums to current
pairings.

Note that both sides here are suprema over FINITE regular-piece families, and
for a fixed family the two sums are in general different: Stokes only holds over
all of `V_reg`.  So a proof must also supply the exhaustion step, that finite
disjoint regular pieces approximate `V_reg` in measure.

A PREREQUISITE for using such a sequence exists on BOTH sides.
`Pending.PatchFormMass` proves `formPieceMass_mono_of_image_subset` — a family is
dominated by any family covering more of `V_reg` — for an ARBITRARY
`a : SmoothRealForm n M 2` and arbitrary avoided sets, and deduces
`directed_formPieceMass`.

On the left-hand side `Pending.ACTopMassComparison` applies it to `acTopMass q`.
The obstruction recorded here in earlier rounds was that `patchDensity` is built
from `coordinateCurrentForm`, which adds a `smoothDDC` term read in the chart at
the centre of the patch, so that transferring the comparison would need the
chart-change law for that term.  That law already existed:
`Pending.SmoothDDCForm.ddcForm` bundles `ddᶜv` of a chart-smooth real function as
a genuine `SmoothRealForm n M 2`, and its `compatible` field is exactly the law.
Hence, for the hypothesis `hv` of this theorem,
`coordinateCurrentForm q e = (β + ddᶜv).coeff e`, and
`ACTopMassComparison.acTopMass_eq_iSup_formPieceMass` writes BOTH sides of this
statement as suprema of `formPieceMass` over the SAME index type (the pole set
of a real potential is empty): `β + ddᶜv` on the left, `β` on the right.  The
proof below performs that reduction, so the `sorry` it still carries is the
supremum identity and nothing else — no presentation, no pole set, no potential
in the `EReal` sense, no admissibility bookkeeping.

What remains is the classical content, and the exhaustion step is no longer part of
it: one monotone sequence of regular-piece families absorbing every compact part of
`V_reg` is constructed in `Pending.RegularPieceExhaustion` and computes the supremum of
every smooth two-form.  Note that a family-by-family identity is FALSE — the two sums
differ on a fixed family — so the exhaustion is not optional.  What is left is the
vanishing of `∫_{V_reg}((β + ddᶜv)^k - β^k)` along such a sequence, for `dim V ≠ 0`; see
the docstring of `iSup_formPieceMass_currentForm_eq` for the exact residue. -/
theorem acTopMass_eq_backgroundMass [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    (hv : ∃ v : M → ℝ, ChartSmooth (n := n) v ∧ q.potential = fun x => (v x : EReal)) :
    acTopMass q = backgroundMass beta V := by
  obtain ⟨v, hvs, hpot⟩ := hv
  rw [ACTopMassComparison.acTopMass_eq_iSup_formPieceMass q hvs hpot,
    backgroundMass_eq_iSup_formPieceMass beta V]
  exact iSup_formPieceMass_currentForm_eq beta V q hq hvs hpot

/-- The zero potential is chart-smooth, so the zero-potential presentations of
`SubvarietyStokesMass` are covered by the Stokes interface. -/
theorem exists_chartSmooth_of_potential_eq_zero
    {beta : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (q : AdmissibleRestrictedCurrentPresentation beta alpha V epsilon)
    (hv : q.potential = fun _ => 0) :
    ∃ v : M → ℝ, ChartSmooth (n := n) v ∧ q.potential = fun x => (v x : EReal) := by
  refine ⟨fun _ => 0, fun e => contDiffOn_const, ?_⟩
  rw [hv]
  funext x
  simp

end

end SGPT.Foundations.Analysis.Pending.SubvarietyStokesMassInterfaces
