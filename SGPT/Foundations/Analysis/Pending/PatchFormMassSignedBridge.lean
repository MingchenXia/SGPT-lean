import SGPT.Foundations.Analysis.Pending.RegularPieceInnerRegular
import SGPT.Foundations.Analysis.Pending.PatchDensityTelescope

set_option autoImplicit false

/-!
# From the `ℝ≥0∞` piece masses to signed parameter integrals

`Pending.PatchFormMass.formPieceMass` is a finite sum of `lintegral`s of
`ENNReal.ofReal` of the parameter densities, while everything the Stokes
obligation `Pending.SubvarietyStokesMassInterfaces.iSup_formPieceMass_currentForm_eq`
has available about those densities is POINTWISE and SIGNED: the telescope identity
`Pending.PatchDensityTelescope.patchFormDensity_currentForm_sub` and the mixed
Monge--Ampère description of the defect in `Pending.PatchDensityLocalPotential`.

This module is the bridge between the two, and nothing more.  It is step (i) of the
three-step route recorded on the hgraph node of that declaration.  There is no
geometry here: given

* nonnegativity of both densities on each piece (which
  `PatchDensityTelescope.patchFormDensity_kahler_nonneg` and
  `patchFormDensity_currentForm_nonneg` supply), and
* FINITENESS of the two piece masses,

the `ENNReal` mass of a finite family is the sum of `ENNReal.ofReal` of the ordinary
Bochner integrals of the densities over the pieces
(`formPieceMass_eq_sum_ofReal_setIntegral`), each density is `IntegrableOn` its piece
(`integrableOn_patchFormDensity`), and therefore two forms whose signed defect
integrates to zero on every piece have the same piece mass
(`formPieceMass_eq_of_setIntegral_defect_eq_zero`).

The point of the last statement is the shape of its hypothesis: a vanishing SIGNED
integral over each piece separately.  That is what integration by parts against a
partition of unity produces, up to the collar error; the `ENNReal` truncation of
`ENNReal.ofReal` can no longer interfere once we are here.

Finiteness is a real hypothesis, not a technicality: `ENNReal.ofReal` sends every
negative value to `0`, so without nonnegativity the `lintegral` forgets part of the
integrand, and without finiteness the difference of two masses is meaningless.  Both
are discharged for the Stokes obligation -- nonnegativity pointwise as above, and
finiteness from `Pending.SubvarietyBackgroundMass.backgroundMass_ne_top` for the
background side.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.PatchFormMassSignedBridge

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  PatchFormMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parameter density of a smooth two-form is a.e.-strongly measurable on a
measurable parameter set inside the patch domain: it is continuous there. -/
theorem aestronglyMeasurable_patchFormDensity (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain) :
    AEStronglyMeasurable (fun w => patchFormDensity a P w) (volume.restrict S) :=
  ((RegularPatchTransition.continuousOn_actualTopPowerDensity_patchCoordinateForm
    a P).mono hsub).aestronglyMeasurable hS

/-- **A nonnegative parameter density with finite `lintegral` is integrable.**  This is
where the `ℝ≥0∞` world is left behind. -/
theorem integrableOn_patchFormDensity (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain)
    (hnn : ∀ w ∈ S, 0 ≤ patchFormDensity a P w)
    (hfin : ∫⁻ w in S, ENNReal.ofReal (patchFormDensity a P w) ≠ ⊤) :
    IntegrableOn (fun w => patchFormDensity a P w) S := by
  have hnn' : 0 ≤ᵐ[volume.restrict S] fun w => patchFormDensity a P w := by
    filter_upwards [ae_restrict_mem hS] with w hw using hnn w hw
  refine ⟨aestronglyMeasurable_patchFormDensity a P hS hsub, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal hnn').mpr (lt_top_iff_ne_top.mpr hfin)

/-- The `lintegral` over a piece is the `ENNReal.ofReal` of the Bochner integral. -/
theorem setLIntegral_eq_ofReal_setIntegral (a : SmoothRealForm n M 2) (P : RegularPatch V)
    {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S) (hsub : S ⊆ P.parameterDomain)
    (hnn : ∀ w ∈ S, 0 ≤ patchFormDensity a P w)
    (hfin : ∫⁻ w in S, ENNReal.ofReal (patchFormDensity a P w) ≠ ⊤) :
    ∫⁻ w in S, ENNReal.ofReal (patchFormDensity a P w) =
      ENNReal.ofReal (∫ w in S, patchFormDensity a P w) := by
  have hnn' : 0 ≤ᵐ[volume.restrict S] fun w => patchFormDensity a P w := by
    filter_upwards [ae_restrict_mem hS] with w hw using hnn w hw
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrableOn_patchFormDensity a P hS hsub hnn hfin) hnn').symm

variable {avoid : Set M}

/-- Each piece integral of a finite family is bounded by the family mass, hence finite
as soon as the mass is. -/
theorem setLIntegral_piece_ne_top {a : SmoothRealForm n M 2} (F : RegularPieceFamily V avoid)
    (hfin : formPieceMass a F ≠ ⊤) (i : Fin F.size) :
    ∫⁻ w in F.piece i, ENNReal.ofReal (patchFormDensity a (F.patch i) w) ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin ?_
  exact Finset.single_le_sum
    (f := fun j : Fin F.size => ∫⁻ w in F.piece j,
      ENNReal.ofReal (patchFormDensity a (F.patch j) w))
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- **The piece mass of a finite family as a sum of ordinary integrals.** -/
theorem formPieceMass_eq_sum_ofReal_setIntegral (a : SmoothRealForm n M 2)
    (F : RegularPieceFamily V avoid)
    (hnn : ∀ i, ∀ w ∈ F.piece i, 0 ≤ patchFormDensity a (F.patch i) w)
    (hfin : formPieceMass a F ≠ ⊤) :
    formPieceMass a F =
      ∑ i, ENNReal.ofReal (∫ w in F.piece i, patchFormDensity a (F.patch i) w) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact setLIntegral_eq_ofReal_setIntegral a (F.patch i) (F.measurableSet_piece i)
    (F.piece_subset i) (hnn i) (setLIntegral_piece_ne_top F hfin i)

/-- **The bridge.**  Two smooth real two-forms with nonnegative densities and finite
piece masses have the SAME piece mass as soon as the signed defect of their densities
integrates to zero over every piece.

This is the only statement of the module the Stokes obligation consumes: it turns an
identity of `ℝ≥0∞` suprema into the vanishing of finitely many ordinary integrals of a
signed function, which is what integration by parts produces. -/
theorem formPieceMass_eq_of_setIntegral_defect_eq_zero (a b : SmoothRealForm n M 2)
    (F : RegularPieceFamily V avoid)
    (hann : ∀ i, ∀ w ∈ F.piece i, 0 ≤ patchFormDensity a (F.patch i) w)
    (hbnn : ∀ i, ∀ w ∈ F.piece i, 0 ≤ patchFormDensity b (F.patch i) w)
    (hafin : formPieceMass a F ≠ ⊤) (hbfin : formPieceMass b F ≠ ⊤)
    (hdef : ∀ i, ∫ w in F.piece i,
        (patchFormDensity a (F.patch i) w - patchFormDensity b (F.patch i) w) = 0) :
    formPieceMass a F = formPieceMass b F := by
  rw [formPieceMass_eq_sum_ofReal_setIntegral a F hann hafin,
    formPieceMass_eq_sum_ofReal_setIntegral b F hbnn hbfin]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hia := integrableOn_patchFormDensity a (F.patch i) (F.measurableSet_piece i)
    (F.piece_subset i) (hann i) (setLIntegral_piece_ne_top F hafin i)
  have hib := integrableOn_patchFormDensity b (F.patch i) (F.measurableSet_piece i)
    (F.piece_subset i) (hbnn i) (setLIntegral_piece_ne_top F hbfin i)
  have hsub := integral_sub hia hib
  rw [hdef i] at hsub
  have : ∫ w in F.piece i, patchFormDensity a (F.patch i) w =
      ∫ w in F.piece i, patchFormDensity b (F.patch i) w := by linarith [hsub]
  rw [this]

end

end SGPT.Foundations.Analysis.Pending.PatchFormMassSignedBridge
