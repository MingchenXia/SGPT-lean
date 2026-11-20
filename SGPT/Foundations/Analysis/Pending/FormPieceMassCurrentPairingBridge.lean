import SGPT.Foundations.Analysis.Pending.RegularPieceGoodExhaustion

set_option autoImplicit false

/-!
# From local telescope potentials to finite regular-piece mass identities

`RegularPieceGoodExhaustion.HasLocalTelescopePotential` already puts the
density defect on every member of a good finite family into the coordinate
mixed-Hessian form.  This file packages the local potentials selected for a
finite family and rewrites each signed defect integral as the finite sum of
its mixed-Hessian integrals.  Thus it supplies the exact finite input expected
by the separate `PatchFormMassSignedBridge` reduction from signed integral
vanishing to equality of `formPieceMass` values.

No integration current is constructed here.  In particular, the scalar
`RegularLocusClosednessReduction.ScalarStokes` pairing is still a pairing
against the abstract regular-locus parameter measure, whereas `formPieceMass`
uses Lebesgue measure in the parameters of arbitrary regular patches.  The
missing geometric bridge is therefore a form-valued pairing/area-formula
identification, not a global mass equality or a common-limit assumption.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.FormPieceMassCurrentPairingBridge

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open RegularPieceGoodExhaustion

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- Local potential data selected for every member of one finite regular-piece
family.  The final field is the pointwise Stokes telescope identity on the
chosen neighbourhood. -/
structure FormPieceTelescopeData
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    {avoid : Set M} (F : RegularPieceFamily V avoid) where
  omega : Fin F.size → Set (ComplexModel V.dim)
  potential : Fin F.size → ComplexModel V.dim → ℝ
  piece_subset : ∀ i, F.piece i ⊆ omega i
  omega_open : ∀ i, IsOpen (omega i)
  omega_subset_domain : ∀ i, omega i ⊆ (F.patch i).parameterDomain
  potential_smooth : ∀ i, ContDiffOn ℝ ∞ (potential i) (omega i)
  restricted_potential_smooth : ∀ i,
    ContDiffOn ℝ ∞ (fun y => v ((F.patch i).toManifold y)) (omega i)
  density_telescope : ∀ i w, w ∈ omega i →
    PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w -
        PatchFormMass.patchFormDensity beta.form.val (F.patch i) w =
      ∑ j : Fin V.dim, MixedMongeAmpere.mixedDensity
        (PatchDensityLocalPotential.telescopeFunctions (potential i)
          (fun y => v ((F.patch i).toManifold y)) j) w

namespace FormPieceTelescopeData

variable {beta : KahlerBackground n M}
  {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}
  {avoid : Set M} {F : RegularPieceFamily V avoid}

/-- A good family supplies one telescope-potential datum for every one of its
finitely many pieces. -/
noncomputable def of_localTelescopePotential
    (hgood : ∀ i, HasLocalTelescopePotential q hvs (F.patch i) (F.piece i)) :
    FormPieceTelescopeData beta q hvs F := by
  choose omega potential hpiece hopen hsub hpotential hrestricted hdensity using hgood
  exact
    { omega := omega
      potential := potential
      piece_subset := hpiece
      omega_open := hopen
      omega_subset_domain := hsub
      potential_smooth := hpotential
      restricted_potential_smooth := hrestricted
      density_telescope := hdensity }

/-- The signed telescope integrand selected for one piece. -/
def telescopeIntegrand (D : FormPieceTelescopeData beta q hvs F) (i : Fin F.size) :
    ComplexModel V.dim → ℝ :=
  fun w => ∑ j : Fin V.dim, MixedMongeAmpere.mixedDensity
    (PatchDensityLocalPotential.telescopeFunctions (D.potential i)
      (fun y => v ((F.patch i).toManifold y)) j) w

/-- The finite regular-piece mass with every current density replaced by its
local background-plus-telescope expression.  This remains in `ℝ≥0∞`, so no
finiteness or sign condition is needed for the identity below. -/
def telescopeMass (D : FormPieceTelescopeData beta q hvs F) : ℝ≥0∞ :=
  ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal
    (PatchFormMass.patchFormDensity beta.form.val (F.patch i) w + D.telescopeIntegrand i w)

/-- On the actual parameter piece, the signed density defect is exactly the
selected telescope integrand. -/
theorem density_defect_eq_telescopeIntegrand
    (D : FormPieceTelescopeData beta q hvs F) (i : Fin F.size)
    {w : ComplexModel V.dim} (hw : w ∈ F.piece i) :
    PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w -
        PatchFormMass.patchFormDensity beta.form.val (F.patch i) w =
      D.telescopeIntegrand i w := by
  exact D.density_telescope i w (D.piece_subset i hw)

/-- The `formPieceMass` of the current is exactly the finite sum obtained by
replacing each local density with the background density plus its selected
mixed-Hessian telescope.  This is the direct `formPieceMass` bridge; it has no
global supremum or limiting assertion. -/
theorem formPieceMass_current_eq_telescopeMass
    (D : FormPieceTelescopeData beta q hvs F) :
    PatchFormMass.formPieceMass (ACTopMassComparison.currentForm q hvs) F = D.telescopeMass := by
  unfold PatchFormMass.formPieceMass telescopeMass
  refine Finset.sum_congr rfl fun i _ => ?_
  apply setLIntegral_congr_fun (F.measurableSet_piece i)
  intro w hw
  have h := D.density_defect_eq_telescopeIntegrand i hw
  have hreal :
      PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w =
        PatchFormMass.patchFormDensity beta.form.val (F.patch i) w + D.telescopeIntegrand i w := by
    linarith
  exact congrArg ENNReal.ofReal hreal

/-- The signed integral of the density defect on one regular piece reduces to
the finite sum of mixed-Hessian telescope integrals.  Integrability is exactly
the remaining analytic datum at this finite stage. -/
theorem setIntegral_density_defect_eq_telescopeSum
    (D : FormPieceTelescopeData beta q hvs F) (i : Fin F.size)
    (hintegrable : ∀ j : Fin V.dim,
      IntegrableOn (fun w => MixedMongeAmpere.mixedDensity
        (PatchDensityLocalPotential.telescopeFunctions (D.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) w) (F.piece i)) :
    ∫ w in F.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (F.patch i) w) =
      ∑ j : Fin V.dim, ∫ w in F.piece i, MixedMongeAmpere.mixedDensity
        (PatchDensityLocalPotential.telescopeFunctions (D.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) w := by
  calc
    ∫ w in F.piece i,
        (PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w -
          PatchFormMass.patchFormDensity beta.form.val (F.patch i) w) =
        ∫ w in F.piece i, D.telescopeIntegrand i w := by
          apply setIntegral_congr_fun (F.measurableSet_piece i)
          intro w hw
          exact D.density_defect_eq_telescopeIntegrand i hw
    _ = ∑ j : Fin V.dim, ∫ w in F.piece i, MixedMongeAmpere.mixedDensity
        (PatchDensityLocalPotential.telescopeFunctions (D.potential i)
          (fun y => v ((F.patch i).toManifold y)) j) w := by
          unfold telescopeIntegrand
          exact integral_finsetSum Finset.univ (fun j _ => hintegrable j)

end FormPieceTelescopeData

end

end SGPT.Foundations.Analysis.Pending.FormPieceMassCurrentPairingBridge
