import SGPT.Foundations.Analysis.Pending.PartitionPairingCollarErrorReduction
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound

set_option autoImplicit false

/-!
# Finite regular-piece mass for a smooth positive current

The signed finite-pairing reduction needs the current-side regular-piece mass
to be finite before it may use `ENNReal.toReal`.  For a chart-smooth potential
this is not additional current-theoretic input.  Compact Kähler domination
bounds the smooth form `β + ddᶜ v` above by a fixed multiple of `β`; monotonicity
of the genuine top-power density then bounds every regular-piece mass by the
corresponding finite background mass.

This module carries out exactly that source-free reduction.  It uses neither a
finite Stokes pairing nor a limiting assertion.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ClosedCurrentMassFinitenessReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open PatchFormMass
open TopPowerDensityUpperBound

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

variable {beta : KahlerBackground n M}
  {q : AdmissibleRestrictedCurrentPresentation beta
    (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩}
  {v : M → ℝ} {hvs : ChartSmooth (n := n) v}

/-- Pointwise negation of a smooth real form.  `SmoothRealForm` deliberately
does not carry an additive typeclass, so this small bundled operation lets the
compact Kähler-domination theorem be applied to `-a`. -/
def negForm (a : SmoothRealForm n M 2) : SmoothRealForm n M 2 where
  coeff := fun e z => -a.coeff e z
  smooth := fun e => (a.smooth e).neg
  compatible := by
    intro e f z hz w
    simpa only [ContinuousAlternatingMap.neg_apply] using
      congrArg Neg.neg (a.compatible e f z hz w)

@[simp] theorem negForm_coeff (a : SmoothRealForm n M 2)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (negForm a).coeff e z = -a.coeff e z := rfl

/-- A compact Kähler background pointwise dominates the top density of the
smooth positive current attached to a real potential. -/
theorem patchFormDensity_currentForm_le_kahler_multiple [CompactSpace M]
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : RegularPatch V) {w : ComplexModel V.dim},
      w ∈ P.parameterDomain →
        patchFormDensity (ACTopMassComparison.currentForm q hvs) P w ≤
          C ^ V.dim * patchFormDensity beta.form.val P w := by
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_isSemipositive_add_smul
    (negForm (ACTopMassComparison.currentForm q hvs)) beta.form.val beta.isKahler.1
  refine ⟨C, hC, fun P w hw => ?_⟩
  let e := complexChartAt (n := n) P.center
  let L := fderiv ℝ P.coordinateParametrization w
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hpole : e.val.symm (P.coordinateParametrization w) ∉ poleSet q.potential := by
    rw [ACTopMassComparison.poleSet_eq_empty q hpot]
    simp
  obtain ⟨hcur11, hcurpos⟩ :=
    AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive q e hz hpole
  rw [ACTopMassComparison.coordinateCurrentForm_eq q hvs hpot] at hcur11 hcurpos
  obtain ⟨hcur11', hcurpos'⟩ :=
    PatchDensityTelescope.isOneOne_and_semipositive_patchCoordinateForm
      (ACTopMassComparison.currentForm q hvs) P hw hcur11 hcurpos
  have hbeta11 : IsOneOne (RegularPatchTransition.patchCoordinateForm beta.form.val P w) :=
    (PatchDensityTelescope.isOneOne_and_semipositive_patchCoordinateForm beta.form.val P hw
      (fun a b => beta.form.property.2 _ _ hz a b)
      (fun z => beta.isSemipositive _ _ hz z)).1
  have hLI : ∀ z : ComplexModel V.dim, L (Complex.I • z) = Complex.I • L z :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul
      P hw
  have hle : ∀ z : ComplexModel V.dim,
      RegularPatchTransition.patchCoordinateForm (ACTopMassComparison.currentForm q hvs) P w
          ![z, Complex.I • z] ≤
        C * RegularPatchTransition.patchCoordinateForm beta.form.val P w
          ![z, Complex.I • z] := by
    intro z
    have h := hdom e (P.coordinateParametrization w) hz (L z)
    have hcurrent :
        RegularPatchTransition.patchCoordinateForm (ACTopMassComparison.currentForm q hvs) P w
            ![z, Complex.I • z] =
          (ACTopMassComparison.currentForm q hvs).coeff e (P.coordinateParametrization w)
            ![L z, Complex.I • L z] := by
      simp only [RegularPatchTransition.patchCoordinateForm,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      ext i
      fin_cases i <;> simp [L, hLI]
    have hbackground :
        RegularPatchTransition.patchCoordinateForm beta.form.val P w ![z, Complex.I • z] =
          beta.form.val.coeff e (P.coordinateParametrization w)
            ![L z, Complex.I • L z] := by
      simp only [RegularPatchTransition.patchCoordinateForm,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      ext i
      fin_cases i <;> simp [L, hLI]
    rw [hcurrent, hbackground]
    have h' : 0 ≤
        -((ACTopMassComparison.currentForm q hvs).coeff e (P.coordinateParametrization w)
          ![L z, Complex.I • L z]) +
          C * (beta.form.val.coeff e (P.coordinateParametrization w)
            ![L z, Complex.I • L z]) := by
      simpa only [negForm_coeff, ContinuousAlternatingMap.neg_apply] using h
    linarith
  exact actualTopPowerDensity_le_pow_mul hcur11' hcurpos' hbeta11 hle

/-- The pointwise compact domination integrates over every finite regular-piece
family. -/
theorem formPieceMass_currentForm_le_kahler_multiple [CompactSpace M]
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : RegularPieceFamily V (∅ : Set M)),
      formPieceMass (ACTopMassComparison.currentForm q hvs) F ≤
        ENNReal.ofReal (C ^ V.dim) * formPieceMass beta.form.val F := by
  obtain ⟨C, hC, hdens⟩ := patchFormDensity_currentForm_le_kahler_multiple
    (q := q) (hvs := hvs) (beta := beta) hpot
  refine ⟨C, hC, fun F => ?_⟩
  unfold formPieceMass
  calc
    (∑ i, ∫⁻ w in F.piece i,
        ENNReal.ofReal (patchFormDensity (ACTopMassComparison.currentForm q hvs) (F.patch i) w))
        ≤ ∑ i, ∫⁻ w in F.piece i,
            ENNReal.ofReal (C ^ V.dim) *
              ENNReal.ofReal (patchFormDensity beta.form.val (F.patch i) w) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (F.measurableSet_piece i)] with w hw
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hdens (F.patch i) (F.piece_subset i hw))
    _ = ENNReal.ofReal (C ^ V.dim) *
          ∑ i, ∫⁻ w in F.piece i,
            ENNReal.ofReal (patchFormDensity beta.form.val (F.patch i) w) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ =>
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Every finite regular-piece mass of a smooth positive current is finite.
The only finiteness input is the already-derived background mass of `V`. -/
theorem formPieceMass_currentForm_ne_top [CompactSpace M]
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (F : RegularPieceFamily V (∅ : Set M)) :
    formPieceMass (ACTopMassComparison.currentForm q hvs) F ≠ ⊤ := by
  obtain ⟨C, _, hbound⟩ := formPieceMass_currentForm_le_kahler_multiple
    (q := q) (hvs := hvs) (beta := beta) hpot
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) (hbound F)
  have hglobal : (⨆ G : RegularPieceFamily V (∅ : Set M),
      formPieceMass beta.form.val G) ≠ ⊤ :=
    SubvarietyStokesMassInterfaces.backgroundMass_ne_top' beta V
  exact ne_top_of_le_ne_top hglobal (le_iSup (fun G : RegularPieceFamily V (∅ : Set M) =>
    formPieceMass beta.form.val G) F)

end

end SGPT.Foundations.Analysis.Pending.ClosedCurrentMassFinitenessReduction
