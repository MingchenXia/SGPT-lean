import SGPT.Foundations.Analysis.Pending.RestrictedVolumePositivity
import SGPT.Foundations.Analysis.Pending.NonNefLocusKahlerIndependence
import SGPT.Foundations.Analysis.Pending.KahlerDomination

set_option autoImplicit false

/-!
# Restricted volumes do not depend on the Kähler form

Source: CT22, Section 2 ("it is also not hard to see that it is independent of the
choice of `ω`"); Copy-4, `eq:def-restricted-volume`; blueprint
`ana:locus-properties`.

On a compact manifold, for Kähler forms `ω, ω'` pick `c > 0` with `cω' - ω ≥ 0`.
An `ε`-admissible presentation for `ω` is a `cε`-admissible presentation for `ω'`
(same representative and potential, since `θ + cεω' = (θ + εω) + ε(cω' - ω)`),
and on every regular patch off the poles the restricted form grows by the
semipositive `(1,1)`-form `ε(cω' - ω)|_V`, so its top-power density grows.  Hence
`env_ω(ε) ≤ env_{ω'}(cε)`, so `⟨α^k⟩_{ω} ≤ ⟨α^k⟩_{ω'}`, and by symmetry equality.
The non-nef locus is independent of the Kähler form
(`NonNefLocusKahlerIndependence`).  Everything here is sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere FirstPass.NonKahlerLocus RestrictedMassEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega omega' : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- An `ε`-admissible presentation for `ω` is `cε`-admissible for `ω'` when
`cω' - ω` is semipositive. -/
def changeKahler {ε : PositiveError} (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    (omega' : KahlerBackground n M) {c : ℝ} (hc : 0 < c)
    (hD : (-omega.form + c • omega'.form).val.IsSemipositive) :
    AdmissibleRestrictedCurrentPresentation omega' alpha V ⟨c * ε, mul_pos hc ε.2⟩ where
  representative := p.representative
  represents := p.represents
  potential := p.potential
  potential_psh := by
    have hsemi : ((ε : ℝ) • (-omega.form + c • omega'.form)).val.IsSemipositive := by
      intro e z hz v
      rw [ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      exact mul_nonneg ε.2.le (hD e z hz v)
    have hsum := LocalPotentials.isThetaPshPotential_add_of_semipositive p.potential_psh hsemi
    have hform : p.representative + (ε : ℝ) • omega.form +
        (ε : ℝ) • (-omega.form + c • omega'.form) =
        p.representative + (c * ε : ℝ) • omega'.form := by
      rw [smul_add, smul_neg, smul_smul, mul_comm]
      abel
    rwa [hform] at hsum
  smoothAnalyticSingularities := p.smoothAnalyticSingularities
  not_carrier_subset_poleSet := p.not_carrier_subset_poleSet

theorem coordinateCurrentForm_changeKahler {ε : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    {c : ℝ} (hc : 0 < c) (hD : (-omega.form + c • omega'.form).val.IsSemipositive)
    (e : ComplexChart n M) (z : ComplexModel n) :
    coordinateCurrentForm (changeKahler p omega' hc hD) e z =
      coordinateCurrentForm p e z +
        (ε : ℝ) • (-omega.form + c • omega'.form).val.coeff e z := by
  simp only [coordinateCurrentForm, perturbedRepresentative, changeKahler,
    ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ClosedRealOneOneForm.coeff_neg]
  ext v
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.neg_apply, smul_eq_mul]
  ring

/-- Changing the Kähler form does not decrease the restricted mass. -/
theorem acTopMass_le_changeKahler {ε : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V ε)
    {c : ℝ} (hc : 0 < c) (hD : (-omega.form + c • omega'.form).val.IsSemipositive) :
    acTopMass p ≤ acTopMass (changeKahler p omega' hc hD) := by
  refine iSup_le fun F => le_trans ?_ (le_iSup _ F)
  refine Finset.sum_le_sum fun i _ => lintegral_mono_ae ?_
  refine (ae_restrict_iff' (F.measurableSet_piece i)).mpr (Eventually.of_forall ?_)
  intro w hw
  apply ENNReal.ofReal_le_ofReal
  set P := F.patch i
  set e := complexChartAt (n := n) P.center
  set L := fderiv ℝ P.coordinateParametrization w
  have hdom : w ∈ P.parameterDomain := F.piece_subset i hw
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hdom)
  have hpole : e.val.symm (P.coordinateParametrization w) ∉ poleSet p.potential := by
    intro hmem
    exact Set.disjoint_left.mp (F.image_disjoint_avoid i) ⟨w, hw, rfl⟩ hmem
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hdom
  obtain ⟨hA1, hA2⟩ := coordinateCurrentForm_isOneOne_and_semipositive p e hz hpole
  have hB1 : IsOneOne ((ε : ℝ) • (-omega.form + c • omega'.form).val.coeff e
      (P.coordinateParametrization w)) := by
    intro a b
    simp only [ContinuousAlternatingMap.smul_apply,
      (-omega.form + c • omega'.form).2.2 e _ hz a b]
  have hB2 : CoefficientSemipositive ((ε : ℝ) • (-omega.form + c • omega'.form).val.coeff e
      (P.coordinateParametrization w)) := by
    intro v
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    exact mul_nonneg ε.2.le (hD e _ hz v)
  have key := actualTopPowerDensity_le_add (isOneOne_compContinuousLinearMap hA1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hA2 L hL)
    (isOneOne_compContinuousLinearMap hB1 L hL)
    (coefficientSemipositive_compContinuousLinearMap hB2 L hL)
  simp only [patchDensity]
  rw [coordinateCurrentForm_changeKahler p hc hD]
  convert key using 2
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.add_apply, e, L]

/-- **One direction of Kähler independence.** -/
theorem numericalRestrictedVolume_le_of_kahler [CompactSpace M]
    (omega omega' : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    numericalRestrictedVolume omega alpha V ≤ numericalRestrictedVolume omega' alpha V := by
  by_cases hV : V.carrier ⊆ nonNefLocus omega alpha
  · rw [numericalRestrictedVolume_eq_zero_of_subset_nonNefLocus omega alpha V hV]
    exact zero_le
  have hV' : ¬ V.carrier ⊆ nonNefLocus omega' alpha := by
    rwa [← NonNefLocusKahlerIndependence.nonNefLocus_kahler_independent omega omega' alpha]
  obtain ⟨c, hc, hD⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omega' (-omega.form)
  rw [RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega alpha V hV,
    RestrictedVolumePositivity.numericalRestrictedVolume_eq_iInf omega' alpha V hV']
  refine le_iInf fun ε' => ?_
  set ε : PositiveError := ⟨c⁻¹ * ε', mul_pos (inv_pos.mpr hc) ε'.2⟩ with hε
  refine (iInf_le _ ε).trans ?_
  refine iSup_le fun p => ?_
  have heq : (⟨c * ε, mul_pos hc ε.2⟩ : PositiveError) = ε' := by
    apply Subtype.ext
    simp only [hε]
    field_simp
  refine (acTopMass_le_changeKahler p hc hD).trans ?_
  rw [← heq]
  exact le_iSup (fun q : AdmissibleRestrictedCurrentPresentation omega' alpha V _ =>
    (acTopMassData omega').topMass q) (changeKahler p omega' hc hD)

/-- **Restricted volumes do not depend on the Kähler form.** -/
theorem numericalRestrictedVolume_kahler_independent [CompactSpace M]
    (omega omega' : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    numericalRestrictedVolume omega alpha V = numericalRestrictedVolume omega' alpha V :=
  (numericalRestrictedVolume_le_of_kahler omega omega' alpha V).antisymm
    (numericalRestrictedVolume_le_of_kahler omega' omega alpha V)

end

end SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence
