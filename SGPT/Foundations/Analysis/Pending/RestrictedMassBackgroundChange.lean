import SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence

set_option autoImplicit false

/-!
# Changing the background Kähler form of an admissible mass envelope

`Pending.RestrictedVolumeKahlerIndependence` already changes the background
Kähler form of ONE admissible presentation: for `c ω' - ω` semipositive,
`changeKahler` reads an `ε`-admissible presentation for `ω` as a
`cε`-admissible presentation for `ω'`, with `acTopMass_le_changeKahler` the
comparison of masses.  Both are sorry-free.

What CT22's Lemma 4.3 consumes is the same statement with the two errors
prescribed independently: given errors `ε, ε'` and Kähler forms `ω, ω'` with
`ε' ω' - ε ω` semipositive,
```
  E_ω(α, V, ε) ≤ E_{ω'}(α, V, ε')
```
for the admissible mass envelopes.  That is the special case `c = ε'/ε`, since
`ε'ω' - εω = ε (c ω' - ω)` and `c ε = ε'`; no new analysis is involved and none
is repeated here.

Its use is with `ω' = g^*ω - Θ_E`, the exceptional correction of
`Pending.ExceptionalMetric.exists_exceptionalMetric`: that is the first step of
the pushforward argument in `Pending.ExceptionalPushforwardMass`.  The `ω' = ω`
case is monotonicity of the envelope in the error, which is already proved in
`Pending.RestrictedVolumePositivity.restrictedMassEnvelope_mono`; it is not
restated here.
-/

open Set
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RestrictedMassBackgroundChange

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.RestrictedVolumeKahlerIndependence

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The envelope only depends on the error through its value. -/
theorem restrictedMassEnvelope_congr_error (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    {ε₁ ε₂ : PositiveError} (h : ε₁ = ε₂) :
    restrictedMassEnvelope (acTopMassData omega) alpha V ε₁ =
      restrictedMassEnvelope (acTopMassData omega) alpha V ε₂ := by
  subst h
  rfl

/-- **The admissible mass envelope is monotone under a background change.**  If
`ε' ω' - ε ω` is a semipositive `(1,1)`-form then the `ε`-envelope for the
background `ω` is at most the `ε'`-envelope for the background `ω'`. -/
theorem restrictedMassEnvelope_le_of_isSemipositive
    (omega omega' : KahlerBackground n M) (alpha : RealBottChern n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) {ε ε' : PositiveError}
    (h : ((ε' : ℝ) • omega'.form - (ε : ℝ) • omega.form).val.IsSemipositive) :
    restrictedMassEnvelope (acTopMassData omega) alpha V ε ≤
      restrictedMassEnvelope (acTopMassData omega') alpha V ε' := by
  have hεne : ((ε : ℝ)) ≠ 0 := ne_of_gt ε.2
  have hc : 0 < (ε' : ℝ) / (ε : ℝ) := div_pos ε'.2 ε.2
  have hform : ((ε : ℝ))⁻¹ • ((ε' : ℝ) • omega'.form - (ε : ℝ) • omega.form)
      = -omega.form + ((ε' : ℝ) / (ε : ℝ)) • omega'.form := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hεne, one_smul, div_eq_inv_mul]
    abel
  have hD : (-omega.form + ((ε' : ℝ) / (ε : ℝ)) • omega'.form).val.IsSemipositive := by
    have hs := KahlerDomination.isSemipositive_smul h (A := ((ε : ℝ))⁻¹)
      (inv_nonneg.mpr ε.2.le)
    rwa [hform] at hs
  have heq : (⟨(ε' : ℝ) / (ε : ℝ) * (ε : ℝ), mul_pos hc ε.2⟩ : PositiveError) = ε' := by
    apply Subtype.ext
    field_simp
  refine iSup_le fun p => ?_
  refine (acTopMass_le_changeKahler p hc hD).trans ?_
  have hle : acTopMass (changeKahler p omega' hc hD) ≤
      restrictedMassEnvelope (acTopMassData omega') alpha V
        ⟨(ε' : ℝ) / (ε : ℝ) * (ε : ℝ), mul_pos hc ε.2⟩ :=
    le_iSup (fun q : AdmissibleRestrictedCurrentPresentation omega' alpha V
      ⟨(ε' : ℝ) / (ε : ℝ) * (ε : ℝ), mul_pos hc ε.2⟩ =>
        (acTopMassData omega').topMass q) (changeKahler p omega' hc hD)
  exact hle.trans (le_of_eq (restrictedMassEnvelope_congr_error omega' alpha V heq))

end

end SGPT.Foundations.Analysis.Pending.RestrictedMassBackgroundChange
