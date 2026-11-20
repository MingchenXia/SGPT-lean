import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity
import SGPT.Foundations.Analysis.Pending.ExceptionalPushforwardDensity
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

set_option autoImplicit false

/-!
# Comparing two parameter densities at one regular-patch parameter

The density clause of CT22, Lemma 4.3 compares the parameter density of the
*limit* current `θ + ε₀ω + ddᶜψ` at a smooth point of `ψ` with the densities of
a regularizing sequence `θ + εω + ddᶜψ_m`, `ε₀ < ε`.  Nothing in that comparison
needs the regularization: it needs only that, at the single chart point in
question, the coordinate `(1,1)`-form of the second current dominates that of
the first on complex lines.  This module proves exactly that, and nothing else.

The mathematical content is the determinant monotonicity
`FirstPass.MongeAmpere.actualTopPowerDensity_le_add` (for semipositive real
`(1,1)`-forms `A` and `B`, `det A ≤ det (A + B)`), transported through the
complex-linear differential of a regular parametrization.  It is stated here
once, for two arbitrary closed real `(1,1)`-forms and two arbitrary potentials,
because the same comparison is made three times in the restricted-volume chain
with different pairs.

What this buys for CT22, Lemma 4.3: its density clause
`ofReal (potentialPatchDensity (θ + ε₀ω) ψ P v) ≤ liminf_m ofReal (patchDensity (p m) P v)`
is reduced by `ofReal_potentialPatchDensity_le_liminf_of_eventually` below to the
**one-sided Hessian bound**
`ddᶜψ ≤ (ε - ε₀)ω + ddᶜψ_m` at the chart point, eventually in `m`.  That is a
statement about the regularization alone: no liminf, no measure, no density.
It is strictly weaker than local `C²` convergence, which is how the clause is
usually quoted, and it is the form a Demailly-type approximation should be asked
to supply.
-/

open Set Filter
open scoped Topology ContDiff ENNReal

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.PotentialPatchDensityComparison

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.NumericalRestrictedVolume FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.AdmissibleCurrentFormPositivity
open ExceptionalPushforwardDensity
open RestrictedMassEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The coordinate `(1,1)`-form of `a + ddᶜψ` in the chart of a regular patch,
read at the chart image of a patch parameter.  `potentialPatchDensity` is the
genuine top power of its pullback by the differential of the parametrization. -/
def potentialCoordinateForm (a : ClosedRealOneOneForm n M) (psi : M → EReal)
    (P : RegularPatch V) (v : ComplexModel V.dim) : CoordinateRealTwoForm n :=
  a.val.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization v) +
    smoothDDC (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
      (P.coordinateParametrization v)

theorem potentialPatchDensity_eq_actualTopPowerDensity
    (a : ClosedRealOneOneForm n M) (psi : M → EReal)
    (P : RegularPatch V) (v : ComplexModel V.dim) :
    potentialPatchDensity a psi P v =
      actualTopPowerDensity ((potentialCoordinateForm a psi P v).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization v)) :=
  rfl

/-- Pullback of a sum of coordinate two-forms. -/
theorem add_compContinuousLinearMap {k m : ℕ} (A B : CoordinateRealTwoForm m)
    (L : ComplexModel k →L[ℝ] ComplexModel m) :
    (A + B).compContinuousLinearMap L =
      A.compContinuousLinearMap L + B.compContinuousLinearMap L := by
  ext v
  simp

/-- **Determinant monotonicity at one patch parameter.**  If the coordinate
`(1,1)`-form of `b + ddᶜφ` is the one of `a + ddᶜψ` plus a semipositive `(1,1)`
form, the parameter density does not decrease. -/
theorem potentialPatchDensity_le_of_sub
    {a b : ClosedRealOneOneForm n M} {psi phi : M → EReal}
    (P : RegularPatch V) {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (hA1 : IsOneOne (potentialCoordinateForm a psi P v))
    (hA2 : CoefficientSemipositive (potentialCoordinateForm a psi P v))
    (hB1 : IsOneOne (potentialCoordinateForm b phi P v - potentialCoordinateForm a psi P v))
    (hB2 : CoefficientSemipositive
      (potentialCoordinateForm b phi P v - potentialCoordinateForm a psi P v)) :
    potentialPatchDensity a psi P v ≤ potentialPatchDensity b phi P v := by
  have hL := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hv
  have key := actualTopPowerDensity_le_add
    (isOneOne_compContinuousLinearMap hA1 _ hL)
    (coefficientSemipositive_compContinuousLinearMap hA2 _ hL)
    (isOneOne_compContinuousLinearMap hB1 _ hL)
    (coefficientSemipositive_compContinuousLinearMap hB2 _ hL)
  refine key.trans_eq (congrArg actualTopPowerDensity ?_)
  have hadd : potentialCoordinateForm a psi P v +
      (potentialCoordinateForm b phi P v - potentialCoordinateForm a psi P v) =
      potentialCoordinateForm b phi P v := by abel
  rw [← add_compContinuousLinearMap, hadd]
  rfl

/-- **The comparison in its usable form.**  Only a pointwise domination on
complex lines at the single chart point is needed, together with the
`(1,1)`-property of both coordinate forms and semipositivity of the smaller
one. -/
theorem potentialPatchDensity_le_of_apply_le
    {a b : ClosedRealOneOneForm n M} {psi phi : M → EReal}
    (P : RegularPatch V) {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (hA1 : IsOneOne (potentialCoordinateForm a psi P v))
    (hA2 : CoefficientSemipositive (potentialCoordinateForm a psi P v))
    (hB1 : IsOneOne (potentialCoordinateForm b phi P v))
    (hle : ∀ u : ComplexModel n,
      potentialCoordinateForm a psi P v ![u, Complex.I • u] ≤
        potentialCoordinateForm b phi P v ![u, Complex.I • u]) :
    potentialPatchDensity a psi P v ≤ potentialPatchDensity b phi P v := by
  refine potentialPatchDensity_le_of_sub P hv hA1 hA2 ?_ ?_
  · intro u w
    simp only [ContinuousAlternatingMap.sub_apply, hA1 u w, hB1 u w]
  · intro u
    simp only [ContinuousAlternatingMap.sub_apply, sub_nonneg]
    exact hle u

/-- The coordinate form of `a + ddᶜψ` is of type `(1,1)` wherever the chart
expression of `ψ` is twice differentiable. -/
theorem isOneOne_potentialCoordinateForm
    (a : ClosedRealOneOneForm n M) (psi : M → EReal)
    (P : RegularPatch V) (v : ComplexModel V.dim)
    (hz : P.coordinateParametrization v ∈
      (complexChartAt (n := n) P.center).val.target)
    (hpsi : ContDiffAt ℝ 2
      (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
      (P.coordinateParametrization v)) :
    IsOneOne (potentialCoordinateForm a psi P v) := by
  intro u w
  simp only [potentialCoordinateForm, ContinuousAlternatingMap.add_apply,
    a.2.2 _ _ hz u w, smoothDDC_isOneOne hpsi u w]

/-! ### A germ of the potential determines the coordinate form and the density -/

/-- Two potentials with the same chart germ at the chart image of a patch
parameter have the same coordinate `(1,1)`-form there.  Only the germ of the
real chart expression matters, which is what `smoothDDC` reads. -/
theorem potentialCoordinateForm_congr (a : ClosedRealOneOneForm n M)
    {psi phi : M → EReal} (P : RegularPatch V) (v : ComplexModel V.dim)
    (hgerm : (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
      =ᶠ[𝓝 (P.coordinateParametrization v)]
      fun y => (phi ((complexChartAt (n := n) P.center).val.symm y)).toReal) :
    potentialCoordinateForm a psi P v = potentialCoordinateForm a phi P v := by
  simp only [potentialCoordinateForm, smoothDDC_congr hgerm]

/-- The parameter density only depends on the germ of the potential's chart
expression at the chart image of the parameter. -/
theorem potentialPatchDensity_congr (a : ClosedRealOneOneForm n M)
    {psi phi : M → EReal} (P : RegularPatch V) (v : ComplexModel V.dim)
    (hgerm : (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
      =ᶠ[𝓝 (P.coordinateParametrization v)]
      fun y => (phi ((complexChartAt (n := n) P.center).val.symm y)).toReal) :
    potentialPatchDensity a psi P v = potentialPatchDensity a phi P v := by
  simp only [potentialPatchDensity_eq_actualTopPowerDensity,
    potentialCoordinateForm_congr a P v hgerm]

/-! ### The liminf reduction promised by CT22, Lemma 4.3, clause (ii) -/

section Liminf

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {epsilon : PositiveError}

/-- The coordinate form of an admissible presentation, read at a patch
parameter, is the `potentialCoordinateForm` of its perturbed representative and
its potential.  Definitional, and the bridge between the two spellings of the
same density. -/
theorem potentialCoordinateForm_perturbedRepresentative
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (v : ComplexModel V.dim) :
    potentialCoordinateForm (perturbedRepresentative p) p.potential P v =
      coordinateCurrentForm p (complexChartAt (n := n) P.center)
        (P.coordinateParametrization v) :=
  rfl

/-- **CT22, Lemma 4.3, clause (ii), reduced to a pointwise Hessian bound.**
The `liminf` inequality
`ofReal (potentialPatchDensity a psi P v) ≤ liminf_m ofReal (patchDensity (p m) P v)`
follows as soon as, *eventually in* `m`, the coordinate `(1,1)`-form of
`p m` dominates that of `a + ddᶜψ` on complex lines at the single chart point in
question.  No measure, no convergence and no regularization enters: the content
is the determinant monotonicity of `potentialPatchDensity_le_of_apply_le`
followed by `le_liminf_of_le`. -/
theorem ofReal_potentialPatchDensity_le_liminf_of_eventually
    {a : ClosedRealOneOneForm n M} {psi : M → EReal}
    (p : ℕ → AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (hA1 : IsOneOne (potentialCoordinateForm a psi P v))
    (hA2 : CoefficientSemipositive (potentialCoordinateForm a psi P v))
    (hB1 : ∀ᶠ m in atTop, IsOneOne
      (coordinateCurrentForm (p m) (complexChartAt (n := n) P.center)
        (P.coordinateParametrization v)))
    (hle : ∀ᶠ m in atTop, ∀ u : ComplexModel n,
      potentialCoordinateForm a psi P v ![u, Complex.I • u] ≤
        coordinateCurrentForm (p m) (complexChartAt (n := n) P.center)
          (P.coordinateParametrization v) ![u, Complex.I • u]) :
    ENNReal.ofReal (potentialPatchDensity a psi P v) ≤
      liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop := by
  refine le_liminf_of_le (by isBoundedDefault) ?_
  · filter_upwards [hB1, hle] with m hm1 hmle
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep := potentialPatchDensity_le_of_apply_le (a := a) (b := perturbedRepresentative (p m))
      (psi := psi) (phi := (p m).potential) P hv hA1 hA2
      (by rw [potentialCoordinateForm_perturbedRepresentative]; exact hm1)
      (by
        intro u
        rw [potentialCoordinateForm_perturbedRepresentative]
        exact hmle u)
    simpa [patchDensity_eq_potentialPatchDensity] using hstep

/-- The same reduction when the germ of `p m`'s potential *is* that of `psi`
eventually, and the extra positive part comes from the perturbed representative
alone.  This is the shape the collar gluing of CT22, Lemma 4.3 produces: the
glued potential coincides with `psi` near the parameter, so the two coordinate
forms differ only by the semipositive `(epsilon - epsilon_0) omega`, and the
`liminf` is attained by an eventually constant sequence. -/
theorem ofReal_potentialPatchDensity_le_liminf_of_eventually_germ
    {a : ClosedRealOneOneForm n M} {psi : M → EReal}
    (p : ℕ → AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (hz : P.coordinateParametrization v ∈
      (complexChartAt (n := n) P.center).val.target)
    (hpsi : ContDiffAt ℝ 2
      (fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
      (P.coordinateParametrization v))
    (hA2 : CoefficientSemipositive (potentialCoordinateForm a psi P v))
    (hgerm : ∀ᶠ m in atTop,
      (fun y => ((p m).potential ((complexChartAt (n := n) P.center).val.symm y)).toReal)
        =ᶠ[𝓝 (P.coordinateParametrization v)]
        fun y => (psi ((complexChartAt (n := n) P.center).val.symm y)).toReal)
    (hform : ∀ᶠ m in atTop, ∀ u : ComplexModel n,
      a.val.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization v)
          ![u, Complex.I • u] ≤
        (perturbedRepresentative (p m)).val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization v) ![u, Complex.I • u]) :
    ENNReal.ofReal (potentialPatchDensity a psi P v) ≤
      liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop := by
  refine ofReal_potentialPatchDensity_le_liminf_of_eventually p P hv
    (isOneOne_potentialCoordinateForm a psi P v hz hpsi) hA2 ?_ ?_
  · filter_upwards [hgerm] with m hm
    rw [← potentialCoordinateForm_perturbedRepresentative,
      potentialCoordinateForm_congr _ P v hm]
    exact isOneOne_potentialCoordinateForm _ psi P v hz hpsi
  · filter_upwards [hgerm, hform] with m hm hmform u
    rw [← potentialCoordinateForm_perturbedRepresentative,
      potentialCoordinateForm_congr _ P v hm]
    simp only [potentialCoordinateForm, ContinuousAlternatingMap.add_apply]
    exact add_le_add (hmform u) le_rfl

end Liminf

end SGPT.Foundations.Analysis.Pending.PotentialPatchDensityComparison
