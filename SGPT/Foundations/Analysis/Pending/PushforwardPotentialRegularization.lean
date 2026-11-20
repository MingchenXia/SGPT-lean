import SGPT.Foundations.Analysis.Pending.PushforwardPotentialRegularizationInterface

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The one remaining analytic input of CT22 Lemma 4.3: regularizing the pushforward

Everything modification-theoretic in CT22's Lemma 4.3 is now proved:
`Pending.ExceptionalPushforwardPotential` pushes the exceptionally corrected current
across the centre, and `Pending.ExceptionalPushforwardDensity` identifies the upstairs
parameter density with the downstairs one, with no loss in `ε₀`.  What is left is a
statement about a compact Kähler manifold alone, with no blowup in it:

**Demailly regularization of a quasi-plurisubharmonic potential.**  A `(θ + ε₀ω)`-PSH
potential `ψ` is approximated by potentials with smooth analytic singularities, losing at
most `δ_m → 0` of positivity and creating no new poles; for `2ε₀ ≤ ε` the approximants are
`ε`-admissible once `δ_m ≤ ε - ε₀`, and on the open set where `ψ` is smooth a regularized
maximum against `ψ` on a collar makes their densities EVENTUALLY EQUAL to the density of
`θ + ε₀ω + ddᶜψ` — whence the `liminf` clause with an eventually constant sequence
(I-0460).  The `ε`-density dominates the `ε₀`-density by monotonicity of the top power in
a semipositive summand, so no loss appears there either.

The density clause is asked only where the chart expression of `ψ` is actually smooth.
That is not a convenience: `Pending.ExceptionalPushforwardDensity.potentialPatchDensity`
is built from `smoothDDC`, which is a pointwise formula in `fderiv` and carries no
information at a point where `ψ` is not differentiable.  The consumer supplies exactly
this hypothesis, from
`Pending.ExceptionalPushforwardDensity.eventually_contDiffAt_chartFunction_pushforward`.

`hW` is not removable: an `ε`-admissible presentation along `W` must have a potential that
is not identically `-∞` on `W`, so without it the conclusion can be empty.  Each presentation
uses the project's `HasManifoldAnalyticSingularitiesSmoothOffPole` convention.  Thus this
module asserts smoothness only on the complement of the polar set; it makes no
smooth-across-poles claim.

The direct source theorem needs only the strict gap `ε₀ < ε`: the outer CT22 statement's
`2ε₀ ≤ ε` supplies it because `ε₀ > 0`.  The outer wrapper retains its bigness and
positive-dimensionality arguments to preserve the public CT22 parameter list, but neither
belongs to the regularization source boundary.
-/

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.PushforwardPotentialRegularization

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  FirstPass.NumericalRestrictedVolumeScaffold FirstPass.NumericalRestrictedVolume

noncomputable section

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **Source-interface wrapper (Demailly regularization of the pushed-down potential; CT22
Lemma 4.3, the analytic half of step 3).** For a big class `{θ}` on a compact Kähler `Y`,
a `(θ + ε₀ω)`-PSH potential `ψ` that is not identically `-∞` on `W`, and `2ε₀ ≤ ε`, there
is a sequence of `ε`-admissible presentations of `{θ}` along `W` which

* creates no pole where `ψ` has none, and
* dominates, in the `liminf` sense, the parameter density of `θ + ε₀ω + ddᶜψ` at every
  patch parameter where `ψ` is finite and its chart expression is smooth.

This is the ONLY remaining input of CT22's Lemma 4.3; it mentions no modification. -/
theorem exists_regularization_of_thetaPshPotential [CompactSpace Y]
    (theta : ClosedRealOneOneForm n Y)
    (_hbig : IsBigClass (RealBottChern.ofRepresentative theta))
    (omega : KahlerBackground n Y)
    (W : ClosedIrreducibleAnalyticSubvariety n Y) (_hdim_pos : 0 < W.dim)
    (eps0 eps : PositiveError) (heps : 2 * (eps0 : ℝ) ≤ (eps : ℝ))
    (psi : Y → EReal)
    (hpsi : IsThetaPshPotential (theta + (eps0 : ℝ) • omega.form).val psi)
    (hW : ¬ W.carrier ⊆ poleSet psi) :
    ∃ p : ℕ → AdmissibleRestrictedCurrentPresentation omega
        (RealBottChern.ofRepresentative theta) W eps,
      (∀ y ∉ poleSet psi, ∀ m, y ∉ poleSet (p m).potential) ∧
      ∀ (P : RegularPatch W) (v : ComplexModel W.dim), v ∈ P.parameterDomain →
        P.toManifold v ∉ poleSet psi →
        (∀ᶠ y in 𝓝 (P.coordinateParametrization v),
          ContDiffAt ℝ ∞
            (fun y' => (psi ((complexChartAt (n := n) P.center).val.symm y')).toReal) y) →
        ENNReal.ofReal (ExceptionalPushforwardDensity.potentialPatchDensity
            (theta + (eps0 : ℝ) • omega.form) psi P v)
          ≤ liminf (fun m => ENNReal.ofReal (patchDensity (p m) P v)) atTop :=
  by
    have hgap : (eps0 : ℝ) < (eps : ℝ) := by
      nlinarith [eps0.2]
    exact ct22Lemma43_exists_regularization_of_thetaPshPotential theta omega W eps0 eps hgap
      psi hpsi hW

end

end SGPT.Foundations.Analysis.Pending.PushforwardPotentialRegularization
