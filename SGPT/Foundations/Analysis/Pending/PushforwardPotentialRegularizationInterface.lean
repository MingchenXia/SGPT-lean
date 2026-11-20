import SGPT.Foundations.Analysis.Pending.PushforwardPotentialCollarConstruction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Regularization of a pushed-down potential: source boundary

This file isolates the analytic Step 3 in Collins--Tosatti 2022 (CT22), Lemma
4.3: after the current has been pushed across the exceptional centre, Demailly
regularization produces admissible analytic-singularity presentations whose
densities recover the smooth-locus density of the original potential.  The
regularization input is Demailly, *Regularization of closed positive currents
and intersection theory*, J. Algebraic Geom. 1 (1992), Theorem 1.1.  This
step only regularizes an almost-positive current: it needs neither the
bigness of `{θ}` nor positive dimension of `W`, and only the strict error gap
`ε₀ < ε`.

The project proves all modification geometry, pole transport, density
identification, and the Fatou passage in
`Pending.ExceptionalPushforwardFatouReduction`.

**No longer a boundary.**  The theorem below is now PROVED, by the collar
construction of `Pending.PushforwardPotentialCollarConstruction`, from the single
classical input `bou02-volume:2.6` (Demailly 1992), stated as
`Pending.DemaillyAlgebraicApproximation.exists_algebraicApproximation`.  The
statement is unchanged; only the `sorry` is gone.  Wiring it in this way was the
human's decision of 30 Sep (I-0598, item 3).
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

/-- **CT22, Lemma 4.3, Step 3**, proved by the collar construction of
`Pending.PushforwardPotentialCollarConstruction` from Demailly's approximation with
algebraic singularities (`bou02-volume:2.6`) as the only named classical input. -/
theorem ct22Lemma43_exists_regularization_of_thetaPshPotential [CompactSpace Y]
    (theta : ClosedRealOneOneForm n Y)
    (omega : KahlerBackground n Y)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (eps0 eps : PositiveError) (hgap : (eps0 : ℝ) < (eps : ℝ))
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
  PushforwardPotentialCollarConstruction.exists_regularization_of_thetaPshPotential
    theta omega W eps0 eps hgap psi hpsi hW

end

end SGPT.Foundations.Analysis.Pending.PushforwardPotentialRegularization
