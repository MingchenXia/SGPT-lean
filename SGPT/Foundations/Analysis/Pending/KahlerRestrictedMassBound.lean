import SGPT.Foundations.Analysis.Pending.KahlerMassTruncation

set_option autoImplicit false

/-!
# Restricted masses of a Kähler form are bounded

Source: CT22, Lemma 2.1 (`ct22-restricted-volumes:finite`), the special case of a
Kähler class and error `1`; Boucksom, *On the volume of a line bundle*,
Proposition 2.6 (non-pluripolar masses in a fixed class are bounded by the
cohomological mass); blueprint `ana:kahler-restricted-mass-bound`.

Let `(X, β)` be compact Kähler and `V ⊆ X` an irreducible analytic subvariety of
dimension `k`.  For every `β`-psh function `u` with analytic singularities whose
poles do not contain `V`,
`∫_{V_reg \ P(u)} ((β + ddᶜu)|_{V_reg})^k ≤ ∫_{V_reg} β^k < ∞`.

In the first-pass encoding such a `u` is exactly the potential of an admissible
presentation of the zero class at error `1` for the background `β` with the zero
representative (`θ + 1·β = β`), and the left-hand side is its `acTopMass`.

**Proof.**  The smooth truncations `u_j = -j + P(u + j)` are smooth `β`-psh
functions equal to `u` near `{u > -j + 1}`; by monotone convergence the mass of `u`
is at most the supremum of the masses of the `u_j`
(`KahlerMassTruncation.acTopMass_le_iSup_truncPresentation`).  Each of those equals
`∫_{V_reg} β^k` by Stokes against the closed current `[V]`, which is finite by
Lelong; these two smooth statements are the remaining named inputs
`SubvarietyStokesMass.acTopMass_eq_of_smooth` and
`SubvarietyStokesMass.acTopMass_ne_top_of_zero_potential`.

Unlike CT22's own proof of Lemma 2.1, this uses neither Demailly regularization
nor Boucksom's bound on Lelong numbers in a class: those are needed there only
because the class and the lower bound `-Aω` vary.
`Pending.RestrictedMassFiniteness.exists_acTopMass_le` (CT22, Lemma 2.1 in full)
is PROVED from this statement by fixing a representative of the class, moving
the smooth `ddᶜ`-difference of representatives into the potential, and dominating
`θ + εω` by a multiple of `ω`.
-/

open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.KahlerRestrictedMassBound

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Kähler restricted mass bound** (CT22, Lemma 2.1 for a Kähler class at error `1`).
PROVED by smooth truncation (`KahlerMassTruncation`) from Stokes against `[V]` and
Lelong's finiteness for smooth potentials (`SubvarietyStokesMass`).  On a compact complex manifold with a Kähler form `β`, the
restricted absolutely continuous top masses `∫_{V_reg \ P(u)} (β + ddᶜu)^{dim V}`
of the `β`-psh potentials `u` with smooth analytic singularities not identically
singular along `V` are uniformly bounded. -/
theorem exists_acTopMass_le_of_zero_representative [CompactSpace M]
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ q : AdmissibleRestrictedCurrentPresentation beta
          (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩,
        q.representative = 0 → acTopMass q ≤ C :=
  KahlerMassTruncation.exists_acTopMass_le_of_zero_representative_of_stokes beta V

end

end SGPT.Foundations.Analysis.Pending.KahlerRestrictedMassBound
