import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
import SGPT.Foundations.Analysis.Pending.RooftopContactConcentration

set_option autoImplicit false

/-!
# Xia's inequality (2.35), below the Step-1 stack

This module holds one theorem, Xia's (2.35) in the general form that takes the
envelope-concentration statement as a hypothesis.  It was written in
`Pending.DominationPrincipleContactChain` for the chain of
`xia-sgpt:page-0088`, and its statement is unchanged here; only its home moved,
together with its namespace, so the declaration's full name is the same as
before.

**Why it moved.**  The source runs this same computation twice: on
`xia-sgpt:page-0088` for Theorem 2.4.5, and on `xia-sgpt:page-0085` inside the
proof of Lemma 2.4.4 itself (Step 1.3).  The second consumer,
`Pending.ThetaPshTruncatedAffineLimitMassChain`, sits *below*
`Pending.ConvexCombEnvelopeMass`, whereas `DominationPrincipleContactChain` sits
above it; so the shared lemma cannot live in the latter without making the
import graph circular.  This module imports only what the proof needs:
multilinearity through `Pending.NonPluripolarConvexCombLower` and Lemma 2.4.2
through `Pending.RooftopContactConcentration`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
open SGPT.Foundations.Analysis.Pending.RooftopContactConcentration
open SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, SGPT, inequality (2.35) (`xia-sgpt:page-0085`), in its general
form.**  Let `p ≤ u` be `theta`-PSH potentials, `a > 1`, and let `eta` be any
`theta`-PSH potential whose barrier `gamma := a⁻¹ eta + (1 - a⁻¹) u` lies below
`p`.  If the non-pluripolar measure of `eta` gives no mass to the set where
`eta` stays strictly below the obstacle `a p + (1 - a) u`, then

  `a^{-n} theta^n_eta ≤ 1_{D} theta^n_p`,   `D = {gamma = p}`.

The hypothesis `hconc` is Xia's Theorem 2.4.4 for that obstacle; everything
else is proved here from the multilinearity bound of
`Pending.NonPluripolarConvexCombLower` and Lemma 2.4.2 in the form
`RooftopContactConcentration.measure_le_of_subset_contact`.

Xia uses this twice with different data: on `xia-sgpt:page-0085` inside the
proof of Lemma 2.4.4 (with `p = varphi ∨ (phi - k)` and `eta = eta_k`), consumed
by `Pending.ThetaPshTruncatedAffineLimitMassChain`, and on `xia-sgpt:page-0088`
inside the proof of Theorem 2.4.5, consumed by
`Pending.DominationPrincipleContactChain`.  The contact set is identified with `{eta ≥ a p + (1 - a) u}`
through `le_convexCombValue_of_convexCombValue_le`, so no quasi-everywhere
statement about the envelope is needed. -/
theorem ofReal_pow_smul_measure_le_contact
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {p u eta : M → EReal}
    (hp : IsThetaPshPotential theta.val p)
    (hu : IsThetaPshPotential theta.val u)
    (heta : IsThetaPshPotential theta.val eta)
    {a : ℝ} (ha : 1 < a) (hpu : p ≤ u)
    (hbar : convexComb a⁻¹ eta u ≤ p)
    (hconc : diagonalPotentialMeasure theta eta heta
      {x | eta x < convexComb a p u x} = 0)
    (B : Set M) :
    ENNReal.ofReal (a⁻¹ ^ n) * diagonalPotentialMeasure theta eta heta B ≤
      diagonalPotentialMeasure theta p hp
        (B ∩ {x | convexComb a⁻¹ eta u x = p x}) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have heps1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hutop : ∀ x, u x ≠ ⊤ := fun x => hu.1.quasiPlurisubharmonic.ne_top x
  have hetatop : ∀ x, eta x ≠ ⊤ := fun x => heta.1.quasiPlurisubharmonic.ne_top x
  set S : Set M := {x : M | ¬ eta x < convexComb a p u x} with hSdef
  have hScompl : Sᶜ = {x : M | eta x < convexComb a p u x} := by
    ext x
    simp [hSdef]
  have hSD : ∀ x ∈ S, convexComb a⁻¹ eta u x = p x := fun x hx =>
    le_antisymm (hbar x)
      (le_convexCombValue_of_convexCombValue_le ha (hpu x) (hutop x) (hetatop x)
        (not_lt.mp hx))
  have hgpsh : IsThetaPshPotential theta.val (convexComb a⁻¹ eta u) :=
    isThetaPshPotential_convexComb heta hu heps0 heps1
  calc ENNReal.ofReal (a⁻¹ ^ n) * diagonalPotentialMeasure theta eta heta B
      ≤ ENNReal.ofReal (a⁻¹ ^ n) *
          (diagonalPotentialMeasure theta eta heta (B ∩ S) +
            diagonalPotentialMeasure theta eta heta Sᶜ) := by
        have hstep : diagonalPotentialMeasure theta eta heta B ≤
            diagonalPotentialMeasure theta eta heta (B ∩ S) +
              diagonalPotentialMeasure theta eta heta Sᶜ := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro x hx
          by_cases hxS : x ∈ S
          · exact Or.inl ⟨hx, hxS⟩
          · exact Or.inr hxS
        gcongr
    _ = ENNReal.ofReal (a⁻¹ ^ n) *
          diagonalPotentialMeasure theta eta heta (B ∩ S) := by
        rw [hScompl, hconc, add_zero]
    _ ≤ diagonalPotentialMeasure theta (convexComb a⁻¹ eta u) hgpsh (B ∩ S) :=
        ofReal_pow_smul_diagonalPotentialMeasure_le_convexComb theta heta hu
          heps0 heps1 hgpsh (B ∩ S)
    _ ≤ diagonalPotentialMeasure theta p hp (B ∩ S) :=
        measure_le_of_subset_contact omega theta hgpsh hp hbar _
          fun x hx => hSD x hx.2
    _ ≤ diagonalPotentialMeasure theta p hp
          (B ∩ {x : M | convexComb a⁻¹ eta u x = p x}) :=
        measure_mono fun x hx => ⟨hx.1, hSD x hx.2⟩

end

end SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChain
