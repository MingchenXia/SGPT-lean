import SGPT.Foundations.Analysis.Pending.ChoquetRegularization
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false

/-!
# Xia's (2.20) as a reduction: `P_θ(f) ≤ f` quasi-everywhere

Xia, SGPT, (2.20) (`xia-sgpt:page-0078`) and the blueprint node
`ana:rooftop-obstacle-bound`: if `P_θ(f)` is a genuine `θ`-PSH potential then
`P_θ(f) ≤ f` quasi-everywhere.

Its converse half is already true by construction here: `rooftopCompetitors` is
defined with `u ≤ f` *quasi-everywhere*, so a `θ`-PSH competitor which is below
`f` quasi-everywhere is below `P_θ(f)` everywhere
(`FirstPass.le_rooftopEnvelope`).  Nothing in this module is needed for that.

## What this module is, and what it is not

It is a **reduction with no `sorry`**.  The two classical facts the argument
needs are taken as explicit *predicate hypotheses*, not as named interfaces:

* `CountablyStablePluripolar` — a countable union of locally pluripolar subsets
  of `M` is locally pluripolar.  The workspace has only finite unions
  (`Pending.manifoldLocallyPluripolar_union`).
* `NegligibleSetsPluripolar` — for a sequence of `θ`-PSH potentials bounded
  above by one real constant, the set where the upper-semicontinuous
  regularization of the supremum exceeds the raw supremum is locally
  pluripolar.  The workspace has the *Lebesgue-null* version of exactly this
  statement, proved: `Pending.AeRegularizedSupremum.ae_uscRegularization_sSup_eq_on_ball`
  (Xia, Proposition 1.2.5).  Upgrading "null" to "pluripolar" is the
  Bedford--Taylor negligible-sets theorem, which this workspace has
  deliberately avoided so far.

These are precisely the two inputs the human decision requested in inbox item
`I-0510`.  The workspace's normal route for an unreachable input is a named
interface carrying an explicit `sorry`; that route is exactly what `I-0510`
gates, so it is *deliberately not taken here*, and predicate hypotheses are used
instead.  That is a flagged deviation, recorded in this docstring and in the
round's inbox item, not a licence: the standing protection `I-0569` offers the
predicate-hypothesis form as a **circularity detector**, not as permission to
bypass the interface rule.  What it does buy is the detector's verdict: the
reduction below is proved and `#print axioms` on it reports no `sorryAx`, so the
route is not circular, and a single instantiation discharges the whole lemma
once the two facts exist.

Consequently this module has **no consumer today** and changes no route.  It is
a conditional statement, not a proved producer of `ana:rooftop-obstacle-bound`.

## The argument

Choquet's lemma (`Pending.exists_seq_uscRegularization_iSup_eq`; `M` is second
countable) replaces the uncountable competitor family by a *sequence* `(s_k)`
with the same regularized supremum, which is the only reason a countable
stability statement suffices.  Each `s_k` lies below `f` quasi-everywhere, so
by countable stability `⨆_k s_k ≤ f` quasi-everywhere; and every `s_k` lies
below `P_θ(f)`, which is upper semicontinuous and never `+∞`, hence bounded
above by one real constant on the compact `M`, which is the uniform bound the
negligibility hypothesis consumes.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Countable stability of local pluripolarity**, as an explicit predicate.
`Pending.manifoldLocallyPluripolar_union` is the binary case. -/
def CountablyStablePluripolar (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] : Prop :=
  ∀ S : ℕ → Set M, (∀ j, ManifoldLocallyPluripolar (n := n) (S j)) →
    ManifoldLocallyPluripolar (n := n) (⋃ j, S j)

/-- **Negligible sets are pluripolar**, as an explicit predicate, for a
sequence of `θ`-PSH potentials below one real level.  The Lebesgue-null form of
the same statement is proved in `Pending.AeRegularizedSupremum`. -/
def NegligibleSetsPluripolar (theta : SmoothRealForm n M 2) : Prop :=
  ∀ (u : ℕ → M → EReal) (C : ℝ), (∀ j, IsThetaPshPotential theta (u j)) →
    (∀ j x, u j x ≤ (C : EReal)) →
      QuasiEverywhere (n := n)
        (fun x => uscRegularization (⨆ j, u j) x ≤ (⨆ j, u j) x)

/-- Countable stability is exactly what makes a countable family of
quasi-everywhere statements a single one. -/
theorem quasiEverywhere_forall (hcount : CountablyStablePluripolar n M)
    {P : ℕ → M → Prop} (hP : ∀ j, QuasiEverywhere (n := n) (P j)) :
    QuasiEverywhere (n := n) (fun x => ∀ j, P j x) := by
  refine ManifoldLocallyPluripolar.mono (hcount (fun j => {x | ¬ P j x}) hP) ?_
  intro x hx
  obtain ⟨j, hj⟩ := not_forall.mp hx
  exact mem_iUnion.mpr ⟨j, hj⟩

variable [CompactSpace M] [Nonempty M]

omit [CompactSpace M] in
/-- A genuine rooftop envelope has a nonempty competitor family: an empty one
makes the envelope identically `⊥`, which is not locally nondegenerate. -/
theorem nonempty_rooftopCompetitors {theta : SmoothRealForm n M 2} {f : M → EReal}
    (hP : IsThetaPshPotential theta (rooftopEnvelope theta f)) :
    (rooftopCompetitors theta f).Nonempty := by
  rcases eq_empty_or_nonempty (rooftopCompetitors theta f) with h | h
  · exfalso
    have hbot : rooftopEnvelope theta f = ⊥ := rooftopEnvelope_of_empty h
    obtain ⟨y, -, hy⟩ := hP.2 (Classical.arbitrary M) univ isOpen_univ (mem_univ _)
    exact hy (by rw [hbot]; rfl)
  · exact h

/-- **Xia, SGPT, (2.20)** (`xia-sgpt:page-0078`), blueprint node
`ana:rooftop-obstacle-bound`, as a reduction to its two classical inputs.

No `sorry` is introduced: the two inputs are hypotheses, and everything between
them and the conclusion is proved here. -/
theorem rooftopEnvelope_le_quasiEverywhere
    (hcount : CountablyStablePluripolar n M)
    {theta : SmoothRealForm n M 2} (hneg : NegligibleSetsPluripolar theta)
    {f : M → EReal}
    (hP : IsThetaPshPotential theta (rooftopEnvelope theta f)) :
    QuasiEverywhere (n := n) (fun x => rooftopEnvelope theta f x ≤ f x) := by
  classical
  obtain ⟨A, hA⟩ := exists_real_upper_bound_of_upperSemicontinuous
    (upperSemicontinuous_rooftopEnvelope theta f)
    (fun x => hP.1.quasiPlurisubharmonic.ne_top x)
  obtain ⟨s, hsF, hs⟩ :=
    exists_seq_uscRegularization_iSup_eq (nonempty_rooftopCompetitors hP)
  have hsenv : ∀ k, s k ≤ rooftopEnvelope theta f := fun k =>
    le_rooftopEnvelope (hsF k).1 (hsF k).2
  have hsA : ∀ k x, s k x ≤ (A : EReal) := fun k x => (hsenv k x).trans (hA x)
  have hreg : uscRegularization (⨆ k, s k) = rooftopEnvelope theta f := hs
  have hQneg := hneg s A (fun k => (hsF k).1) hsA
  have hQle : QuasiEverywhere (n := n) (fun x => ∀ k, s k x ≤ f x) :=
    quasiEverywhere_forall hcount (fun k => (hsF k).2)
  refine (quasiEverywhere_and hQneg hQle).mono ?_
  intro x hx
  have h1 : rooftopEnvelope theta f x ≤ (⨆ k, s k) x := by
    rw [← hreg]; exact hx.1
  refine h1.trans ?_
  simpa only [iSup_apply] using iSup_le (fun k => hx.2 k)

end

end SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere
