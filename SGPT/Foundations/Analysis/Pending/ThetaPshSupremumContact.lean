import SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact
import SGPT.Foundations.Analysis.FirstPass.Envelopes

set_option autoImplicit false

/-!
# Xia's Corollary 2.4.4 for `V_theta`, from Lemma 2.4.3

Xia, SGPT, Corollary 2.4.4 (`xia-sgpt:page-0094`), "in particular" clause:
`theta^n_{V_theta} = 1_{V_theta = 0} theta^n`.  Since `V_theta <= 0`, the
clause says exactly that the non-pluripolar Monge--Ampère measure of the
canonical reference gives no mass to `{V_theta < 0}`.

`V_theta = thetaPshSupremum theta` is by definition the largest `theta`-PSH
potential below the obstacle `f = 0`.  That obstacle is **continuous**, hence
lower semicontinuous, so Xia's Lemma 2.4.3 --- proved in
`Pending.PolydiskPatchBalayageContact.diagonalPotentialMeasure_lt_eq_zero` ---
applies to it verbatim.  The three side conditions of that lemma are all
immediate here:

* `hf`  : the constant `0` is lower semicontinuous;
* `hwf` : `FirstPass.thetaPshSupremum_le_zero`;
* `hmax`: `FirstPass.le_thetaPshSupremum` --- this is the *definition* of
  `V_theta` as a supremum, so no envelope theory is needed.

What is **not** discharged here is Lemma 2.4.3's remaining hypothesis `hloc`:
each point of the test set must lie in the source of a patch on which
`V_theta` is two-sided bounded.  That is Xia's Lemma 2.4.1 (`P_theta(f)` is
locally bounded outside `nK({theta})`), which needs the class to be big and is
not available in this workspace.  So `hloc` is carried as an explicit
hypothesis, exactly as Lemma 2.4.3 carries it, and the statement below is the
honest half of
`Pending.SingularityEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero`:
that interface is now Lemma 2.4.1 and nothing else.  No existing statement is
touched.

Nothing here assumes the test set is measurable, open, or inside a chart.

`Pending.PatchBoundedNeighborhood` supersedes the statement below by replacing
`hloc` with plain local boundedness; this module is kept because it isolates the
one point that matters — that the obstacle of Corollary 2.4.4 is the continuous
constant `0`, so no envelope theory and no concentration theorem is used.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaPshSupremumContact

open FirstPass FirstPass.MongeAmpere
open FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.PolydiskPatchBalayageContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {theta : ClosedRealOneOneForm n M}

/-- **Xia, SGPT, Corollary 2.4.4 (`xia-sgpt:page-0094`), modulo Lemma 2.4.1.**
The non-pluripolar Monge--Ampère measure of `V_theta` gives no mass to a set of
points where `V_theta` is strictly negative and locally bounded.

This is Lemma 2.4.3 applied to the continuous obstacle `0`; the only hypothesis
not discharged from the definition of `V_theta` is the local boundedness
`hloc`, i.e. Xia's Lemma 2.4.1. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_boundedOn (hn : 0 < n)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) {S : Set M}
    (hS : ∀ x ∈ S, thetaPshSupremum theta.val x < 0)
    (hloc : ∀ x ∈ S, ∃ (P : Patch (fun _ : Fin n => theta)
        (fun _ => thetaPshSupremum theta.val)) (_ : Fin n),
      x ∈ P.source ∧
        IsBoundedPotentialOn (thetaPshSupremum theta.val) P.source) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV S = 0 :=
  diagonalPotentialMeasure_lt_eq_zero (f := (0 : M → EReal)) hn
    lowerSemicontinuous_const
    (fun y => thetaPshSupremum_le_zero theta.val y)
    (fun v hv hv0 => le_thetaPshSupremum hv hv0)
    hV hS hloc

end

end SGPT.Foundations.Analysis.Pending.ThetaPshSupremumContact
