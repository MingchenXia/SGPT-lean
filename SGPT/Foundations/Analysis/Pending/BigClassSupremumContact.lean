import SGPT.Foundations.Analysis.Pending.PatchBoundedNeighborhood
import SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound
import SGPT.Foundations.Analysis.Pending.NonKahlerLocusPoleSet
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.GlobalPotentialTransforms
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false

/-!
# Xia's Corollary 2.4.4 for a big class

`Pending.PatchBoundedNeighborhood` reduced Xia's Corollary 2.4.4
(`xia-sgpt:page-0094`) — `theta^n_{V_theta}` gives no mass to `{V_theta < 0}` —
to one existential: a normalized `theta`-PSH potential `psi ≤ 0` which is
two-sided bounded on a neighbourhood of every point off its own polar set.
That existential is Xia's Lemma 2.4.1 (`xia-sgpt:page-0074`), whose hypothesis
is that `{theta}` is **big**, and whose proof is Boucksom's theorem: a big
class contains a Kähler current with analytic singularities.

This module assembles the reference from the two inputs already on disk.

* `Pending.NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus`
  (Boucksom, *Divisorial Zariski decompositions*, Thm 3.17) produces a Kähler
  current `T` in the class with global analytic singularities.
* `Pending.AnalyticSingularityLocalBound` turns that presentation into the
  local two-sided bound off the poles.

The three intermediate moves are the standard ones.  `T` is a current for its
own representative `theta_T` and dominates a Kähler form `omega`; writing
`theta = theta_T + dd^c h` (Bott--Chern) makes `T.potential - h` a
`(theta - omega)`-PSH potential, adding the semipositive `omega` back makes it
`theta`-PSH, and subtracting its compact supremum normalizes it.  None of these
changes the polar set or the local boundedness, because `h` and the constant
are finite and continuous.

Bigness is genuinely used and is carried as a hypothesis: for a merely
pseudo-effective `{theta}` there is no Kähler current at all.  Xia's Theorem
2.4.4 as printed also carries no bigness — it inherits it from the sentence
heading Lemma 2.4.3 and from the proof — so the three workspace interfaces
match the printed statement and what is missing there is the non-big case, not
a hypothesis.

Corollary 2.4.4 itself is *not* stated here: it is the obstacle-`0` instance of
`Pending.BigClassEnvelopeContact.diagonalPotentialMeasure_lt_eq_zero_of_isBigClass`,
where it is recorded once.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BigClassSupremumContact

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure
open SGPT.Foundations.Analysis.Pending.AnalyticSingularityLocalBound

noncomputable section

/-! ### Stability of a local two-sided bound under a continuous shift -/

section Shift

variable {M : Type*}

/-- A two-sided bound survives subtracting a bounded real function and a
constant.  Both corrections are finite, so no `EReal` degeneracy occurs. -/
theorem isBoundedPotentialOn_sub_of_abs_le {v : M → EReal} {S : Set M}
    (hv : IsBoundedPotentialOn v S) {g : M → ℝ} {K : ℝ}
    (hg : ∀ x ∈ S, |g x| ≤ K) (C : ℝ) :
    IsBoundedPotentialOn (fun y => v y - (g y : EReal) - (C : EReal)) S := by
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨a - K - C, b + K - C, fun x hx => ?_⟩
  dsimp only
  obtain ⟨hlow, hhigh⟩ := hab x hx
  have hnbot : v x ≠ ⊥ := fun h => by simp [h] at hlow
  have hntop : v x ≠ ⊤ := fun h => by simp [h] at hhigh
  have hcoe : v x = ((v x).toReal : EReal) := (EReal.coe_toReal hntop hnbot).symm
  obtain ⟨hg1, hg2⟩ := abs_le.mp (hg x hx)
  rw [hcoe] at hlow hhigh ⊢
  rw [← EReal.coe_sub, ← EReal.coe_sub]
  rw [EReal.coe_le_coe_iff] at hlow hhigh
  exact ⟨EReal.coe_le_coe_iff.mpr (by linarith),
    EReal.coe_le_coe_iff.mpr (by linarith)⟩

end Shift

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable [CompactSpace M] [Nonempty M]

/-! ### The normalized reference of a big class -/

/-- **Xia, SGPT, Lemma 2.4.1, in the form the concentration theorem needs.**
A big class has a normalized `theta`-PSH potential which is two-sided bounded
near every point off its polar set.  The potential is the Kähler-current
potential of Boucksom's theorem, transported to `theta` and normalized. -/
theorem exists_normalized_reference_of_isBigClass (hn : 0 < n)
    (theta : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative theta)) :
    ∃ psi : M → EReal, IsThetaPshPotential theta.val psi ∧ psi ≤ 0 ∧
      poleSet psi = nonKahlerLocus (RealBottChern.ofRepresentative theta) ∧
      ∀ x, psi x ≠ ⊥ → ∃ N ∈ 𝓝 x, IsBoundedPotentialOn psi N := by
  classical
  obtain ⟨T, hsing, -, hpole⟩ :=
    NonKahlerLocusPoleSet.exists_kahlerCurrent_poleSet_eq_nonKahlerLocus hn _ hbig
  obtain ⟨h, hh, heq⟩ := (RealBottChern.ofRepresentative_eq_iff _ _).mp T.represents
  have hcont : Continuous h := KahlerCurrentMax.continuous_of_chartSmooth hh
  -- `T.potential - h` is `(theta - omega)`-PSH
  have hsub : ThetaPlurisubharmonic (theta - T.lowerBound.form).val
      (fun y => T.potential y - (h y : EReal)) := by
    refine GlobalPotentialTransforms.thetaPlurisubharmonic_sub_smooth hh
      (fun e z hz => ?_) T.strictlyPsh.1
    simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.coeff_neg]
    rw [heq e z hz]
    abel
  -- adding the semipositive Kähler form back gives a `theta`-PSH potential
  have hform : (theta - T.lowerBound.form) + T.lowerBound.form = theta := by
    abel
  have hpsh : ThetaPlurisubharmonic theta.val (fun y => T.potential y - (h y : EReal)) := by
    have := SGPT.Foundations.Analysis.Pending.LocalPotentials.thetaPlurisubharmonic_add_of_semipositive
      hsub T.lowerBound.isSemipositive
    rwa [hform] at this
  have hnd : LocallyNondegenerate (fun y => T.potential y - (h y : EReal)) := by
    intro x U hU hxU
    obtain ⟨y, hyU, hy⟩ := T.strictlyPsh.2 x U hU hxU
    refine ⟨y, hyU, ?_⟩
    show T.potential y - (h y : EReal) ≠ ⊥
    rw [sub_eq_add_neg, ← EReal.coe_neg]
    exact EReal.add_ne_bot_iff.mpr ⟨hy, EReal.coe_ne_bot _⟩
  have hpot : IsThetaPshPotential theta.val (fun y => T.potential y - (h y : EReal)) :=
    ⟨hpsh, hnd⟩
  obtain ⟨C, hC⟩ := hpot.exists_global_upper_bound
  -- the finite corrections do not move the polar set
  have hbot_iff : ∀ x : M,
      (T.potential x - (h x : EReal)) - (C : EReal) = ⊥ ↔ T.potential x = ⊥ := by
    intro x
    constructor
    · intro hb
      by_contra hne
      have hnetop : T.potential x ≠ ⊤ :=
        T.strictlyPsh.1.quasiPlurisubharmonic.ne_top x
      have hcoe : T.potential x = (((T.potential x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hnetop hne).symm
      rw [hcoe, ← EReal.coe_sub, ← EReal.coe_sub] at hb
      exact (EReal.coe_ne_bot _) hb
    · intro hb
      rw [hb]
      simp
  refine ⟨fun y => (T.potential y - (h y : EReal)) - (C : EReal), hpot.sub_const C,
    sub_const_nonpositive_of_le hC, ?_, ?_⟩
  · rw [← hpole]
    ext x
    simpa only [poleSet, Set.mem_ofPred_eq] using hbot_iff x
  intro x hx
  -- off the poles of `T.potential`, use the analytic presentation
  have hTx : T.potential x ≠ ⊥ := fun hbot => hx ((hbot_iff x).mpr hbot)
  obtain ⟨N₁, hN₁, hb₁⟩ :=
    exists_isBoundedPotentialOn_of_hasAnalyticSingularities hsing hTx
  obtain ⟨K, -, hK⟩ := boundedRealGermAt_of_continuousAt (hcont.continuousAt (x := x))
  exact ⟨N₁ ∩ {y | |h y| ≤ K}, Filter.inter_mem hN₁ hK,
    isBoundedPotentialOn_sub_of_abs_le (hb₁.mono inter_subset_left)
      (fun y hy => hy.2) C⟩

end

end SGPT.Foundations.Analysis.Pending.BigClassSupremumContact
