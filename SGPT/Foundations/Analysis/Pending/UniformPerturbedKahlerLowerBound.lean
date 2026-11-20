import SGPT.Foundations.Analysis.FirstPass.KahlerCurrentPerturbation
import SGPT.Foundations.Analysis.Pending.KahlerDomination
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# Bigness is a uniform Kähler lower bound on the perturbed classes

The last classical input of the full-space non-big branch,
`Pending.UniformAmbientVolumeBigness.isBigClass_of_hasUniformAmbientMassLowerBound`,
is Boucksom's Grauert--Riemenschneider criterion (`bou02-volume:4.8`).  Its proof
ends with the display (`bou02-volume:4.8`)
`n(∫_{X_k} b_k^{n-1} ∧ ω_k)(α + ε_k ω) ≥ δ ω` with the integrals uniformly
bounded: a Kähler lower bound on the *perturbed* classes `α + ε{ω}` that does
**not** degenerate as `ε → 0`.  The final step is then to let `ε → 0`.

This module formalizes that final step, and its converse.  Both are elementary
and both are proved here:

* `isBigClass_of_hasUniformPerturbedKahlerLowerBound` — if for arbitrarily small
  `ε > 0` the class `α + ε{ω}` carries a Kähler current whose lower bound is
  `c ω` for one fixed `c > 0`, then `α` is big.  Take `ε < c` and subtract `ε ω`
  from the representative: the potential and the inequality are untouched, only
  the Kähler lower bound shrinks from `c ω` to `(c - ε) ω`.
* `exists_hasUniformPerturbedKahlerLowerBound_of_isBigClass` — the converse, on a
  compact manifold: a Kähler current in `α` dominates `A⁻¹ ω` for some `A > 0` by
  Kähler domination, and adding `ε ω` only increases the lower bound.

So the two are **equivalent** (`isBigClass_iff_hasUniformPerturbedKahlerLowerBound`).
That equivalence is the point: it is the reason the tempting split of
`bou02-volume:4.8` into "the uniform lower bound at every small error" plus "let
`ε → 0`" is a *restatement* of its own consumer in the sense of `I-0166` /
`I-0194`, not a reduction of it, and must not be introduced as a named interface.
The mathematical content of `bou02-volume:4.8` is upstream of this display — the
Demailly--Păun concentration of mass and the Aubin--Calabi--Yau theorem on the
blow-up towers `X_k × X_k` — and none of it is touched here.

Two pieces of `KahlerCurrent` API that were missing are proved on the way:
`weakenLowerBound` (a Kähler current may be re-presented with any smaller Kähler
lower bound) and `subSmulKahler` (the converse of
`FirstPass.NonKahlerLocus.KahlerCurrent.addSmulKahler`, available exactly when
the lower bound splits off `ε ω`).
-/

namespace SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ## Two missing pieces of the `KahlerCurrent` API -/

/-- The sum of two semipositive closed real `(1,1)`-forms is semipositive. -/
theorem isSemipositive_add {a b : ClosedRealOneOneForm n M}
    (ha : a.val.IsSemipositive) (hb : b.val.IsSemipositive) :
    (a + b).val.IsSemipositive := by
  intro e z hz v
  simpa [ClosedRealOneOneForm.coeff_add] using add_nonneg (ha e z hz v) (hb e z hz v)

/-- **A Kähler current may be re-presented with a smaller Kähler lower bound.**
The representative and the potential are unchanged; only the lower bound moves
down, which is legitimate because `ω' - ω''` is semipositive. -/
def weakenLowerBound {alpha : RealBottChern n M} (T : KahlerCurrent alpha)
    (omega' : KahlerBackground n M)
    (h : (T.lowerBound.form - omega'.form).val.IsSemipositive) :
    KahlerCurrent alpha where
  representative := T.representative
  represents := T.represents
  potential := T.potential
  lowerBound := omega'
  strictlyPsh := by
    have hsum := LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh h
    have heq : (T.representative - T.lowerBound.form)
        + (T.lowerBound.form - omega'.form) = T.representative - omega'.form := by
      abel
    rwa [heq] at hsum

@[simp] theorem weakenLowerBound_potential {alpha : RealBottChern n M}
    (T : KahlerCurrent alpha) (omega' : KahlerBackground n M)
    (h : (T.lowerBound.form - omega'.form).val.IsSemipositive) :
    (weakenLowerBound T omega' h).potential = T.potential := rfl

@[simp] theorem weakenLowerBound_lowerBound {alpha : RealBottChern n M}
    (T : KahlerCurrent alpha) (omega' : KahlerBackground n M)
    (h : (T.lowerBound.form - omega'.form).val.IsSemipositive) :
    (weakenLowerBound T omega' h).lowerBound = omega' := rfl

/-- **Subtracting `ε ω` from a Kähler current, the converse of
`KahlerCurrent.addSmulKahler`.**  A Kähler current in `α + ε{ω}` whose Kähler
lower bound splits as `ω'' + ε ω` descends to a Kähler current in `α` with the
same potential and lower bound `ω''`. -/
def subSmulKahler {alpha : RealBottChern n M} (omega : KahlerBackground n M)
    {epsilon : ℝ}
    (T : KahlerCurrent (alpha + epsilon • RealBottChern.ofRepresentative omega.form))
    (omega'' : KahlerBackground n M)
    (h : T.lowerBound.form = omega''.form + epsilon • omega.form) :
    KahlerCurrent alpha where
  representative := T.representative - epsilon • omega.form
  represents := by
    have h0 : RealBottChern.ofRepresentative (T.representative - epsilon • omega.form)
        = RealBottChern.ofRepresentative T.representative
          - epsilon • RealBottChern.ofRepresentative omega.form := by
      simp [sub_eq_add_neg]
    rw [h0, T.represents]
    abel
  potential := T.potential
  lowerBound := omega''
  strictlyPsh := by
    have heq : (T.representative - epsilon • omega.form) - omega''.form
        = T.representative - T.lowerBound.form := by
      rw [h]; abel
    rw [heq]
    exact T.strictlyPsh

@[simp] theorem subSmulKahler_potential {alpha : RealBottChern n M}
    (omega : KahlerBackground n M) {epsilon : ℝ}
    (T : KahlerCurrent (alpha + epsilon • RealBottChern.ofRepresentative omega.form))
    (omega'' : KahlerBackground n M)
    (h : T.lowerBound.form = omega''.form + epsilon • omega.form) :
    (subSmulKahler omega T omega'' h).potential = T.potential := rfl

/-! ## The uniform perturbed Kähler lower bound -/

/-- **A uniform Kähler lower bound on the perturbed classes.**  For arbitrarily
small errors `ε > 0` the class `α + ε{ω}` carries a Kähler current whose Kähler
lower bound is exactly `c ω` — one and the same `c` for every such `ε`.  This is
the shape of the penultimate display of Boucksom's proof of
`bou02-volume:4.8`. -/
def HasUniformPerturbedKahlerLowerBound (omega : KahlerBackground n M)
    (alpha : RealBottChern n M) (c : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < delta ∧
    ∃ T : KahlerCurrent (alpha + epsilon • RealBottChern.ofRepresentative omega.form),
      T.lowerBound.form = c • omega.form

/-- **Letting the error tend to zero: the last step of Boucksom's proof of the
Grauert--Riemenschneider criterion.**  A uniform Kähler lower bound `c ω` on the
perturbed classes makes `α` itself big: choose an error `ε < c` and subtract
`ε ω`, which leaves the potential and the inequality alone and only shrinks the
Kähler lower bound to `(c - ε) ω`. -/
theorem isBigClass_of_hasUniformPerturbedKahlerLowerBound
    (omega : KahlerBackground n M) (alpha : RealBottChern n M) {c : ℝ} (hc : 0 < c)
    (h : HasUniformPerturbedKahlerLowerBound omega alpha c) : IsBigClass alpha := by
  obtain ⟨epsilon, hpos, hlt, T, hT⟩ := h c hc
  have hce : 0 < c - epsilon := by linarith
  refine ⟨subSmulKahler omega T (KahlerBackground.smul hce omega) ?_⟩
  rw [hT, KahlerBackground.smul_form, ← add_smul]
  congr 1
  ring

variable [CompactSpace M]

/-- **The converse.**  On a compact Kähler manifold a big class has a uniform
Kähler lower bound on all of its perturbations: a Kähler current in `α`
dominates `A⁻¹ ω` for some `A > 0` by Kähler domination
(`Pending.KahlerDomination.exists_pos_isSemipositive_add_smul` applied to `-ω`
against the current's own lower bound), and adding `ε ω` only increases the
lower bound. -/
theorem exists_hasUniformPerturbedKahlerLowerBound_of_isBigClass
    (omega : KahlerBackground n M) (alpha : RealBottChern n M) (h : IsBigClass alpha) :
    ∃ c : ℝ, 0 < c ∧ HasUniformPerturbedKahlerLowerBound omega alpha c := by
  obtain ⟨T⟩ := h
  obtain ⟨A, hA, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul T.lowerBound (-omega.form)
  have hAinv : (0 : ℝ) < A⁻¹ := inv_pos.2 hA
  -- `T.lowerBound ≥ A⁻¹ ω`
  have hdom : (T.lowerBound.form - A⁻¹ • omega.form).val.IsSemipositive := by
    have := KahlerDomination.isSemipositive_smul hsemi hAinv.le
    have heq : A⁻¹ • (-omega.form + A • T.lowerBound.form)
        = T.lowerBound.form - A⁻¹ • omega.form := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hA), one_smul, smul_neg]
      abel
    rwa [heq] at this
  refine ⟨A⁻¹, hAinv, fun delta hdelta => ⟨delta / 2, by positivity, by linarith, ?_⟩⟩
  have hepspos : (0 : ℝ) < delta / 2 := by positivity
  refine ⟨weakenLowerBound (T.addSmulKahler omega hepspos)
    (KahlerBackground.smul hAinv omega) ?_, ?_⟩
  · have heq : (T.addSmulKahler omega hepspos).lowerBound.form
        - (KahlerBackground.smul hAinv omega).form
        = (T.lowerBound.form - A⁻¹ • omega.form) + (delta / 2) • omega.form := by
      show T.lowerBound.form + (delta / 2) • omega.form - A⁻¹ • omega.form = _
      abel
    rw [heq]
    exact isSemipositive_add hdom
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hepspos.le)
  · rfl

/-- **Bigness is exactly a uniform Kähler lower bound on the perturbed classes.**
Recorded so that no future round states the uniform bound as a named classical
interface: it follows from its own consumer by `mpr`, so the split carries no
content.  The mathematics of `bou02-volume:4.8` lies
upstream of this display. -/
theorem isBigClass_iff_hasUniformPerturbedKahlerLowerBound
    (omega : KahlerBackground n M) (alpha : RealBottChern n M) :
    IsBigClass alpha ↔ ∃ c : ℝ, 0 < c ∧ HasUniformPerturbedKahlerLowerBound omega alpha c :=
  ⟨exists_hasUniformPerturbedKahlerLowerBound_of_isBigClass omega alpha,
    fun ⟨_, hc, h⟩ => isBigClass_of_hasUniformPerturbedKahlerLowerBound omega alpha hc h⟩

end

end SGPT.Foundations.Analysis.Pending.UniformPerturbedKahlerLowerBound
