import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.Pending.CoordinateDensityMixedPullback

set_option autoImplicit false

/-!
# The telescoping expansion of the top density of a sum of two real two-forms

Stokes against the integration current of a subvariety compares the two numbers
`∫_{V_reg}(β + ddᶜv)^k` and `∫_{V_reg}β^k`.  Its first step is purely algebraic and
pointwise: the difference of the two DENSITIES is a sum of `k` mixed densities, each
of which carries the two-form `ddᶜv` in exactly one slot.  That is what makes the
difference an exact form after the chain rule, and it is what this module proves.

Write `A` for the coordinate two-form of `β` and `B` for that of `ddᶜv`, both read in
the parameters of one regular patch.  With

`hybridFamily A B j = (A + B, …, A + B, A, …, A)` (`A + B` in the slots below `j`),

the mixed density of `Pending.CoordinateWedgeFamily` satisfies

`density (hybridFamily A B (j+1)) − density (hybridFamily A B j)
  = density (telescopeFamily A B j)`,

where `telescopeFamily A B j` is `hybridFamily A B j` with `B` put in slot `j`: the two
hybrid families differ in the single slot `j`, where they carry `A + B` and `A`, so
multilinearity of `Pending.CoordinateWedgeFamilyPairing.actualMixedTopDensityMultilinear`
in that slot gives the difference at once.  Summing over `j < n` telescopes, and the
two ends of the telescope are the diagonal values

`hybridFamily A B 0 = (A, …, A)`,  `hybridFamily A B n = (A + B, …, A + B)`,

whose mixed densities are the exterior-power densities of `A` and of `A + B`
(`actualMixedTopDensity_const`).  Hence

`actualTopPowerDensity (A + B) − actualTopPowerDensity A
  = ∑_{j < n} actualMixedTopDensity (telescopeFamily A B j)`.

This is the identity `u^n − w^n = (u − w) ∧ ∑_j u^j ∧ w^{n−1−j}` of the exterior
algebra, with `u = A + B` and `w = A`, read on the standard real frame.  No positivity
and no type restriction is used: `A` and `B` are arbitrary real two-forms, which is
what the intended application needs, since `ddᶜv` is sign-indefinite.

Degenerate dimensions are included.  For `n = 0` the sum is empty and both densities
are the empty wedge `1`, so the identity reads `1 − 1 = 0`.  For `n = 1` it is
`(A + B) − A = B` on the positively oriented real frame.
-/

namespace SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere

noncomputable section

variable {n : ℕ}

/-- The hybrid family carrying `A + B` in the slots of index below `j` and `A` in the
rest.  At `j = 0` it is the constant family `A`, at `j = n` the constant family
`A + B`. -/
def hybridFamily (A B : CoordinateRealTwoForm n) (j : ℕ) :
    Fin n → CoordinateRealTwoForm n :=
  fun i => if (i : ℕ) < j then A + B else A

/-- The `j`-th term of the telescope: `A + B` in the slots below `j`, `B` in the slot
`j` itself and `A` above it. -/
def telescopeFamily (A B : CoordinateRealTwoForm n) (j : Fin n) :
    Fin n → CoordinateRealTwoForm n :=
  Function.update (hybridFamily A B (j : ℕ)) j B

@[simp] theorem hybridFamily_zero (A B : CoordinateRealTwoForm n) :
    hybridFamily A B 0 = fun _ => A := by
  funext i
  simp [hybridFamily]

@[simp] theorem hybridFamily_top (A B : CoordinateRealTwoForm n) :
    hybridFamily A B n = fun _ => A + B := by
  funext i
  simp [hybridFamily, i.isLt]

@[simp] theorem telescopeFamily_apply_self (A B : CoordinateRealTwoForm n) (j : Fin n) :
    telescopeFamily A B j j = B := by
  simp [telescopeFamily]

theorem telescopeFamily_apply_of_lt (A B : CoordinateRealTwoForm n) {j i : Fin n}
    (h : (i : ℕ) < (j : ℕ)) : telescopeFamily A B j i = A + B := by
  have hne : i ≠ j := fun hij => absurd (congrArg Fin.val hij) (Nat.ne_of_lt h)
  simp [telescopeFamily, hybridFamily, Function.update_of_ne hne, h]

theorem telescopeFamily_apply_of_gt (A B : CoordinateRealTwoForm n) {j i : Fin n}
    (h : (j : ℕ) < (i : ℕ)) : telescopeFamily A B j i = A := by
  have hne : i ≠ j := fun hij => absurd (congrArg Fin.val hij) (Nat.ne_of_gt h)
  simp [telescopeFamily, hybridFamily, Function.update_of_ne hne, Nat.not_lt_of_gt h]

/-- The hybrid family at `j` is its own update at the slot `j` by `A`: that slot carries
`A` because `¬ j < j`. -/
theorem hybridFamily_eq_update_self (A B : CoordinateRealTwoForm n) (j : Fin n) :
    hybridFamily A B (j : ℕ) = Function.update (hybridFamily A B (j : ℕ)) j A := by
  refine (Function.update_eq_self_iff.2 ?_).symm
  simp [hybridFamily]

/-- Passing from `j` to `j + 1` in the hybrid family changes exactly the slot `j`, from
`A` to `A + B`. -/
theorem hybridFamily_succ (A B : CoordinateRealTwoForm n) (j : Fin n) :
    hybridFamily A B ((j : ℕ) + 1) =
      Function.update (hybridFamily A B (j : ℕ)) j (A + B) := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp [hybridFamily]
  · rw [Function.update_of_ne hij]
    have : ((i : ℕ) < (j : ℕ) + 1) ↔ ((i : ℕ) < (j : ℕ)) := by
      refine ⟨fun h => ?_, fun h => h.trans (Nat.lt_succ_self _)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') hij
    simp only [hybridFamily, this]

/-- **One step of the telescope.**  The mixed densities of two consecutive hybrid
families differ by the mixed density of the telescope term, because the two families
differ in the single slot `j`. -/
theorem actualMixedTopDensity_hybridFamily_succ (A B : CoordinateRealTwoForm n)
    (j : Fin n) :
    actualMixedTopDensity (hybridFamily A B ((j : ℕ) + 1)) =
      actualMixedTopDensity (hybridFamily A B (j : ℕ)) +
        actualMixedTopDensity (telescopeFamily A B j) := by
  classical
  have h := actualMixedTopDensityMultilinear.map_update_add
    (hybridFamily A B (j : ℕ)) j A B
  rw [hybridFamily_succ A B j]
  simpa only [actualMixedTopDensityMultilinear_apply, telescopeFamily,
    ← hybridFamily_eq_update_self A B j] using h

/-- The telescope term as a function of the natural-number index, extended by zero. -/
private def term (A B : CoordinateRealTwoForm n) (j : ℕ) : ℝ :=
  if h : j < n then actualMixedTopDensity (telescopeFamily A B ⟨j, h⟩) else 0

private theorem hybrid_eq_sum (A B : CoordinateRealTwoForm n) :
    ∀ m : ℕ, m ≤ n →
      actualMixedTopDensity (hybridFamily A B m) =
        actualTopPowerDensity A + ∑ j ∈ Finset.range m, term A B j
  | 0, _ => by simp
  | (m + 1), hm => by
      have hmn : m < n := hm
      have hstep := actualMixedTopDensity_hybridFamily_succ A B (⟨m, hmn⟩ : Fin n)
      have hterm : term A B m = actualMixedTopDensity (telescopeFamily A B ⟨m, hmn⟩) := by
        simp [term, hmn]
      have hprev := hybrid_eq_sum A B m (le_of_lt hmn)
      calc actualMixedTopDensity (hybridFamily A B (m + 1))
          = actualMixedTopDensity (hybridFamily A B m) +
              actualMixedTopDensity (telescopeFamily A B ⟨m, hmn⟩) := hstep
        _ = (actualTopPowerDensity A + ∑ j ∈ Finset.range m, term A B j) +
              actualMixedTopDensity (telescopeFamily A B ⟨m, hmn⟩) := by rw [hprev]
        _ = actualTopPowerDensity A + ∑ j ∈ Finset.range (m + 1), term A B j := by
              rw [Finset.sum_range_succ, hterm]
              ring

/-- **The telescoping expansion of the top density of a sum.**  For arbitrary real
two-forms `A` and `B` the exterior-power density of `A + B` is that of `A` plus the `n`
mixed densities in which `B` occupies exactly one slot, `A + B` the slots below it and
`A` the slots above.

This is the pointwise algebraic step of Stokes against a subvariety: with `A` the
coordinate form of the background `β` and `B` that of `ddᶜv`, every summand carries
`ddᶜv` once, hence is an exact form after the chain rule. -/
theorem actualTopPowerDensity_add (A B : CoordinateRealTwoForm n) :
    actualTopPowerDensity (A + B) =
      actualTopPowerDensity A + ∑ j : Fin n, actualMixedTopDensity (telescopeFamily A B j) := by
  have h := hybrid_eq_sum A B n le_rfl
  rw [hybridFamily_top, actualMixedTopDensity_const] at h
  rw [h, ← Fin.sum_univ_eq_sum_range (term A B) n]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  simp [term, j.isLt]

/-- The difference form of the telescoping expansion. -/
theorem actualTopPowerDensity_add_sub (A B : CoordinateRealTwoForm n) :
    actualTopPowerDensity (A + B) - actualTopPowerDensity A =
      ∑ j : Fin n, actualMixedTopDensity (telescopeFamily A B j) := by
  rw [actualTopPowerDensity_add]
  ring

/-! ## Compatibility with pullback -/

/-- Composition with a continuous linear map is additive in the alternating form. -/
theorem compContinuousLinearMap_add {p m : ℕ} (f g : (ComplexModel m) [⋀^Fin p]→L[ℝ] ℝ)
    (L : ComplexModel n →L[ℝ] ComplexModel m) :
    (f + g).compContinuousLinearMap L =
      f.compContinuousLinearMap L + g.compContinuousLinearMap L := by
  ext v
  rfl

/-- **Pullback passes through the telescope.**  Composing both arguments with a real-linear
map composes every slot of every telescope term with it; the slot structure is built from
`+` alone, which commutes with composition. -/
theorem telescopeFamily_compContinuousLinearMap {k : ℕ} (A B : CoordinateRealTwoForm k)
    (L : ComplexModel k →L[ℝ] ComplexModel k) (j : Fin k) :
    telescopeFamily (A.compContinuousLinearMap L) (B.compContinuousLinearMap L) j =
      fun i => (telescopeFamily A B j i).compContinuousLinearMap L := by
  funext i
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · rw [telescopeFamily_apply_of_lt _ _ h, telescopeFamily_apply_of_lt _ _ h,
      compContinuousLinearMap_add]
  · have hij : i = j := Fin.ext h
    subst hij
    rw [telescopeFamily_apply_self, telescopeFamily_apply_self]
  · rw [telescopeFamily_apply_of_gt _ _ h, telescopeFamily_apply_of_gt _ _ h]

/-- **The Jacobian law for the telescope terms.**  Under a real-linear endomorphism every
telescope term's mixed density is multiplied by the real determinant, exactly as the
exterior-power density is.  Hence the whole telescope sum transforms by the Jacobian. -/
theorem sum_actualMixedTopDensity_telescopeFamily_compContinuousLinearMap
    (A B : CoordinateRealTwoForm n) (L : ComplexModel n →L[ℝ] ComplexModel n) :
    (∑ j : Fin n, actualMixedTopDensity
        (telescopeFamily (A.compContinuousLinearMap L) (B.compContinuousLinearMap L) j)) =
      LinearMap.det (L : ComplexModel n →ₗ[ℝ] ComplexModel n) *
        ∑ j : Fin n, actualMixedTopDensity (telescopeFamily A B j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [telescopeFamily_compContinuousLinearMap A B L j,
    actualMixedTopDensity_compContinuousLinearMap]

end

end SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope
