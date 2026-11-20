import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation

set_option autoImplicit false

/-!
# Normalization laws for the rooftop envelope

Step 1.1 of the proof of Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0080`) is a
reduction to a nonpositive obstacle, in two moves: replace `f` by
`min {f, C}` for a constant `C` bounding `P_theta(f)`, and then translate by
a constant.  Both moves are laws of the envelope, and both are proved here.

* `rooftopEnvelope_add_const`: `P_theta(f + c) = P_theta(f) + c` for a finite
  real `c`.  Translation is a bijection of the competitor family with itself.
* `rooftopEnvelope_min_const_of_le`: if `P_theta(f) <= C` pointwise then
  `P_theta(min {f, C}) = P_theta(f)`.  Every competitor for `f` already lies
  below `P_theta(f)`, hence below `C`, so truncating the obstacle at `C` does
  not remove it.

`rooftopEnvelope_normalization` is the two moves together: the obstacle
`min {f, C} - C` is nonpositive and its envelope is `P_theta(f) - C`.

Nothing here assumes that `P_theta(f)` is a genuine potential, that the
competitor family is nonempty, or that the manifold is compact.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization

open SGPT.Foundations.Analysis.FirstPass

noncomputable section

/-- Adding a finite real constant and then its negative is the identity. -/
theorem add_coe_add_neg (a : EReal) (c : ℝ) :
    a + (c : EReal) + ((-c : ℝ) : EReal) = a := by
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

/-- Adding a finite real constant's negative and then the constant is the
identity. -/
theorem add_coe_neg_add (a : EReal) (c : ℝ) :
    a + ((-c : ℝ) : EReal) + (c : EReal) = a := by
  rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- One half of the translation law. -/
theorem rooftopEnvelope_add_const_le (theta : SmoothRealForm n M 2)
    (f : M → EReal) (c : ℝ) :
    rooftopEnvelope theta (fun x => f x + (c : EReal)) ≤
      fun x => rooftopEnvelope theta f x + (c : EReal) := by
  refine (rooftopEnvelope_le_iff
    (upperSemicontinuous_add_coe_const
      (upperSemicontinuous_rooftopEnvelope theta f) c)).mpr ?_
  intro u hu huf
  have hshift : IsThetaPshPotential theta (fun x => u x + ((-c : ℝ) : EReal)) :=
    IsThetaPshPotential.add_const hu (-c)
  have hshiftf : QuasiEverywhere (n := n)
      (fun x => u x + ((-c : ℝ) : EReal) ≤ f x) := by
    refine huf.mono fun x hx => ?_
    have hstep := add_le_add hx (le_refl (((-c : ℝ) : EReal)))
    rwa [add_coe_add_neg (f x) c] at hstep
  have hle := le_rooftopEnvelope hshift hshiftf
  intro x
  have hstep := add_le_add (hle x) (le_refl ((c : ℝ) : EReal))
  rwa [add_coe_neg_add (u x) c] at hstep

/-- **Translation law.**  The rooftop envelope commutes with adding a finite
real constant to the obstacle. -/
theorem rooftopEnvelope_add_const (theta : SmoothRealForm n M 2)
    (f : M → EReal) (c : ℝ) :
    rooftopEnvelope theta (fun x => f x + (c : EReal)) =
      fun x => rooftopEnvelope theta f x + (c : EReal) := by
  refine le_antisymm (rooftopEnvelope_add_const_le theta f c) ?_
  have hback := rooftopEnvelope_add_const_le theta
    (fun x => f x + (c : EReal)) (-c)
  have hfun : (fun x => (f x + (c : EReal)) + ((-c : ℝ) : EReal)) = f := by
    funext x
    rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  rw [hfun] at hback
  intro x
  have hstep := add_le_add (hback x) (le_refl ((c : ℝ) : EReal))
  rwa [add_coe_neg_add (rooftopEnvelope theta (fun y => f y + (c : EReal)) x) c]
    at hstep

/-- **Truncation law.**  If the envelope of `f` is bounded above by a finite
constant `C`, truncating the obstacle at `C` does not change the envelope. -/
theorem rooftopEnvelope_min_const_of_le (theta : SmoothRealForm n M 2)
    {f : M → EReal} {C : ℝ} (hC : ∀ x, rooftopEnvelope theta f x ≤ (C : EReal)) :
    rooftopEnvelope theta (fun x => min (f x) ((C : ℝ) : EReal)) =
      rooftopEnvelope theta f := by
  refine le_antisymm (rooftopEnvelope_mono fun x => min_le_left _ _) ?_
  refine (rooftopEnvelope_le_iff (upperSemicontinuous_rooftopEnvelope theta _)).mpr ?_
  intro u hu huf
  have huC : ∀ x, u x ≤ ((C : ℝ) : EReal) := fun x =>
    (le_rooftopEnvelope hu huf x).trans (hC x)
  exact le_rooftopEnvelope hu (huf.mono fun x hx => le_min hx (huC x))

/-- **Step 1.1 of Xia's Theorem 2.4.4.**  From a finite upper bound `C` for
the envelope, the obstacle may be replaced by a nonpositive one at the cost of
translating the envelope by `-C`. -/
theorem rooftopEnvelope_normalization (theta : SmoothRealForm n M 2)
    {f : M → EReal} {C : ℝ} (hC : ∀ x, rooftopEnvelope theta f x ≤ (C : EReal)) :
    (∀ x, min (f x) ((C : ℝ) : EReal) + ((-C : ℝ) : EReal) ≤ 0) ∧
      rooftopEnvelope theta
          (fun x => min (f x) ((C : ℝ) : EReal) + ((-C : ℝ) : EReal)) =
        fun x => rooftopEnvelope theta f x + ((-C : ℝ) : EReal) := by
  constructor
  · intro x
    calc min (f x) ((C : ℝ) : EReal) + ((-C : ℝ) : EReal)
        ≤ ((C : ℝ) : EReal) + ((-C : ℝ) : EReal) :=
          add_le_add (min_le_right _ _) le_rfl
      _ = 0 := by rw [← EReal.coe_add, add_neg_cancel, EReal.coe_zero]
  · rw [rooftopEnvelope_add_const theta (fun x => min (f x) ((C : ℝ) : EReal)) (-C),
      rooftopEnvelope_min_const_of_le theta hC]

end

end SGPT.Foundations.Analysis.Pending.RooftopEnvelopeNormalization
