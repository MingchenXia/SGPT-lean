import SGPT.TestCurve.TestConfigFiltration
import SGPT.Foundations.Schemes.SectionRingValuation

/-!
# Bihomogeneous calculus in `R(X, L)[t, t⁻¹]`

Auxiliary algebra for the finite generation of the filtration of an ample test configuration
(lane FG-REL, [BHJ17, Prop. 2.15]). The Laurent section ring
`R(X, L)[t, t⁻¹] = SGPT.TestCurve.TestConfig.LaurentSecRing f a` is bigraded by the power `j` of
`t` and the degree `m` of the section; `mono j m s = t^j s` are its bihomogeneous elements.

## Main definitions

* `monoLin j m`: `s ↦ t^j s` as a `ℂ`-linear map.
* `bproj j m`: the projection onto the bihomogeneous component of bidegree `(j, m)`.
* `tElt`: the element `t = t¹ · 1`.

## Main results

* `coeffAt_mono_mul`: `coeff_{(j'+j, m'+m)}(t^{j'} s' · u) = s' · coeff_{(j, m)}(u)`.
* `bproj_mono_mul`, `bproj_tElt_mul`: the projections commute with multiplication by
  bihomogeneous elements (with the corresponding shift).
* `mono_mul_injective`: on an integral scheme, multiplication by a nonzero bihomogeneous
  element is injective (the Laurent section ring is a domain).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}

theorem mono_add (j : ℤ) (m : ℕ) (s s' : SectionSpace f L m) :
    (mono j m (s + s') : LaurentSecRing f a) = mono j m s + mono j m s' := by
  unfold mono SecRing.of
  rw [map_add, AddMonoidAlgebra.single_add]

theorem mono_smul (j : ℤ) (m : ℕ) (c : ℂ) (s : SectionSpace f L m) :
    (mono j m (c • s) : LaurentSecRing f a) = c • mono j m s := by
  unfold mono
  rw [AddMonoidAlgebra.smul_single]
  congr 1
  refine DFinsupp.ext fun n => ?_
  change SecRing.comp n (SecRing.of m (c • s) : SecRing f a) =
    SecRing.comp n (c • (SecRing.of m s : SecRing f a))
  rw [SecRing.comp_smul]
  by_cases h : n = m
  · subst h
    rw [SecRing.comp_of_same, SecRing.comp_of_same]
  · rw [SecRing.comp_of_ne h, SecRing.comp_of_ne h, smul_zero]

variable (f a) in
/-- `s ↦ t^j s` as a linear map. -/
def monoLin (j : ℤ) (m : ℕ) : SectionSpace f L m →ₗ[ℂ] LaurentSecRing f a where
  toFun s := mono j m s
  map_add' := mono_add j m
  map_smul' := mono_smul j m

@[simp] theorem monoLin_apply (j : ℤ) (m : ℕ) (s : SectionSpace f L m) :
    monoLin f a j m s = mono j m s := rfl

variable (f a) in
/-- The projection onto the bihomogeneous component of bidegree `(j, m)`. -/
def bproj (j : ℤ) (m : ℕ) : LaurentSecRing f a →ₗ[ℂ] LaurentSecRing f a :=
  (monoLin f a j m).comp (coeffAt j m)

theorem bproj_apply (j : ℤ) (m : ℕ) (z : LaurentSecRing f a) :
    bproj f a j m z = mono j m (coeffAt j m z) := rfl

theorem bproj_mono_same (j : ℤ) (m : ℕ) (s : SectionSpace f L m) :
    bproj f a j m (mono j m s) = mono j m s := by
  rw [bproj_apply, coeffAt_mono_same]

theorem bproj_mono_of_ne {j j' : ℤ} {m m' : ℕ} (h : ¬(j' = j ∧ m' = m))
    (s : SectionSpace f L m') : bproj f a j m (mono j' m' s) = 0 := by
  rw [bproj_apply, coeffAt_mono, dif_neg h, mono_zero]

/-- A bihomogeneous element is fixed or killed by every projection. -/
theorem bproj_mono (j : ℤ) (m : ℕ) {j' : ℤ} {m' : ℕ} (s : SectionSpace f L m') :
    bproj f a j m (mono j' m' s) = mono j' m' s ∨ bproj f a j m (mono j' m' s) = 0 := by
  by_cases h : j' = j ∧ m' = m
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl (bproj_mono_same _ _ _)
  · exact Or.inr (bproj_mono_of_ne h s)

/-! ### Products -/

theorem secRing_comp_of_mul (m' m : ℕ) (s' : SectionSpace f L m') (y : SecRing f a) :
    SecRing.comp (m' + m) ((SecRing.of m' s' : SecRing f a) * y) =
      SectionSpace.mul f a m' m s' (SecRing.comp m y) := by
  induction y using DirectSum.induction_on with
  | zero =>
    rw [mul_zero, SecRing.comp_zero, SecRing.comp_zero, map_zero]
  | of n t =>
    change SecRing.comp (m' + m) ((SecRing.of m' s' : SecRing f a) * SecRing.of n t) =
      SectionSpace.mul f a m' m s' (SecRing.comp m (SecRing.of n t))
    rw [SecRing.of_mul_of]
    by_cases h : n = m
    · subst h
      rw [SecRing.comp_of_same, SecRing.comp_of_same]
    · rw [SecRing.comp_of_ne (by omega), SecRing.comp_of_ne (Ne.symm h), map_zero]
  | add y y' hy hy' =>
    rw [mul_add, SecRing.comp_add, hy, hy', SecRing.comp_add, map_add]

/-- The coefficient of a product with a bihomogeneous element. -/
theorem coeffAt_mono_mul (j' j : ℤ) (m' m : ℕ) (s' : SectionSpace f L m')
    (u : LaurentSecRing f a) :
    coeffAt (j' + j) (m' + m) (mono j' m' s' * u) = SectionSpace.mul f a m' m s' (coeffAt j m u) := by
  change SecRing.comp (m' + m) ((AddMonoidAlgebra.single j' (SecRing.of m' s') * u).coeff (j' + j)) =
    SectionSpace.mul f a m' m s' (SecRing.comp m (u.coeff j))
  rw [AddMonoidAlgebra.coeff_single_mul_add, secRing_comp_of_mul]

theorem bproj_mono_mul (j' j : ℤ) (m' m : ℕ) (s' : SectionSpace f L m') (u : LaurentSecRing f a) :
    bproj f a (j' + j) (m' + m) (mono j' m' s' * u) = mono j' m' s' * bproj f a j m u := by
  rw [bproj_apply, bproj_apply, coeffAt_mono_mul, mono_mul_mono]

variable (f a) in
/-- The element `t ∈ R(X, L)[t, t⁻¹]`. -/
def tElt : LaurentSecRing f a := mono 1 0 (secOne f L)

theorem tElt_eq : (tElt f a : LaurentSecRing f a) = AddMonoidAlgebra.single 1 1 := rfl

variable (f a) in
/-- The element `t⁻¹ ∈ R(X, L)[t, t⁻¹]`. -/
def tInv : LaurentSecRing f a := AddMonoidAlgebra.single (-1) 1

theorem tInv_mul_tElt : tInv f a * tElt f a = 1 := by
  rw [tElt_eq, tInv, AddMonoidAlgebra.single_mul_single, one_mul, neg_add_cancel]
  rfl

theorem tElt_mul_tInv : tElt f a * tInv f a = 1 := by
  rw [mul_comm, tInv_mul_tElt]

theorem tElt_mul_mono (j : ℤ) (m : ℕ) (s : SectionSpace f L m) :
    tElt f a * mono j m s = mono (1 + j) m s := by
  rw [tElt_eq]
  unfold mono
  rw [AddMonoidAlgebra.single_mul_single, one_mul]

theorem coeffAt_tElt_mul (j : ℤ) (m : ℕ) (u : LaurentSecRing f a) :
    coeffAt (1 + j) m (tElt f a * u) = coeffAt j m u := by
  change SecRing.comp m ((AddMonoidAlgebra.single 1 (1 : SecRing f a) * u).coeff (1 + j)) =
    SecRing.comp m (u.coeff j)
  rw [AddMonoidAlgebra.coeff_single_mul_add, one_mul]

theorem bproj_tElt_mul (j : ℤ) (m : ℕ) (u : LaurentSecRing f a) :
    bproj f a (1 + j) m (tElt f a * u) = tElt f a * bproj f a j m u := by
  rw [bproj_apply, bproj_apply, coeffAt_tElt_mul, tElt_mul_mono]

theorem tElt_mul_cancel {u v : LaurentSecRing f a} (h : tElt f a * u = tElt f a * v) : u = v := by
  have := congrArg (fun z => tInv f a * z) h
  simp only [← mul_assoc, tInv_mul_tElt, one_mul] at this
  exact this

/-! ### The domain property -/

instance secRing_isDomain [IsIntegral X] : IsDomain (SecRing f a) :=
  inferInstanceAs (IsDomain (IntrinsicLineBundle.sectionRing ⟨L, a⟩))

instance laurentSecRing_noZeroDivisors [IsIntegral X] : NoZeroDivisors (LaurentSecRing f a) :=
  inferInstance

theorem mono_ne_zero [IsIntegral X] {j : ℤ} {m : ℕ} {s : SectionSpace f L m} (hs : s ≠ 0) :
    (mono j m s : LaurentSecRing f a) ≠ 0 := by
  intro h
  apply hs
  have := congrArg (coeffAt j m) h
  rwa [coeffAt_mono_same, map_zero] at this

/-- Multiplication by a nonzero element is injective (the Laurent section ring of an integral
scheme is a domain). -/
theorem mul_left_injective_of_ne_zero [IsIntegral X] {u : LaurentSecRing f a} (hu : u ≠ 0)
    {v w : LaurentSecRing f a} (h : u * v = u * w) : v = w := by
  have : u * (v - w) = 0 := by rw [mul_sub, h, sub_self]
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hu
  · exact sub_eq_zero.mp h'

end SGPT.TestCurve.FGRel
