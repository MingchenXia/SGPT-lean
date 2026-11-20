import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-!
# Hermitian backgrounds without a closedness assumption

The Hermitian form in FPT, Section 14.8, is a genuine smooth real two-form,
compatible with changes of holomorphic coordinates, positive and of type
`(1,1)`. Its exterior derivative is unrestricted. This module retains the
existing Kähler backgrounds as the closed special case.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.Hermitian

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A Hermitian background is an actual smooth strictly positive real
`(1,1)`-form. Closedness is deliberately not a field. -/
structure Background (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  form : SmoothRealForm n M 2
  isHermitian : form.IsHermitian

namespace Background

/-- A Hermitian background has type `(1,1)` in every actual chart. -/
theorem isTypeOneOne (ω : Background n M) : ω.form.IsTypeOneOne :=
  fun e z hz => (ω.isHermitian e z hz).1

/-- Strict Hermitian positivity implies semipositivity, including the zero
tangent vector and complex dimension zero. -/
theorem isSemipositive (ω : Background n M) : ω.form.IsSemipositive := by
  intro e z hz v
  by_cases hv : v = 0
  · subst v
    rw [(ω.form.coeff e z).map_coord_zero (0 : Fin 2) rfl]
  · exact ((ω.isHermitian e z hz).2 v hv).le

/-- Forget only the closedness of an existing Kähler background. -/
def ofKahler (ω : KahlerBackground n M) : Background n M :=
  ⟨ω.form.val, ω.isKahler.1⟩

@[simp] theorem ofKahler_form (ω : KahlerBackground n M) :
    (ofKahler ω).form = ω.form.val := rfl

/-- When a Hermitian background is closed it is the same geometric object
as an existing Kähler background. -/
def toKahler (ω : Background n M) (hω : ω.form.IsClosed) : KahlerBackground n M where
  form := ⟨ω.form, hω, ω.isTypeOneOne⟩
  isKahler := ⟨ω.isHermitian, hω⟩

@[simp] theorem toKahler_form (ω : Background n M) (hω : ω.form.IsClosed) :
    (ω.toKahler hω).form.val = ω.form := rfl

/-- The explicit flat example is also a Hermitian background. -/
def flat (n : ℕ) : Background n (ComplexModel n) :=
  ⟨flatKahlerForm n, (flatKahlerForm_isKahler n).1⟩

end Background

end SGPT.PSH.Hermitian
