import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Real.Basic

/-! # Scalar extension of the joint kernel of original integer functionals -/

open scoped TensorProduct

noncomputable section
universe u v w

namespace SGPT.Foundations.Envelope.NativeNumericalCarrierComparison

variable {M : Type u} [AddCommGroup M] {ι : Type v}

/-- The actual rational extension of an original integer functional. -/
def rationalFunctional (f : M →ₗ[ℤ] ℤ) : ℚ ⊗[ℤ] M →ₗ[ℚ] ℚ :=
  (((Int.castAddHom ℚ).toIntLinearMap).comp f).liftBaseChange ℚ

@[simp]
theorem rationalFunctional_tmul (f : M →ₗ[ℤ] ℤ) (r : ℚ) (m : M) :
    rationalFunctional f (r ⊗ₜ[ℤ] m) = r * (f m : ℚ) := rfl

/-- The actual real extension of the same original integer functional. -/
def realFunctional (f : M →ₗ[ℤ] ℤ) : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ :=
  (((Int.castAddHom ℝ).toIntLinearMap).comp f).liftBaseChange ℝ

@[simp]
theorem realFunctional_tmul (f : M →ₗ[ℤ] ℤ) (r : ℝ) (m : M) :
    realFunctional f (r ⊗ₜ[ℤ] m) = r * (f m : ℝ) := rfl

/-- Clearing a single denominator proves rational joint detection for the
SAME original integer functionals, without finite-dimensionality. -/
theorem rationalFunctional_jointly_detects (f : ι → M →ₗ[ℤ] ℤ)
    (hf : ∀ m : M, (∀ i, f i m = 0) → m = 0)
    (x : ℚ ⊗[ℤ] M) (hx : ∀ i, rationalFunctional (f i) x = 0) : x = 0 := by
  obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ M 1) x
  change s • x = (1 : ℚ) ⊗ₜ[ℤ] m at hms
  have hm : m = 0 := by
    apply hf
    intro i
    have h := congrArg (rationalFunctional (f i)) hms
    have hi : (f i m : ℚ) = 0 := by
      simpa only [Submonoid.smul_def, map_zsmul, hx i, zsmul_zero,
        rationalFunctional_tmul, one_mul] using h.symm
    exact_mod_cast hi
  apply IsLocalizedModule.smul_injective (TensorProduct.mk ℤ ℚ M 1) s
  simp only [hms, hm, TensorProduct.tmul_zero, smul_zero]

section RationalVectorSpace

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Extend the actual rational functional to real scalars. -/
def realOfRationalFunctional (f : V →ₗ[ℚ] ℚ) : ℝ ⊗[ℚ] V →ₗ[ℝ] ℝ :=
  ((Algebra.linearMap ℚ ℝ).comp f).liftBaseChange ℝ

@[simp]
theorem realOfRationalFunctional_tmul (f : V →ₗ[ℚ] ℚ) (r : ℝ) (v : V) :
    realOfRationalFunctional f (r ⊗ₜ[ℚ] v) = r * (f v : ℝ) := rfl

private theorem realOfRational_coordinate {β : Type w} [DecidableEq β]
    (b : Module.Basis β ℚ ℝ) (f : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) (j : β) :
    f (TensorProduct.equivFinsuppOfBasisLeft b x j) =
      b.repr (realOfRationalFunctional f x) j := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
        realOfRationalFunctional_tmul]
      have hm : r * (f v : ℝ) = (f v) • r := by
        rw [Rat.smul_def, mul_comm]
      rw [hm, map_smul, map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      exact mul_comm _ _
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, hx, hy]

/-- A rational basis of the REAL COEFFICIENT space proves whole real tensor
detection from the same rational functionals. No dimension bound is assumed
for the original vector space. -/
theorem realOfRational_jointly_detects (f : ι → V →ₗ[ℚ] ℚ)
    (hf : ∀ v : V, (∀ i, f i v = 0) → v = 0)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ i, realOfRationalFunctional (f i) x = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis ℚ ℝ
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := V) b
  have he : e x = 0 := by
    ext j
    change e x j = 0
    apply hf
    intro i
    rw [show f i (e x j) = b.repr (realOfRationalFunctional (f i) x) j from
      realOfRational_coordinate b (f i) x j]
    rw [hx i, map_zero, Finsupp.zero_apply]
  apply e.injective
  simpa only [map_zero] using he

end RationalVectorSpace

/-- Real scalar extension preserves joint detection of the SAME original
integer family. Rationalization and the scalar tower are constructed internally. -/
theorem realFunctional_jointly_detects (f : ι → M →ₗ[ℤ] ℤ)
    (hf : ∀ m : M, (∀ i, f i m = 0) → m = 0)
    (x : ℝ ⊗[ℤ] M) (hx : ∀ i, realFunctional (f i) x = 0) : x = 0 := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ M
  have hc (i : ι) :
      (realOfRationalFunctional (rationalFunctional (f i))).comp e.symm.toLinearMap =
        realFunctional (f i) := by
    ext m
    simp [e]
  have hq : ∀ i, realOfRationalFunctional (rationalFunctional (f i)) (e.symm x) = 0 := by
    intro i
    have h := congrArg (fun l => l x) (hc i)
    exact h.trans (hx i)
  have hz := realOfRational_jointly_detects (fun i => rationalFunctional (f i))
    (fun y hy => rationalFunctional_jointly_detects f hf y hy) (e.symm x) hq
  apply e.symm.injective
  simpa only [map_zero] using hz



/-- The WHOLE original integer degree vector. -/
def integerVector (f : ι → M →ₗ[ℤ] ℤ) : M →ₗ[ℤ] (ι → ℤ) := LinearMap.pi f

/-- The original simultaneous integer degree kernel. -/
def integerKernel (f : ι → M →ₗ[ℤ] ℤ) : Submodule ℤ M := (integerVector f).ker

/-- The actual original integer-kernel quotient. -/
abbrev IntegerQuotient (f : ι → M →ₗ[ℤ] ℤ) := M ⧸ integerKernel f

/-- Every SAME original degree descends to the actual integer quotient. -/
def quotientIntegerFunctional (f : ι → M →ₗ[ℤ] ℤ) (i : ι) :
    IntegerQuotient f →ₗ[ℤ] ℤ :=
  (integerKernel f).liftQ (f i) (by
    intro m hm
    exact congrFun hm i)

@[simp]
theorem quotientIntegerFunctional_mk (f : ι → M →ₗ[ℤ] ℤ) (i : ι) (m : M) :
    quotientIntegerFunctional f i ((integerKernel f).mkQ m) = f i m := rfl

/-- Integer separation on the quotient is PRODUCED from its literal kernel,
not provided as a numerical-matching assumption. -/
theorem quotientIntegerFunctional_jointly_detects (f : ι → M →ₗ[ℤ] ℤ)
    (x : IntegerQuotient f) (hx : ∀ i, quotientIntegerFunctional f i x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ := (integerKernel f).mkQ_surjective x
  change Submodule.Quotient.mk m = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change integerVector f m = 0
  ext i
  exact hx i

/-- The WHOLE original real-extended degree vector. -/
def realVector (f : ι → M →ₗ[ℤ] ℤ) : ℝ ⊗[ℤ] M →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi fun i => realFunctional (f i)

/-- The actual real scalar extension quotient by every SAME original degree. -/
abbrev RealQuotient (f : ι → M →ₗ[ℤ] ℤ) := (ℝ ⊗[ℤ] M) ⧸ (realVector f).ker

/-- Joint original integer detection gives actual real vector injectivity. -/
theorem realVector_injective (f : ι → M →ₗ[ℤ] ℤ)
    (hf : ∀ m : M, (∀ i, f i m = 0) → m = 0) :
    Function.Injective (realVector f) := by
  intro x y h
  apply sub_eq_zero.mp
  apply realFunctional_jointly_detects f hf
  intro i
  rw [map_sub]
  apply sub_eq_zero.mpr
  exact congrFun h i

/-- The SAME original integer quotient map on its real scalar extension. -/
def tensorProjection (f : ι → M →ₗ[ℤ] ℤ) :
    ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] IntegerQuotient f :=
  (integerKernel f).mkQ.baseChange ℝ

@[simp]
theorem tensorProjection_tmul (f : ι → M →ₗ[ℤ] ℤ) (r : ℝ) (m : M) :
    tensorProjection f (r ⊗ₜ[ℤ] m) = r ⊗ₜ[ℤ] (integerKernel f).mkQ m := rfl

/-- Every actual real quotient tensor lifts through the original quotient. -/
theorem tensorProjection_surjective (f : ι → M →ₗ[ℤ] ℤ) :
    Function.Surjective (tensorProjection f) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul r q =>
      obtain ⟨m, rfl⟩ := (integerKernel f).mkQ_surjective q
      exact ⟨r ⊗ₜ[ℤ] m, rfl⟩
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩

/-- The real degree vector retains the literal original quotient triangle. -/
theorem realVector_tensorProjection (f : ι → M →ₗ[ℤ] ℤ) :
    (realVector (quotientIntegerFunctional f)).comp (tensorProjection f) = realVector f := by
  ext m i
  rfl

/-- The kernel equality is proved from the SAME original degrees and internal
integer-quotient separation, with no external matching condition. -/
theorem tensorProjection_ker (f : ι → M →ₗ[ℤ] ℤ) :
    (tensorProjection f).ker = (realVector f).ker := by
  have hi := realVector_injective (quotientIntegerFunctional f)
    (quotientIntegerFunctional_jointly_detects f)
  have hk : (realVector (quotientIntegerFunctional f)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hi
  rw [← realVector_tensorProjection, LinearMap.ker_comp, hk, Submodule.comap_bot]

/-- The SAME original integer common-kernel quotient and original real
common-kernel quotient are canonically equivalent after scalar extension. -/
def quotientComparison (f : ι → M →ₗ[ℤ] ℤ) :
    RealQuotient f ≃ₗ[ℝ] ℝ ⊗[ℤ] IntegerQuotient f :=
  (Submodule.quotEquivOfEq _ _ (tensorProjection_ker f).symm) ≪≫ₗ
    (tensorProjection f).quotKerEquivOfSurjective (tensorProjection_surjective f)

/-- The comparison preserves EVERY original tensor and its original class. -/
theorem quotientComparison_mk_tmul (f : ι → M →ₗ[ℤ] ℤ) (r : ℝ) (m : M) :
    quotientComparison f (Submodule.Quotient.mk (r ⊗ₜ[ℤ] m)) =
      r ⊗ₜ[ℤ] (integerKernel f).mkQ m := by
  simp [quotientComparison]

end SGPT.Foundations.Envelope.NativeNumericalCarrierComparison
