import SGPT.Okounkov.NativeFirstFlagGermSumResidual
import Mathlib.Algebra.Order.Group.PiLex
import Mathlib.Order.Fin.Tuple

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- An actual member of the ORIGINAL last flag carrier, whose singleton and
nonemptiness are produced by original smooth connected flag geometry. -/
abbrev OriginalFlagGermPoint {n : ℕ} (F : OriginalFlagGeometry.{u} n) := F.flag (Fin.last n)

namespace OriginalFlagGermPoint

instance nonempty {n : ℕ} (F : OriginalFlagGeometry.{u} n) : Nonempty (OriginalFlagGermPoint F) := by
  obtain ⟨x, hx⟩ := F.smooth.last_eq_singleton
  refine ⟨⟨x, ?_⟩⟩
  change x ∈ F.flag (Fin.last n)
  rw [hx]
  exact mem_singleton x

/-- Original nesting puts the SAME endpoint in the actual first divisor. -/
def first {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : OriginalFlagGermPoint F) : F.tail.carrier :=
  ⟨x.1, F.smooth.2.1 (Fin.le_last (1 : Fin (m + 2))) x.property⟩

/-- The SAME original endpoint is the last endpoint of the ORIGINAL tail
flag, in its literal inherited-atlas subtype carrier. -/
def tail {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : OriginalFlagGermPoint F) : OriginalFlagGermPoint F.tail :=
  ⟨first F x, x.property⟩

end OriginalFlagGermPoint

/-- The WHOLE actual original flag vector, by dimension recursion on the
SAME internally manufactured nonzero literal ORIGINAL tail residuals. -/
def originalFlagGermVector : {n : ℕ} → (F : OriginalFlagGeometry.{u} n) →
    (x : OriginalFlagGermPoint F) →
    (f : NativeHolGerm n F.carrier x.1) → f ≠ 0 → Fin n → ℕ
  | 0, _, _, _, _ => Fin.elim0
  | _m + 1, F, x, f, hf =>
    Fin.cons (originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) f)
      (originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) f hf))

/-- The actual original recursive tuple as a lexicographically ordered
integer vector, retaining literal component values. -/
def originalFlagGermLexVector {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) :
    Lex (Fin n → ℤ) :=
  toLex fun i => (originalFlagGermVector F x f hf i : ℤ)

private theorem vector_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (heq : f = g) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  subst g
  rfl

private theorem firstOrderNat_one {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) : originalFirstFlagGermOrderNat F x 1 = 0 :=
  ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F x 1 one_ne_zero).symm.trans
    (originalFirstFlagGermOrder F x).map_one)

private theorem firstQuotient_one {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) : originalFirstFlagGermQuotient F x 1 one_ne_zero = 1 := by
  apply originalFirstFlagGermQuotient_unique
  rw [firstOrderNat_one, pow_zero, one_mul]

private theorem firstResidual_one {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) : originalFirstFlagGermResidual F x 1 one_ne_zero = 1 := by
  change originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x 1 one_ne_zero) = 1
  rw [firstQuotient_one, map_one]

theorem originalFlagGermVector_one {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) : originalFlagGermVector F x 1 one_ne_zero = 0 := by
  induction n with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact firstOrderNat_one F (OriginalFlagGermPoint.first F x)
    · change originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) 1 one_ne_zero)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) 1 one_ne_zero) j = 0
      have hc := vector_congr F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) 1 one_ne_zero) 1
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) 1 one_ne_zero)
        one_ne_zero (firstResidual_one F (OriginalFlagGermPoint.first F x))
      exact (congrFun hc j).trans (congrFun (ih F.tail (OriginalFlagGermPoint.tail F x)) j)

/-- Actual original exponents and literal tail residual product laws give
addition of the WHOLE original recursive nonzero tuple, with no valuation
law or value tuple certificate supplied. -/
theorem originalFlagGermVector_mul {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFlagGermVector F x (f * g) (mul_ne_zero hf hg) =
      originalFlagGermVector F x f hf + originalFlagGermVector F x g hg := by
  induction n with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ m ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact originalFirstFlagGermOrderNat_mul F (OriginalFlagGermPoint.first F x) f g hf hg
    · have hfg : f * g ≠ 0 := mul_ne_zero hf hg
      change originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) (f * g) hfg)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x)
          (f * g) hfg) j =
        originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
          (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf)
          (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) f hf) j +
        originalFlagGermVector F.tail (OriginalFlagGermPoint.tail F x)
          (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) g hg)
          (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) g hg) j
      have hprodNe : originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf *
          originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) g hg ≠ 0 := by
        intro hz
        exact originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) (f * g) hfg
          ((originalFirstFlagGermResidual_mul F (OriginalFlagGermPoint.first F x) f g hf hg).trans hz)
      have hc := vector_congr F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) (f * g) hfg)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf *
          originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) g hg)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) (f * g) hfg)
        hprodNe
        (originalFirstFlagGermResidual_mul F (OriginalFlagGermPoint.first F x) f g hf hg)
      exact (congrFun hc j).trans (congrFun (ih F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) f hf)
        (originalFirstFlagGermResidual F (OriginalFlagGermPoint.first F x) g hg)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) f hf)
        (originalFirstFlagGermResidual_ne_zero F (OriginalFlagGermPoint.first F x) g hg)) j)

end SGPT.Okounkov
