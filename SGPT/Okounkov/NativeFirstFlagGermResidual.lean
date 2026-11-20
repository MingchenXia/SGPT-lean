import SGPT.Okounkov.NativeFirstFlagGermOrder

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Actual natural multiplicity of the SAME selected original equation.
Its agreement with first order is asserted for nonzero original germs. -/
def originalFirstFlagGermOrderNat {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) : ℕ :=
  multiplicity (originalFirstFlagGermParameter F x) f

theorem originalFirstFlagGermOrderNat_spec {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    originalFirstFlagGermOrder F x f = (originalFirstFlagGermOrderNat F x f : ℕ∞) := by
  have hfinite : FiniteMultiplicity (originalFirstFlagGermParameter F x) f :=
    finiteMultiplicity_iff_emultiplicity_ne_top.mpr fun h =>
      hf ((originalFirstFlagGermOrder_eq_top_iff F x f).mp h)
  exact hfinite.emultiplicity_eq_multiplicity

private theorem exists_fixedOrderQuotient {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    ∃ q : NativeHolGerm (m + 1) F.carrier x.1,
      f = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f * q ∧
      originalFirstFlagGermRestriction F x q ≠ 0 := by
  obtain ⟨a, q, hfac, hres, hvalue, _⟩ := exists_originalFirstFlagGermOrder_division F x f hf
  have ha : a = originalFirstFlagGermOrderNat F x f :=
    ENat.natCast_inj.mp (hvalue.symm.trans (originalFirstFlagGermOrderNat_spec F x f hf))
  exact ⟨q, ha ▸ hfac, hres⟩

/-- The actual quotient of a nonzero original germ by its SAME maximal
selected equation power, internally produced from true fixed-order division. -/
def originalFirstFlagGermQuotient {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    NativeHolGerm (m + 1) F.carrier x.1 :=
  Classical.choose (exists_fixedOrderQuotient F x f hf)

theorem originalFirstFlagGermQuotient_spec {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    f = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
      originalFirstFlagGermQuotient F x f hf ∧
      originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x f hf) ≠ 0 :=
  Classical.choose_spec (exists_fixedOrderQuotient F x f hf)

/-- Whole quotient uniqueness follows by actual nonzero cancellation, so
the quotient does not depend on a supplied division witness. -/
theorem originalFirstFlagGermQuotient_unique {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0)
    (q : NativeHolGerm (m + 1) F.carrier x.1)
    (hq : f = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f * q) :
    originalFirstFlagGermQuotient F x f hf = q :=
  mul_left_cancel₀ (pow_ne_zero _ (originalFirstFlagGermParameter_spec F x).1.ne_zero)
    ((originalFirstFlagGermQuotient_spec F x f hf).1.symm.trans hq)

/-- The actual nonzero ORIGINAL tail residual, by literal restriction of the
actual original quotient. No residual value is an input. -/
def originalFirstFlagGermResidual {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    NativeHolGerm m F.tail.carrier x :=
  originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x f hf)

theorem originalFirstFlagGermResidual_ne_zero {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    originalFirstFlagGermResidual F x f hf ≠ 0 :=
  (originalFirstFlagGermQuotient_spec F x f hf).2

theorem originalFirstFlagGermOrderNat_mul {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFirstFlagGermOrderNat F x (f * g) =
      originalFirstFlagGermOrderNat F x f + originalFirstFlagGermOrderNat F x g := by
  apply ENat.natCast_inj.mp
  calc
    (originalFirstFlagGermOrderNat F x (f * g) : ℕ∞) = originalFirstFlagGermOrder F x (f * g) :=
      (originalFirstFlagGermOrderNat_spec F x (f * g) (mul_ne_zero hf hg)).symm
    _ = originalFirstFlagGermOrder F x f + originalFirstFlagGermOrder F x g :=
      (originalFirstFlagGermOrder F x).map_mul f g
    _ = ((originalFirstFlagGermOrderNat F x f + originalFirstFlagGermOrderNat F x g : ℕ) : ℕ∞) := by
      rw [originalFirstFlagGermOrderNat_spec F x f hf,
        originalFirstFlagGermOrderNat_spec F x g hg, ENat.natCast_add]

theorem originalFirstFlagGermQuotient_mul {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFirstFlagGermQuotient F x (f * g) (mul_ne_zero hf hg) =
      originalFirstFlagGermQuotient F x f hf * originalFirstFlagGermQuotient F x g hg := by
  apply originalFirstFlagGermQuotient_unique
  rw [originalFirstFlagGermOrderNat_mul F x f g hf hg]
  calc
    f * g = (originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
        originalFirstFlagGermQuotient F x f hf) *
      (originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x g *
        originalFirstFlagGermQuotient F x g hg) :=
      congrArg₂ (fun a b => a * b) (originalFirstFlagGermQuotient_spec F x f hf).1
        (originalFirstFlagGermQuotient_spec F x g hg).1
    _ = _ := by rw [pow_add]; ring

theorem originalFirstFlagGermResidual_mul {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0) :
    originalFirstFlagGermResidual F x (f * g) (mul_ne_zero hf hg) =
      originalFirstFlagGermResidual F x f hf * originalFirstFlagGermResidual F x g hg := by
  change originalFirstFlagGermRestriction F x
      (originalFirstFlagGermQuotient F x (f * g) (mul_ne_zero hf hg)) = _
  rw [originalFirstFlagGermQuotient_mul F x f g hf hg, map_mul]
  rfl

theorem originalFirstFlagGermOrderNat_le_add_of_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0)
    (heq : originalFirstFlagGermOrderNat F x f = originalFirstFlagGermOrderNat F x g) :
    originalFirstFlagGermOrderNat F x f ≤ originalFirstFlagGermOrderNat F x (f + g) := by
  have h := (originalFirstFlagGermOrder F x).map_add f g
  rw [originalFirstFlagGermOrderNat_spec F x f hf,
    originalFirstFlagGermOrderNat_spec F x g hg,
    originalFirstFlagGermOrderNat_spec F x (f + g) hs, heq, min_self] at h
  rw [heq]
  exact_mod_cast h

theorem originalFirstFlagGermQuotient_add_of_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0)
    (heq : originalFirstFlagGermOrderNat F x f = originalFirstFlagGermOrderNat F x g)
    (hsame : originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f) :
    originalFirstFlagGermQuotient F x (f + g) hs =
      originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermQuotient F x g hg := by
  apply originalFirstFlagGermQuotient_unique
  rw [hsame]
  calc
    f + g = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
        originalFirstFlagGermQuotient F x f hf +
      originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x g *
        originalFirstFlagGermQuotient F x g hg :=
      congrArg₂ (fun a b => a + b) (originalFirstFlagGermQuotient_spec F x f hf).1
        (originalFirstFlagGermQuotient_spec F x g hg).1
    _ = _ := by rw [heq, mul_add]

theorem originalFirstFlagGermResidual_add_of_eq {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0)
    (heq : originalFirstFlagGermOrderNat F x f = originalFirstFlagGermOrderNat F x g)
    (hsame : originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f) :
    originalFirstFlagGermResidual F x (f + g) hs =
      originalFirstFlagGermResidual F x f hf + originalFirstFlagGermResidual F x g hg := by
  change originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x (f + g) hs) = _
  rw [originalFirstFlagGermQuotient_add_of_eq F x f g hf hg hs heq hsame, map_add]
  rfl

end SGPT.Okounkov
