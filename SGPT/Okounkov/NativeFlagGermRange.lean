import SGPT.Okounkov.NativeFlagGermValuation

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

private theorem vector_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f g : NativeHolGerm n F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (h : f = g) :
    originalFlagGermVector F x f hf = originalFlagGermVector F x g hg := by
  subst g
  rfl

/-- The SAME internally selected original first equation has exactly the
first standard basis vector, including all of its true residual entries. -/
theorem originalFlagGermVector_parameter {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F) :
    originalFlagGermVector F x
      (originalFirstFlagGermParameter F (OriginalFlagGermPoint.first F x))
      (originalFirstFlagGermParameter_spec F (OriginalFlagGermPoint.first F x)).1.ne_zero =
      Fin.cons (α := fun _ : Fin (m + 1) => ℕ) 1 0 := by
  let y := OriginalFlagGermPoint.first F x
  let t := originalFirstFlagGermParameter F y
  have ht : t ≠ 0 := (originalFirstFlagGermParameter_spec F y).1.ne_zero
  have htval : originalFirstFlagGermOrder F y t = (1 : ℕ∞) := by
    change emultiplicity (originalFirstFlagGermParameter F y) (originalFirstFlagGermParameter F y) = 1
    simpa using
      emultiplicity_pow_self_of_prime (originalFirstFlagGermParameter_spec F y).1 1
  have ha : originalFirstFlagGermOrderNat F y t = 1 :=
    ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F y t ht).symm.trans htval)
  have hq : originalFirstFlagGermQuotient F y t ht = 1 := by
    apply originalFirstFlagGermQuotient_unique
    rw [ha, pow_one, mul_one]
  have hr : originalFirstFlagGermResidual F y t ht = 1 := by
    change originalFirstFlagGermRestriction F y (originalFirstFlagGermQuotient F y t ht) = 1
    rw [hq, map_one]
  funext i
  refine Fin.cases ha (fun j => ?_) i
  have hc := vector_congr F.tail (OriginalFlagGermPoint.tail F x)
    (originalFirstFlagGermResidual F y t ht) 1
    (originalFirstFlagGermResidual_ne_zero F y t ht) one_ne_zero hr
  exact (congrFun hc j).trans
    (congrFun (originalFlagGermVector_one F.tail (OriginalFlagGermPoint.tail F x)) j)

/-- Every natural tuple is internally attained by a genuine nonzero
ORIGINAL holomorphic germ, using actual local holomorphic extension along
the literal original first restriction at each stage. -/
theorem originalFlagGermVector_nat_surjective {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F) (b : Fin n → ℕ) :
    ∃ (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0), originalFlagGermVector F x f hf = b := by
  induction n with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      funext i
      exact Fin.elim0 i
  | succ m ih =>
      let y := OriginalFlagGermPoint.first F x
      obtain ⟨g, hg, hb⟩ := ih F.tail (OriginalFlagGermPoint.tail F x) (fun i => b i.succ)
      obtain ⟨h, hh⟩ := originalFirstFlagGermRestriction_surjective F y g
      have hres : originalFirstFlagGermRestriction F y h ≠ 0 := by
        rw [hh]
        exact hg
      have hhval := (originalFirstFlagGermOrder_eq_zero_iff F y h).mpr hres
      have hhne : h ≠ 0 := by
        intro hz
        exact hres (hz ▸ map_zero _)
      let t := originalFirstFlagGermParameter F y
      have ht := (originalFirstFlagGermParameter_spec F y).1
      have hf : t ^ b 0 * h ≠ 0 := mul_ne_zero (pow_ne_zero _ ht.ne_zero) hhne
      have hvalue : originalFirstFlagGermOrder F y (t ^ b 0 * h) = (b 0 : ℕ∞) := by
        rw [(originalFirstFlagGermOrder F y).map_mul,
          show originalFirstFlagGermOrder F y (t ^ b 0) = (b 0 : ℕ∞) from
            emultiplicity_pow_self_of_prime ht _, hhval, add_zero]
      have ha : originalFirstFlagGermOrderNat F y (t ^ b 0 * h) = b 0 :=
        ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F y _ hf).symm.trans hvalue)
      have hq : originalFirstFlagGermQuotient F y (t ^ b 0 * h) hf = h := by
        apply originalFirstFlagGermQuotient_unique
        rw [ha]
      have hr : originalFirstFlagGermResidual F y (t ^ b 0 * h) hf = g := by
        change originalFirstFlagGermRestriction F y
          (originalFirstFlagGermQuotient F y (t ^ b 0 * h) hf) = g
        rw [hq, hh]
      refine ⟨t ^ b 0 * h, hf, ?_⟩
      funext i
      refine Fin.cases ha (fun j => ?_) i
      have hc := vector_congr F.tail (OriginalFlagGermPoint.tail F x)
        (originalFirstFlagGermResidual F y (t ^ b 0 * h) hf) g
        (originalFirstFlagGermResidual_ne_zero F y (t ^ b 0 * h) hf) hg hr
      exact (congrFun hc j).trans (congrFun hb j)

end SGPT.Okounkov
