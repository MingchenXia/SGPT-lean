import SGPT.Okounkov.NativeFirstFlagGermResidual

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Unequal actual original first orders internally produce a nonzero sum,
the lower first order, its SAME-equation quotient and the literal lower
residual. No nonzero-sum/order/residual certificate is supplied. -/
theorem exists_originalFirstFlagGermResidual_add_of_lt {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0)
    (hlt : originalFirstFlagGermOrderNat F x f < originalFirstFlagGermOrderNat F x g) :
    ∃ hs : f + g ≠ 0,
      originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f ∧
      originalFirstFlagGermQuotient F x (f + g) hs =
        originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermParameter F x ^
          (originalFirstFlagGermOrderNat F x g - originalFirstFlagGermOrderNat F x f) *
          originalFirstFlagGermQuotient F x g hg ∧
      originalFirstFlagGermResidual F x (f + g) hs = originalFirstFlagGermResidual F x f hf := by
  have hcmp : originalFirstFlagGermOrder F x f < originalFirstFlagGermOrder F x g := by
    rw [originalFirstFlagGermOrderNat_spec F x f hf, originalFirstFlagGermOrderNat_spec F x g hg]
    exact_mod_cast hlt
  have hvalue := (originalFirstFlagGermOrder F x).map_add_eq_of_lt_left hcmp
  have hs : f + g ≠ 0 := by
    intro hzero
    have htop := (originalFirstFlagGermOrder_eq_top_iff F x (f + g)).mpr hzero
    exact hf ((originalFirstFlagGermOrder_eq_top_iff F x f).mp (hvalue.symm.trans htop))
  have hNat : originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f :=
    ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F x (f + g) hs).symm.trans
      (hvalue.trans (originalFirstFlagGermOrderNat_spec F x f hf)))
  have hfactor : f + g = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
      (originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermParameter F x ^
        (originalFirstFlagGermOrderNat F x g - originalFirstFlagGermOrderNat F x f) *
        originalFirstFlagGermQuotient F x g hg) := by
    calc
      f + g = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
          originalFirstFlagGermQuotient F x f hf +
        originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x g *
          originalFirstFlagGermQuotient F x g hg :=
        congrArg₂ (fun a b => a + b) (originalFirstFlagGermQuotient_spec F x f hf).1
          (originalFirstFlagGermQuotient_spec F x g hg).1
      _ = _ := by
        rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hlt.le]
  have hquot : originalFirstFlagGermQuotient F x (f + g) hs =
      originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermParameter F x ^
        (originalFirstFlagGermOrderNat F x g - originalFirstFlagGermOrderNat F x f) *
        originalFirstFlagGermQuotient F x g hg := by
    apply originalFirstFlagGermQuotient_unique
    rw [hNat]
    exact hfactor
  have htmem : originalFirstFlagGermParameter F x ∈
      RingHom.ker (originalFirstFlagGermRestriction F x) := by
    rw [(originalFirstFlagGermParameter_spec F x).2.2]
    exact Ideal.subset_span (Set.mem_singleton _)
  have htres : originalFirstFlagGermRestriction F x (originalFirstFlagGermParameter F x) = 0 := htmem
  refine ⟨hs, hNat, hquot, ?_⟩
  change originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x (f + g) hs) =
    originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x f hf)
  rw [hquot, map_add, map_mul, map_pow, htres,
    zero_pow (Nat.sub_pos_of_lt hlt).ne', zero_mul, add_zero]

/-- Equal first orders and NONZERO computed original tail residual sum
internally produce the actual nonzero sum, its unchanged first order and
literal tail sum. No sum witness/order/residual identity is input. -/
theorem exists_originalFirstFlagGermResidual_add_of_eq_ne_zero {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0)
    (heq : originalFirstFlagGermOrderNat F x f = originalFirstFlagGermOrderNat F x g)
    (hres : originalFirstFlagGermResidual F x f hf + originalFirstFlagGermResidual F x g hg ≠ 0) :
    ∃ hs : f + g ≠ 0,
      originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f ∧
      originalFirstFlagGermResidual F x (f + g) hs =
        originalFirstFlagGermResidual F x f hf + originalFirstFlagGermResidual F x g hg := by
  have hresq : originalFirstFlagGermRestriction F x
      (originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermQuotient F x g hg) ≠ 0 := by
    change originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x f hf) +
      originalFirstFlagGermRestriction F x (originalFirstFlagGermQuotient F x g hg) ≠ 0 at hres
    simpa only [map_add] using hres
  have hqne : originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermQuotient F x g hg ≠ 0 := by
    intro hz
    exact hresq (hz ▸ map_zero _)
  have hfactor : f + g = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
      (originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermQuotient F x g hg) := by
    calc
      f + g = originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f *
          originalFirstFlagGermQuotient F x f hf +
        originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x g *
          originalFirstFlagGermQuotient F x g hg :=
        congrArg₂ (fun a b => a + b) (originalFirstFlagGermQuotient_spec F x f hf).1
          (originalFirstFlagGermQuotient_spec F x g hg).1
      _ = _ := by rw [heq, mul_add]
  have hs : f + g ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero (pow_ne_zero _ (originalFirstFlagGermParameter_spec F x).1.ne_zero) hqne
  have hqvalue := (originalFirstFlagGermOrder_eq_zero_iff F x
    (originalFirstFlagGermQuotient F x f hf + originalFirstFlagGermQuotient F x g hg)).mpr hresq
  have hpowvalue : originalFirstFlagGermOrder F x
      (originalFirstFlagGermParameter F x ^ originalFirstFlagGermOrderNat F x f) =
        (originalFirstFlagGermOrderNat F x f : ℕ∞) :=
    emultiplicity_pow_self_of_prime (originalFirstFlagGermParameter_spec F x).1 _
  have hvalue : originalFirstFlagGermOrder F x (f + g) =
      (originalFirstFlagGermOrderNat F x f : ℕ∞) := by
    rw [hfactor, (originalFirstFlagGermOrder F x).map_mul, hpowvalue, hqvalue, add_zero]
  have hNat : originalFirstFlagGermOrderNat F x (f + g) = originalFirstFlagGermOrderNat F x f :=
    ENat.natCast_inj.mp ((originalFirstFlagGermOrderNat_spec F x (f + g) hs).symm.trans hvalue)
  exact ⟨hs, hNat, originalFirstFlagGermResidual_add_of_eq F x f g hf hg hs heq hNat⟩

/-- Actual leading residual cancellation forces strict increase of the
original first order for a nonzero tied-order sum. -/
theorem originalFirstFlagGermOrderNat_lt_add_of_residual_cancel {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f g : NativeHolGerm (m + 1) F.carrier x.1)
    (hf : f ≠ 0) (hg : g ≠ 0) (hs : f + g ≠ 0)
    (heq : originalFirstFlagGermOrderNat F x f = originalFirstFlagGermOrderNat F x g)
    (hcancel : originalFirstFlagGermResidual F x f hf + originalFirstFlagGermResidual F x g hg = 0) :
    originalFirstFlagGermOrderNat F x f < originalFirstFlagGermOrderNat F x (f + g) := by
  have hle := originalFirstFlagGermOrderNat_le_add_of_eq F x f g hf hg hs heq
  have hne : originalFirstFlagGermOrderNat F x (f + g) ≠ originalFirstFlagGermOrderNat F x f := by
    intro hsame
    have hres := originalFirstFlagGermResidual_add_of_eq F x f g hf hg hs heq hsame
    exact originalFirstFlagGermResidual_ne_zero F x (f + g) hs (hres.trans hcancel)
  omega

end SGPT.Okounkov
