import SGPT.Okounkov.NativeFlagGermLeaves

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff nonZeroDivisors
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- Equal genuine LOCAL fraction values admit actual scalar cancellation,
by clearing original denominators and using genuine original germ leaves.
The scalar embedding is the literal original constant-germ injection. -/
theorem exists_originalFlagGermFraction_scalar_cancel {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (q r : FractionRing (NativeHolGerm n F.carrier x.1))
    (hqne : q ≠ 0) (hrne : r ≠ 0)
    (hvalue : originalFlagGermFractionValuation F x q = originalFlagGermFractionValuation F x r) :
    ∃ c : ℂ, c ≠ 0 ∧ originalFlagGermFractionValuation F x q <
      originalFlagGermFractionValuation F x (q +
        algebraMap (NativeHolGerm n F.carrier x.1)
          (FractionRing (NativeHolGerm n F.carrier x.1)) (NativeHolGerm.constHom c) * r) := by
  let R := NativeHolGerm n F.carrier x.1
  let K := FractionRing R
  let j : R →+* K := algebraMap R K
  let v := originalFlagGermFractionValuation F x
  obtain ⟨f, d, hd, hq⟩ := IsFractionRing.div_surjective R q
  obtain ⟨g, e, he, hr⟩ := IsFractionRing.div_surjective R r
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
  have hdK : j d ≠ 0 := (map_ne_zero_iff j (IsFractionRing.injective R K)).mpr hd0
  have heK : j e ≠ 0 := (map_ne_zero_iff j (IsFractionRing.injective R K)).mpr he0
  have hf : f ≠ 0 := by
    intro hz
    apply hqne
    rw [← hq, hz, map_zero, zero_div]
  have hg : g ≠ 0 := by
    intro hz
    apply hrne
    rw [← hr, hz, map_zero, zero_div]
  let a : R := f * e
  let b : R := g * d
  let s : R := d * e
  have ha : a ≠ 0 := mul_ne_zero hf he0
  have hb : b ≠ 0 := mul_ne_zero hg hd0
  have hA : j a = q * j s := by
    rw [← hq]
    change j (f * e) = (j f / j d) * j (d * e)
    rw [map_mul, map_mul]
    rw [← mul_assoc, div_mul_cancel₀ _ hdK]
  have hB : j b = r * j s := by
    rw [← hr]
    change j (g * d) = (j g / j e) * j (d * e)
    rw [map_mul, map_mul]
    rw [mul_comm (j d) (j e), ← mul_assoc, div_mul_cancel₀ _ heK]
  have hAv : originalFlagGermValuation F x a = v q + v (j s) := by
    rw [← originalFlagGermFractionValuation_algebraMap F x a]
    change v (j a) = _
    rw [hA, v.map_mul]
  have hBv : originalFlagGermValuation F x b = v r + v (j s) := by
    rw [← originalFlagGermFractionValuation_algebraMap F x b]
    change v (j b) = _
    rw [hB, v.map_mul]
  have habval : originalFlagGermValuation F x a = originalFlagGermValuation F x b := by
    rw [hAv, hBv]
    exact congrArg (fun t => t + v (j s)) hvalue
  rw [originalFlagGermValuation_apply_of_ne_zero F x a ha,
    originalFlagGermValuation_apply_of_ne_zero F x b hb] at habval
  have hablex := WithTop.coe_injective habval
  have hab : originalFlagGermVector F x a ha = originalFlagGermVector F x b hb := by
    funext i
    have hi := congrFun hablex i
    change (originalFlagGermVector F x a ha i : ℤ) = (originalFlagGermVector F x b hb i : ℤ) at hi
    exact_mod_cast hi
  obtain ⟨c, hc, hcancel⟩ := exists_originalFlagGerm_scalar_cancel F x a b ha hb hab
  have hcommon : j (a + NativeHolGerm.constHom c * b) =
      (q + j (NativeHolGerm.constHom c) * r) * j s := by
    rw [map_add, map_mul j (NativeHolGerm.constHom c) b, hA, hB]
    ring
  have hsumv : originalFlagGermValuation F x (a + NativeHolGerm.constHom c * b) =
      v (q + j (NativeHolGerm.constHom c) * r) + v (j s) := by
    rw [← originalFlagGermFractionValuation_algebraMap F x (a + NativeHolGerm.constHom c * b)]
    change v (j (a + NativeHolGerm.constHom c * b)) = _
    rw [hcommon, v.map_mul]
  refine ⟨c, hc, ?_⟩
  have hstrict : v q + v (j s) < v (q + j (NativeHolGerm.constHom c) * r) + v (j s) := by
    rw [← hAv, ← hsumv]
    exact hcancel
  exact lt_of_add_lt_add_right hstrict

end SGPT.Okounkov
