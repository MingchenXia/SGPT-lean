import SGPT.Okounkov.NativeFlagGermFractionValuation

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

/-- Actual invertibility and natural product components force the entire
original flag vector of every actual original unit to vanish. -/
theorem originalFlagGermVector_eq_zero_of_isUnit {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) (hu : IsUnit f) :
    originalFlagGermVector F x f hf = 0 := by
  obtain ⟨u, rfl⟩ := hu
  have hinv : ((u⁻¹ : (NativeHolGerm n F.carrier x.1)ˣ) : NativeHolGerm n F.carrier x.1) ≠ 0 :=
    Units.ne_zero _
  have hprod := originalFlagGermVector_mul F x (u : NativeHolGerm n F.carrier x.1)
    (u⁻¹ : (NativeHolGerm n F.carrier x.1)ˣ) hf hinv
  have hc := vector_congr F x _ 1 (mul_ne_zero hf hinv) one_ne_zero (Units.mul_inv u)
  have hsum := hprod.symm.trans (hc.trans (originalFlagGermVector_one F x))
  funext i
  exact (Nat.add_eq_zero_iff.mp (congrFun hsum i)).1

theorem NativeHolGerm.const_ne_zero {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {x : M} (c : ℂ) (hc : c ≠ 0) :
    (NativeHolGerm.constHom c : NativeHolGerm n M x) ≠ 0 := by
  intro hz
  have h := congrArg NativeHolGerm.eval hz
  exact hc h

theorem originalFlagGermVector_const {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (c : ℂ) (hc : c ≠ 0) :
    originalFlagGermVector F x (NativeHolGerm.constHom c)
      (NativeHolGerm.const_ne_zero c hc) = 0 :=
  originalFlagGermVector_eq_zero_of_isUnit F x _ (NativeHolGerm.const_ne_zero c hc)
    ((isUnit_iff_ne_zero.mpr hc).map NativeHolGerm.constHom)

theorem originalFlagGermValuation_const {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (c : ℂ) (hc : c ≠ 0) :
    originalFlagGermValuation F x (NativeHolGerm.constHom c) = 0 := by
  rw [originalFlagGermValuation_apply_of_ne_zero F x _ (NativeHolGerm.const_ne_zero c hc)]
  change ((toLex (fun i => (originalFlagGermVector F x (NativeHolGerm.constHom c)
    (NativeHolGerm.const_ne_zero c hc) i : ℤ)) : Lex (Fin n → ℤ)) :
      WithTop (Lex (Fin n → ℤ))) = 0
  rw [originalFlagGermVector_const F x c hc]
  rfl

theorem originalFirstFlagGermRestriction_const {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) (c : ℂ) :
    originalFirstFlagGermRestriction F x (NativeHolGerm.constHom c) = NativeHolGerm.constHom c :=
  rfl

private theorem firstConstOrderNat {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) (c : ℂ) (hc : c ≠ 0) :
    originalFirstFlagGermOrderNat F x (NativeHolGerm.constHom c) = 0 := by
  have hres : originalFirstFlagGermRestriction F x (NativeHolGerm.constHom c) ≠ 0 := by
    rw [originalFirstFlagGermRestriction_const]
    exact NativeHolGerm.const_ne_zero c hc
  apply ENat.natCast_inj.mp
  exact (originalFirstFlagGermOrderNat_spec F x _ (NativeHolGerm.const_ne_zero c hc)).symm.trans
    ((originalFirstFlagGermOrder_eq_zero_iff F x _).mpr hres)

private theorem firstConstResidual {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (x : F.tail.carrier) (c : ℂ) (hc : c ≠ 0) :
    originalFirstFlagGermResidual F x (NativeHolGerm.constHom c)
      (NativeHolGerm.const_ne_zero c hc) = NativeHolGerm.constHom c := by
  have hq : originalFirstFlagGermQuotient F x (NativeHolGerm.constHom c)
      (NativeHolGerm.const_ne_zero c hc) = NativeHolGerm.constHom c := by
    apply originalFirstFlagGermQuotient_unique
    rw [firstConstOrderNat F x c hc, pow_zero, one_mul]
  change originalFirstFlagGermRestriction F x
    (originalFirstFlagGermQuotient F x (NativeHolGerm.constHom c)
      (NativeHolGerm.const_ne_zero c hc)) = NativeHolGerm.constHom c
  rw [hq, originalFirstFlagGermRestriction_const]

theorem originalFirstFlagGermResidual_const_mul {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (c : ℂ) (hc : c ≠ 0) (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    originalFirstFlagGermResidual F x (NativeHolGerm.constHom c * f)
      (mul_ne_zero (NativeHolGerm.const_ne_zero c hc) hf) =
      NativeHolGerm.constHom c * originalFirstFlagGermResidual F x f hf := by
  rw [originalFirstFlagGermResidual_mul F x _ f (NativeHolGerm.const_ne_zero c hc) hf,
    firstConstResidual F x c hc]

end SGPT.Okounkov
