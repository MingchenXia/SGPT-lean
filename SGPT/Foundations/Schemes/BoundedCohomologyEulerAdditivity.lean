import SGPT.Foundations.Schemes.HomogeneousCechDimensionShift
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual exact linear maps and a genuinely finite middle module give
the actual rank-nullity decomposition. No Euler identity is a premise. -/
theorem actualExact_finrank_eq_range_add_range
    {K : Type} {A B C : Type*} [Field K] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module K A] [Module K B] [Module K C] [Module.Finite K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (he : Function.Exact f g) :
    Module.finrank K B = Module.finrank K (LinearMap.range f) +
      Module.finrank K (LinearMap.range g) := by
  have hk : LinearMap.ker g = LinearMap.range f := by
    ext b
    exact he b
  have hd := LinearMap.finrank_range_add_finrank_ker g
  rw [hk] at hd
  omega

/-- Actual alternating finite dimension differences telescope to the
last genuine connecting rank. This is only the finite integer identity. -/
theorem alternating_dimension_sum_eq_connecting_rank
    (u v w c : ℕ → ℤ) (N : ℕ)
    (h0 : u 0 - v 0 + w 0 = c 0)
    (hs : ∀ i, u (i + 1) - v (i + 1) + w (i + 1) = c i + c (i + 1)) :
    (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (u i - v i + w i)) =
      (-1 : ℤ) ^ N * c N := by
  induction N with
  | zero => simp [h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hs N, pow_succ]
    ring

/-- Actual bounded homology support gives the finite homological Euler
sum, without any finite-dimensional assumption on the complex terms. -/
theorem boundedCochain_homologyEulerChar_eq_sum
    {K : Type} [Field K] (C : CochainComplex (ModuleCat K) ℕ) (N : ℕ)
    (hzero : ∀ p, N ≤ p → IsZero (C.homology p)) :
    C.homologyEulerChar = ∑ p ∈ Finset.range (N + 1), (-1 : ℤ) ^ p *
      (Module.finrank K (C.homology p) : ℤ) := by
  rw [HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    _ (Finset.range (N + 1))]
  · simp
  · intro p hp
    apply Finset.mem_range.mpr
    by_contra! hle
    have : Subsingleton (C.homology p) := ModuleCat.subsingleton_of_isZero
      (hzero p (by omega))
    exact hp Module.finrank_zero_of_subsingleton


/-- A genuine short exact cochain sequence with actual finite homology and
bounded actual support has additive homological Euler characteristic. The
possibly infinite affine-section terms never enter a dimension formula. -/
theorem boundedCochain_homologyEulerChar_additive
    {K : Type} [Field K] (S : ShortComplex (CochainComplex (ModuleCat K) ℕ))
    (hS : S.ShortExact)
    [∀ p, Module.Finite K (S.X₁.homology p)]
    [∀ p, Module.Finite K (S.X₂.homology p)]
    [∀ p, Module.Finite K (S.X₃.homology p)]
    (N : ℕ)
    (h₁ : ∀ p, N ≤ p → IsZero (S.X₁.homology p))
    (h₂ : ∀ p, N ≤ p → IsZero (S.X₂.homology p))
    (h₃ : ∀ p, N ≤ p → IsZero (S.X₃.homology p)) :
    S.X₂.homologyEulerChar = S.X₁.homologyEulerChar + S.X₃.homologyEulerChar := by
  let f (i : ℕ) := (HomologicalComplex.homologyMap S.f i).hom
  let g (i : ℕ) := (HomologicalComplex.homologyMap S.g i).hom
  let δ (i : ℕ) := (hS.δ i (i + 1) (by rfl)).hom
  let u (i : ℕ) : ℤ := (Module.finrank K (S.X₁.homology i) : ℤ)
  let v (i : ℕ) : ℤ := (Module.finrank K (S.X₂.homology i) : ℤ)
  let w (i : ℕ) : ℤ := (Module.finrank K (S.X₃.homology i) : ℤ)
  let c (i : ℕ) : ℤ := (Module.finrank K (LinearMap.range (δ i)) : ℤ)
  have e₂ (i : ℕ) : Function.Exact (f i) (g i) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.homology_exact₂ i)
  have e₃ (i : ℕ) : Function.Exact (g i) (δ i) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ i (i + 1) (by rfl))
  have e₁ (i : ℕ) : Function.Exact (δ i) (f (i + 1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ i (i + 1) (by rfl))
  have hinj : Function.Injective (f 0) := by
    have : Mono S.f := hS.mono_f
    have : Mono (S.f.f 0) := inferInstance
    have : Mono (HomologicalComplex.homologyMap S.f 0) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f 0 (by
        intro i hi
        change i + 1 = 0 at hi
        omega)
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have h0 : u 0 - v 0 + w 0 = c 0 := by
    have hX := (LinearEquiv.ofInjective (f 0) hinj).finrank_eq
    have hY := actualExact_finrank_eq_range_add_range (f 0) (g 0) (e₂ 0)
    have hZ := actualExact_finrank_eq_range_add_range (g 0) (δ 0) (e₃ 0)
    have hu : u 0 = (Module.finrank K (LinearMap.range (f 0)) : ℤ) := by dsimp [u]; exact_mod_cast hX
    have hv : v 0 = (Module.finrank K (LinearMap.range (f 0)) : ℤ) +
        (Module.finrank K (LinearMap.range (g 0)) : ℤ) := by dsimp [v]; exact_mod_cast hY
    have hw : w 0 = (Module.finrank K (LinearMap.range (g 0)) : ℤ) + c 0 := by dsimp [w, c]; exact_mod_cast hZ
    rw [hu, hv, hw]
    ring
  have hs : ∀ i, u (i + 1) - v (i + 1) + w (i + 1) = c i + c (i + 1) := by
    intro i
    have hX := actualExact_finrank_eq_range_add_range (δ i) (f (i + 1)) (e₁ i)
    have hY := actualExact_finrank_eq_range_add_range (f (i + 1)) (g (i + 1)) (e₂ (i + 1))
    have hZ := actualExact_finrank_eq_range_add_range (g (i + 1)) (δ (i + 1)) (e₃ (i + 1))
    dsimp [u, v, w, c]
    omega
  have ht := alternating_dimension_sum_eq_connecting_rank u v w c N h0 hs
  have hz : c N = 0 := by
    have : Subsingleton (S.X₁.homology (N + 1)) :=
      ModuleCat.subsingleton_of_isZero (h₁ (N + 1) (Nat.le_succ N))
    have : Subsingleton (LinearMap.range (δ N)) := inferInstance
    simp only [c, Module.finrank_zero_of_subsingleton, Nat.cast_zero]
  rw [hz, mul_zero] at ht
  rw [boundedCochain_homologyEulerChar_eq_sum S.X₂ N h₂,
    boundedCochain_homologyEulerChar_eq_sum S.X₁ N h₁,
    boundedCochain_homologyEulerChar_eq_sum S.X₃ N h₃]
  change (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * v i) =
    (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * u i) +
    (∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * w i)
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at ht
  linarith

end
end SGPT.Foundations.Schemes
