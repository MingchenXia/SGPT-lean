import SGPT.Unibranch.HironakaG10LfGradedFlat
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Generic flatness (EGA IV 6.9.2, Matsumura Th. 24.1; lane G10LF, sub-item G5.b of `hGF`)

`A` a Noetherian domain, `B` a finite-type `A`-algebra, `M` a finite `B`-module: there is `a ≠ 0` in `A`
such that `Aₐ ⊗_A M` is flat over `Aₐ` (**`exists_flat_localization_of_finiteType`**); more precisely
`FlatAfter A a M`: `R' ⊗_A M` is flat over every flat `A`-algebra `R'` in which `a` is a unit.

Proof (Stacks 051R-style, no dimension theory): `FlatAfter A a` is stable under isomorphism, extensions and
increasing unions; finite `A`-modules satisfy it (mathlib's `exists_free_localizedModule_powers` at the
generic point); for `R[X] ⧸ q` filter by degree: the successive quotients are `R ⧸ Jₖ`, `Jₖ` the leading
coefficient ideals of `q`, which stabilize; prime filtrations reduce finite `R[X]`-modules to cyclic ones;
induction on the number of variables.

Consequence for graded modules (Frisch (II,1)(i)): ONE `a` works for every direct summand of `M`
(`FlatAfter.of_retract`).

No named input. BP: hironaka-g10lf-generic-freeness.tex.
-/

set_option autoImplicit false

open Function TensorProduct Polynomial

namespace SGPT.Unibranch.HironakaG10LfGenericFlat

universe u v w

variable (A : Type u) [CommRing A]

/-- `M` becomes flat over every flat `A`-algebra (in `A`'s universe) in which `a` is a unit. -/
def FlatAfter (a : A) (M : Type v) [AddCommGroup M] [Module A M] : Prop :=
  ∀ (R' : Type u) [CommRing R'] [Algebra A R'] [Module.Flat A R'], IsUnit (algebraMap A R' a) →
    Module.Flat R' (R' ⊗[A] M)

variable {A}

theorem FlatAfter.of_equiv {a : A} {M : Type v} {M' : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] (h : FlatAfter A a M) (e : M ≃ₗ[A] M') : FlatAfter A a M' := by
  intro R' _ _ _ hu
  have := h R' hu
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') e).symm

theorem FlatAfter.mul_right {a : A} {M : Type v} [AddCommGroup M] [Module A M]
    (h : FlatAfter A a M) (c : A) : FlatAfter A (a * c) M := by
  intro R' _ _ _ hu
  rw [map_mul] at hu
  exact h R' (isUnit_of_mul_isUnit_left hu)

theorem FlatAfter.mul_left {a : A} {M : Type v} [AddCommGroup M] [Module A M]
    (h : FlatAfter A a M) (c : A) : FlatAfter A (c * a) M := by
  rw [mul_comm]
  exact h.mul_right c

theorem FlatAfter.of_dvd {a b : A} {M : Type v} [AddCommGroup M] [Module A M]
    (h : FlatAfter A a M) (hab : a ∣ b) : FlatAfter A b M := by
  obtain ⟨c, rfl⟩ := hab
  exact h.mul_right c

theorem flatAfter_of_subsingleton (a : A) (M : Type v) [AddCommGroup M] [Module A M]
    [Subsingleton M] : FlatAfter A a M := by
  intro R' _ _ _ _
  have : Subsingleton (R' ⊗[A] M) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul r m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  infer_instance

/-- **Extensions.** -/
theorem FlatAfter.of_exact {a : A} {M₁ : Type v} {M₂ : Type w} {M₃ : Type*} [AddCommGroup M₁]
    [Module A M₁] [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hf : Injective f) (hg : Surjective g) (hfg : Exact f g)
    (h₁ : FlatAfter A a M₁) (h₃ : FlatAfter A a M₃) : FlatAfter A a M₂ := by
  intro R' _ _ _ hu
  have := h₁ R' hu
  have := h₃ R' hu
  refine HironakaG10LfGradedFlat.flat_of_exact (f.baseChange R') (g.baseChange R') ?_ ?_ ?_
  · rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective R' hg
  · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact R' hfg

/-- **Retracts.** -/
theorem FlatAfter.of_retract {a : A} {M : Type v} {N : Type w} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (h : FlatAfter A a M) (i : N →ₗ[A] M) (r : M →ₗ[A] N)
    (hri : r ∘ₗ i = LinearMap.id) : FlatAfter A a N := by
  intro R' _ _ _ hu
  have := h R' hu
  refine Module.Flat.of_retract (i.baseChange R') (r.baseChange R') ?_
  rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]

/-- **Increasing unions.** -/
theorem FlatAfter.of_monotone {R : Type*} [CommRing R] [Algebra A R] {a : A} {M : Type v}
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] (V : ℕ → Submodule R M)
    (hV : Monotone V) (hcov : ∀ m, ∃ k, m ∈ V k) (h : ∀ k, FlatAfter A a (V k)) :
    FlatAfter A a M := by
  intro R' _ _ _ hu
  let ι : ∀ k, V k →ₗ[A] M := fun k => (V k).subtype.restrictScalars A
  let W : ℕ → Submodule R' (R' ⊗[A] M) := fun k => LinearMap.range ((ι k).baseChange R')
  have hW : Monotone W := by
    intro k l hkl
    rintro _ ⟨y, rfl⟩
    refine ⟨(Submodule.inclusion (hV hkl) |>.restrictScalars A).baseChange R' y, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hall : ∀ z : R' ⊗[A] M, ∃ k, z ∈ W k := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | tmul r m =>
      obtain ⟨k, hk⟩ := hcov m
      exact ⟨k, ⟨r ⊗ₜ[A] ⟨m, hk⟩, rfl⟩⟩
    | add x y hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      exact ⟨max k l, Submodule.add_mem _ (hW (le_max_left k l) hk) (hW (le_max_right k l) hl)⟩
  have hWflat : ∀ k, Module.Flat R' (W k) := by
    intro k
    have := h k R' hu
    have hinj : Injective ((ι k).baseChange R') := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective _ hinj).symm
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨P, hP, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype x
  obtain ⟨S, hS⟩ := hP
  choose kf hkf using hall
  have hPk : P ≤ W (S.sup kf) := by
    rw [← hS, Submodule.span_le]
    intro z hz
    exact hW (Finset.le_sup hz) (hkf z)
  set k := S.sup kf
  have hx' : LinearMap.rTensor I (W k).subtype (LinearMap.rTensor I (Submodule.inclusion hPk) y) =
      LinearMap.rTensor I P.subtype y := by
    rw [← LinearMap.rTensor_comp_apply]
    rfl
  rw [← hx'] at hx ⊢
  have h1 : LinearMap.rTensor R' (W k).subtype
      (I.subtype.lTensor (W k) (LinearMap.rTensor I (Submodule.inclusion hPk) y)) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hx]
  have h2 := (Module.Flat.rTensor_preserves_injective_linearMap (M := R') _ Subtype.val_injective)
    (h1.trans (map_zero _).symm)
  have := hWflat k
  have h3 := (Module.Flat.lTensor_preserves_injective_linearMap (M := W k) _ Subtype.val_injective)
    (h2.trans (map_zero _).symm)
  rw [h3, map_zero]

/-- **Finite modules over a Noetherian domain** are generically flat (free). -/
theorem exists_flatAfter_of_finite [IsDomain A] [IsNoetherianRing A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module.Finite A M] : ∃ a : A, a ≠ 0 ∧ FlatAfter A a M := by
  have := Module.finitePresentation_of_finite A M
  have : Module.Free (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Free.of_divisionRing (FractionRing A) (LocalizedModule (nonZeroDivisors A) M)
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, ?_⟩
  intro R' _ _ _ hu
  let : Algebra (Localization.Away r) R' := (IsLocalization.Away.lift r hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) R' :=
    IsScalarTower.of_algebraMap_eq fun a => (IsLocalization.Away.lift_eq r hu a).symm
  let e₁ : Localization.Away r ⊗[A] M ≃ₗ[Localization.Away r] LocalizedModule.Away r M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv
  have : Module.Flat (Localization.Away r) (Localization.Away r ⊗[A] M) :=
    Module.Flat.of_linearEquiv e₁
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) R' R' M).symm

/-! ### The degree filtration of a cyclic `R[X]`-module -/

section Cyclic

variable {R : Type u} [CommRing R]

theorem mem_leadingCoeffNth_iff (q : Ideal R[X]) (k : ℕ) (x : R) :
    x ∈ q.leadingCoeffNth k ↔ ∃ p ∈ q, (∀ m : ℕ, k < m → p.coeff m = 0) ∧ p.coeff k = x := by
  simp only [Ideal.leadingCoeffNth, Ideal.degreeLE, Submodule.mem_map, Submodule.mem_inf,
    Polynomial.mem_degreeLE, Ideal.mem_ofPolynomial, Polynomial.lcoeff_apply,
    Polynomial.degree_le_iff_coeff_zero, Nat.cast_lt]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, h3⟩
    exact ⟨p, h2, h1, h3⟩
  · rintro ⟨p, h2, h1, h3⟩
    exact ⟨p, ⟨h1, h2⟩, h3⟩

/-- The degree filtration of `R[X] ⧸ q`: classes of polynomials of degree `< k`. -/
noncomputable def degFilt (q : Ideal R[X]) (k : ℕ) : Submodule R (R[X] ⧸ q) :=
  LinearMap.range (((Submodule.mkQ q).restrictScalars R).comp (degreeLT R k).subtype)

theorem degFilt_mono (q : Ideal R[X]) : Monotone (degFilt q) := by
  intro k l hkl
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨p, degreeLT_mono hkl p.2⟩, rfl⟩

theorem degFilt_cover (q : Ideal R[X]) (n : R[X] ⧸ q) : ∃ k, n ∈ degFilt q k := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective q n
  refine ⟨p.natDegree + 1, ⟨⟨p, ?_⟩, rfl⟩⟩
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem degFilt_zero_subsingleton (q : Ideal R[X]) : Subsingleton (degFilt q 0) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : degFilt q 0, z = 0 := by
    rintro ⟨_, ⟨p, rfl⟩⟩
    have hp : (p : R[X]) = 0 := by
      have := p.2
      rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at this
      exact Polynomial.ext fun m => by rw [this m (Nat.zero_le m), Polynomial.coeff_zero]
    apply Subtype.ext
    change Submodule.mkQ q (p : R[X]) = 0
    rw [hp, map_zero]
  rw [h x, h y]

end Cyclic

section CyclicStep

variable {R : Type u} [CommRing R] [Algebra A R]

/-- `0 → F_k → F_{k+1} → R ⧸ J_k → 0` (`J_k` the leading coefficient ideal of degree `k`). -/
theorem flatAfter_degFilt_succ {a : A} (q : Ideal R[X]) (k : ℕ)
    (h₁ : FlatAfter A a (degFilt q k)) (h₃ : FlatAfter A a (R ⧸ q.leadingCoeffNth k)) :
    FlatAfter A a (degFilt q (k + 1)) := by
  let ψ : degreeLT R (k + 1) →ₗ[R] R[X] ⧸ q :=
    ((Submodule.mkQ q).restrictScalars R).comp (degreeLT R (k + 1)).subtype
  let ψ' : degreeLT R (k + 1) →ₗ[R] degFilt q (k + 1) := ψ.rangeRestrict
  have hψ' : Surjective ψ' := LinearMap.surjective_rangeRestrict ψ
  let φ : degreeLT R (k + 1) →ₗ[R] R ⧸ q.leadingCoeffNth k :=
    (Submodule.mkQ (q.leadingCoeffNth k)).comp
      ((Polynomial.lcoeff R k).comp (degreeLT R (k + 1)).subtype)
  have hφ : ∀ p, φ p = Submodule.Quotient.mk ((p : R[X]).coeff k) := fun p => rfl
  have hdegp : ∀ p : degreeLT R (k + 1), ∀ m : ℕ, k < m → (p : R[X]).coeff m = 0 := by
    intro p m hm
    have := p.2
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at this
    exact this m hm
  have hker : LinearMap.ker ψ' ≤ LinearMap.ker φ := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hq : (p : R[X]) ∈ q := by
      have h0 : Submodule.mkQ q (p : R[X]) = 0 := congrArg Subtype.val hp
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    rw [hφ, Submodule.Quotient.mk_eq_zero, mem_leadingCoeffNth_iff]
    exact ⟨p, hq, hdegp p, rfl⟩
  let e := ψ'.quotKerEquivOfSurjective hψ'
  let g : degFilt q (k + 1) →ₗ[R] R ⧸ q.leadingCoeffNth k :=
    (LinearMap.ker ψ').liftQ φ hker ∘ₗ e.symm.toLinearMap
  have hg : ∀ p, g (ψ' p) = φ p := by
    intro p
    have h1 : e.symm (ψ' p) = Submodule.Quotient.mk p := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker ψ').liftQ φ hker (e.symm (ψ' p)) = φ p
    rw [h1, Submodule.liftQ_apply]
  let f : degFilt q k →ₗ[R] degFilt q (k + 1) :=
    Submodule.inclusion (degFilt_mono q (Nat.le_succ k))
  have hf : Injective f := Submodule.inclusion_injective _
  have hgs : Surjective g := by
    intro z
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (q.leadingCoeffNth k) z
    have hmem : Polynomial.C r * Polynomial.X ^ k ∈ degreeLT R (k + 1) := by
      rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
    refine ⟨ψ' ⟨_, hmem⟩, ?_⟩
    rw [hg, hφ]
    change Submodule.Quotient.mk ((Polynomial.C r * Polynomial.X ^ k).coeff k) = _
    rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    rfl
  have hfg : Exact f g := by
    intro v
    obtain ⟨p, rfl⟩ := hψ' v
    rw [hg, hφ, Submodule.Quotient.mk_eq_zero, mem_leadingCoeffNth_iff]
    constructor
    · rintro ⟨h, hhq, hhdeg, hhk⟩
      have hdeg : (p : R[X]) - h ∈ degreeLT R k := by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        rw [Polynomial.coeff_sub]
        rcases eq_or_lt_of_le hm with rfl | hlt
        · rw [hhk, sub_self]
        · rw [hdegp p m hlt, hhdeg m hlt, sub_self]
      refine ⟨⟨_, ⟨⟨(p : R[X]) - h, hdeg⟩, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change Submodule.mkQ q ((p : R[X]) - h) = Submodule.mkQ q (p : R[X])
      have h0 : Submodule.mkQ q h = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hhq
      rw [map_sub, h0, sub_zero]
    · rintro ⟨⟨_, ⟨p', rfl⟩⟩, hw⟩
      have h1 : Submodule.mkQ q (p' : R[X]) = Submodule.mkQ q (p : R[X]) := congrArg Subtype.val hw
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h1
      have hp' : ∀ m : ℕ, k ≤ m → (p' : R[X]).coeff m = 0 := by
        have := p'.2
        rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at this
        exact this
      refine ⟨(p : R[X]) - p', ?_, fun m hm => ?_, ?_⟩
      · rw [← neg_sub]
        exact q.neg_mem h1
      · rw [Polynomial.coeff_sub, hdegp p m hm, hp' m hm.le, sub_self]
      · rw [Polynomial.coeff_sub, hp' k le_rfl, sub_zero]
  exact FlatAfter.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hgs hfg h₁ h₃

/-- **Cyclic modules over `R[X]`.** If every `R ⧸ J` is generically flat over `A`, so is every
`R[X] ⧸ q`. -/
theorem exists_flatAfter_quotient_polynomial [IsDomain A] [IsNoetherianRing R]
    (hR : ∀ J : Ideal R, ∃ a : A, a ≠ 0 ∧ FlatAfter A a (R ⧸ J)) (q : Ideal R[X]) :
    ∃ a : A, a ≠ 0 ∧ FlatAfter A a (R[X] ⧸ q) := by
  obtain ⟨k₀, hk₀⟩ := (monotone_stabilizes_iff_noetherian (R := R) (M := R)).mpr inferInstance
    ⟨fun k => q.leadingCoeffNth k, fun _ _ h => q.leadingCoeffNth_mono h⟩
  choose af haf hflat using fun k => hR (q.leadingCoeffNth k)
  let a := ∏ k ∈ Finset.range (k₀ + 1), af k
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => haf k
  have hJ : ∀ k, FlatAfter A a (R ⧸ q.leadingCoeffNth k) := by
    intro k
    by_cases hk : k ≤ k₀
    · exact (hflat k).of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))
    · have h1 : q.leadingCoeffNth k = q.leadingCoeffNth k₀ := (hk₀ k (by omega)).symm
      rw [h1]
      exact (hflat k₀).of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))
  have hV : ∀ k, FlatAfter A a (degFilt q k) := by
    intro k
    induction k with
    | zero =>
      have := degFilt_zero_subsingleton q
      exact flatAfter_of_subsingleton a _
    | succ k ih => exact flatAfter_degFilt_succ q k ih (hJ k)
  exact ⟨a, ha, FlatAfter.of_monotone (degFilt q) (degFilt_mono q) (degFilt_cover q) hV⟩

end CyclicStep

/-! ### Induction on the number of variables -/

variable (A) in
/-- Every finite `R`-module (in universe `v`, with a compatible `A`-action) is generically flat over
`A`. -/
def GenFlat (R : Type*) [CommRing R] [Algebra A R] : Prop :=
  ∀ (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N] [Module A N]
    [IsScalarTower A R N], ∃ a : A, a ≠ 0 ∧ FlatAfter A a N

/-- Transfer along a surjective `A`-algebra map. -/
theorem GenFlat.of_surjective {R R' : Type*} [CommRing R] [CommRing R'] [Algebra A R] [Algebra A R']
    (φ : R →ₐ[A] R') (hφ : Surjective φ) (h : GenFlat.{u, v} A R) : GenFlat.{u, v} A R' := by
  intro N _ _ _ _ _
  let _ : Module R N := Module.compHom N φ.toRingHom
  have : IsScalarTower A R N := IsScalarTower.of_algebraMap_smul fun a n => by
    change φ (algebraMap A R a) • n = a • n
    rw [AlgHom.commutes, algebraMap_smul]
  let _ : Algebra R R' := φ.toRingHom.toAlgebra
  have : IsScalarTower R R' N := IsScalarTower.of_algebraMap_smul fun r n => rfl
  have : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R') hφ
  have : Module.Finite R N := Module.Finite.trans R' N
  exact h N

/-- **One more variable.** -/
theorem genFlat_polynomial [IsDomain A] {R : Type u} [CommRing R] [Algebra A R] [IsNoetherianRing R]
    (hR : GenFlat.{u, u} A R) : GenFlat.{u, w} A R[X] := by
  intro N _ _ hN _ _
  have hRJ : ∀ J : Ideal R, ∃ a : A, a ≠ 0 ∧ FlatAfter A a (R ⧸ J) := fun J => hR (R ⧸ J)
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R[X] hN
    (motive := fun N _ _ _ => ∀ [Module A N] [IsScalarTower A R[X] N],
      ∃ a : A, a ≠ 0 ∧ FlatAfter A a N) ?_ ?_ ?_
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, flatAfter_of_subsingleton 1 N⟩
  · intro N _ _ _ p e _ _
    obtain ⟨a, ha, h⟩ := exists_flatAfter_quotient_polynomial hRJ p.1
    exact ⟨a, ha, h.of_equiv (e.restrictScalars A).symm⟩
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    let _ : Module A N₁ := Module.compHom N₁ (algebraMap A R[X])
    have : IsScalarTower A R[X] N₁ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let _ : Module A N₃ := Module.compHom N₃ (algebraMap A R[X])
    have : IsScalarTower A R[X] N₃ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    obtain ⟨a₁, ha₁, h₁⟩ := h₁
    obtain ⟨a₃, ha₃, h₃⟩ := h₃
    exact ⟨a₁ * a₃, mul_ne_zero ha₁ ha₃, FlatAfter.of_exact (f.restrictScalars A)
      (g.restrictScalars A) hf hg hfg (h₁.mul_right a₃) (h₃.mul_left a₁)⟩

theorem genFlat_mvPolynomial_zero [IsDomain A] [IsNoetherianRing A] :
    GenFlat.{u, v} A (MvPolynomial (Fin 0) A) := by
  intro N _ _ _ _ _
  have : Module.Finite A (MvPolynomial (Fin 0) A) :=
    Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toLinearEquiv
  have : Module.Finite A N := Module.Finite.trans (MvPolynomial (Fin 0) A) N
  exact exists_flatAfter_of_finite N

theorem genFlat_mvPolynomial [IsDomain A] [IsNoetherianRing A] (n : ℕ) :
    GenFlat.{u, u} A (MvPolynomial (Fin n) A) := by
  induction n with
  | zero => exact genFlat_mvPolynomial_zero
  | succ n ih =>
    exact (genFlat_polynomial ih).of_surjective
      ((MvPolynomial.finSuccEquiv A n).symm : Polynomial (MvPolynomial (Fin n) A) →ₐ[A]
        MvPolynomial (Fin (n + 1)) A) (MvPolynomial.finSuccEquiv A n).symm.surjective

theorem genFlat_mvPolynomial' [IsDomain A] [IsNoetherianRing A] (n : ℕ) :
    GenFlat.{u, w} A (MvPolynomial (Fin n) A) := by
  cases n with
  | zero => exact genFlat_mvPolynomial_zero
  | succ n =>
    exact (genFlat_polynomial (genFlat_mvPolynomial n)).of_surjective
      ((MvPolynomial.finSuccEquiv A n).symm : Polynomial (MvPolynomial (Fin n) A) →ₐ[A]
        MvPolynomial (Fin (n + 1)) A) (MvPolynomial.finSuccEquiv A n).symm.surjective

/-- **Generic flatness** (EGA IV 6.9.2, Matsumura Th. 24.1, flat form): `A` a Noetherian domain, `B` a
finite-type `A`-algebra, `M` a finite `B`-module. Some `a ≠ 0` makes `M` flat over every flat
`A`-algebra in which `a` is a unit. -/
theorem exists_flatAfter_of_finiteType [IsDomain A] [IsNoetherianRing A] {B : Type*} [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] (M : Type w) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module A M] [IsScalarTower A B M] :
    ∃ a : A, a ≠ 0 ∧ FlatAfter A a M := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType A B›
  exact (genFlat_mvPolynomial' n).of_surjective φ hφ M

/-- **Generic flatness, localized form**: `Aₐ ⊗_A M` is flat over `Aₐ` for some `a ≠ 0`. -/
theorem exists_flat_localization_of_finiteType [IsDomain A] [IsNoetherianRing A] {B : Type*}
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (M : Type w) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module A M] [IsScalarTower A B M] :
    ∃ a : A, a ≠ 0 ∧ Module.Flat (Localization.Away a) (Localization.Away a ⊗[A] M) := by
  obtain ⟨a, ha, h⟩ := exists_flatAfter_of_finiteType (A := A) (B := B) M
  exact ⟨a, ha, h _ (IsLocalization.Away.algebraMap_isUnit a)⟩

/-- **Graded form (Frisch (II,1)(i)): one `a` for all summands.** If `M = ⨁ₖ Mₖ` (internal direct sum of
`A`-submodules), every `Aₐ ⊗ Mₖ` is flat over `Aₐ`, for the single `a` of `M`. -/
theorem FlatAfter.of_isInternal {a : A} {M : Type v} [AddCommGroup M] [Module A M]
    {ι : Type*} [DecidableEq ι] (Mk : ι → Submodule A M) (hM : DirectSum.IsInternal Mk)
    (h : FlatAfter A a M) (k : ι) : FlatAfter A a (Mk k) := by
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap Mk) hM
  refine h.of_retract (Mk k).subtype
    ((DirectSum.component A ι (fun k => Mk k) k) ∘ₗ e.symm.toLinearMap) ?_
  apply LinearMap.ext
  intro x
  have hx : e.symm (x : M) = DirectSum.lof A ι (fun k => Mk k) k x := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of Mk k x).symm
  change DirectSum.component A ι (fun k => Mk k) k (e.symm (x : M)) = x
  rw [hx, DirectSum.component.lof_self]

/-- **Graded generic flatness, localized form.** -/
theorem exists_flat_localization_of_isInternal [IsDomain A] [IsNoetherianRing A] {B : Type*}
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (M : Type w) [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module A M] [IsScalarTower A B M] {ι : Type*} [DecidableEq ι]
    (Mk : ι → Submodule A M) (hM : DirectSum.IsInternal Mk) :
    ∃ a : A, a ≠ 0 ∧ ∀ k, Module.Flat (Localization.Away a) (Localization.Away a ⊗[A] Mk k) := by
  obtain ⟨a, ha, h⟩ := exists_flatAfter_of_finiteType (A := A) (B := B) M
  exact ⟨a, ha, fun k => (h.of_isInternal Mk hM k) _ (IsLocalization.Away.algebraMap_isUnit a)⟩

end SGPT.Unibranch.HironakaG10LfGenericFlat
