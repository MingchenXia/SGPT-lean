import SGPT.Okounkov.OF6ZariskiDivisorial
import SGPT.Okounkov.OF4AbhyankarInequality
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.FiniteType

/-!
# Zariski's realization of the divisorial first coordinate on a normal affine model

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` and the proof of the cited
[CFKLRS17, Theorem 2.9]: for a valuation `ν : ℂ(X)^× → ℤⁿ_lex` of maximal rational rank, the first
coordinate `ν₁` is a divisorial valuation, and *Zariski's theorem realizes it as the
order of vanishing `ord_E` along a prime divisor `E` of a normal birational model of `X`*.

This file proves Zariski's theorem on an affine chart of the model.

* `finite_integralClosure_of_isFractionRing`: the normalization of a finitely generated domain
  over a field of characteristic zero, in an arbitrary fraction field, is finite (transport of
  `SGPT.Unibranch.finite_integralClosure_of_finiteType`).
* `exists_normalChart_of_divisorial` (abstract form): let `K/k` (char. `0`) have no `m + 2`
  algebraically independent elements, `B ⊆ K` a finitely generated `k`-domain with fraction field
  `K`, and `v` a nontrivial valuation of `K` with values in `G ∪ {∞}` (`G` an ordered group),
  nonnegative on `B`, with `m` elements `y_j` whose residues are algebraically independent. Then
  for the finitely generated `A' = k[B, y] ⊆ K` and its normalization `A` (integral closure of `A'`
  in `K`): `A` is a normal finitely generated `k`-domain with fraction field `K`, `v ≥ 0` on `A`,
  `q = {a ∈ A : v(a) > 0}` is a nonzero prime with no prime strictly between `0` and `q` (height
  one), `A_q` is a discrete valuation ring, and the valuation ring of `v` is exactly `A_q`.
* `exists_normalChart_prefixOne` (**Zariski's realization of `ν₁`**): for `X` integral, smooth of
  relative dimension `n = m + 1` over `ℂ`, a surjective `ν : ℂ(X)^× → ℤⁿ_lex` and an affine open
  `V ⊆ X` on which `ν ≥ 0` (e.g. an affine neighbourhood of the centre of `ν`), the first
  coordinate `ν₁` is the order of vanishing along the prime divisor `E = V(q)` of the normal affine
  variety `Spec A` (finitely generated, birational to `X`, mapping to `V` since
  `Γ(X, V) ⊆ A`): the valuation ring of `ν₁` is the discrete valuation ring `A_q`.

What is not formalized: the compactification of `Spec A` to a normal *proper* birational model of
`X` (so that `E` becomes a `SGPT.NAPotential.Berkovich.PrimeDivisorOver X`), and the remaining
steps of [CFKLRS17, Thm 2.9] (local uniformization of the residual valuation on `E`, lifted to a
model of `X`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open IsLocalRing

/-- **Finiteness of the normalization** of a finitely generated domain over a field of
characteristic zero, in an arbitrary fraction field `L`. -/
theorem finite_integralClosure_of_isFractionRing (k R L : Type*) [Field k] [CharZero k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] [Field L] [Algebra R L]
    [IsFractionRing R L] : Module.Finite R (integralClosure R L) := by
  have := SGPT.Unibranch.finite_integralClosure_of_finiteType k R
  let e : FractionRing R ≃ₐ[R] L := IsLocalization.algEquiv (nonZeroDivisors R) (FractionRing R) L
  rw [← integralClosure_map_algEquiv e]
  exact Module.Finite.equiv (e.subalgebraMap (integralClosure R (FractionRing R))).toLinearEquiv

section Abstract

variable {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
  {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- The subalgebra `{x : v(x) ≥ 0}` of `K` (a valuation trivial on the image of `B`). -/
def nonnegSubalgebra {B : Type*} [CommRing B] [Algebra k B] [Algebra B K] [IsScalarTower k B K]
    (v : AddValuation K (WithTop G)) (hB : ∀ b : B, 0 ≤ v (algebraMap B K b)) :
    Subalgebra k K where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    change 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  algebraMap_mem' c := by
    change 0 ≤ v (algebraMap k K c)
    rw [IsScalarTower.algebraMap_apply k B K]
    exact hB _

/-- **Zariski's realization of a divisorial valuation on a normal affine chart** (abstract
form). See the module docstring. -/
theorem exists_normalChart_of_divisorial
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra B K] [IsScalarTower k B K] [IsFractionRing B K]
    (v : AddValuation K (WithTop G)) (hB : ∀ b : B, 0 ≤ v (algebraMap B K b))
    {x₀ : K} (hx₀ : v x₀ ≠ 0) (hx₀' : x₀ ≠ 0)
    {m : ℕ} (htr : ∀ z : Fin (m + 2) → K, ¬ AlgebraicIndependent k z)
    (y : Fin m → K)
    (hy : ∀ Q : MvPolynomial (Fin m) k, Q ≠ 0 → v (MvPolynomial.aeval y Q) = 0) :
    ∃ A' : Subalgebra k K,
      A' = (IsScalarTower.toAlgHom k B K).range ⊔ Algebra.adjoin k (Set.range y) ∧
      A'.FG ∧ (∀ b : B, algebraMap B K b ∈ A') ∧ (∀ j, y j ∈ A') ∧
      ∃ hA : ∀ a : integralClosure A' K, 0 ≤ v (algebraMap (integralClosure A' K) K a),
        Algebra.FiniteType k (integralClosure A' K) ∧
        IsIntegrallyClosed (integralClosure A' K) ∧
        IsFractionRing (integralClosure A' K) K ∧
        centerIdeal v hA ≠ ⊥ ∧
        (∀ p : Ideal (integralClosure A' K), p.IsPrime → p ≤ centerIdeal v hA →
          p = ⊥ ∨ p = centerIdeal v hA) ∧
        (haveI := centerIdeal_isPrime v hA;
          IsDiscreteValuationRing (Localization.AtPrime (centerIdeal v hA))) ∧
        ∀ x : K, 0 ≤ v x ↔ ∃ a s : integralClosure A' K, s ∉ centerIdeal v hA ∧
          x * algebraMap (integralClosure A' K) K s = algebraMap (integralClosure A' K) K a := by
  classical
  let φ : B →ₐ[k] K := IsScalarTower.toAlgHom k B K
  let A' : Subalgebra k K := φ.range ⊔ Algebra.adjoin k (Set.range y)
  have hFG : A'.FG := by
    refine Subalgebra.FG.sup ?_ ⟨Finset.univ.image y, by simp⟩
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φ (Algebra.FiniteType.out)
  have hBA : ∀ b : B, algebraMap B K b ∈ A' := fun b =>
    (le_sup_left : φ.range ≤ A') ⟨b, IsScalarTower.toAlgHom_apply k B K b⟩
  have hyA : ∀ j, y j ∈ A' := fun j =>
    (le_sup_right : Algebra.adjoin k (Set.range y) ≤ A') (Algebra.subset_adjoin ⟨j, rfl⟩)
  have hA'O : A' ≤ nonnegSubalgebra v hB := by
    refine sup_le ?_ ?_
    · rintro _ ⟨b, rfl⟩
      change 0 ≤ v (φ b)
      rw [IsScalarTower.toAlgHom_apply]
      exact hB b
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      change 0 ≤ v (y j)
      have h := hy (MvPolynomial.X j) (MvPolynomial.X_ne_zero j)
      rw [MvPolynomial.aeval_X] at h
      rw [h]
  have hA'nonneg : ∀ a : A', 0 ≤ v (algebraMap A' K a) := fun a => hA'O a.2
  -- `A'` is a finitely generated domain with fraction field `K`
  have : Algebra.FiniteType k A' := (Subalgebra.fg_iff_finiteType A').mp hFG
  have : FaithfulSMul A' K := (faithfulSMul_iff_algebraMap_injective A' K).mpr Subtype.val_injective
  have : IsFractionRing A' K := IsFractionRing.of_field A' K fun z => by
    obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact ⟨⟨_, hBA b₁⟩, ⟨_, hBA b₂⟩, rfl⟩
  -- its normalization
  let C := integralClosure A' K
  have : Module.Finite A' C := finite_integralClosure_of_isFractionRing k A' K
  have hCft : Algebra.FiniteType k C := Algebra.FiniteType.trans (S := A') inferInstance
    inferInstance
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hCic : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hCfr : IsFractionRing C K := integralClosure.isFractionRing_of_finite_extension K K
  have hA : ∀ c : C, 0 ≤ v (algebraMap C K c) := fun c =>
    nonneg_of_isIntegral (R := A') v hA'nonneg c.2
  -- no `m + 2` independent elements in `C`
  have htrC : ∀ z : Fin (m + 2) → C, ¬ AlgebraicIndependent k z := fun z hz =>
    htr _ (hz.map' (f := IsScalarTower.toAlgHom k C K) Subtype.val_injective)
  -- the `y_j` in `C`
  let y' : Fin m → C := fun j => ⟨y j, isIntegral_algebraMap (x := (⟨y j, hyA j⟩ : A'))⟩
  have hy'K : ∀ Q : MvPolynomial (Fin m) k,
      algebraMap C K (MvPolynomial.aeval y' Q) = MvPolynomial.aeval y Q := by
    intro Q
    have h := MvPolynomial.comp_aeval_apply (R := k) (f := y') (IsScalarTower.toAlgHom k C K) Q
    rw [IsScalarTower.coe_toAlgHom'] at h
    exact h
  let q := centerIdeal v hA
  have : q.IsPrime := centerIdeal_isPrime v hA
  have hyq : AlgebraicIndependent k (Ideal.Quotient.mk q ∘ y') := by
    refine (injective_iff_map_eq_zero _).mpr fun Q hQ => ?_
    by_contra hQ0
    have h := MvPolynomial.comp_aeval_apply (R := k) (f := y') (Ideal.Quotient.mkₐ k q) Q
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    have hmem : MvPolynomial.aeval y' Q ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, h]
      exact hQ
    have hpos : 0 < v (algebraMap C K (MvPolynomial.aeval y' Q)) := hmem
    rw [hy'K, hy Q hQ0] at hpos
    exact lt_irrefl _ hpos
  have hq0 : q ≠ ⊥ := by
    intro hq
    obtain ⟨a, b, hb, ha⟩ := IsFractionRing.div_surjective (A := C) x₀
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_div] at ha
      exact hx₀' ha.symm
    have hzero : ∀ c : C, c ≠ 0 → v (algebraMap C K c) = 0 := by
      intro c hc
      refine le_antisymm ?_ (hA c)
      by_contra hlt
      have hcq : c ∈ q := lt_of_not_ge hlt
      rw [hq, Ideal.mem_bot] at hcq
      exact hc hcq
    apply hx₀
    rw [← ha, AddValuation.map_div, hzero a ha0, hzero b hb0, sub_zero]
  have hheight : ∀ p : Ideal C, p.IsPrime → p ≤ q → p = ⊥ ∨ p = q :=
    fun p hp hpq => eq_bot_or_eq_of_le_of_residue_independent htrC y' hyq p hpq
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime q) :=
    isDiscreteValuationRing_localization q hq0 hheight
  refine ⟨A', rfl, hFG, hBA, hyA, hA, hCft, hCic, hCfr, hq0, hheight, hdvr, fun x => ?_⟩
  exact nonneg_iff_exists_mul_mem v hA q (fun a => Iff.rfl) x

omit [CharZero k] in
/-- Every valuation nonnegative on `B` and on the `y_j` is nonnegative on the normalization of
`k[B, y]` (valuation rings are integrally closed). -/
theorem nonneg_integralClosure_of_nonneg
    {B : Type*} [CommRing B] [Algebra k B] [Algebra B K] [IsScalarTower k B K]
    {ι : Type*} (y : ι → K) {G' : Type*} [AddCommGroup G'] [LinearOrder G']
    [IsOrderedAddMonoid G'] (w : AddValuation K (WithTop G'))
    (hwB : ∀ b : B, 0 ≤ w (algebraMap B K b)) (hwy : ∀ j, 0 ≤ w (y j))
    (a : integralClosure ↥(((IsScalarTower.toAlgHom k B K).range ⊔
      Algebra.adjoin k (Set.range y) : Subalgebra k K)) K) :
    0 ≤ w (a : K) := by
  have hA'O : ((IsScalarTower.toAlgHom k B K).range ⊔ Algebra.adjoin k (Set.range y) :
      Subalgebra k K) ≤ nonnegSubalgebra w hwB := by
    refine sup_le ?_ ?_
    · rintro _ ⟨b, rfl⟩
      change 0 ≤ w (IsScalarTower.toAlgHom k B K b)
      rw [IsScalarTower.toAlgHom_apply]
      exact hwB b
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact hwy j
  exact nonneg_of_isIntegral w (fun c => hA'O c.2) a.2

end Abstract

end SGPT.Okounkov.OF6
