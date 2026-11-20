import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Complex.Basic

/-!
# Generic smoothness of a principal prime divisor: the algebraic core


Let `A` be a complex algebra with a submersive presentation (the ring of a standard smooth affine
chart), `𝔮 ⊂ A` a prime ideal and `u ∈ 𝔮` with `s 𝔮 ⊆ (u)` for some `s ∉ 𝔮`.  The prime divisor
`V(𝔮)` is smooth at a general point: there is a maximal ideal `𝔪 ⊇ 𝔮`, `s ∉ 𝔪`, at which some
partial derivative `∂ₖ u` of `u` (with respect to the free coordinates of the presentation) does
not vanish.  The analytic input is abstracted as a family of injective `ℂ`-algebra maps
`θ_𝔪 : A → ℂ⟦X₁, …, Xₙ⟧` with constant coefficient vanishing exactly on `𝔪` (the Taylor
expansions at the complex points, `SGPT.Okounkov.schemeNativeFormalGerm`).

* `eq_zero_of_pderiv_mem_span`: a formal power series over `ℂ` without constant term all of whose
  partial derivatives lie in the ideal it generates is zero (look at a monomial of least degree);
* `partialDeriv`, `derivation_eq_sum`: the partial derivatives `∂ₖ` dual to the basis `d tₖ`
  of `Ω_{A/ℂ}` (Mathlib's `SubmersivePresentation.basisKaehler`), and the expansion
  `δ a = ∑ₖ ∂ₖ a • δ tₖ` of every derivation;
* `exists_maximal_partialDeriv_notMem`: the generic smoothness statement above (if `∂ₖ u ∈ 𝔪` at
  all such `𝔪`, then `∂ₖ u ∈ 𝔮` since `A` is a Jacobson ring, so `∂ₖ u ∈ (u)` after inverting
  `s`, and the Taylor expansion of `u` at one point is zero by the formal lemma);
* `exists_pointDerivation_ne_zero`: at such a maximal ideal, a family of point derivations
  parametrised linearly by `v ∈ ℂⁿ`, faithful on `A` and with `n` free coordinates, does not
  kill `u`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes2

open MvPowerSeries

/-! ### The formal lemma -/

/-- **A formal power series without constant term whose partial derivatives all lie in the ideal
it generates is zero.**  If `Φ ≠ 0`, let `xᵉ` be a monomial of least degree `d ≥ 1` of `Φ` and
`eₗ ≥ 1`; the coefficient of `x^{e - eₗ}` in `∂ₗ Φ` is `eₗ · Φₑ ≠ 0`, while in `G Φ` it is `0`. -/
theorem eq_zero_of_pderiv_mem_span {σ : Type*} {Φ : MvPowerSeries σ ℂ}
    (h0 : constantCoeff Φ = 0) (hd : ∀ l, pderiv ℂ l Φ ∈ Ideal.span {Φ}) : Φ = 0 := by
  classical
  by_contra hΦ
  have hex : ∃ d : ℕ, ∃ e : σ →₀ ℕ, e.degree = d ∧ coeff e Φ ≠ 0 := by
    by_contra hno
    apply hΦ
    ext e
    by_contra hne
    exact hno ⟨_, e, rfl, hne⟩
  set d := Nat.find hex with hd_def
  obtain ⟨e, hed, he⟩ := Nat.find_spec hex
  have hmin : ∀ a : σ →₀ ℕ, a.degree < d → coeff a Φ = 0 := by
    intro a ha
    by_contra hne
    exact Nat.find_min hex (hd_def ▸ ha) ⟨a, rfl, hne⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact he (by simpa using h0)
  obtain ⟨l, hl⟩ : ∃ l, e l ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he0 (Finsupp.ext hall)
  set e' := e - Finsupp.single l 1 with he'
  have hee : e' + Finsupp.single l 1 = e := by
    ext j
    simp only [he', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hj : j = l
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp (hd l)
  have hlhs : coeff e' (pderiv ℂ l Φ) = coeff e Φ * (e' l + 1) := by
    rw [coeff_pderiv, hee]
  have hrhs : coeff e' (G * Φ) = 0 := by
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp' := Finset.mem_antidiagonal.mp hp
    have hdeg : p.2.degree < d := by
      have h1 : p.1.degree + p.2.degree = e'.degree := by
        rw [← hp', map_add]
      have h2 : e'.degree + 1 = e.degree := by
        rw [← hee, map_add, Finsupp.degree_single]
      omega
    rw [hmin _ hdeg, mul_zero]
  have hcast : (e' l : ℂ) + 1 ≠ 0 := by
    have : ((e' l + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
    simpa using this
  rw [← hG, hrhs] at hlhs
  exact he (by simpa [hcast] using hlhs.symm)

/-! ### Partial derivatives along the free coordinates of a submersive presentation -/

section Kaehler

variable {A : Type*} [CommRing A] [Algebra ℂ A] {ι σ : Type*} [Finite ι] [Finite σ]
  (P : Algebra.SubmersivePresentation ℂ A ι σ)

/-- The free coordinates of a submersive presentation: the variables not used by the
relations. -/
abbrev FreeIndex : Type _ := ((Set.range P.map)ᶜ : Set ι)

instance : Fintype (FreeIndex P) := Fintype.ofFinite _

/-- The partial derivative `∂ₖ : A → A` along the free coordinate `tₖ` (the `k`-th coordinate of
`d a` in the basis `(d tₖ)ₖ` of `Ω_{A/ℂ}`). -/
def partialDeriv (k : FreeIndex P) : Derivation ℂ A A :=
  (P.basisKaehler.coord k).compDer (KaehlerDifferential.D ℂ A)

omit [Finite ι] in
theorem partialDeriv_apply (k : FreeIndex P) (a : A) :
    partialDeriv P k a = P.basisKaehler.repr (KaehlerDifferential.D ℂ A a) k := rfl

omit [Finite ι] in
open Classical in
/-- `∂ₖ tⱼ = δₖⱼ`. -/
theorem partialDeriv_val (k j : FreeIndex P) :
    partialDeriv P k (P.val j) = if j = k then 1 else 0 := by
  rw [partialDeriv_apply, ← Algebra.SubmersivePresentation.basisKaehler_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

/-- **Every derivation is determined by its values on the free coordinates**:
`δ a = ∑ₖ ∂ₖ a • δ tₖ`. -/
theorem derivation_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module ℂ M]
    [IsScalarTower ℂ A M] (δ : Derivation ℂ A M) (a : A) :
    δ a = ∑ k : FreeIndex P, partialDeriv P k a • δ (P.val k) := by
  rw [← δ.liftKaehlerDifferential_comp_D, ← P.basisKaehler.sum_repr (KaehlerDifferential.D ℂ A a),
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.SubmersivePresentation.basisKaehler_apply,
    Derivation.liftKaehlerDifferential_comp_D, partialDeriv_apply]

end Kaehler

/-! ### Generic smoothness -/

section Generic

variable {A : Type*} [CommRing A] [Algebra ℂ A] {ι σ : Type*} [Finite ι] [Finite σ]
  (P : Algebra.SubmersivePresentation ℂ A ι σ)

/-- **Generic smoothness of a principal prime divisor.**  Let `𝔮 ⊂ A` be prime, `u ∈ 𝔮` nonzero
and `s ∉ 𝔮` with `s 𝔮 ⊆ (u)`.  Assume that at every maximal ideal `𝔪 ⊇ 𝔮` with `s ∉ 𝔪` there
is an injective `ℂ`-algebra map `θ_𝔪 : A → ℂ⟦X⟧` whose constant coefficient vanishes exactly on
`𝔪`.  If `A` is a Jacobson domain, some such `𝔪` does not contain some `∂ₖ u`. -/
theorem exists_maximal_partialDeriv_notMem [IsDomain A] [IsJacobsonRing A] {n : ℕ}
    {𝔮 : Ideal A} [h𝔮 : 𝔮.IsPrime] {u s : A} (hu0 : u ≠ 0) (hu : u ∈ 𝔮) (hs : s ∉ 𝔮)
    (hsq : ∀ a ∈ 𝔮, s * a ∈ Ideal.span {u})
    (θ : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → s ∉ 𝔪 → A →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
    (hθinj : ∀ 𝔪 h₁ h₂ h₃, Function.Injective (θ 𝔪 h₁ h₂ h₃))
    (hθ0 : ∀ 𝔪 h₁ h₂ h₃ a, constantCoeff (θ 𝔪 h₁ h₂ h₃ a) = 0 ↔ a ∈ 𝔪) :
    ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ 𝔮 ≤ 𝔪 ∧ s ∉ 𝔪 ∧ ∃ k, partialDeriv P k u ∉ 𝔪 := by
  by_contra H
  push Not at H
  have hJ : 𝔮.jacobson = 𝔮 := IsJacobsonRing.out inferInstance h𝔮.isRadical
  -- all partial derivatives of `u` lie in `𝔮`
  have hk : ∀ k, partialDeriv P k u ∈ 𝔮 := by
    intro k
    have hmem : s * partialDeriv P k u ∈ 𝔮.jacobson := by
      refine Ideal.mem_sInf.mpr fun J ⟨hqJ, hJmax⟩ => ?_
      by_cases hsJ : s ∈ J
      · exact J.mul_mem_right _ hsJ
      · exact J.mul_mem_left _ (H J hJmax hqJ hsJ k)
    rw [hJ] at hmem
    exact (h𝔮.mem_or_mem hmem).resolve_left hs
  have hc : ∀ k, ∃ c, s * partialDeriv P k u = u * c := fun k => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hsq _ (hk k))
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  -- a maximal ideal over `𝔮` avoiding `s`
  obtain ⟨𝔪, h𝔮𝔪, h𝔪, hs𝔪⟩ : ∃ 𝔪 : Ideal A, 𝔮 ≤ 𝔪 ∧ 𝔪.IsMaximal ∧ s ∉ 𝔪 := by
    have hs' : s ∉ 𝔮.jacobson := by rwa [hJ]
    simpa [Ideal.jacobson, Ideal.mem_sInf] using hs'
  set θ₀ := θ 𝔪 h𝔪 h𝔮𝔪 hs𝔪 with hθ₀
  let : Algebra A (MvPowerSeries (Fin n) ℂ) := θ₀.toRingHom.toAlgebra
  have : IsScalarTower ℂ A (MvPowerSeries (Fin n) ℂ) :=
    IsScalarTower.of_algebraMap_eq fun x => (θ₀.commutes x).symm
  have hu0' : constantCoeff (θ₀ u) = 0 := (hθ0 𝔪 h𝔪 h𝔮𝔪 hs𝔪 u).mpr (h𝔮𝔪 hu)
  have hsunit : IsUnit (θ₀ s) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr fun h => hs𝔪 ((hθ0 𝔪 h𝔪 h𝔮𝔪 hs𝔪 s).mp h)
  have hder : ∀ l, pderiv ℂ l (θ₀ u) ∈ Ideal.span {θ₀ u} := by
    intro l
    let δ : Derivation ℂ A (MvPowerSeries (Fin n) ℂ) := (pderiv ℂ l).compAlgebraMap A
    have hδ : ∀ a, δ a = pderiv ℂ l (θ₀ a) := fun a => rfl
    have hexp := derivation_eq_sum P δ u
    rw [hδ] at hexp
    have hsmul : ∀ (a : A) (m : MvPowerSeries (Fin n) ℂ), a • m = θ₀ a * m := fun _ _ => rfl
    simp only [hsmul] at hexp
    have hmul : θ₀ s * pderiv ℂ l (θ₀ u) =
        θ₀ u * ∑ k : FreeIndex P, θ₀ (c k) * δ (P.val k) := by
      rw [hexp, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul, hc k, map_mul, mul_assoc]
    obtain ⟨w, hw⟩ := hsunit
    have : pderiv ℂ l (θ₀ u) = θ₀ u * (↑w⁻¹ * ∑ k : FreeIndex P, θ₀ (c k) * δ (P.val k)) := by
      rw [← hw] at hmul
      calc pderiv ℂ l (θ₀ u) = ↑w⁻¹ * (↑w * pderiv ℂ l (θ₀ u)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = _ := by rw [hmul]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hz : θ₀ u = 0 := eq_zero_of_pderiv_mem_span hu0' hder
  exact hu0 (hθinj 𝔪 h𝔪 h𝔮𝔪 hs𝔪 (by rw [hz, map_zero]))

/-- **A faithful linear family of point derivations does not kill `u`** at a point where some
`∂ₖ u` does not vanish.  Let `ev : A → ℂ` be a `ℂ`-algebra map and `F v` (`v ∈ ℂⁿ`) point
derivations at `ev` (additive, Leibniz, zero on constants), linear in `v`, such that `F v = 0`
forces `v = 0`.  If the presentation has `n` free coordinates and `ev (∂ₖ u) ≠ 0`, then
`F v u ≠ 0` for some `v`. -/
theorem exists_pointDerivation_ne_zero {n : ℕ} (ev : A →ₐ[ℂ] ℂ)
    (F : (Fin n → ℂ) → A → ℂ)
    (hadd : ∀ v a b, F v (a + b) = F v a + F v b)
    (hmul : ∀ v a b, F v (a * b) = ev a * F v b + ev b * F v a)
    (hconst : ∀ v (c : ℂ), F v (algebraMap ℂ A c) = 0)
    (hlin_add : ∀ v w a, F (v + w) a = F v a + F w a)
    (hlin_smul : ∀ (c : ℂ) v a, F (c • v) a = c * F v a)
    (hfaith : ∀ v, (∀ a, F v a = 0) → v = 0)
    (hcard : Fintype.card (FreeIndex P) = n) {u : A} {k₀ : FreeIndex P}
    (hk₀ : ev (partialDeriv P k₀ u) ≠ 0) :
    ∃ v, F v u ≠ 0 := by
  classical
  let : Algebra A ℂ := ev.toRingHom.toAlgebra
  have : IsScalarTower ℂ A ℂ := IsScalarTower.of_algebraMap_eq fun x => (ev.commutes x).symm
  have hsmul : ∀ (a : A) (z : ℂ), a • z = ev a * z := fun _ _ => rfl
  -- each `F v` is a derivation
  let L : (Fin n → ℂ) → A →ₗ[ℂ] ℂ := fun v =>
    { toFun := F v
      map_add' := hadd v
      map_smul' := fun c a => by
        rw [Algebra.smul_def, hmul, hconst, mul_zero, add_zero, RingHom.id_apply, smul_eq_mul,
          AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] }
  let D : (Fin n → ℂ) → Derivation ℂ A ℂ := fun v =>
    Derivation.mk' (L v) (fun a b => by
      change F v (a * b) = ev a * F v b + ev b * F v a
      exact hmul v a b)
  have hD : ∀ v a, D v a = F v a := fun _ _ => rfl
  have hexp : ∀ v a, F v a = ∑ k : FreeIndex P, ev (partialDeriv P k a) * F v (P.val k) := by
    intro v a
    rw [← hD, derivation_eq_sum P (D v) a]
    rfl
  -- the linear map `v ↦ (F v tₖ)ₖ` is injective, hence surjective
  let Λ : (Fin n → ℂ) →ₗ[ℂ] (FreeIndex P → ℂ) :=
    { toFun := fun v k => F v (P.val k)
      map_add' := fun v w => by ext k; exact hlin_add v w _
      map_smul' := fun c v => by ext k; exact hlin_smul c v _ }
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hfaith v
    intro a
    rw [hexp]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : F v (P.val k) = 0 := congrFun hv k
    rw [this, mul_zero]
  have hsurj : Function.Surjective Λ := by
    have hdim : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ (FreeIndex P → ℂ) := by
      rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, hcard]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨v, hv⟩ := hsurj (Pi.single k₀ 1)
  refine ⟨v, ?_⟩
  rw [hexp]
  have hv' : ∀ k : FreeIndex P, F v (P.val k) = (Pi.single k₀ (1 : ℂ) : FreeIndex P → ℂ) k := fun k => by
    have h := congrFun hv k
    exact h
  simp only [hv', Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact hk₀

end Generic

end SGPT.NAPotential.AlgPrimes2

end
