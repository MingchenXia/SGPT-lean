import SGPT.Okounkov.OF5AdmissibleFlagValuation
import SGPT.NAPotential.AlgPrimes2Divisor
import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGermFactoriality

/-!
# The order along a prime divisor is at most the multiplicity at its points

Source: chapter *The theory of Okounkov bodies*, `thm:nuOk`, where `ν(φ, E)` for the prime divisor
`E = Y₁` of `X` is the generic Lelong number `min_{x ∈ E} ν(φ, x)` of `def:pshfunctions:L1101`.
The comparison of `ν(φ, E)` with the Lelong numbers at **all** points of `E(ℂ)` (not only at the
points of the analytic branch of `E(ℂ)` through a smooth point of `E`) rests on the elementary
inequality

  `ord_E(g) ≤ mult_x(g)` for every point `x ∈ E(ℂ)` and every `g ∈ 𝒪_{X,x}`,

which we prove here with the analytic multiplicity (the `𝔪`-adic order of the analytic germ):
if `ord_E(g) ≥ b` then the analytic germ of `g` at `x` lies in `𝔪_x^b`.

## Proof

`𝒪_{X,x} → 𝒪^an_{X,x}` is faithfully flat and `𝒪^an_{X,x}` is factorial. Let `t ∈ 𝒪_{X,x}` with
`ord_E(t) = 1`. Some prime factor `π` of the analytic germ of `t` satisfies
`{r : π ∣ r^an} ⊆ 𝔮_E` (otherwise the product of witnesses `s_π ∉ 𝔮_E`, `π ∣ s_π^an`, is divisible
by `t^an`, hence by `t` by faithful flatness, hence lies in the prime `𝔮_E`). Writing `g = t^b r/s`
in `𝒪_{X,E}` with `s ∉ 𝔮_E` (localization) gives `π^b ∣ g^an`, and `π ∈ 𝔪_x`.

No smoothness of `E` at `x` and no analytic irreducibility of `E(ℂ)` is used.

## Main results

* `SGPT.Okounkov.OF7.map_mem_maximalIdeal_pow` (commutative algebra);
* `SGPT.Okounkov.OF7.stalkToModel_mem_maximalIdeal_pow_of_le_ord`: for `z` of codimension one,
  `z ⤳ x`, `g ∈ 𝒪_{X,x}` with `b ≤ ord_z(g)`, the analytic germ of `g` at `x` lies in `𝔪^b`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.OF7

open AlgebraicGeometry CategoryTheory Topology IsLocalRing
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.NAPotential.FSPos SGPT.NAPotential.AlgPrimes2

/-! ### Commutative algebra -/

section Algebra

/-- **Faithfully flat maps reflect divisibility.** -/
theorem dvd_of_map_dvd {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : φ.FaithfullyFlat) {a b : R} (h : φ a ∣ φ b) : a ∣ b := by
  let := φ.toAlgebra
  let : Module.FaithfullyFlat R S := hφ
  rw [← Ideal.mem_span_singleton] at h ⊢
  have hmap : Ideal.span {φ a} = (Ideal.span {a}).map φ := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hmap] at h
  have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (Ideal.span {a})
  rw [← this]
  exact h

/-- **A prime factor cutting out `𝔮`.** Let `φ : R → A` be faithfully flat with `A` factorial,
`𝔮` a prime of `R` and `t ∈ 𝔮` nonzero. Some prime factor `π` of `φ(t)` has
`φ⁻¹(π A) ⊆ 𝔮`. -/
theorem exists_prime_dvd_comap_le {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] (φ : R →+* A) (hφ : φ.FaithfullyFlat)
    (q : Ideal R) (hq : q.IsPrime) {t : R} (ht : t ∈ q) (ht0 : t ≠ 0) :
    ∃ π : A, Prime π ∧ π ∣ φ t ∧ ∀ r : R, π ∣ φ r → r ∈ q := by
  classical
  have hφt : φ t ≠ 0 := fun h => ht0 (hφ.injective (by rw [h, map_zero]))
  by_contra hcon
  push Not at hcon
  have hsel : ∀ π ∈ UniqueFactorizationMonoid.factors (φ t), ∃ s : R, π ∣ φ s ∧ s ∉ q := by
    intro π hπ
    exact hcon π (UniqueFactorizationMonoid.prime_of_factor π hπ)
      (UniqueFactorizationMonoid.dvd_of_mem_factors hπ)
  choose! s hs using hsel
  set F := UniqueFactorizationMonoid.factors (φ t) with hF
  have h1 : (F.map id).prod ∣ (F.map (fun π => φ (s π))).prod :=
    Multiset.prod_dvd_prod_of_dvd _ _ (fun π hπ => (hs π hπ).1)
  rw [Multiset.map_id] at h1
  have h2 : φ t ∣ φ (F.map s).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    exact (UniqueFactorizationMonoid.factors_prod hφt).symm.dvd.trans h1
  obtain ⟨c, hc⟩ := dvd_of_map_dvd φ hφ h2
  have hmem : (F.map s).prod ∈ q := by
    rw [hc]
    exact q.mul_mem_right c ht
  obtain ⟨r, hr, hrq⟩ := (hq.multiset_prod_mem_iff_exists_mem _).mp hmem
  obtain ⟨π, hπ, rfl⟩ := Multiset.mem_map.mp hr
  exact (hs π hπ).2 hrq

/-- **Order along a prime versus multiplicity, abstract form.** Let `ρ : R → D` be an injective
map to a discrete valuation ring such that every element of `D` is a fraction `ρ r / ρ s` with
`ρ s` a unit (a localization at a prime), and `φ : R → A` faithfully flat to a factorial local
domain. If `ρ g = ϖ^b u` for a uniformizer `ϖ`, then `φ g ∈ 𝔪_A^b`. -/
theorem map_mem_maximalIdeal_pow {R D A : Type*} [CommRing R] [CommRing D] [IsDomain D]
    [IsDiscreteValuationRing D] [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [IsLocalRing A] (ρ : R →+* D) (hρ : Function.Injective ρ)
    (hL : ∀ c : D, ∃ r s : R, IsUnit (ρ s) ∧ ρ s * c = ρ r)
    (φ : R →+* A) (hφ : φ.FaithfullyFlat) {ϖ : D} (hϖ : Irreducible ϖ) {g : R} {b : ℕ}
    {u : D} (hg : ρ g = ϖ ^ b * u) :
    φ g ∈ maximalIdeal A ^ b := by
  obtain ⟨t, s₀, hs₀, ht⟩ := hL ϖ
  set q : Ideal R := (maximalIdeal D).comap ρ with hqdef
  have hq : q.IsPrime := Ideal.IsPrime.comap ρ
  have htq : t ∈ q := by
    change ρ t ∈ maximalIdeal D
    rw [← ht]
    exact Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hϖ.not_isUnit)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at ht
    exact hϖ.ne_zero ((hs₀.mul_right_eq_zero).mp ht)
  obtain ⟨π, hπ, hπt, hπq⟩ := exists_prime_dvd_comap_le φ hφ q hq htq ht0
  have hnot : ∀ s : R, IsUnit (ρ s) → ¬π ∣ φ s := by
    intro s hs hdvd
    have h := hπq s hdvd
    exact (mem_maximalIdeal _).mp h hs
  obtain ⟨r₁, s₁, hs₁, hu⟩ := hL u
  have hkey : g * s₀ ^ b * s₁ = t ^ b * r₁ := by
    apply hρ
    simp only [map_mul, map_pow]
    rw [hg, ← ht, ← hu]
    ring
  have hφkey : φ g * φ s₀ ^ b * φ s₁ = φ t ^ b * φ r₁ := by
    rw [← map_pow, ← map_mul, ← map_mul, hkey, map_mul, map_pow]
  have hdvd : π ^ b ∣ φ g * φ s₀ ^ b * φ s₁ := by
    rw [hφkey]
    exact (pow_dvd_pow_of_dvd hπt b).mul_right _
  have h1 := hπ.pow_dvd_of_dvd_mul_right b (hnot s₁ hs₁) hdvd
  have hs₀b : ¬π ∣ φ s₀ ^ b := fun h => hnot s₀ hs₀ (hπ.dvd_of_dvd_pow h)
  have h2 := hπ.pow_dvd_of_dvd_mul_right b hs₀b h1
  obtain ⟨c, hc⟩ := h2
  rw [hc]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow ((mem_maximalIdeal _).mpr hπ.not_isUnit) b)

end Algebra

/-! ### The scheme: specialization to a point of codimension one -/

section Scheme

variable {X : Scheme.{0}} [IsIntegral X]

/-- The specialization map `𝒪_{X,x} → 𝒪_{X,z}` (`z ⤳ x`) of an integral scheme is injective. -/
theorem stalkSpecializes_injective {z x : X} (h : z ⤳ x) :
    Function.Injective (X.presheaf.stalkSpecializes h).hom := by
  intro a b hab
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [← OF5.algebraMap_stalkSpecializes h a, ← OF5.algebraMap_stalkSpecializes h b, hab]

omit [IsIntegral X] in
/-- **`𝒪_{X,z}` is a localization of `𝒪_{X,x}`** (`z ⤳ x`): every element of `𝒪_{X,z}` is a
fraction of elements of `𝒪_{X,x}` with a unit denominator. -/
theorem exists_stalkSpecializes_fraction {z x : X} (h : z ⤳ x) (c : X.presheaf.stalk z) :
    ∃ r s : X.presheaf.stalk x, IsUnit ((X.presheaf.stalkSpecializes h).hom s) ∧
      (X.presheaf.stalkSpecializes h).hom s * c = (X.presheaf.stalkSpecializes h).hom r := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hzV : z ∈ V := h.mem_open V.isOpen hxV
  obtain ⟨a, t, ht, hc⟩ := exists_germ_mul_eq hV (hV.primeIdealOf ⟨z, hzV⟩) hzV
    (hV.fromSpec_primeIdealOf ⟨z, hzV⟩) c
  have hspec : ∀ w, (X.presheaf.stalkSpecializes h).hom (X.presheaf.germ V x hxV w) =
      X.presheaf.germ V z hzV w := fun w => by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨z, hzV⟩
  have hlocz : IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hzV⟩
  have hunit : IsUnit (X.presheaf.germ V z hzV t) := by
    by_contra hnu
    apply ht
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal t).mp ((mem_maximalIdeal _).mpr hnu)
  refine ⟨X.presheaf.germ V x hxV a, X.presheaf.germ V x hxV t, ?_, ?_⟩
  · rw [hspec]
    exact hunit
  · rw [hspec, hspec, mul_comm, hc]

variable [IsLocallyNoetherian X]

/-- The order at `z` of a uniformizer of the discrete valuation ring `𝒪_{X,z}` is one. -/
theorem ord_irreducible {z : X} (hz : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ) :
    Scheme.ord (algebraMap (X.presheaf.stalk z) X.functionField ϖ) z = 1 := by
  have hw0 : algebraMap (X.presheaf.stalk z) X.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hϖ.ne_zero
  rw [Scheme.ord_eq_iff hz hw0]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  change Ring.ordFrac (X.presheaf.stalk z) _ = _
  rw [Ring.ordFrac_irreducible hϖ]
  rfl

/-- **`ord_z ≥ b` means divisibility by the `b`-th power of a uniformizer.** -/
theorem exists_eq_pow_mul_of_le_ord {z x : X} (hz : Order.coheight z = 1) (hzx : z ⤳ x)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] {ϖ : X.presheaf.stalk z} (hϖ : Irreducible ϖ)
    {g : X.presheaf.stalk x} (hg : g ≠ 0) {b : ℕ}
    (hb : (b : ℤ) ≤ Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) z) :
    ∃ u : X.presheaf.stalk z, (X.presheaf.stalkSpecializes hzx).hom g = ϖ ^ b * u := by
  set ρ := (X.presheaf.stalkSpecializes hzx).hom with hρ
  have hρg : ρ g ≠ 0 := fun h0 =>
    hg (stalkSpecializes_injective hzx (by rw [map_zero]; exact h0))
  obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hρg hϖ
  set alg := algebraMap (X.presheaf.stalk z) X.functionField with halg
  have hinj : Function.Injective alg := IsFractionRing.injective _ _
  have hϖ0 : alg ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hw0 : alg (w : X.presheaf.stalk z) ≠ 0 := (map_ne_zero_iff _ hinj).mpr w.ne_zero
  have hpow : ∀ j : ℕ, Scheme.ord (alg ϖ ^ j) z = j := by
    intro j
    induction j with
    | zero =>
      have h1 := Scheme.ord_mul (X := X) (x := z) (one_ne_zero (α := X.functionField))
        (one_ne_zero (α := X.functionField))
      rw [mul_one] at h1
      simp only [pow_zero, Nat.cast_zero]
      omega
    | succ j ih =>
      rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_irreducible hz hϖ]
      push_cast
      ring
  have hord : Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) z = k := by
    rw [← OF5.algebraMap_stalkSpecializes hzx g, ← hρ, hw, map_mul, map_pow,
      Scheme.ord_mul hw0 (pow_ne_zero _ hϖ0), OF5.ord_eq_zero_of_isUnit hz w.isUnit, hpow,
      zero_add]
  rw [hord] at hb
  have hbk : b ≤ k := by exact_mod_cast hb
  refine ⟨(w : X.presheaf.stalk z) * ϖ ^ (k - b), ?_⟩
  rw [hw, mul_left_comm, ← pow_add, Nat.add_sub_cancel' hbk]

end Scheme

/-! ### The analytic germ at a complex point -/

section Analytic

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  [IsProper f] [IsIntegral X]

local instance of7GermPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance of7GermPointCharts :
    ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance of7GermPointManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- **`ord_E(g) ≤ mult_x(g)` at every point `x ∈ E(ℂ)`.** Let `z` be a point of codimension one of
the smooth integral complex scheme `X` (`E = {z}‾` a prime divisor, possibly singular at `x`) and
`x` a complex point of `E` (`z ⤳ x`). If `g ∈ 𝒪_{X,x}` is nonzero with `b ≤ ord_E(g)`, then the
analytic germ of `g` at `x` (in the preferred chart, `stalkToModel`) lies in `𝔪^b`. -/
theorem stalkToModel_mem_maximalIdeal_pow_of_le_ord [IsLocallyNoetherian X]
    (x : SchemeComplexPoint f) {z : X} (hz : Order.coheight z = 1)
    (hzx : z ⤳ schemeComplexPointImage f x)
    {g : X.presheaf.stalk (schemeComplexPointImage f x)} (hg : g ≠ 0) {b : ℕ}
    (hb : (b : ℤ) ≤ Scheme.ord
      (algebraMap (X.presheaf.stalk (schemeComplexPointImage f x)) X.functionField g) z) :
    stalkToModel f (m + 1) x g ∈ maximalIdeal (HolGerm (ComplexModel (m + 1))) ^ b := by
  have : IsDiscreteValuationRing (X.presheaf.stalk z) :=
    isDiscreteValuationRing_stalk f (m + 1) hz
  have : UniqueFactorizationMonoid (HolGerm (ComplexModel (m + 1))) :=
    ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean (m + 1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  obtain ⟨u, hu⟩ := exists_eq_pow_mul_of_le_ord hz hzx hϖ hg hb
  exact map_mem_maximalIdeal_pow (X.presheaf.stalkSpecializes hzx).hom
    (stalkSpecializes_injective hzx) (exists_stalkSpecializes_fraction hzx)
    (stalkToModel f (m + 1) x) (stalkToModel_faithfullyFlat x) hϖ hu

end Analytic

end SGPT.Okounkov.OF7
