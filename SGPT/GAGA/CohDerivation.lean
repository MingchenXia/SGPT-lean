import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Ideals stable under a derivation: transversal elements are nonzerodivisors

Infrastructure of lane COHERENT (source `lma:fibIeq`, `chapter_trace.tex` lines 1166--1193;
blueprint `claude-coherent.tex`). This is the commutative-algebra core of the coherent-sheaf
input of the reverse Bertini theorem.

Let `R` be a commutative ring in which every `k + 1` (`k : ℕ`) is a unit (e.g. a `ℂ`-algebra),
`D : R → R` an additive map with the Leibniz rule (`IsLeibniz`), and `J ⊆ R` an ideal stable
under `D` (`IsStable`). If `s ∈ R` has `D s` a unit, then

* `mem_sup_span_of_pow_mul_mem`: `s^k r ∈ J` implies `r ∈ J + (s)` (apply `D` once and induct
  on `k`: `D(s^{k+1} r) = s^k ((k+1) D(s) r + s D(r))`);
* `mem_of_mul_mem` (`R` Noetherian local, `s` in the maximal ideal): `s` is a nonzerodivisor on
  `R/J`. Indeed `s h ∈ J` gives `h ∈ J + (s^m)` for every `m`, and Krull's intersection theorem
  in the finite `R`-module `R/J` gives `h ∈ J`;
* `eq_of_le_sup_span` (Nakayama): if `I ⊆ J ⊆ I + (s)`, then `J = I + s J`, hence `J = I`.

Geometrically: on a complex manifold with a holomorphic vector field `ξ` and a coherent ideal
`J` stable under `ξ`, a function `t` with `ξ t` invertible (here `t` the coordinate of `Δ*` and
`ξ` the generator of the `S¹`-action, `ξ t = i t`) has no fibre of `t` among the associated
subvarieties of `𝒪/J`; and if `J ≡ I` modulo the ideal `(t - z)` of a fibre, then `J = I` along
that fibre. No primary decomposition of coherent sheaves is needed.
-/

set_option autoImplicit false

namespace SGPT.GAGA.Coherent

variable {R : Type*} [CommRing R]

/-- `D : R → R` is additive and satisfies the Leibniz rule (a derivation of `R` over `ℤ`, not
bundled). -/
structure IsLeibniz (D : R → R) : Prop where
  map_add : ∀ a b, D (a + b) = D a + D b
  map_mul : ∀ a b, D (a * b) = a * D b + b * D a

theorem IsLeibniz.map_zero {D : R → R} (hD : IsLeibniz D) : D 0 = 0 := by
  have h := hD.map_add 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

/-- The ideal `J` is stable under `D`. -/
def IsStable (D : R → R) (J : Ideal R) : Prop :=
  ∀ a ∈ J, D a ∈ J

/-- The sum of two `D`-stable ideals is `D`-stable. -/
theorem IsStable.sup {D : R → R} (hD : IsLeibniz D) {I J : Ideal R} (hI : IsStable D I)
    (hJ : IsStable D J) : IsStable D (I ⊔ J) := by
  intro a ha
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
  rw [hD.map_add]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy)) (Ideal.mem_sup_right (hJ z hz))

/-- `D(s^{k+1} r) = s^k ((k + 1) D(s) r + s D(r))`. -/
theorem IsLeibniz.map_pow_succ_mul {D : R → R} (hD : IsLeibniz D) (s r : R) (k : ℕ) :
    D (s ^ (k + 1) * r) = s ^ k * (((k : R) + 1) * D s * r + s * D r) := by
  induction k generalizing r with
  | zero =>
    rw [zero_add, pow_one, pow_zero, hD.map_mul]
    push_cast
    ring
  | succ k ih =>
    have h : s ^ (k + 1 + 1) * r = s ^ (k + 1) * (s * r) := by ring
    rw [h, ih, hD.map_mul]
    push_cast
    ring

/-- **Division by a transversal element.** If `J` is `D`-stable, `D s` is a unit and every
`k + 1` is a unit, then `s^k r ∈ J` implies `r ∈ J + (s)`. -/
theorem mem_sup_span_of_pow_mul_mem {D : R → R} (hD : IsLeibniz D) {J : Ideal R}
    (hJ : IsStable D J) {s : R} (hs : IsUnit (D s)) (hR : ∀ k : ℕ, IsUnit ((k : R) + 1)) :
    ∀ (k : ℕ) (r : R), s ^ k * r ∈ J → r ∈ J ⊔ Ideal.span {s} := by
  intro k
  induction k with
  | zero =>
    intro r hr
    rw [pow_zero, one_mul] at hr
    exact Ideal.mem_sup_left hr
  | succ k ih =>
    intro r hr
    have h1 := hJ _ hr
    rw [hD.map_pow_succ_mul] at h1
    have h2 := ih _ h1
    have h3 : ((k : R) + 1) * D s * r ∈ J ⊔ Ideal.span {s} := by
      have he : ((k : R) + 1) * D s * r = (((k : R) + 1) * D s * r + s * D r) - s * D r := by
        ring
      rw [he]
      exact Ideal.sub_mem _ h2
        (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨D r, mul_comm _ _⟩))
    obtain ⟨u, hu⟩ := ((hR k).mul hs).exists_left_inv
    have he : u * (((k : R) + 1) * D s * r) = r := by
      rw [show u * (((k : R) + 1) * D s * r) = (u * (((k : R) + 1) * D s)) * r by ring, hu,
        one_mul]
    rw [← he]
    exact Ideal.mul_mem_left _ u h3

/-- If `r ∈ J + (s)`, then `r = j + s c` with `j ∈ J`. -/
theorem exists_of_mem_sup_span {J : Ideal R} {s r : R} (hr : r ∈ J ⊔ Ideal.span {s}) :
    ∃ j ∈ J, ∃ c : R, r = j + s * c := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hr
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  exact ⟨y, hy, c, by ring⟩

/-- **Transversal elements are nonzerodivisors modulo a stable ideal.** Let `R` be Noetherian
local, `J` a `D`-stable ideal, `s` in the maximal ideal with `D s` a unit, and every `k + 1` a
unit. Then `s h ∈ J` implies `h ∈ J`. -/
theorem mem_of_mul_mem [IsNoetherianRing R] [IsLocalRing R] {D : R → R} (hD : IsLeibniz D)
    {J : Ideal R} (hJ : IsStable D J) {s : R} (hs : IsUnit (D s))
    (hsm : s ∈ IsLocalRing.maximalIdeal R) (hR : ∀ k : ℕ, IsUnit ((k : R) + 1)) {h : R}
    (hh : s * h ∈ J) : h ∈ J := by
  have key : ∀ m : ℕ, ∃ j ∈ J, ∃ r : R, h = j + s ^ m * r := by
    intro m
    induction m with
    | zero => exact ⟨0, J.zero_mem, h, by ring⟩
    | succ m ih =>
      obtain ⟨j, hj, r, hjr⟩ := ih
      have hr : s ^ (m + 1) * r ∈ J := by
        have he : s ^ (m + 1) * r = s * h - s * j := by rw [hjr]; ring
        rw [he]
        exact J.sub_mem hh (J.mul_mem_left s hj)
      obtain ⟨j', hj', c, hc⟩ :=
        exists_of_mem_sup_span (mem_sup_span_of_pow_mul_mem hD hJ hs hR _ _ hr)
      refine ⟨j + s ^ m * j', J.add_mem hj (J.mul_mem_left _ hj'), c, ?_⟩
      rw [hjr, hc]
      ring
  have hI : (Ideal.span {s} : Ideal R) ≠ ⊤ := by
    intro htop
    have : (⊤ : Ideal R) ≤ IsLocalRing.maximalIdeal R := by
      rw [← htop, Ideal.span_le]
      simpa using hsm
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp this)
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (Ideal.span {s}) hI
  have hmem : (Ideal.Quotient.mk J h) ∈
      (⨅ i : ℕ, (Ideal.span {s}) ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨j, hj, r, hjr⟩ := key i
    have he : Ideal.Quotient.mk J h = s ^ i • Ideal.Quotient.mk J r := by
      rw [hjr, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 hj, zero_add, map_mul,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self s) i)
      Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact (Ideal.Quotient.eq_zero_iff_mem).1 hmem

/-- **Nakayama along a transversal element.** In a Noetherian local ring, let `J` be
`D`-stable, `s` in the maximal ideal with `D s` a unit, every `k + 1` a unit, and
`I ⊆ J ⊆ I + (s)`. Then `J = I`. -/
theorem eq_of_le_sup_span [IsNoetherianRing R] [IsLocalRing R] {D : R → R} (hD : IsLeibniz D)
    {I J : Ideal R} (hJ : IsStable D J) {s : R} (hs : IsUnit (D s))
    (hsm : s ∈ IsLocalRing.maximalIdeal R) (hR : ∀ k : ℕ, IsUnit ((k : R) + 1))
    (hIJ : I ≤ J) (hJI : J ≤ I ⊔ Ideal.span {s}) : J = I := by
  refine le_antisymm ?_ hIJ
  have hsmul : J ≤ I ⊔ Ideal.span {s} • J := by
    intro g hg
    obtain ⟨i, hi, c, hc⟩ := exists_of_mem_sup_span (hJI hg)
    have hsc : s * c ∈ J := by
      have he : s * c = g - i := by rw [hc]; ring
      rw [he]
      exact J.sub_mem hg (hIJ hi)
    have hcJ : c ∈ J := mem_of_mul_mem hD hJ hs hsm hR hsc
    rw [hc]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hi)
      (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self s) hcJ))
  have hjac : (Ideal.span {s} : Ideal R) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact IsLocalRing.maximalIdeal_le_jacobson _ hsm
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J) hjac hsmul

end SGPT.GAGA.Coherent
