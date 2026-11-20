import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Generic normality of domains with finite normalization

Source: needed for [BJ22] (`references/bj22-trivval`), §1.2 and §2.1 ("the normalization of the
blow-up is a test configuration"), towards `thm:BJappseq` of `chapter_NApotential.tex`. Blueprint:
`claude-bj-model3.tex`, node `claude-bj-model3:generic-normal`.

If the integral closure `Ã` of a domain `A` in its fraction field `K` is a finite `A`-module,
then `A` is *generically normal*: there is `d ≠ 0` such that the localization `A_d` is integrally
closed. Indeed a common denominator `d` of a finite generating set of `Ã` satisfies `d Ã ⊆ A`, and
every element of `K` integral over `A_d` has a multiple by a power of `d` integral over `A`.

Geometrically: the normalization of an integral scheme of finite type over a field is an
isomorphism over a nonempty open set (`BJModel3Normal`).

## Main results

* `exists_smul_isInteger_of_finite_integralClosure`: a common denominator `d ≠ 0` of the
  integral closure, `d • x ∈ A` for every `x ∈ K` integral over `A`;
* `isIntegrallyClosed_of_isLocalization_away`: then every localization `A_d` is integrally closed;
* `exists_isIntegrallyClosed_away`: the combination.
-/

set_option autoImplicit false

namespace SGPT.NAPotential.BJModel3

open scoped nonZeroDivisors

section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **A common denominator of a finite integral closure.** If the integral closure of the domain
`R` in its fraction field is a finite `R`-module, there is `d ≠ 0` in `R` with `d • x ∈ R` for every
element `x` of the fraction field integral over `R`. -/
theorem exists_smul_isInteger_of_finite_integralClosure
    [Module.Finite R (integralClosure R (FractionRing R))] :
    ∃ d : R, d ≠ 0 ∧ ∀ x : FractionRing R, IsIntegral R x →
      IsLocalization.IsInteger R (d • x) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := integralClosure R (FractionRing R))
  obtain ⟨⟨b, hb⟩, hbs⟩ := IsLocalization.exist_integer_multiples_of_finset (R := R)
    (R⁰) (s.image fun a : integralClosure R (FractionRing R) => (a : FractionRing R))
  refine ⟨b, nonZeroDivisors.ne_zero hb, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : integralClosure R (FractionRing R)) ∈
      Submodule.span R (s : Set (integralClosure R (FractionRing R))) := by
    rw [hs]; trivial
  have key : ∀ y ∈ Submodule.span R (s : Set (integralClosure R (FractionRing R))),
      IsLocalization.IsInteger R (b • (y : FractionRing R)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact hbs _ (Finset.mem_image_of_mem _ hy)
    | zero => simpa using IsLocalization.isInteger_zero
    | add y z _ _ hy hz =>
      rw [Subalgebra.coe_add, smul_add]
      exact IsLocalization.isInteger_add hy hz
    | smul c y _ hy =>
      rw [Subalgebra.coe_smul, smul_comm]
      exact IsLocalization.isInteger_smul hy
  exact key _ hmem

set_option backward.isDefEq.respectTransparency.types false in
/-- **Localizations at a common denominator are integrally closed.** Let `d ≠ 0` in the domain `R`
be such that `d • x ∈ R` for every `x` in the fraction field integral over `R`. Then every
localization `R_d` is integrally closed. -/
theorem isIntegrallyClosed_of_isLocalization_away (S : Type*) [CommRing S] [Algebra R S]
    {d : R} (hd : d ≠ 0) [IsLocalization.Away d S]
    (hint : ∀ x : FractionRing R, IsIntegral R x → IsLocalization.IsInteger R (d • x)) :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  have hM : Submonoid.powers d ≤ R⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra]; dsimp only [g]
        rw [IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) S K
  refine (isIntegrallyClosed_iff_isIntegralClosure (K := K)).mpr
    ⟨IsFractionRing.injective _ _, fun {x} ↦ ⟨?_, fun e ↦ e.choose_spec ▸ isIntegral_algebraMap⟩⟩
  intro hx
  obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization (Submonoid.powers d) _
  obtain ⟨z, hz⟩ := hint _ hy
  refine ⟨IsLocalization.mk' S z (⟨d * y, Submonoid.mul_mem _ (Submonoid.mem_powers d) y_mem⟩ : Submonoid.powers d),
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id, hz, Submonoid.mk_smul, smul_smul, Algebra.smul_def]

/-- **Generic normality.** If the integral closure of the domain `R` in its fraction field is a
finite `R`-module, there is `d ≠ 0` such that every localization `R_d` is integrally closed. -/
theorem exists_isIntegrallyClosed_away
    [Module.Finite R (integralClosure R (FractionRing R))] :
    ∃ d : R, d ≠ 0 ∧ ∀ (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away d S],
      IsIntegrallyClosed S := by
  obtain ⟨d, hd, hint⟩ := exists_smul_isInteger_of_finite_integralClosure (R := R)
  exact ⟨d, hd, fun S _ _ _ => isIntegrallyClosed_of_isLocalization_away S hd hint⟩

end

end SGPT.NAPotential.BJModel3
