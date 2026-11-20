import SGPT.Okounkov.OF4AbhyankarInequality
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The centre of a maximal-rank valuation is a closed point

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (valuations of `ℂ(X)` with value
group `ℤⁿ_lex` and maximal rational rank `n = dim X`), first step of the proof of
[CFKLRS17, Thm 2.9].

Let `X` be an integral scheme smooth of relative dimension `n` over `ℂ` and
`ν : ℂ(X)^× → ℤⁿ_lex` surjective. If `c` is a centre of `ν` (`ν ≥ 0` on `𝒪_{X,c}`, `ν > 0` on
`𝔪_{X,c}`; on a proper `X` the centre exists and is unique), then

* `exists_sub_const_mem_maximalIdeal`: every `g ∈ 𝒪_{X,c}` is congruent to a constant modulo
  `𝔪_{X,c}`, i.e. `κ(c) = ℂ`;
* `isClosed_of_isValuationCenter`: `c` is a closed point of `X`.

So maximal-rank valuations are *zero-dimensional*: centred at closed points, with residue field
`ℂ` (`exists_val_sub_const_pos`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF4

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes IsLocalRing

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f]

/-- **The residue field of the centre is `ℂ`.** -/
theorem exists_sub_const_mem_maximalIdeal
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν)
    {c : X} (hc : AlgebraicValuation.IsValuationCenter ν c) (g : X.presheaf.stalk c) :
    ∃ a : ℂ, g - X.presheaf.germ ⊤ c trivial (schemeGlobalConstants f a) ∈
      maximalIdeal (X.presheaf.stalk c) := by
  obtain ⟨a, ha⟩ := exists_val_sub_const_pos f n ν hν
    (algebraMap (X.presheaf.stalk c) X.functionField g) (hc.1 g)
  refine ⟨a, ?_⟩
  have hval : algebraMap (X.presheaf.stalk c) X.functionField
      (g - X.presheaf.germ ⊤ c trivial (schemeGlobalConstants f a)) =
      algebraMap (X.presheaf.stalk c) X.functionField g -
        @algebraMap ℂ X.functionField _ _ (schemeFunctionFieldAlgebra f) a := by
    rw [map_sub]
    congr 1
    exact Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) (x := c) trivial _
  by_contra hm
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hm
  have h1 : ν (algebraMap (X.presheaf.stalk c) X.functionField (u : X.presheaf.stalk c)) +
      ν (algebraMap (X.presheaf.stalk c) X.functionField
        ((u⁻¹ : (X.presheaf.stalk c)ˣ) : X.presheaf.stalk c)) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
  have h0 := ((add_eq_zero_iff_of_nonneg (hc.1 _) (hc.1 _)).1 h1).1
  rw [hu, hval] at h0
  rw [h0] at ha
  exact lt_irrefl _ ha

/-- The residue field map of `f` at the centre is surjective. -/
theorem residueFieldMap_surjective
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν)
    {c : X} (hc : AlgebraicValuation.IsValuationCenter ν c) :
    Function.Surjective (f.residueFieldMap c).hom := by
  intro r
  obtain ⟨g, rfl⟩ := X.residue_surjective c r
  obtain ⟨a, ha⟩ := exists_sub_const_mem_maximalIdeal f n ν hν hc g
  have hres : X.residue c g =
      X.residue c (X.presheaf.germ ⊤ c trivial (schemeGlobalConstants f a)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ha
  refine ⟨(Spec (.of ℂ)).residue (f c) ((Spec (.of ℂ)).presheaf.germ ⊤ (f c) trivial
    ((Scheme.ΓSpecIso (.of ℂ)).inv a)), ?_⟩
  rw [hres]
  have key := congrArg (fun φ => φ.hom ((Spec (.of ℂ)).presheaf.germ ⊤ (f c) trivial
    ((Scheme.ΓSpecIso (.of ℂ)).inv a))) (Scheme.residue_residueFieldMap f c)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  rw [key]
  exact congrArg (X.residue c).hom (Scheme.Hom.germ_stalkMap_apply f ⊤ c trivial _)

include f in
/-- **The centre of a maximal-rank valuation is a closed point.** -/
theorem isClosed_of_isValuationCenter
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν)
    {c : X} (hc : AlgebraicValuation.IsValuationCenter ν c) : IsClosed ({c} : Set X) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [isClosed_singleton_iff_locallyOfFiniteType]
  have h1 : LocallyOfFiniteType (Spec.map (f.residueFieldMap c)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ (residueFieldMap_surjective f n ν hν hc)
  have h2 : LocallyOfFiniteType ((Spec (.of ℂ)).fromSpecResidueField (f c)) := by
    have hcl : IsClosed ({f c} : Set (Spec (.of ℂ))) := by
      have hsub : ∀ x y : Spec (.of ℂ), x = y := by
        intro x y
        have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime ℂ _ x.asIdeal x.isPrime
        have hy : y.asIdeal = ⊥ := @Ideal.eq_bot_of_prime ℂ _ y.asIdeal y.isPrime
        exact PrimeSpectrum.ext (hx.trans hy.symm)
      have : ({f c} : Set (Spec (.of ℂ))) = Set.univ :=
        Set.eq_univ_of_forall fun x => hsub x (f c)
      rw [this]
      exact isClosed_univ
    have := isClosed_singleton_iff_isClosedImmersion.mp hcl
    infer_instance
  have : LocallyOfFiniteType (X.fromSpecResidueField c ≫ f) := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  exact locallyOfFiniteType_of_comp _ f

/-- On a proper `X`, the centre `valuationCenter f ν` of a surjective `ν : ℂ(X)^× → ℤⁿ_lex` is a
closed point with residue field `ℂ`. -/
theorem isClosed_valuationCenter [IsProper f]
    (ν : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ)))) (hν : Function.Surjective ν) :
    IsClosed ({AlgebraicValuation.valuationCenter f ν} : Set X) :=
  isClosed_of_isValuationCenter f n ν hν (AlgebraicValuation.isValuationCenter_valuationCenter f ν)

end SGPT.Okounkov.OF4
