import SGPT.Okounkov.OF6ZariskiModel
import SGPT.Foundations.Schemes.NativeFanoAffineChartDimension

/-!
# Zariski's realization of the first coordinate `ν₁` of a maximal-rank valuation

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (*a valuation with value group
`ℤⁿ_lex` and maximal rational rank `n` is equivalent to a valuation induced by an admissible flag on
a modification of `X`*, [CFKLRS17, Theorem 2.9]). The proof of the cited theorem starts by
realizing the first coordinate `ν₁ = pr₁ ∘ ν` (a divisorial valuation, lane OF4) as `ord_E` for a
prime divisor `E` on a normal birational model of `X`.

`exists_normalChart_prefixOne`: let `X` be an integral scheme, smooth of relative dimension
`n = m + 1` over `ℂ`, `ν : ℂ(X)^× → ℤⁿ_lex` surjective, and `V ⊆ X` an affine open on which `ν ≥ 0`
(an affine neighbourhood of the centre of `ν`, `exists_normalChart_prefixOne_of_center`). There is
a finitely generated `ℂ`-algebra `A' ⊆ ℂ(X)` containing `Γ(X, V)` whose normalization `A` (the
integral closure of `A'` in `ℂ(X)`) satisfies:

* `A` is a finitely generated normal `ℂ`-domain with fraction field `ℂ(X)` — `Spec A` is a normal
  affine variety with a birational morphism `Spec A → V ⊆ X` (`Γ(X, V) ⊆ A`);
* `ν₁ ≥ 0` on `A`, and its centre `q = {a ∈ A : ν₁(a) > 0}` is a nonzero prime of height one
  (`E = V(q)` is a prime divisor of `Spec A`), `A_q` is a discrete valuation ring;
* **the valuation ring of `ν₁` is `A_q`**: `ν₁(x) ≥ 0 ⟺ x s ∈ A` for some `s ∈ A ∖ q`; since `ν₁` is
  surjective onto `ℤ`, `ν₁ = ord_E`.

Not formalized: the compactification of `Spec A` into a normal *proper* birational model of `X`
(a `SGPT.NAPotential.Berkovich.PrimeDivisorOver X`), and the remaining induction of
[CFKLRS17, Thm 2.9].
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes IsLocalRing

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))

/-- **Zariski's realization of the divisorial first coordinate `ν₁` on a normal affine chart.**
See the module docstring. -/
theorem exists_normalChart_prefixOne {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) (V : X.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (hνV : ∀ s : Γ(X, V), 0 ≤ ν (algebraMap Γ(X, V) X.functionField s)) :
    letI := schemeFunctionFieldAlgebra f
    ∃ A' : Subalgebra ℂ X.functionField, A'.FG ∧
      (∀ s : Γ(X, V), algebraMap Γ(X, V) X.functionField s ∈ A') ∧
      ∃ hA : ∀ a : integralClosure A' X.functionField,
          0 ≤ OF4.prefixOne ν (algebraMap (integralClosure A' X.functionField) X.functionField a),
        Algebra.FiniteType ℂ (integralClosure A' X.functionField) ∧
        IsIntegrallyClosed (integralClosure A' X.functionField) ∧
        IsFractionRing (integralClosure A' X.functionField) X.functionField ∧
        centerIdeal (OF4.prefixOne ν) hA ≠ ⊥ ∧
        (∀ p : Ideal (integralClosure A' X.functionField), p.IsPrime →
          p ≤ centerIdeal (OF4.prefixOne ν) hA → p = ⊥ ∨ p = centerIdeal (OF4.prefixOne ν) hA) ∧
        (haveI := centerIdeal_isPrime (OF4.prefixOne ν) hA;
          IsDiscreteValuationRing (Localization.AtPrime (centerIdeal (OF4.prefixOne ν) hA))) ∧
        ∀ x : X.functionField, 0 ≤ OF4.prefixOne ν x ↔
          ∃ a s : integralClosure A' X.functionField, s ∉ centerIdeal (OF4.prefixOne ν) hA ∧
            x * algebraMap (integralClosure A' X.functionField) X.functionField s =
              algebraMap (integralClosure A' X.functionField) X.functionField a := by
  let := schemeFunctionFieldAlgebra f
  let := affineChartAlgebra f V
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : Algebra.FiniteType ℂ Γ(X, V) := affineChartAlgebra_finiteType f hV
  have : IsScalarTower ℂ Γ(X, V) X.functionField := schemeFunctionField_affineChartScalarTower f V
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  -- `ν₁ ≥ 0` on `Γ(X, V)`
  have hB : ∀ s : Γ(X, V), 0 ≤ OF4.prefixOne ν (algebraMap Γ(X, V) X.functionField s) := by
    intro s
    have h0 : ValCurr.prefixWithTopHom (Nat.succ_le_succ (Nat.zero_le m)) 0 = 0 := map_zero _
    change 0 ≤ ValCurr.prefixWithTopHom _ (ν _)
    rw [← h0]
    exact ValCurr.monotone_prefixWithTopHom _ (hνV s)
  -- an element of `ν₁`-value `1`
  obtain ⟨x, hx⟩ := OF4.exists_val_eq_single ν hν
  have hx0 : OF4.prefixOne ν (x 0) =
      ((toLex (Pi.single (0 : Fin 1) (1 : ℤ)) : Lex (Fin 1 → ℤ)) : WithTop (Lex (Fin 1 → ℤ))) := by
    rw [OF4.prefixOne_coe ν _ _ (hx 0)]
    congr 2
    funext i
    fin_cases i
    simp
  have hx0ne : OF4.prefixOne ν (x 0) ≠ 0 := by
    rw [hx0]
    intro h
    have h' := congrArg (fun z : Lex (Fin 1 → ℤ) => ofLex z 0) (WithTop.coe_injective h)
    simp only [ofLex_toLex, Pi.single_eq_same] at h'
    exact one_ne_zero h'
  have hx0' : x 0 ≠ 0 := by
    intro h
    have h' := hx 0
    rw [h, AddValuation.map_zero] at h'
    exact WithTop.top_ne_coe h'
  -- transcendence degree `m + 1`
  have htr : ∀ z : Fin (m + 2) → X.functionField, ¬ AlgebraicIndependent ℂ z := by
    intro z hz
    have h := hz.cardinalMk_le_trdeg
    rw [nativeSmoothFunctionField_trdeg f (m + 1), Cardinal.mk_fintype, Fintype.card_fin] at h
    norm_cast at h
    omega
  -- `m` elements with independent `ν₁`-residues
  obtain ⟨y, hy⟩ := OF4.exists_residue_independent_prefixOne f ν hν
  obtain ⟨A', -, hFG, hBA, -, hA, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_normalChart_of_divisorial (k := ℂ) (B := Γ(X, V)) (OF4.prefixOne ν) hB hx0ne hx0'
      htr y hy
  exact ⟨A', hFG, hBA, hA, h1, h2, h3, h4, h5, h6, h7⟩

/-- **Zariski's realization of `ν₁` near the centre**: the conclusion of
`exists_normalChart_prefixOne` holds for every affine open `V` containing a centre `c` of `ν`
(`ν ≥ 0` on `𝒪_{X,c}`; on a proper `X` the centre exists,
`SGPT.Okounkov.AlgebraicValuation.exists_isValuationCenter`). -/
theorem exists_normalChart_prefixOne_of_center {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) {c : X} (hc : AlgebraicValuation.IsValuationCenter ν c)
    (V : X.Opens) (hV : IsAffineOpen V) (hcV : c ∈ V) :
    haveI : Nonempty V := ⟨⟨c, hcV⟩⟩
    letI := schemeFunctionFieldAlgebra f
    ∃ A' : Subalgebra ℂ X.functionField, A'.FG ∧
      (∀ s : Γ(X, V), algebraMap Γ(X, V) X.functionField s ∈ A') ∧
      ∃ hA : ∀ a : integralClosure A' X.functionField,
          0 ≤ OF4.prefixOne ν (algebraMap (integralClosure A' X.functionField) X.functionField a),
        Algebra.FiniteType ℂ (integralClosure A' X.functionField) ∧
        IsIntegrallyClosed (integralClosure A' X.functionField) ∧
        IsFractionRing (integralClosure A' X.functionField) X.functionField ∧
        centerIdeal (OF4.prefixOne ν) hA ≠ ⊥ ∧
        (∀ p : Ideal (integralClosure A' X.functionField), p.IsPrime →
          p ≤ centerIdeal (OF4.prefixOne ν) hA → p = ⊥ ∨ p = centerIdeal (OF4.prefixOne ν) hA) ∧
        (haveI := centerIdeal_isPrime (OF4.prefixOne ν) hA;
          IsDiscreteValuationRing (Localization.AtPrime (centerIdeal (OF4.prefixOne ν) hA))) ∧
        ∀ x : X.functionField, 0 ≤ OF4.prefixOne ν x ↔
          ∃ a s : integralClosure A' X.functionField, s ∉ centerIdeal (OF4.prefixOne ν) hA ∧
            x * algebraMap (integralClosure A' X.functionField) X.functionField s =
              algebraMap (integralClosure A' X.functionField) X.functionField a := by
  have : Nonempty V := ⟨⟨c, hcV⟩⟩
  refine exists_normalChart_prefixOne f ν hν V hV fun s => ?_
  have h := hc.1 (X.presheaf.germ V c hcV s)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at h
  exact h

end SGPT.Okounkov.OF6
