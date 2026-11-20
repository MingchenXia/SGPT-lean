import SGPT.Okounkov.OF6ZariskiScheme
import SGPT.Okounkov.OF6ResidualValuation

/-!
# The first step of [CFKLRS17, Thm 2.9]: `ν₁ = ord_E` and the residual valuation on `ℂ(E)`


Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (*a valuation with value group
`ℤⁿ_lex` and maximal rational rank `n` is equivalent to a valuation induced by an admissible flag on
a modification of `X`*, [CFKLRS17, Theorem 2.9]). The proof of the cited theorem is an induction on
`n`: realize the divisorial first coordinate `ν₁` as `ord_E` for a prime divisor `E` of a normal
model, and apply the induction hypothesis to the residual valuation of `ν` on `ℂ(E)`, of rank
`n - 1` and value group `ℤ^{n-1}_lex`.

`exists_normalChart_residual` proves the first step completely on an affine chart of the model:
for `X` integral, smooth of relative dimension `n = m + 1` over `ℂ`, a surjective
`ν : ℂ(X)^× → ℤⁿ_lex` with a centre `c` and an affine open `V ∋ c`, there is a normal finitely
generated `ℂ`-algebra `A ⊆ ℂ(X)` (the normalization of `ℂ[Γ(X, V), y]`) with fraction field `ℂ(X)`
such that

* `ν ≥ 0` on `A` (`Spec A` is a normal affine chart of a model, with `Spec A → V`, and `ν` is
  centred on it);
* `q = {a ∈ A : ν(a)₁ > 0}` is a nonzero prime of height one, `A_q` is a DVR and the valuation ring
  of `ν₁` is `A_q`: `ν₁ = ord_E` for the prime divisor `E = V(q)` (Zariski);
* the **residual valuation** `ν̄` (`ν(a) = (0, ν̄(ā))` for `a ∉ q`) is a valuation of
  `ℂ(E) = Frac(A ⧸ q)` with value group `ℤᵐ_lex` (surjective), nonnegative on the coordinate ring
  `A ⧸ q` of the affine chart of `E` (centred on it), and `trdeg_ℂ ℂ(E) ≤ m` (so `ν̄` has maximal
  rational rank `m = dim E`): the input of the induction hypothesis.

Not formalized: the compactification of these affine charts to proper models, and the induction
step (lifting an admissible flag of a model of `E` adapted to `ν̄` to a smooth model of `X` on which
the prefix centres of `ν` form an admissible flag,
`lexEquivalent_admissibleFlagValuation_of_prefixCentres`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes IsLocalRing MvPolynomial

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))

/-- The elements `x_{j+1}` with `ν(x_{j+1}) = e_{j+1}` have `ν₁`-residues algebraically independent
over `ℂ` (the proof of `SGPT.Okounkov.OF4.exists_residue_independent_prefixOne`, for a given
family). -/
theorem residue_independent_succ {m : ℕ}
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (x : Fin (m + 1) → X.functionField)
    (hx : ∀ i, ν (x i) = ((toLex (Pi.single i (1 : ℤ)) : Lex (Fin (m + 1) → ℤ)) :
      WithTop (Lex (Fin (m + 1) → ℤ)))) :
    ∀ Q : MvPolynomial (Fin m) ℂ, Q ≠ 0 →
      OF4.prefixOne ν (@aeval ℂ X.functionField (Fin m) _ _ (schemeFunctionFieldAlgebra f)
        (fun j => x j.succ) Q) = 0 := by
  let := schemeFunctionFieldAlgebra f
  intro Q hQ
  set g : Fin m → Lex (Fin (m + 1) → ℤ) := fun j => toLex (Pi.single j.succ (1 : ℤ)) with hgdef
  have hg : Function.Injective (OF4.weight g) := by
    intro d d' h
    ext j
    have hj : ∀ e : Fin m →₀ ℕ, ofLex (OF4.weight g e) j.succ = (e j : ℤ) := by
      intro e
      classical
      change (∑ i ∈ e.support, e i • (Pi.single i.succ (1 : ℤ) : Fin (m + 1) → ℤ)) j.succ = _
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, Fin.succ_inj, smul_ite, smul_zero, nsmul_eq_mul,
        mul_one]
      rw [Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · rw [Finsupp.notMem_support_iff.mp h]
        rfl
    have := congrArg (fun z : Lex (Fin (m + 1) → ℤ) => ofLex z j.succ) h
    simp only [hj] at this
    exact_mod_cast this
  obtain ⟨d, -, hd, -⟩ := OF4.val_aeval_eq_weight ν
    (fun c hc => AlgebraicValuation.valuation_algebraMap_eq_zero ν (algebraMap ℂ _) hc)
    (fun j => x j.succ) g (fun j => hx j.succ) hg hQ
  rw [OF4.prefixOne_coe ν _ _ hd]
  have h0 : ofLex (OF4.weight g d) 0 = 0 := by
    classical
    change (∑ i ∈ d.support, d i • (Pi.single i.succ (1 : ℤ) : Fin (m + 1) → ℤ)) 0 = 0
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [(Fin.succ_ne_zero i).symm]
  rw [h0]
  rfl

/-- **The first step of [CFKLRS17, Thm 2.9] on an affine chart**: Zariski's realization of `ν₁`
as `ord_E` and the residual valuation of `ν` on `ℂ(E)`. See the module docstring. -/
theorem exists_normalChart_residual {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) {c : X} (hc : AlgebraicValuation.IsValuationCenter ν c)
    (V : X.Opens) (hV : IsAffineOpen V) (hcV : c ∈ V) :
    haveI : Nonempty V := ⟨⟨c, hcV⟩⟩
    letI := schemeFunctionFieldAlgebra f
    ∃ A' : Subalgebra ℂ X.functionField, A'.FG ∧
      (∀ s : Γ(X, V), algebraMap Γ(X, V) X.functionField s ∈ A') ∧
      ∃ hA : ∀ a : integralClosure A' X.functionField,
          0 ≤ ν (algebraMap (integralClosure A' X.functionField) X.functionField a),
        Algebra.FiniteType ℂ (integralClosure A' X.functionField) ∧
        IsIntegrallyClosed (integralClosure A' X.functionField) ∧
        IsFractionRing (integralClosure A' X.functionField) X.functionField ∧
        firstCenter ν hA ≠ ⊥ ∧
        (∀ p : Ideal (integralClosure A' X.functionField), p.IsPrime →
          p ≤ firstCenter ν hA → p = ⊥ ∨ p = firstCenter ν hA) ∧
        IsDiscreteValuationRing (Localization.AtPrime (firstCenter ν hA)) ∧
        (∀ x : X.functionField, 0 ≤ firstVal ν x ↔
          ∃ a s : integralClosure A' X.functionField, s ∉ firstCenter ν hA ∧
            x * algebraMap (integralClosure A' X.functionField) X.functionField s =
              algebraMap (integralClosure A' X.functionField) X.functionField a) ∧
        (∀ y, 0 ≤ resValuation ν hA y) ∧
        Function.Surjective (resFracValuation ν hA) ∧
        ∀ z : Fin (m + 1) → integralClosure A' X.functionField ⧸ firstCenter ν hA,
          ¬ AlgebraicIndependent ℂ z := by
  have : Nonempty V := ⟨⟨c, hcV⟩⟩
  let := schemeFunctionFieldAlgebra f
  let := affineChartAlgebra f V
  have : Smooth f := SmoothOfRelativeDimension.smooth (m + 1) f
  have : Algebra.FiniteType ℂ Γ(X, V) := affineChartAlgebra_finiteType f hV
  have : IsScalarTower ℂ Γ(X, V) X.functionField := schemeFunctionField_affineChartScalarTower f V
  have : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V hV
  -- `ν ≥ 0` on `Γ(X, V)`
  have hBν : ∀ s : Γ(X, V), 0 ≤ ν (algebraMap Γ(X, V) X.functionField s) := by
    intro s
    have h := hc.1 (X.presheaf.germ V c hcV s)
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at h
    exact h
  have hB : ∀ s : Γ(X, V), 0 ≤ OF4.prefixOne ν (algebraMap Γ(X, V) X.functionField s) :=
    fun s => firstVal_nonneg ν hBν s
  -- elements of values `eᵢ`
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
  have htr : ∀ z : Fin (m + 2) → X.functionField, ¬ AlgebraicIndependent ℂ z := by
    intro z hz
    have h := hz.cardinalMk_le_trdeg
    rw [nativeSmoothFunctionField_trdeg f (m + 1), Cardinal.mk_fintype, Fintype.card_fin] at h
    norm_cast at h
    omega
  let y : Fin m → X.functionField := fun j => x j.succ
  have hy := residue_independent_succ f ν x hx
  have hyν : ∀ j, 0 ≤ ν (y j) := by
    intro j
    change 0 ≤ ν (x j.succ)
    rw [hx j.succ]
    refine WithTop.coe_nonneg.mpr ?_
    have h0 : (toLex (0 : Fin (m + 1) → ℤ) : Lex (Fin (m + 1) → ℤ)) = 0 := rfl
    rw [← h0]
    apply Pi.toLex_monotone
    intro l
    by_cases hl : l = j.succ
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]
  obtain ⟨A', hA'eq, hFG, hBA, -, hA1, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_normalChart_of_divisorial (k := ℂ) (B := Γ(X, V)) (OF4.prefixOne ν) hB hx0ne hx0'
      htr y hy
  subst hA'eq
  have hA : ∀ a : integralClosure ↥((IsScalarTower.toAlgHom ℂ Γ(X, V) X.functionField).range ⊔
      Algebra.adjoin ℂ (Set.range y) : Subalgebra ℂ X.functionField) X.functionField,
      0 ≤ ν (algebraMap _ X.functionField a) :=
    fun a => nonneg_integralClosure_of_nonneg y ν hBν hyν a
  -- `trdeg` bound in the normalization
  have htrC : ∀ z : Fin (m + 2) → integralClosure ↥((IsScalarTower.toAlgHom ℂ Γ(X, V)
      X.functionField).range ⊔ Algebra.adjoin ℂ (Set.range y) : Subalgebra ℂ X.functionField)
      X.functionField, ¬ AlgebraicIndependent ℂ z := fun z hz =>
    htr _ (hz.map' (f := IsScalarTower.toAlgHom ℂ _ X.functionField) Subtype.val_injective)
  refine ⟨_, hFG, hBA, hA, h1, h2, h3, h4, h5, h6, h7, resValuation_nonneg ν hA,
    resFracValuation_surjective ν hA hν fun z hz => (h7 z).mp hz,
    not_algebraicIndependent_quotient htrC _ h4⟩

end SGPT.Okounkov.OF6
