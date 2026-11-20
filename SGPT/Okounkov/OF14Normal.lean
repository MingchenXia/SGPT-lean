import SGPT.Okounkov.OF14Algebraization
import SGPT.Okounkov.OF12ValCurrNormal

/-!
# `rmk:Abhyankar` for normal `X` with a resolution

Source: chapter *The theory of Okounkov bodies*, Section *Flags and valuations*: *"Let `X` be an
irreducible normal projective variety of dimension `n`"*, `rmk:Abhyankar`: *a valuation with value
group `ℤⁿ_lex` and maximal rational rank `n` is equivalent to a valuation induced by an admissible
flag on a modification of `X`* ([CFKLRS17, Thm 2.9]).

For a singular normal `X` we pass through a resolution `ρ : R → X` in the sense of lane OF12
(`OF12.Resolution`: `R` integral smooth projective, `ρ` a morphism over `ℂ` whose induced field map
`ℂ(X) → ℂ(R)` is an isomorphism, with a proper bimeromorphic analytification `R(ℂ) → X^an`).

* `valuationsLexEquivalent_comap_trans`: equivalence of valuations is transported along field
  isomorphisms;
* **`exists_admissibleFlag_lexEquivalent_of_resolution`**: given a resolution `ρ : R → X`, every
  valuation `ν : ℂ(X)^× → ℤⁿ_lex` (`n = m + 1`) with value group `ℤⁿ_lex` is `ν_{Y•} G` for an
  admissible flag `Y•` on the algebraic model `V` of a blow-up tower `π : Y → R(ℂ)`, read on
  `ℂ(X)` through `ℂ(X) ≃ ℂ(R) ≃ ℂ(V)` (the second isomorphism is the pull-back along `π ∘ φ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov.OF14

open CategoryTheory AlgebraicGeometry Set Filter SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.Okounkov.OF9 SGPT.Okounkov.OF5 SGPT.Okounkov.OF6 SGPT.Okounkov.ValCurr
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

/-- **Equivalence of valuations along field isomorphisms.** If `w ∘ e₂ ~ ν ∘ e₁⁻¹`, then
`w ∘ e₂ ∘ e₁ ~ ν`. -/
theorem valuationsLexEquivalent_comap_trans {K L M : Type*} [Field K] [Field L] [Field M] {n : ℕ}
    (e₁ : K ≃+* L) (e₂ : L ≃+* M) (w : AddValuation M (WithTop (Lex (Fin n → ℤ))))
    (ν : AddValuation K (WithTop (Lex (Fin n → ℤ))))
    (h : ValuationsLexEquivalent (w.comap e₂.toRingHom) (ν.comap e₁.symm.toRingHom)) :
    ValuationsLexEquivalent (w.comap (e₁.trans e₂).toRingHom) ν := by
  obtain ⟨G, hG, hEq⟩ := h
  refine ⟨G, hG, ?_⟩
  ext q
  have h1 := congrArg (fun v : AddValuation L (WithTop (Lex (Fin n → ℤ))) => v (e₁ q)) hEq
  change ν (e₁.symm (e₁ q)) = lexWithTopHom G hG (w (e₂ (e₁ q))) at h1
  rw [e₁.symm_apply_apply] at h1
  rw [lexMapValuation_apply]
  exact h1

local instance of14NoTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance of14NoCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n
local instance of14NoManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) :=
  schemeAnalyticTN_isComplexManifold g n

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [IsSeparated f] [QuasiCompact f]
  [LocallyOfFiniteType f] {m : ℕ}

/-- **`rmk:Abhyankar`, existence ([CFKLRS17, Thm 2.9]) for a variety with a resolution.** Let `X`
be an integral complex variety (e.g. normal projective) of dimension `n = m + 1` and
`ρ : R → X` a resolution (`OF12.Resolution`: `R` integral smooth projective, `ρ` birational with
field isomorphism `ϕ : ℂ(X) ≃ ℂ(R)` induced by `ρ`, proper bimeromorphic analytification). Every
valuation `ν : ℂ(X)^× → ℤⁿ_lex` with value group `ℤⁿ_lex` is equivalent to the valuation of an
admissible flag on a modification of `X`: there are a finite sequence of blow-ups with smooth
centres `π : Y → R(ℂ)`, its algebraic model `V` (integral smooth projective, `φ : V(ℂ) ≃ Y`,
`e : ℂ(R) ≃ ℂ(V)` the pull-back along `π ∘ φ`) and an admissible flag `Y•` on `V` with
`ν = ν_{Y•} G` on `ℂ(X)` (read through `e ∘ ϕ`), `G = I + N` unit upper triangular. The
modification is `V(ℂ) ≃ Y → R(ℂ) → X(ℂ)`. -/
theorem exists_admissibleFlag_lexEquivalent_of_resolution (R : OF12.Resolution f m)
    (ν : AddValuation X.functionField (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hν : Function.Surjective ν) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel (m + 1)) Y)
      (_ : IsComplexManifold (m + 1) Y) (π : Y → SchemeComplexPoint R.fY)
      (hseq : IsBlowupSequence (m + 1) (SchemeComplexPoint R.fY) Y π)
      (V : Scheme.{0}) (_ : IsIntegral V) (g : V ⟶ Spec (.of ℂ))
      (hsm : SmoothOfRelativeDimension (m + 1) g) (EV : ClosedProjectiveEmbedding g),
      letI := hsm
      letI := EV.isSeparated
      letI := EV.quasiCompact
      ∃ (φ : SchemeComplexPoint g ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ Y)
        (e : R.Y.functionField ≃+* V.functionField),
        (∀ (q : R.Y.functionField) (v : SchemeComplexPoint g),
          schemeNativeFunctionFieldGerm g (m + 1) v (e q) =
            fracComap (OF13.isAnalyticModification_of_diffeomorph φ) v
              (ratGerm R.fY (HironakaChowLemma.isAnalyticModification_of_isBlowupSequence hseq)
                (φ v) q)) ∧
        ∃ (Yf : Fin (m + 1 + 1) → Set V) (hY : IsAdmissibleFlag g (m + 1) Yf),
          ValuationsLexEquivalent
            ((admissibleFlagValuation hY).comap (R.φ.trans e).toRingHom) ν := by
  have hν' : Function.Surjective (ν.comap R.φ.symm.toRingHom) := fun x => by
    obtain ⟨q, hq⟩ := hν x
    refine ⟨R.φ q, ?_⟩
    change ν (R.φ.symm (R.φ q)) = x
    rw [R.φ.symm_apply_apply]
    exact hq
  obtain ⟨Y, tY, cY, mY, π, hseq, V, hV, g, hsm, EV, hrest⟩ :=
    exists_admissibleFlag_lexEquivalent R.fY R.E (ν.comap R.φ.symm.toRingHom) hν'
  let := hsm
  let := EV.isSeparated
  let := EV.quasiCompact
  obtain ⟨φ, e, hcompat, Yf, hY, hlex⟩ := hrest
  exact ⟨Y, tY, cY, mY, π, hseq, V, hV, g, hsm, EV, φ, e, hcompat, Yf, hY,
    valuationsLexEquivalent_comap_trans R.φ e _ ν hlex⟩

end SGPT.Okounkov.OF14
