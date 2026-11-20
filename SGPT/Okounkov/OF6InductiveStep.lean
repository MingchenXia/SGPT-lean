import SGPT.Okounkov.OF6FlagRecognition
import SGPT.Okounkov.OF6ResidualValuation

/-!
# The inductive step of [CFKLRS17, Thm 2.9] in local form

Source: chapter *The theory of Okounkov bodies*, `rmk:Abhyankar` (*a valuation with value group
`ℤⁿ_lex` and maximal rational rank `n` is equivalent to a valuation induced by an admissible flag on
a modification of `X`*, [CFKLRS17, Theorem 2.9]). The proof is an induction on `n`: the first
coordinate of `ν` is `ord_E` for a prime divisor `E` of a model (Zariski, `OF6ZariskiScheme`), and
the residual valuation `ν̄` of `ν` on `ℂ(E)` (rank `n - 1`, `OF6ResidualScheme`) is, by induction,
equivalent to a flag valuation on a model of `E`; the flag of `E` is then lifted.

This file proves the lifting at the level of local rings, **when `E` is Cartier at the centre**:
let `R` be a Noetherian domain (the local ring of the model at the centre of `ν`), `t ∈ R`
nonzero (a local equation of `E`; `(t)` is prime as `R ⧸ (t)` carries the flag), and `C̄`
local defining equations of a flag of `R ⧸ (t)` (the local ring of `E`). Lifting them gives local
defining equations of a flag
`X ⊇ E ⊇ …` of `R` (`liftChain`: `P₀ = 0`, `P₁ = (t)`, `P_{i+1} = ` preimage of `P̄ᵢ`, equations
`t, T̄₀, …` lifted). If `ν ≥ 0` on `R`, `ν = 0` off the last member, `ν(t) = (1, w)`, and the lifted
equations have values `ν(T_{i+1}) = (0, Ḡᵢ)` for a unitriangular `Ḡ` (i.e. `ν̄(T̄ᵢ) = Ḡᵢ`: the
residual valuation is `ν_{C̄} Ḡ`), then `ν = ν_C G` with the unitriangular
`G = [[1, w], [0, Ḡ]]` (`eq_lexMap_liftChain`). In `eq_lexMap_liftChain_of_residual` the hypothesis
on the lifted equations is replaced by the induction hypothesis itself: the residual valuation of
`ν` along `E` (`ν(a) = (0, ν̄(ā))` off `(t)`, as in `SGPT.Okounkov.OF6.resValuation`) is
`ν̄ = ν_{C̄} Ḡ` on `R ⧸ (t)`.

Not formalized: making `E` Cartier and the model regular at the centre (local uniformization),
and the global models.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.OF6

open SGPT.Okounkov.OF5 SGPT.Okounkov.ValCurr

variable {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}

/-- **The lifted chain** of local defining equations: `P₀ = 0`, `P₁ = (t)`, `P_{i+1} = π⁻¹(P̄ᵢ)`,
`T₀ = t`, `T_{i+1} = T'ᵢ` (lifts of the `T̄ᵢ`). -/
def liftChain (t : R) (ht0 : t ≠ 0)
    (C : OF5.LocalEquationChain (R ⧸ Ideal.span {t}) m) (h0 : C.P 0 = ⊥) (T' : ℕ → R)
    (hT' : ∀ i, Ideal.Quotient.mk _ (T' i) = C.T i) :
    OF5.LocalEquationChain R (m + 1) where
  P i := match i with
    | 0 => ⊥
    | j + 1 => (C.P j).comap (Ideal.Quotient.mk _)
  T i := match i with
    | 0 => t
    | j + 1 => T' j
  isPrime i := match i with
    | 0 => Ideal.isPrime_bot
    | j + 1 => Ideal.comap_isPrime _ _
  succ_eq i hi := match i with
    | 0 => by
      change (C.P 0).comap (Ideal.Quotient.mk _) = ⊥ ⊔ Ideal.span {t}
      rw [h0, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, bot_sup_eq]
    | j + 1 => by
      have hj : j < m := by omega
      change (C.P (j + 1)).comap (Ideal.Quotient.mk _) =
        (C.P j).comap (Ideal.Quotient.mk _) ⊔ Ideal.span {T' j}
      have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {t})) :=
        Ideal.Quotient.mk_surjective
      have hmap : Ideal.map (Ideal.Quotient.mk _) ((C.P j).comap (Ideal.Quotient.mk _) ⊔
          Ideal.span {T' j}) = C.P (j + 1) := by
        rw [Ideal.map_sup, Ideal.map_comap_of_surjective _ hsurj, Ideal.map_span,
          Set.image_singleton, hT' j, C.succ_eq j hj]
      rw [← hmap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker]
      refine sup_eq_left.mpr (le_trans ?_ le_sup_left)
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact (C.P j).zero_mem
  T_notMem i hi := match i with
    | 0 => by
      change t ∉ (⊥ : Ideal R)
      rwa [Ideal.mem_bot]
    | j + 1 => by
      change T' j ∉ (C.P j).comap (Ideal.Quotient.mk _)
      rw [Ideal.mem_comap, hT' j]
      exact C.T_notMem j (by omega)

/-- The block matrix `[[1, w], [0, Ḡ]]`. -/
def liftMatrix (w : Fin m → ℤ) (G : Matrix (Fin m) (Fin m) ℤ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  Fin.cons (Fin.cons 1 w) fun i => Fin.cons 0 (G i)

theorem isUnitUpperTriangular_liftMatrix (w : Fin m → ℤ) {G : Matrix (Fin m) (Fin m) ℤ}
    (hG : IsUnitUpperTriangular G) : IsUnitUpperTriangular (liftMatrix w G) := by
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (Fin.cons 0 (G i) : Fin (m + 1) → ℤ) i.succ = 1
      rw [Fin.cons_succ]
      exact hG.1 i
  · induction i using Fin.cases with
    | zero => exact absurd hji (by simp)
    | succ i =>
      change (Fin.cons 0 (G i) : Fin (m + 1) → ℤ) j = 0
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        rw [Fin.cons_succ]
        exact hG.2 (Fin.succ_lt_succ_iff.mp hji)

variable [IsNoetherianRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The inductive step of [CFKLRS17, Thm 2.9] when `E = V(t)` is Cartier at the centre.** -/
theorem eq_lexMap_liftChain (t : R) (ht0 : t ≠ 0)
    (C : OF5.LocalEquationChain (R ⧸ Ideal.span {t}) m) (h0 : C.P 0 = ⊥) (T' : ℕ → R)
    (hT' : ∀ i, Ideal.Quotient.mk _ (T' i) = C.T i)
    (v : AddValuation K (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a))
    (hunit : ∀ a : R, a ∉ (C.P m).comap (Ideal.Quotient.mk _) → v (algebraMap R K a) = 0)
    (w : Fin m → ℤ) (htv : v (algebraMap R K t) = vecValue (Fin.cons 1 w))
    (G : Matrix (Fin m) (Fin m) ℤ) (hG : IsUnitUpperTriangular G)
    (hTv : ∀ (i : ℕ) (hi : i < m), v (algebraMap R K (T' i)) = vecValue (Fin.cons 0 (G ⟨i, hi⟩))) :
    v = lexMapValuation (liftMatrix w G) (isUnitUpperTriangular_liftMatrix w hG)
      ((liftChain t ht0 C h0 T' hT').fractionValuation K rfl) := by
  refine LocalEquationChain.eq_lexMap_fractionValuation (liftChain t ht0 C h0 T' hT') K rfl v
    _ _ hnonneg (fun i hi => ?_) (fun a ha => hunit a ha)
  match i, hi with
  | 0, _ => exact htv
  | j + 1, hj =>
    have hj' : j < m := by omega
    exact (hTv j hj').trans (by
      change vecValue (Fin.cons 0 (G ⟨j, hj'⟩)) =
        vecValue ((Fin.cons 0 (G ⟨j, hj'⟩) : Fin (m + 1) → ℤ))
      rfl)

/-- **The inductive step, with the induction hypothesis on the residual valuation**: if off `(t)`
the valuation is `ν(a) = (0, ν̄(ā))` with `ν̄ = ν_{C̄} Ḡ` on `R ⧸ (t)` (`Ḡ` unitriangular), then
`ν = ν_C G` for the lifted chain `C` and `G = [[1, w], [0, Ḡ]]`. -/
theorem eq_lexMap_liftChain_of_residual (t : R) (ht0 : t ≠ 0) [(Ideal.span {t}).IsPrime]
    (C : OF5.LocalEquationChain (R ⧸ Ideal.span {t}) m) (h0 : C.P 0 = ⊥) (T' : ℕ → R)
    (hT' : ∀ i, Ideal.Quotient.mk _ (T' i) = C.T i)
    (v : AddValuation K (WithTop (Lex (Fin (m + 1) → ℤ))))
    (hnonneg : ∀ a : R, 0 ≤ v (algebraMap R K a))
    (hunit : ∀ a : R, a ∉ (C.P m).comap (Ideal.Quotient.mk _) → v (algebraMap R K a) = 0)
    (w : Fin m → ℤ) (htv : v (algebraMap R K t) = vecValue (Fin.cons 1 w))
    (G : Matrix (Fin m) (Fin m) ℤ) (hG : IsUnitUpperTriangular G)
    (hres : ∀ a : R, a ∉ Ideal.span {t} → ∃ x : Lex (Fin (m + 1) → ℤ),
      v (algebraMap R K a) = x ∧ ofLex x 0 = 0 ∧
        ((tailHom x : Lex (Fin m → ℤ)) : WithTop (Lex (Fin m → ℤ))) =
          lexMapValuation G hG (C.fractionValuation (FractionRing (R ⧸ Ideal.span {t})) h0)
            (algebraMap (R ⧸ Ideal.span {t}) (FractionRing (R ⧸ Ideal.span {t}))
              (Ideal.Quotient.mk (Ideal.span {t}) a))) :
    v = lexMapValuation (liftMatrix w G) (isUnitUpperTriangular_liftMatrix w hG)
      ((liftChain t ht0 C h0 T' hT').fractionValuation K rfl) := by
  refine eq_lexMap_liftChain K t ht0 C h0 T' hT' v hnonneg hunit w htv G hG fun i hi => ?_
  have hTi : T' i ∉ Ideal.span {t} := by
    intro h
    apply C.T_notMem i hi
    rw [← hT' i, Ideal.Quotient.eq_zero_iff_mem.mpr h]
    exact (C.P i).zero_mem
  obtain ⟨x, hx, hx0, htail⟩ := hres (T' i) hTi
  rw [hT' i, LocalEquationChain.lexMap_fractionValuation_T C _ h0 G hG hi] at htail
  rw [hx]
  congr 2
  funext j
  induction j using Fin.cases with
  | zero => exact hx0
  | succ j =>
    have h := congrArg (fun z : Lex (Fin m → ℤ) => ofLex z j) (WithTop.coe_injective htail)
    exact h

end SGPT.Okounkov.OF6
