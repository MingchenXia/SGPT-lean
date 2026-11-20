import SGPT.Okounkov.TranscendentalCoreGentleSum
import SGPT.Okounkov.TranscendentalCoreValuationBounded
import SGPT.Okounkov.TranscendentalCoreRepresentative

/-!
# Convexity and superadditivity of transcendental Okounkov bodies

Source: blueprint node `tok:body-basic` (chapter `claude-okounkov-transcendental`), i.e.
Darvas--Reboulet--Witt Nyström--Xia--Zhang, *Transcendental Okounkov bodies* (DRWNXZ), §3
(convexity) and Proposition 3.3 (1) for rational `λ` and (2); the book's
`thm:Okounkovtranmain`, convexity in the first sentence and item 2.

Let `ξ = {θ}` and `ξ' = {θ'}`. By `tok:gentle-sum` (`add_smul_mem_gentleCurrents`) and the
linearity of the valuation (`flagValuation_add_smul`),

* `ν(𝒢(ξ))` is closed under rational convex combinations, so its closure `Δ(ξ)` is convex;
* `ν(𝒢(ξ)) + ν(𝒢(ξ')) ⊆ ν(𝒢(ξ + ξ'))`, so `Δ(ξ) + Δ(ξ') ⊆ Δ(ξ + ξ')` (addition is
  continuous);
* `λ ν(𝒢(ξ)) = ν(𝒢(λ ξ))` for `λ ∈ ℚ_{>0}`, so `Δ(λ ξ) = λ Δ(ξ)`.

None of these statements needs bigness. With `representativeIndependence`
(`tok:rep-independence`, CORE) the class version of the superadditivity is the item 2
`SuperadditivityStatement` of the fixed target `OkounkovTranMainStatement`.

## Main results

* `convex_closure_of_ratConvex`: the closure of a set closed under rational convex
  combinations is convex.
* `convex_tradOkounkovBody`: `Δ(ξ)` is convex.
* `tradOkounkovBody_add_subset`: `Δ(ξ) + Δ(ξ') ⊆ Δ(ξ + ξ')`.
* `tradOkounkovBody_rat_smul`: `Δ(λ ξ) = λ Δ(ξ)` for `λ ∈ ℚ_{>0}`.
* `superadditivity`: the item 2 `SuperadditivityStatement` of `thm:Okounkovtranmain`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalBody

open Set Filter
open scoped Pointwise Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.TranscendentalCore

/-! ### Rational convexity -/

section RatConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

/-- The closure of a set closed under rational convex combinations is convex. -/
theorem convex_closure_of_ratConvex {S : Set E}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      (t : ℝ) • x + (1 - (t : ℝ)) • y ∈ S) :
    Convex ℝ (closure S) := by
  -- rational combinations of points of the closure stay in the closure
  have hrat : ∀ x ∈ closure S, ∀ y ∈ closure S, ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      (t : ℝ) • x + (1 - (t : ℝ)) • y ∈ closure S := by
    intro x hx y hy t ht0 ht1
    have hcont : Continuous (Function.uncurry
        (fun a b : E => (t : ℝ) • a + (1 - (t : ℝ)) • b)) := by
      fun_prop
    exact map_mem_closure₂ (f := fun a b : E => (t : ℝ) • a + (1 - (t : ℝ)) • b) hcont hx hy
      (fun a ha b hb => hS a ha b hb t ht0 ht1)
  intro x hx y hy a b ha hb hab
  -- the set of real parameters with `t x + (1 - t) y ∈ closure S` is closed
  set A : Set ℝ := {t | t • x + (1 - t) • y ∈ closure S} with hA
  have hAclosed : IsClosed A :=
    isClosed_closure.preimage (by fun_prop)
  have hIoo : Ioo (0 : ℝ) 1 ⊆ A := by
    have hdense : Dense (range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    refine (hdense.open_subset_closure_inter isOpen_Ioo).trans ?_
    refine closure_minimal ?_ hAclosed
    rintro t ⟨⟨ht0, ht1⟩, q, rfl⟩
    exact hrat x hx y hy q (by exact_mod_cast ht0.le) (by exact_mod_cast ht1.le)
  have hIcc : Icc (0 : ℝ) 1 ⊆ A := by
    have h0 : (0 : ℝ) ∈ A := by
      have := hrat x hx y hy 0 le_rfl zero_le_one
      change (0 : ℝ) • x + (1 - (0 : ℝ)) • y ∈ closure S
      simpa using this
    have h1 : (1 : ℝ) ∈ A := by
      have := hrat x hx y hy 1 zero_le_one le_rfl
      change (1 : ℝ) • x + (1 - (1 : ℝ)) • y ∈ closure S
      simpa using this
    intro t ⟨ht0, ht1⟩
    rcases ht0.lt_or_eq with ht0 | rfl
    · rcases ht1.lt_or_eq with ht1 | rfl
      · exact hIoo ⟨ht0, ht1⟩
      · exact h1
    · exact h0
  have hb' : b = 1 - a := by linarith
  have hmem := hIcc ⟨ha, by linarith⟩
  rw [hb']
  exact hmem

end RatConvex

/-! ### The body of a representative -/

section Body

variable {n : ℕ} {F : OriginalFlagGeometry.{u} n}

/-- `ν(𝒢(ξ))` is closed under rational convex combinations. -/
theorem ratConvex_image_gentleCurrents (θ : ClosedRealOneOneForm n F.carrier) :
    ∀ x ∈ flagValuation F '' gentleCurrents θ, ∀ y ∈ flagValuation F '' gentleCurrents θ,
      ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
        (t : ℝ) • x + (1 - (t : ℝ)) • y ∈ flagValuation F '' gentleCurrents θ := by
  rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩ t ht0 ht1
  have hs : (0 : ℚ) ≤ 1 - t := by linarith
  have hab : 0 < t ∨ 0 < 1 - t := by
    rcases ht0.lt_or_eq with h | h
    · exact Or.inl h
    · right; rw [← h]; norm_num
  have hmem := add_smul_mem_gentleCurrents hφ hψ ht0 hs hab
  have hform : ((t : ℝ) • θ + (((1 - t : ℚ)) : ℝ) • θ) = θ := by
    rw [← add_smul]
    push_cast
    simp
  rw [hform] at hmem
  refine ⟨_, hmem, ?_⟩
  rw [flagValuation_add_smul (isThetaPshPotential_of_mem_gentleCurrents hφ)
    (isThetaPshPotential_of_mem_gentleCurrents hψ) (by exact_mod_cast ht0)
    (by exact_mod_cast hs)]
  push_cast
  rfl

/-- **Blueprint `tok:body-basic`, convexity** (DRWNXZ §3): `Δ_{Y•}(ξ)` is convex. -/
theorem convex_tradOkounkovBody (θ : ClosedRealOneOneForm n F.carrier) :
    Convex ℝ (tradOkounkovBody F θ) := by
  rw [tradOkounkovBody_eq_closure_image]
  exact convex_closure_of_ratConvex (ratConvex_image_gentleCurrents θ)

/-- `ν(𝒢(ξ)) + ν(𝒢(ξ')) ⊆ ν(𝒢(ξ + ξ'))`. -/
theorem image_gentleCurrents_add_subset (θ θ' : ClosedRealOneOneForm n F.carrier) :
    flagValuation F '' gentleCurrents θ + flagValuation F '' gentleCurrents θ' ⊆
      flagValuation F '' gentleCurrents (θ + θ') := by
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, _, ⟨ψ, hψ, rfl⟩, rfl⟩
  have hmem := add_smul_mem_gentleCurrents hφ hψ zero_le_one zero_le_one (Or.inl one_pos)
  have hform : (((1 : ℚ) : ℝ) • θ + ((1 : ℚ) : ℝ) • θ') = θ + θ' := by simp
  rw [hform] at hmem
  refine ⟨_, hmem, ?_⟩
  rw [flagValuation_add_smul (isThetaPshPotential_of_mem_gentleCurrents hφ)
    (isThetaPshPotential_of_mem_gentleCurrents hψ) (by norm_num) (by norm_num)]
  simp

/-- **Blueprint `tok:body-basic`, superadditivity** (DRWNXZ Proposition 3.3 (2)):
`Δ_{Y•}(ξ) + Δ_{Y•}(ξ') ⊆ Δ_{Y•}(ξ + ξ')`. -/
theorem tradOkounkovBody_add_subset (θ θ' : ClosedRealOneOneForm n F.carrier) :
    tradOkounkovBody F θ + tradOkounkovBody F θ' ⊆ tradOkounkovBody F (θ + θ') := by
  rw [tradOkounkovBody_eq_closure_image, tradOkounkovBody_eq_closure_image,
    tradOkounkovBody_eq_closure_image]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hcont : Continuous (Function.uncurry (fun a b : Fin n → ℝ => a + b)) := by fun_prop
  exact map_mem_closure₂ (f := fun a b : Fin n → ℝ => a + b) hcont hx hy
    (fun a ha b hb => image_gentleCurrents_add_subset θ θ' ⟨a, ha, b, hb, rfl⟩)

/-- `λ ν(𝒢(ξ)) ⊆ ν(𝒢(λ ξ))` for `λ ∈ ℚ_{>0}`. -/
theorem rat_smul_image_gentleCurrents_subset (θ : ClosedRealOneOneForm n F.carrier) {q : ℚ}
    (hq : 0 < q) :
    (q : ℝ) • (flagValuation F '' gentleCurrents θ) ⊆
      flagValuation F '' gentleCurrents ((q : ℝ) • θ) := by
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  have hmem := add_smul_mem_gentleCurrents hφ hφ hq.le le_rfl (Or.inl hq)
  have hform : ((q : ℝ) • θ + ((0 : ℚ) : ℝ) • θ) = (q : ℝ) • θ := by simp
  rw [hform] at hmem
  refine ⟨_, hmem, ?_⟩
  rw [flagValuation_add_smul (isThetaPshPotential_of_mem_gentleCurrents hφ)
    (isThetaPshPotential_of_mem_gentleCurrents hφ) (by exact_mod_cast hq.le) (by norm_num)]
  simp

/-- **Blueprint `tok:body-basic`, rational homogeneity** (DRWNXZ Proposition 3.3 (1) for
rational `λ`): `Δ_{Y•}(λ ξ) = λ Δ_{Y•}(ξ)` for `λ ∈ ℚ_{>0}`. -/
theorem tradOkounkovBody_rat_smul (θ : ClosedRealOneOneForm n F.carrier) {q : ℚ} (hq : 0 < q) :
    tradOkounkovBody F ((q : ℝ) • θ) = (q : ℝ) • tradOkounkovBody F θ := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq' : 0 < q⁻¹ := inv_pos.mpr hq
  have himage : flagValuation F '' gentleCurrents ((q : ℝ) • θ) =
      (q : ℝ) • (flagValuation F '' gentleCurrents θ) := by
    refine Subset.antisymm ?_ (rat_smul_image_gentleCurrents_subset θ hq)
    have h := rat_smul_image_gentleCurrents_subset ((q : ℝ) • θ) hq'
    have hform : ((q⁻¹ : ℚ) : ℝ) • (q : ℝ) • θ = θ := by
      rw [smul_smul]
      push_cast
      rw [inv_mul_cancel₀ hqR, one_smul]
    rw [hform] at h
    intro x hx
    refine ⟨((q⁻¹ : ℚ) : ℝ) • x, h ⟨x, hx, rfl⟩, ?_⟩
    change (q : ℝ) • ((q⁻¹ : ℚ) : ℝ) • x = x
    rw [smul_smul]
    push_cast
    rw [mul_inv_cancel₀ hqR, one_smul]
  rw [tradOkounkovBody_eq_closure_image, tradOkounkovBody_eq_closure_image, himage,
    closure_smul₀]

end Body

/-! ### Classes -/

section Classes

variable {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))

/-- The body of a class is the body of any of its representatives. -/
theorem classOkounkovBody_ofRepresentative (θ : ClosedRealOneOneForm (m + 1) F.carrier) :
    TranscendentalMain.classOkounkovBody F (RealBottChern.ofRepresentative θ) =
      tradOkounkovBody F θ :=
  (representativeIndependence F θ).symm

/-- `Δ_{Y•}(α)` is convex for every class `α`. -/
theorem convex_classOkounkovBody (α : RealBottChern (m + 1) F.carrier) :
    Convex ℝ (TranscendentalMain.classOkounkovBody F α) :=
  convex_tradOkounkovBody _

/-- **Source `thm:Okounkovtranmain` (2)** (blueprint `tok:body-basic`; DRWNXZ
Proposition 3.3 (2)): `Δ_{Y•}(α) + Δ_{Y•}(α') ⊆ Δ_{Y•}(α + α')` (the statement holds for all
classes; the target `SuperadditivityStatement` assumes `α`, `α'` big). -/
theorem classOkounkovBody_add_subset (α α' : RealBottChern (m + 1) F.carrier) :
    TranscendentalMain.classOkounkovBody F α + TranscendentalMain.classOkounkovBody F α' ⊆
      TranscendentalMain.classOkounkovBody F (α + α') := by
  have h1 : RealBottChern.ofRepresentative (Quotient.out α) = α := Quotient.out_eq α
  have h2 : RealBottChern.ofRepresentative (Quotient.out α') = α' := Quotient.out_eq α'
  have h : RealBottChern.ofRepresentative (Quotient.out α + Quotient.out α') = α + α' := by
    rw [RealBottChern.ofRepresentative_add, h1, h2]
  rw [← h, classOkounkovBody_ofRepresentative]
  exact tradOkounkovBody_add_subset _ _

/-- **Source `thm:Okounkovtranmain` (2)**: the item `SuperadditivityStatement` of the fixed
target `OkounkovTranMainStatement`. -/
theorem superadditivity : TranscendentalMain.SuperadditivityStatement F :=
  fun α α' _ _ => classOkounkovBody_add_subset F α α'

end Classes

end SGPT.Okounkov.TranscendentalBody
