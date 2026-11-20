import SGPT.Foundations.Analysis.Pending.DiagonalFibreIntegration
import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
import SGPT.Foundations.Analysis.Pending.CoordinateDensityMixedPullback
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The class of `p₁_*(Θ ∧ p₂^*β)` for the smooth product currents

Sources: Demailly--Păun, proof of Theorem 2.12 (`dp04-kahler-cone:2.12`), and Boucksom, the last
paragraph of the proof of Theorem 4.8 (`bou02-volume:4.8`); blueprint `bou:pushforward-lower-bound`
("expanding `(p₁^*b + p₂^*b)^n`, integration along the fibres of `p₁` keeps only the term
`n p₁^*b ∧ p₂^*b^{n-1}`, so `R` lies in `m b`").  TN.4 plan, step B6.

Let `X`, `Y` be compact complex manifolds of dimensions `q + 1` and `p + 1` with Kähler forms
`ω_X`, `ω_Y`, let `a`, `b` be smooth closed real `(1,1)`-forms on `X`, `Y` (no positivity) and `β` a
smooth real `(1,1)`-form on `Y`.  On `X × Y` with the Kähler form `p₁^*ω_X + p₂^*ω_Y` consider the
smooth current `Θ = [X × Y] ∧ (p₁^*a + p₂^*b)^{p+1}` of bidimension `(q + 1, q + 1)`.  Then

`p₁_*(Θ ∧ p₂^*β) = (p + 1) (∫_Y bᵖ ∧ β) · [X] ∧ a`

as currents on `X`, on all test forms (`fibrePushforward_smoothCurrent_prodForm`; the constant is
`fibreIntegral`, which for semipositive closed `b`, `β` is the total mixed mass of `(bᵖ, β)`,
`fibreIntegral_eq_globalMixedMeasure`).  With `Y = X`, `b = a` and `β = ω̃` this is the identity
`R = n (bⁿ⁻¹ · ω̃) b` of `bou:pushforward-lower-bound` for the smooth representatives.

## The pointwise core

In the coordinates `ℂ^{q+1} × ℂ^{p+1}` the density of
`p₁^*α₀ ∧ ⋯ ∧ p₁^*α_{q-1} ∧ p₂^*β ∧ (p₁^*A + p₂^*B)^{p+1}` is
`(p + 1) · D(α, A) · D(Bᵖ, β)` (`actualMixedTopDensity_fibreFamily`):

* multilinear expansion of the `p + 1` sum slots (`MultilinearMap.map_add_univ`);
* a family with `k ≠ q + 1` slots pulled back from the first factor has density `0`
  (`actualMixedTopDensity_eq_zero_of_scaleFst`): pulling back along `(x, y) ↦ (t x, y)` multiplies
  the density by the determinant `t^{2(q+1)}` and each first-factor slot by `t²`;
* the `p + 1` terms with one first-factor sum slot are equal, by a transposition of slots, to the
  density of a block family, which factors (`ProductMixedMeasure.actualMixedTopDensity_append_comp`).

Every test form has, at every point of every chart, coefficients in the span of the products of real
`(1,1)`-forms (`coeff_mem_span_wedgeProd`), so the identity extends to all test forms; the Kähler
volume of `X × Y` is `C(n+m, n) · vol_X ⊗ vol_Y` (`ProductMixedMeasure.globalMixedMeasure_prodForm`),
and Fubini gives the global statement.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.FibrePushforwardProductForm

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents IntegrationCurrent SmoothCurrentTraceMeasure
  ProductComplexManifold ProductMixedMeasure TopDegreeDensity DiagonalFibreIntegration
open scoped ProductComplexManifold

noncomputable section

/-! ### Scaling the first factor -/

section Scaling

variable {n m : ℕ}

/-- The real-linear identification `ℂⁿ × ℂᵐ ≃ ℂⁿ⁺ᵐ`. -/
def prodModelLinearEquiv (n m : ℕ) :
    (ComplexModel n × ComplexModel m) ≃ₗ[ℝ] ComplexModel (n + m) :=
  (prodModelEquiv n m).toLinearEquiv.restrictScalars ℝ

/-- The linear map `(x, y) ↦ (t x, y)` of `ℂⁿ⁺ᵐ = ℂⁿ × ℂᵐ`. -/
def scaleFstLinear (n m : ℕ) (t : ℝ) : ComplexModel (n + m) →ₗ[ℝ] ComplexModel (n + m) :=
  (prodModelLinearEquiv n m : (ComplexModel n × ComplexModel m) →ₗ[ℝ] ComplexModel (n + m)) ∘ₗ
    (LinearMap.prodMap (t • LinearMap.id) LinearMap.id) ∘ₗ
      ((prodModelLinearEquiv n m).symm : ComplexModel (n + m) →ₗ[ℝ] _)

/-- The scaling `(x, y) ↦ (t x, y)`, as a continuous linear map. -/
def scaleFst (n m : ℕ) (t : ℝ) : ComplexModel (n + m) →L[ℝ] ComplexModel (n + m) :=
  LinearMap.toContinuousLinearMap (scaleFstLinear n m t)

theorem finrank_complexModel (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

/-- **The determinant of the scaling** is `t^{2n}`. -/
theorem det_scaleFst (t : ℝ) :
    LinearMap.det (scaleFst n m t : ComplexModel (n + m) →ₗ[ℝ] ComplexModel (n + m)) =
      t ^ (2 * n) := by
  rw [scaleFst, LinearMap.coe_toContinuousLinearMap, scaleFstLinear, LinearMap.det_conj,
    LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_id, LinearMap.det_id,
    finrank_complexModel]
  ring

theorem scaleFst_apply (t : ℝ) (v : ComplexModel (n + m)) :
    scaleFst n m t v =
      prodModelEquiv n m (t • ((prodModelEquiv n m).symm v).1, ((prodModelEquiv n m).symm v).2) :=
  rfl

theorem projFst_comp_scaleFst (t : ℝ) :
    (projFst n m).comp (scaleFst n m t) = t • projFst n m := by
  ext1 v
  simp [projFst_apply, scaleFst_apply]

theorem projSnd_comp_scaleFst (t : ℝ) :
    (projSnd n m).comp (scaleFst n m t) = projSnd n m := by
  ext1 v
  simp [projSnd_apply, scaleFst_apply]

/-- Pulling back a two-form along `t •` a linear map multiplies it by `t²`. -/
theorem compContinuousLinearMap_smul_two {k l : ℕ} (A : CoordinateRealTwoForm k)
    (L : ComplexModel l →L[ℝ] ComplexModel k) (t : ℝ) :
    A.compContinuousLinearMap (t • L) = t ^ 2 • A.compContinuousLinearMap L := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have h := A.toContinuousMultilinearMap.map_smul_univ (fun _ => t) (fun i => L (v i))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  exact h

theorem compContinuousLinearMap_comp {k l r : ℕ} (A : CoordinateRealTwoForm k)
    (L : ComplexModel l →L[ℝ] ComplexModel k) (L' : ComplexModel r →L[ℝ] ComplexModel l) :
    (A.compContinuousLinearMap L).compContinuousLinearMap L' =
      A.compContinuousLinearMap (L.comp L') := by
  ext v
  rfl

/-- The scaling multiplies a first-factor two-form by `t²`. -/
theorem comp_projFst_comp_scaleFst (A : CoordinateRealTwoForm n) (t : ℝ) :
    (A.compContinuousLinearMap (projFst n m)).compContinuousLinearMap (scaleFst n m t) =
      t ^ 2 • A.compContinuousLinearMap (projFst n m) := by
  rw [compContinuousLinearMap_comp, projFst_comp_scaleFst,
    compContinuousLinearMap_smul_two]

/-- The scaling fixes a second-factor two-form. -/
theorem comp_projSnd_comp_scaleFst (B : CoordinateRealTwoForm m) (t : ℝ) :
    (B.compContinuousLinearMap (projSnd n m)).compContinuousLinearMap (scaleFst n m t) =
      B.compContinuousLinearMap (projSnd n m) := by
  rw [compContinuousLinearMap_comp, projSnd_comp_scaleFst]

/-- **Unbalanced families have density zero.**  If the scaling `(x, y) ↦ (2x, y)` multiplies the
slot `i` by `c i` and `∏ c i ≠ 4ⁿ`, the mixed density vanishes: it is multiplied both by the
determinant `4ⁿ` and by `∏ c i`.  (A slot pulled back from the first factor has `c i = 4`, one
pulled back from the second factor `c i = 1`.) -/
theorem actualMixedTopDensity_eq_zero_of_scaleFst {G : Fin (n + m) → CoordinateRealTwoForm (n + m)}
    (c : Fin (n + m) → ℝ)
    (hG : ∀ i, (G i).compContinuousLinearMap (scaleFst n m 2) = c i • G i)
    (hc : ∏ i, c i ≠ 4 ^ n) : actualMixedTopDensity G = 0 := by
  have h1 := actualMixedTopDensity_compContinuousLinearMap G (scaleFst n m 2)
  rw [det_scaleFst] at h1
  simp_rw [hG] at h1
  have h2 := actualMixedTopDensityMultilinear.map_smul_univ c G
  simp only [actualMixedTopDensityMultilinear_apply, smul_eq_mul] at h2
  rw [h2, pow_mul] at h1
  norm_num at h1
  exact h1.resolve_left hc

end Scaling

/-! ### The density of the fibre family -/

section FibreFamily

theorem append_update_right {α : Type*} {k l : ℕ} (x : Fin k → α) (y : Fin l → α) (j : Fin l)
    (a : α) :
    Fin.append x (Function.update y j a) = Function.update (Fin.append x y) (Fin.natAdd k j) a := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h
    rw [Fin.ext_iff] at h
    simp at h
    omega
  · rw [Fin.append_right]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hij, Function.update_of_ne, Fin.append_right]
      intro h
      apply hij
      rw [Fin.ext_iff] at h ⊢
      simp at h
      omega

/-- The mixed density as a multilinear function of the last `l` slots, the first `k` fixed. -/
def appendRight {k l : ℕ} (x : Fin k → CoordinateRealTwoForm (k + l)) :
    MultilinearMap ℝ (fun _ : Fin l => CoordinateRealTwoForm (k + l)) ℝ where
  toFun y := actualMixedTopDensity (Fin.append x y)
  map_update_add' := by
    intro inst y j a b
    have hinst : inst = instDecidableEqFin l := Subsingleton.elim _ _
    subst hinst
    rw [append_update_right, append_update_right, append_update_right]
    exact actualMixedTopDensityMultilinear.map_update_add _ _ _ _
  map_update_smul' := by
    intro inst y j c a
    have hinst : inst = instDecidableEqFin l := Subsingleton.elim _ _
    subst hinst
    rw [append_update_right, append_update_right]
    exact actualMixedTopDensityMultilinear.map_update_smul _ _ _ _

theorem appendRight_apply {k l : ℕ} (x : Fin k → CoordinateRealTwoForm (k + l))
    (y : Fin l → CoordinateRealTwoForm (k + l)) :
    appendRight x y = actualMixedTopDensity (Fin.append x y) := rfl

variable {q p : ℕ}

/-- The one-slot term: with the first-factor sum slot in position `j`, the density is the product
`D(α, A) · D(Bᵖ, β)`. -/
theorem actualMixedTopDensity_fibreFamily_single (α : Fin q → CoordinateRealTwoForm (q + 1))
    (A : CoordinateRealTwoForm (q + 1)) (β B : CoordinateRealTwoForm (p + 1))
    (hα : ∀ i, IsOneOne (α i)) (hA : IsOneOne A) (hβ : IsOneOne β) (hB : IsOneOne B)
    (j : Fin (p + 1)) :
    actualMixedTopDensity (Fin.append
        (Fin.snoc (fun i => (α i).compContinuousLinearMap (projFst (q + 1) (p + 1)))
          (β.compContinuousLinearMap (projSnd (q + 1) (p + 1))))
        (Function.update (fun _ : Fin (p + 1) => B.compContinuousLinearMap (projSnd (q + 1) (p + 1)))
          j (A.compContinuousLinearMap (projFst (q + 1) (p + 1))))) =
      actualMixedTopDensity (Fin.snoc α A) *
        actualMixedTopDensity (Fin.snoc (fun _ : Fin p => B) β) := by
  set P₁ := projFst (q + 1) (p + 1)
  set P₂ := projSnd (q + 1) (p + 1)
  set G := Fin.append (Fin.snoc (fun i => (α i).compContinuousLinearMap P₁)
      (β.compContinuousLinearMap P₂))
    (Function.update (fun _ : Fin (p + 1) => B.compContinuousLinearMap P₂) j
      (A.compContinuousLinearMap P₁)) with hG
  set τ : Equiv.Perm (Fin ((q + 1) + (p + 1))) :=
    Equiv.swap (Fin.castAdd (p + 1) (Fin.last q)) (Fin.natAdd (q + 1) j) with hτ
  have hne : Fin.castAdd (p + 1) (Fin.last q) ≠ Fin.natAdd (q + 1) j := by
    intro h; rw [Fin.ext_iff] at h; simp at h; omega
  have hperm : (fun i => G (τ i)) =
      Fin.append (fun i => ((Fin.snoc α A : Fin (q + 1) → CoordinateRealTwoForm (q + 1)) i).compContinuousLinearMap P₁)
        (fun k => (Function.update (fun _ : Fin (p + 1) => B) j β k).compContinuousLinearMap P₂) := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rw [Fin.append_left]
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · rw [hτ, Equiv.swap_apply_left, hG, Fin.append_right, Function.update_self, Fin.snoc_last]
      · have h1 : Fin.castAdd (p + 1) k'.castSucc ≠ Fin.castAdd (p + 1) (Fin.last q) := by
          intro h; rw [Fin.ext_iff] at h; simp at h; omega
        have h2 : Fin.castAdd (p + 1) k'.castSucc ≠ Fin.natAdd (q + 1) j := by
          intro h; rw [Fin.ext_iff] at h; simp at h; omega
        rw [hτ, Equiv.swap_apply_of_ne_of_ne h1 h2, hG, Fin.append_left, Fin.snoc_castSucc,
          Fin.snoc_castSucc]
    · rw [Fin.append_right]
      by_cases hk : k = j
      · subst hk
        rw [hτ, Equiv.swap_apply_right, hG, Fin.append_left, Fin.snoc_last, Function.update_self]
      · have h1 : Fin.natAdd (q + 1) k ≠ Fin.castAdd (p + 1) (Fin.last q) := by
          intro h; rw [Fin.ext_iff] at h; simp at h; omega
        have h2 : Fin.natAdd (q + 1) k ≠ Fin.natAdd (q + 1) j := by
          intro h; apply hk; rw [Fin.ext_iff] at h ⊢; simp at h; omega
        rw [hτ, Equiv.swap_apply_of_ne_of_ne h1 h2, hG, Fin.append_right, Function.update_of_ne hk,
          Function.update_of_ne hk]
  have hone₁ : ∀ i, IsOneOne ((Fin.snoc α A : Fin (q + 1) → CoordinateRealTwoForm (q + 1)) i) := fun i =>
    Fin.lastCases (by rw [Fin.snoc_last]; exact hA) (fun i => by rw [Fin.snoc_castSucc]; exact hα i) i
  have hone₂ : ∀ k, IsOneOne (Function.update (fun _ : Fin (p + 1) => B) j β k) := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact hβ
    · rw [Function.update_of_ne hk]; exact hB
  rw [← actualMixedTopDensity_perm G τ, hperm, actualMixedTopDensity_append_comp _ _ hone₁ hone₂]
  congr 1
  have hsnoc : (Fin.snoc (fun _ : Fin p => B) β : Fin (p + 1) → CoordinateRealTwoForm (p + 1)) =
      fun k => Function.update (fun _ : Fin (p + 1) => B) j β (Equiv.swap j (Fin.last p) k) := by
    rw [show (fun k => Function.update (fun _ : Fin (p + 1) => B) j β (Equiv.swap j (Fin.last p) k)) =
        Function.update (fun _ : Fin (p + 1) => B) j β ∘ Equiv.swap j (Fin.last p) from rfl,
      Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left]
    rw [← Fin.update_snoc_last]
    congr 1
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]; rfl
  rw [hsnoc, actualMixedTopDensity_perm]

/-- **The density of the fibre family** (`dp04-kahler-cone:2.12`, `bou02-volume:4.8`): in
`ℂ^{q+1} × ℂ^{p+1}`,
`p₁^*α₀ ∧ ⋯ ∧ p₁^*α_{q-1} ∧ p₂^*β ∧ (p₁^*A + p₂^*B)^{p+1}` has density
`(p + 1) · D(α₀, …, α_{q-1}, A) · D(B, …, B, β)`. -/
theorem actualMixedTopDensity_fibreFamily (α : Fin q → CoordinateRealTwoForm (q + 1))
    (A : CoordinateRealTwoForm (q + 1)) (β B : CoordinateRealTwoForm (p + 1))
    (hα : ∀ i, IsOneOne (α i)) (hA : IsOneOne A) (hβ : IsOneOne β) (hB : IsOneOne B) :
    actualMixedTopDensity (Fin.append
        (Fin.snoc (fun i => (α i).compContinuousLinearMap (projFst (q + 1) (p + 1)))
          (β.compContinuousLinearMap (projSnd (q + 1) (p + 1))))
        (fun _ : Fin (p + 1) => A.compContinuousLinearMap (projFst (q + 1) (p + 1)) +
          B.compContinuousLinearMap (projSnd (q + 1) (p + 1)))) =
      ((p + 1 : ℕ) : ℝ) * actualMixedTopDensity (Fin.snoc α A) *
        actualMixedTopDensity (Fin.snoc (fun _ : Fin p => B) β) := by
  set P₁ := projFst (q + 1) (p + 1)
  set P₂ := projSnd (q + 1) (p + 1)
  set x : Fin (q + 1) → CoordinateRealTwoForm ((q + 1) + (p + 1)) :=
    Fin.snoc (fun i => (α i).compContinuousLinearMap P₁) (β.compContinuousLinearMap P₂) with hx
  set u := A.compContinuousLinearMap P₁
  set v := B.compContinuousLinearMap P₂
  set c := actualMixedTopDensity (Fin.snoc α A) *
    actualMixedTopDensity (Fin.snoc (fun _ : Fin p => B) β)
  have hterm : ∀ s : Finset (Fin (p + 1)),
      appendRight x (s.piecewise (fun _ => u) (fun _ => v)) = if s.card = 1 then c else 0 := by
    intro s
    split_ifs with hs
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hs
      rw [Finset.piecewise_singleton, appendRight_apply]
      exact actualMixedTopDensity_fibreFamily_single α A β B hα hA hβ hB j
    · rw [appendRight_apply]
      refine actualMixedTopDensity_eq_zero_of_scaleFst
        (Fin.append (Fin.snoc (fun _ => (4 : ℝ)) 1 : Fin (q + 1) → ℝ)
          (s.piecewise (fun _ => 4) (fun _ => 1)))
        (fun i => ?_) ?_
      · refine Fin.addCases (fun k => ?_) (fun k => ?_) i
        · rw [Fin.append_left, Fin.append_left]
          refine Fin.lastCases ?_ (fun k' => ?_) k
          · rw [Fin.snoc_last, hx, Fin.snoc_last, comp_projSnd_comp_scaleFst, one_smul]
          · rw [Fin.snoc_castSucc, hx, Fin.snoc_castSucc, comp_projFst_comp_scaleFst]
            norm_num
            rfl
        · rw [Fin.append_right, Fin.append_right]
          by_cases hk : k ∈ s
          · rw [Finset.piecewise_eq_of_mem _ _ _ hk, Finset.piecewise_eq_of_mem _ _ _ hk,
              comp_projFst_comp_scaleFst]
            norm_num
            rfl
          · rw [Finset.piecewise_eq_of_notMem _ _ _ hk, Finset.piecewise_eq_of_notMem _ _ _ hk,
              comp_projSnd_comp_scaleFst, one_smul]
      · have h1 : ∏ i : Fin (q + 1), (Fin.snoc (fun _ => (4 : ℝ)) 1 : Fin (q + 1) → ℝ) i = 4 ^ q := by
          rw [Fin.prod_univ_castSucc]
          simp
        have h2 : ∏ i, (s.piecewise (fun _ => (4 : ℝ)) (fun _ => 1)) i = 4 ^ s.card := by
          rw [Finset.prod_piecewise]
          simp
        rw [Fin.prod_univ_add]
        simp only [Fin.append_left, Fin.append_right]
        rw [h1, h2, ← pow_add]
        intro h
        have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 4) (by norm_num) h
        exact hs (by simp at this; omega)
  change appendRight x ((fun _ => u) + (fun _ => v)) = _
  rw [MultilinearMap.map_add_univ, Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun s : Finset (Fin (p + 1)) => s.card = 1).card = p + 1 := by
    have : (Finset.univ.filter fun s : Finset (Fin (p + 1)) => s.card = 1) =
        Finset.powersetCard 1 Finset.univ := by
      ext s
      simp [Finset.mem_powersetCard]
    rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_one_right]
  rw [hcard]
  ring

end FibreFamily

/-! ### Chains of wedges in coordinates, and the span of products of `(1,1)`-forms -/

section Chain

variable {N : ℕ}

/-- `Φ ↦ Φ ∧ Γ₀ ∧ ⋯ ∧ Γ_{r-1}` on coordinate forms, as a linear map. -/
def coordChain : (r : ℕ) → (Fin r → RealForm N 2) → (k : ℕ) →
    RealForm N (2 * k) →ₗ[ℝ] RealForm N (2 * (k + r))
  | 0, _, _ => LinearMap.id
  | r + 1, Γ, k => (wedgeBilin N (2 * (k + r))).flip (Γ (Fin.last r)) ∘ₗ
      coordChain r (fun i => Γ i.castSucc) k

theorem coordChain_succ_apply (r : ℕ) (Γ : Fin (r + 1) → RealForm N 2) (k : ℕ)
    (Φ : RealForm N (2 * k)) :
    coordChain (r + 1) Γ k Φ =
      coordinateWedge (coordChain r (fun i => Γ i.castSucc) k Φ) (Γ (Fin.last r)) := rfl

/-- On a product of two-forms the chain is the longer product. -/
theorem coordChain_wedgeProd : ∀ (r : ℕ) (Γ : Fin r → RealForm N 2) (k : ℕ)
    (α : Fin k → RealForm N 2),
    coordChain r Γ k (wedgeProd k α) = wedgeProd (k + r) (Fin.append α Γ)
  | 0, Γ, k, α => by
    change wedgeProd k α = _
    rw [Fin.append_right_nil _ _ rfl]
    congr 1
  | r + 1, Γ, k, α => by
    rw [coordChain_succ_apply, coordChain_wedgeProd r _ k α, ← wedgeProd_snoc, ← Fin.append_snoc]
    congr 2
    exact Fin.snoc_init_self Γ

/-- **The coefficients of a chain of test forms** are the coordinate chain of the coefficients. -/
theorem chainTestLM_coeff_eq {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] : ∀ (r : ℕ) (γ : Fin r → SmoothRealForm N M 2)
    (hγ : ∀ i, (γ i).IsTypeOneOne) (k : ℕ) (φ : testSpace N M k) (e : ComplexChart N M)
    (z : ComplexModel N),
    ((chainTestLM r γ hγ k φ : testSpace N M (k + r)) : SmoothRealForm N M (2 * (k + r))).coeff e z =
      coordChain r (fun j => (γ j).coeff e z) k ((φ : SmoothRealForm N M (2 * k)).coeff e z)
  | 0, _, _, _, _, _, _ => rfl
  | r + 1, γ, hγ, k, φ, e, z => by
    rw [chainTestLM_succ_apply, wedgeTwo_coeff,
      chainTestLM_coeff_eq r (fun i => γ i.castSucc) (fun i => hγ i.castSucc) k φ e z]
    rfl

theorem wedgeProd_compContinuousLinearMap {M' : ℕ} (L : ComplexModel M' →L[ℝ] ComplexModel N) :
    ∀ (k : ℕ) (α : Fin k → RealForm N 2),
      (wedgeProd k α).compContinuousLinearMap L =
        wedgeProd k (fun i => (α i).compContinuousLinearMap L)
  | 0, α => by ext v; rfl
  | k + 1, α => by
    rw [wedgeProd_succ, wedgeProd_succ, coordinateWedge_compContinuousLinearMap,
      wedgeProd_compContinuousLinearMap L k]

theorem coordinateWedge_zero_left {k l : ℕ} (C : RealForm N l) :
    coordinateWedge (0 : RealForm N k) C = 0 := by
  have := coordinateWedge_smul_left (n := N) (p := k) (0 : ℝ) 0 C
  rwa [zero_smul, zero_smul] at this

variable (N) in
/-- The span of the products of `k` real `(1,1)`-forms. -/
def wedgeProdSpan (k : ℕ) : Submodule ℝ (RealForm N (2 * k)) :=
  Submodule.span ℝ {P | ∃ α : Fin k → RealForm N 2, (∀ i, IsOneOne (α i)) ∧ P = wedgeProd k α}

theorem wedgeProd_mem_wedgeProdSpan {k : ℕ} {α : Fin k → RealForm N 2} (hα : ∀ i, IsOneOne (α i)) :
    wedgeProd k α ∈ wedgeProdSpan N k :=
  Submodule.subset_span ⟨α, hα, rfl⟩

theorem coordinateWedge_mem_wedgeProdSpan {k : ℕ} {P : RealForm N (2 * k)}
    (hP : P ∈ wedgeProdSpan N k) {B : RealForm N 2} (hB : IsOneOne B) :
    coordinateWedge P B ∈ wedgeProdSpan N (k + 1) := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [← wedgeProd_snoc]
    refine wedgeProd_mem_wedgeProdSpan fun i => ?_
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]; exact hB
    · rw [Fin.snoc_castSucc]; exact hα i
  | zero =>
    rw [coordinateWedge_zero_left]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [coordinateWedge_add_left]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [coordinateWedge_smul_left]
    exact Submodule.smul_mem _ c hx

/-- **Test forms are pointwise combinations of products of `(1,1)`-forms.** -/
theorem coeff_mem_wedgeProdSpan {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
    [IsComplexManifold N M] : ∀ (k : ℕ) {φ : SmoothRealForm N M (2 * k)},
    φ ∈ testSpace N M k → ∀ (e : ComplexChart N M) (z : ComplexModel N), z ∈ e.val.target →
      φ.coeff e z ∈ wedgeProdSpan N k
  | 0, φ, hφ, e, z, hz => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      rw [smulFun_coeff, unitForm_coeff]
      exact Submodule.smul_mem _ _ (wedgeProd_mem_wedgeProdSpan (α := Fin.elim0) fun i => i.elim0)
    | zero => rw [coeff_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [coeff_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [coeff_smul]; exact Submodule.smul_mem _ c hx
  | k + 1, φ, hφ, e, z, hz => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, β, hβ, rfl⟩ := hx
      rw [wedgeTwo_coeff]
      exact coordinateWedge_mem_wedgeProdSpan (coeff_mem_wedgeProdSpan k hP e z hz) (hβ e z hz)
    | zero => rw [coeff_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [coeff_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [coeff_smul]; exact Submodule.smul_mem _ c hx

end Chain

/-! ### The pointwise identity for test-form coefficients -/

section Pointwise

variable {q p : ℕ}

/-- **The fibre identity at a point**: for a coordinate `2q`-form `Φ` on `ℂ^{q+1}` in the span of
products of `(1,1)`-forms,
`(p₁^*Φ ∧ p₂^*β) ∧ (p₁^*A + p₂^*B)^{p+1}` has density `(p+1) · (Φ ∧ A) · D(Bᵖ, β)`. -/
theorem topDensity_fibreChain {Φ : RealForm (q + 1) (2 * q)} (hΦ : Φ ∈ wedgeProdSpan (q + 1) q)
    (A : RealForm (q + 1) 2) (β B : RealForm (p + 1) 2) (hA : IsOneOne A) (hβ : IsOneOne β)
    (hB : IsOneOne B) :
    topDensity (coordChain (p + 1)
        (fun _ => A.compContinuousLinearMap (projFst (q + 1) (p + 1)) +
          B.compContinuousLinearMap (projSnd (q + 1) (p + 1))) (q + 1)
        (coordinateWedge (Φ.compContinuousLinearMap (projFst (q + 1) (p + 1)))
          (β.compContinuousLinearMap (projSnd (q + 1) (p + 1))))) =
      ((p + 1 : ℕ) : ℝ) * topDensity (coordinateWedge Φ A) *
        actualMixedTopDensity (Fin.snoc (fun _ : Fin p => B) β) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [wedgeProd_compContinuousLinearMap, ← wedgeProd_snoc, coordChain_wedgeProd,
      topDensity_wedgeProd, ← wedgeProd_snoc, topDensity_wedgeProd]
    exact actualMixedTopDensity_fibreFamily α A β B hα hA hβ hB
  | zero =>
    have h0 : (0 : RealForm (q + 1) (2 * q)).compContinuousLinearMap (projFst (q + 1) (p + 1)) = 0 :=
      by ext v; rfl
    rw [h0, coordinateWedge_zero_left, coordinateWedge_zero_left, map_zero, topDensity_zero]
    simp
  | add x y _ _ hx hy =>
    have hadd : (x + y).compContinuousLinearMap (projFst (q + 1) (p + 1)) =
        x.compContinuousLinearMap (projFst (q + 1) (p + 1)) +
          y.compContinuousLinearMap (projFst (q + 1) (p + 1)) := by ext v; rfl
    rw [hadd, coordinateWedge_add_left, map_add, topDensity_add, hx, hy, coordinateWedge_add_left,
      topDensity_add]
    ring
  | smul c x _ hx =>
    have hsmul : (c • x).compContinuousLinearMap (projFst (q + 1) (p + 1)) =
        c • x.compContinuousLinearMap (projFst (q + 1) (p + 1)) := by ext v; rfl
    rw [hsmul, coordinateWedge_smul_left, map_smul, topDensity_smul, hx, coordinateWedge_smul_left,
      topDensity_smul]
    ring

end Pointwise

/-! ### Fibre integration of the smooth product currents -/

section Global

variable {q p : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (q + 1)) X]
  [IsComplexManifold (q + 1) X] {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (p + 1)) Y] [IsComplexManifold (p + 1) Y]

/-- The coefficients of `p₁^*a + p₂^*b` in a product chart. -/
theorem prodForm_coeff (a : ClosedRealOneOneForm (q + 1) X) (b : ClosedRealOneOneForm (p + 1) Y)
    (e : ComplexChart (q + 1) X) (e' : ComplexChart (p + 1) Y) {z : ComplexModel (q + 1)}
    {z' : ComplexModel (p + 1)} (hz : z ∈ e.val.target) (hz' : z' ∈ e'.val.target) :
    (prodForm a b).val.coeff (prodComplexChart e e') (prodModelEquiv (q + 1) (p + 1) (z, z')) =
      (a.val.coeff e z).compContinuousLinearMap (projFst (q + 1) (p + 1)) +
        (b.val.coeff e' z').compContinuousLinearMap (projSnd (q + 1) (p + 1)) := by
  rw [prodForm, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.pullback_val,
    ClosedRealOneOneForm.pullback_val, pullback_fst_coeff _ e e' hz hz',
    pullback_snd_coeff _ e e' hz hz']

/-- The density of `(p₁^*ω_X + p₂^*ω_Y)^{n+m}` in a product chart. -/
theorem topDensity_formPow_prodForm (a : ClosedRealOneOneForm (q + 1) X)
    (b : ClosedRealOneOneForm (p + 1) Y) (e : ComplexChart (q + 1) X) (e' : ComplexChart (p + 1) Y)
    {z : ComplexModel (q + 1)} {z' : ComplexModel (p + 1)} (hz : z ∈ e.val.target)
    (hz' : z' ∈ e'.val.target) :
    topDensity ((formPow (prodForm a b).val ((q + 1) + (p + 1))).coeff (prodComplexChart e e')
        (prodModelEquiv (q + 1) (p + 1) (z, z'))) =
      (((q + 1) + (p + 1)).choose (q + 1) : ℝ) *
        topDensity ((formPow a.val (q + 1)).coeff e z) *
          topDensity ((formPow b.val (p + 1)).coeff e' z') := by
  rw [formPow_coeff, formPow_coeff, formPow_coeff, prodForm_coeff a b e e' hz hz',
    topDensity_formPower, topDensity_formPower, topDensity_formPower, ← actualMixedTopDensity_const,
    ← actualMixedTopDensity_const, ← actualMixedTopDensity_const,
    actualMixedTopDensity_const_add_comp _ _ (a.2.2 e z hz) (b.2.2 e' z' hz')]

/-- **The pointwise fibre identity on `X × Y`**: the ratio to `(p₁^*ω_X + p₂^*ω_Y)^{n+m}` of
`p₁^*φ ∧ p₂^*β ∧ (p₁^*a + p₂^*b)^{p+1}` at `(x, y)` is
`(p + 1)/C(n+m, n)` times the ratio of `φ ∧ a` at `x` and of `bᵖ ∧ β` at `y`. -/
theorem topRatio_fibreChain (wX : KahlerBackground (q + 1) X) (wY : KahlerBackground (p + 1) Y)
    (a : ClosedRealOneOneForm (q + 1) X) (b : ClosedRealOneOneForm (p + 1) Y)
    {β : SmoothRealForm (p + 1) Y 2} (hβ : β.IsTypeOneOne) (φ : testSpace (q + 1) X q) (x : X)
    (y : Y) :
    topRatio (prodKahlerBackground wX wY).form.val
        ((chainTestLM (p + 1) (fun _ => (prodForm a b).val) (fun _ => (prodForm a b).2.2) (q + 1)
          (wedgeTestLM (isTypeOneOne_pullback contMDiff_snd hβ) q
            (pullbackTestLM contMDiff_fst q φ)) : testSpace ((q + 1) + (p + 1)) (X × Y)
              ((q + 1) + (p + 1))) : SmoothRealForm ((q + 1) + (p + 1)) (X × Y)
                (2 * ((q + 1) + (p + 1)))) (x, y) =
      ((p + 1 : ℕ) : ℝ) / ((((q + 1) + (p + 1)).choose (q + 1) : ℕ) : ℝ) *
        topRatio wX.form.val ((chainTestLM 1 (fun j => (![a] j).val) (fun j => (![a] j).2.2) q φ :
          testSpace (q + 1) X (q + 1)) : SmoothRealForm (q + 1) X (2 * (q + 1))) x *
        topRatio wY.form.val (wedgeTwo (formPow b.val p) β) y := by
  set e := complexChartAt (n := q + 1) x
  set e' := complexChartAt (n := p + 1) y
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have hz' : e'.val y ∈ e'.val.target := e'.val.map_source (mem_complexChartAt_source y)
  have hE : complexChartAt (n := (q + 1) + (p + 1)) (x, y) = prodComplexChart e e' := rfl
  have hEx : (prodComplexChart e e').val (x, y) =
      prodModelEquiv (q + 1) (p + 1) (e.val x, e'.val y) := rfl
  simp only [topRatio, chartRatio]
  rw [hE, hEx, chainTestLM_coeff_eq, prodKahlerBackground_form,
    topDensity_formPow_prodForm wX.form wY.form e e' hz hz', chainTestLM_coeff_eq]
  have hγ : (fun _ : Fin (p + 1) => (prodForm a b).val.coeff (prodComplexChart e e')
      (prodModelEquiv (q + 1) (p + 1) (e.val x, e'.val y))) =
      fun _ => (a.val.coeff e (e.val x)).compContinuousLinearMap (projFst (q + 1) (p + 1)) +
        (b.val.coeff e' (e'.val y)).compContinuousLinearMap (projSnd (q + 1) (p + 1)) := by
    funext _
    exact prodForm_coeff a b e e' hz hz'
  have hfib : ((wedgeTestLM (isTypeOneOne_pullback contMDiff_snd hβ) q
      (pullbackTestLM contMDiff_fst q φ) : testSpace ((q + 1) + (p + 1)) (X × Y) (q + 1)) :
        SmoothRealForm ((q + 1) + (p + 1)) (X × Y) (2 * (q + 1))).coeff (prodComplexChart e e')
          (prodModelEquiv (q + 1) (p + 1) (e.val x, e'.val y)) =
      coordinateWedge (((φ : SmoothRealForm (q + 1) X (2 * q)).coeff e (e.val x)).compContinuousLinearMap
        (projFst (q + 1) (p + 1))) ((β.coeff e' (e'.val y)).compContinuousLinearMap
          (projSnd (q + 1) (p + 1))) := by
    rw [coe_fibreTest hβ φ, wedgeTwo_coeff, pullback_fst_coeff _ e e' hz hz',
      pullback_snd_coeff _ e e' hz hz']
  rw [hγ, hfib, topDensity_fibreChain (coeff_mem_wedgeProdSpan q φ.2 e _ hz) _ _ _
    (a.2.2 e _ hz) (hβ e' _ hz') (b.2.2 e' _ hz')]
  have hX : coordChain 1 (fun j => (![a] j).val.coeff e (e.val x)) q
      ((φ : SmoothRealForm (q + 1) X (2 * q)).coeff e (e.val x)) =
      coordinateWedge ((φ : SmoothRealForm (q + 1) X (2 * q)).coeff e (e.val x))
        (a.val.coeff e (e.val x)) := rfl
  have hY : topDensity ((wedgeTwo (formPow b.val p) β).coeff e' (e'.val y)) =
      actualMixedTopDensity (Fin.snoc (fun _ : Fin p => b.val.coeff e' (e'.val y))
        (β.coeff e' (e'.val y))) := by
    rw [wedgeTwo_coeff, formPow_coeff, formPower_eq_wedgeProd, ← wedgeProd_snoc,
      topDensity_wedgeProd]
  rw [hX, hY]
  ring

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace X]
  [CompactSpace Y]

/-- `∫_Y bᵖ ∧ β`, the constant produced by integration along the fibres of `p₁`. -/
def fibreIntegral (wY : KahlerBackground (p + 1) Y) (b : ClosedRealOneOneForm (p + 1) Y)
    (β : SmoothRealForm (p + 1) Y 2) : ℝ :=
  ∫ y, topRatio wY.form.val (wedgeTwo (formPow b.val p) β) y ∂(kahlerVolume wY)

/-- **The Kähler volume of `X × Y`** for `p₁^*ω_X + p₂^*ω_Y` is `C(n+m, n) · vol_X ⊗ vol_Y`. -/
theorem kahlerVolume_prodKahlerBackground {n m : ℕ} {X' : Type*} [TopologicalSpace X']
    [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X'] [MeasurableSpace X'] [BorelSpace X']
    [CompactSpace X'] {Y' : Type*} [TopologicalSpace Y'] [ChartedSpace (ComplexModel m) Y']
    [IsComplexManifold m Y'] [MeasurableSpace Y'] [BorelSpace Y'] [CompactSpace Y']
    (wX : KahlerBackground n X') (wY : KahlerBackground m Y') :
    kahlerVolume (prodKahlerBackground wX wY) =
      ((n + m).choose n : ENNReal) • (kahlerVolume wX).prod (kahlerVolume wY) := by
  have hX : ThetaPlurisubharmonic wX.form.val (fun _ => 0) :=
    ((LocalPotentials.isThetaPshPotential_zero_iff wX.form).mpr wX.isSemipositive).1
  have hY : ThetaPlurisubharmonic wY.form.val (fun _ => 0) :=
    ((LocalPotentials.isThetaPshPotential_zero_iff wY.form).mpr wY.isSemipositive).1
  have hXY : ∀ _ : Fin (n + m), ThetaPlurisubharmonic (prodForm wX.form wY.form).val (fun _ => 0) :=
    fun _ => ((LocalPotentials.isThetaPshPotential_zero_iff (prodKahlerBackground wX wY).form).mpr
      (prodKahlerBackground wX wY).isSemipositive).1
  exact globalMixedMeasure_prodForm wX.form wY.form hX hY hXY

/-- For semipositive closed `b` and `β`, the fibre constant `∫_Y bᵖ ∧ β` is the total mixed mass
of `(b, …, b, β)` (zero potentials), the quantity of TN23's class invariance
(`MixedMassClassInvariance.globalMixedMeasure_real_univ_add_ddc`). -/
theorem fibreIntegral_eq_globalMixedMeasure (wY : KahlerBackground (p + 1) Y)
    (b β : ClosedRealOneOneForm (p + 1) Y)
    (hθ : ∀ i, ThetaPlurisubharmonic
      ((Fin.snoc (fun _ : Fin p => b) β : Fin (p + 1) → ClosedRealOneOneForm (p + 1) Y) i).val
        (fun _ => 0)) :
    fibreIntegral wY b β.val =
      (GlobalNonPluripolar.globalMixedMeasure
        (Fin.snoc (fun _ : Fin p => b) β : Fin (p + 1) → ClosedRealOneOneForm (p + 1) Y)
          (fun _ _ => 0) hθ).real univ := by
  set Φ : SmoothRealForm (p + 1) Y (2 * (p + 1)) := wedgeTwo (formPow b.val p) β.val with hΦdef
  have hcoeff : ∀ (e : ComplexChart (p + 1) Y) z,
      (fun i => ((Fin.snoc (fun _ : Fin p => b) β : Fin (p + 1) → ClosedRealOneOneForm (p + 1) Y)
        i).val.coeff e z) = Fin.snoc (fun _ : Fin p => b.val.coeff e z) (β.val.coeff e z) := by
    intro e z
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  have hden : ∀ (e : ComplexChart (p + 1) Y) z, topDensity (Φ.coeff e z) =
      actualMixedTopDensity fun i =>
        ((Fin.snoc (fun _ : Fin p => b) β : Fin (p + 1) → ClosedRealOneOneForm (p + 1) Y)
          i).val.coeff e z := by
    intro e z
    rw [hcoeff, hΦdef, wedgeTwo_coeff, formPow_coeff, formPower_eq_wedgeProd, ← wedgeProd_snoc,
      topDensity_wedgeProd]
  have hmeas := SmoothCurrentTraceMeasure.withDensity_topRatio_eq_globalMixedMeasure wY Φ hθ
    fun e z _ => hden e z
  have hnn : ∀ y, 0 ≤ topRatio wY.form.val Φ y := by
    intro y
    set e := complexChartAt (n := p + 1) y
    have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
    simp only [topRatio, chartRatio]
    refine div_nonneg ?_ (topDensity_formPow_pos wY.isKahler.1 hz).le
    rw [hden]
    exact actualMixedTopDensity_nonneg fun i =>
      SmoothMixedMeasureDensity.isSemipositiveOneOne_coeff (hθ i) hz
  rw [fibreIntegral, ← hΦdef, ← hmeas, measureReal_def, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      (continuous_topRatio wY.isKahler.1 Φ).aestronglyMeasurable]

/-- **"`R` lies in `m b`"** (`bou:pushforward-lower-bound`, `dp04-kahler-cone:2.12`,
`bou02-volume:4.8`): for smooth closed real `(1,1)`-forms `a` on `X`, `b` on `Y` and a real
`(1,1)`-form `β` on `Y`,

`p₁_*([X × Y] ∧ (p₁^*a + p₂^*b)^{p+1} ∧ p₂^*β) = (p + 1) (∫_Y bᵖ ∧ β) · [X] ∧ a`

as currents on `X` (all test forms; no positivity). -/
theorem fibrePushforward_smoothCurrent_prodForm (wX : KahlerBackground (q + 1) X)
    (wY : KahlerBackground (p + 1) Y) (a : ClosedRealOneOneForm (q + 1) X)
    (b : ClosedRealOneOneForm (p + 1) Y) {β : SmoothRealForm (p + 1) Y 2} (hβ : β.IsTypeOneOne) :
    fibrePushforward hβ
        (smoothCurrent (prodKahlerBackground wX wY) fun _ : Fin (p + 1) => prodForm a b) =
      (((p + 1 : ℕ) : ℝ) * fibreIntegral wY b β) • smoothCurrent wX ![a] := by
  ext φ
  rw [fibrePushforward_apply, LinearMap.smul_apply, smoothCurrent_apply, smoothCurrent_apply,
    integrationCurrent_apply, integrationCurrent_apply, smul_eq_mul,
    kahlerVolume_prodKahlerBackground, integral_smul_measure]
  simp_rw [topRatio_fibreChain wX wY a b hβ φ]
  have hC : ((((q + 1) + (p + 1)).choose (q + 1) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_prod_mul, ENNReal.toReal_natCast, fibreIntegral, smul_eq_mul]
  field_simp

end Global

end

end SGPT.Foundations.Analysis.Pending.FibrePushforwardProductForm
