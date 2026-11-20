import SGPT.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing
import SGPT.Foundations.Analysis.FirstPass.StandardKahlerTopPower
import SGPT.Foundations.Analysis.FirstPass.StandardHermitianTwoForm
import SGPT.Foundations.Analysis.Pending.ConstantFormProducts

/-!
# Exterior products of block-diagonal two-forms on the standard frame

Blueprint `claude-hodge-star` (lane HODGE-STAR, package `HodgeStar`), node
`claude-hodge-star:lem-block-pairing`: the combinatorial core of the Kähler star identity
`*γ = (Λγ) ω^{n-1}/(n-1)! - γ ∧ ω^{n-2}/(n-2)!` (Xia, *Foundations of pluripotential theory*,
`lem:kahler-trace-star`).

Write `e_{(k,0)} = e_k`, `e_{(k,1)} = i e_k` for the standard real frame of `ℂⁿ`.  A real
two-form `A` is *block diagonal* if `A(e_x, e_y) = 0` whenever `x` and `y` lie in different
complex lines.  TN expresses the exterior product of `n` two-forms on the frame as a signed sum
over the permutations of `Fin n × Fin 2` (`coordinateWedgeFamily_apply_eq_pairingSum`).  We show:

* `pairingSum_eq_sum_perm_of_offBlock`: if all factors **but one** are block diagonal, then only
  block permutations contribute and
  `A₀ ∧ ⋯ ∧ A_{n-1} (e) = ∑_{π ∈ S_n} ∏ᵢ Aᵢ(e_{(π i, 0)}, e_{(π i, 1)})`;
* `sum_perm_apply`, `sum_perm_apply_mul`: the sums over `S_n` with one or two marked slots;
* `wedge_power_standard_apply`: `(ω₀^{∧ m} ∧ ξ)(e) = m! ∑_k ξ(e_k, i e_k)` on `ℂ^{m+1}`;
* `wedge_power_wedge_standard_apply`:
  `(ω₀^{∧ m} ∧ D ∧ ξ)(e) = m! ((∑ λ)(∑ ξ_k) - ∑ λ_k ξ_k)` on `ℂ^{m+2}`, for the standard Kähler
  form `ω₀` and a block-diagonal `(1,1)`-form `D` with weights `λ`;

where `ξ` is an **arbitrary** real two-form.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace SGPT.Hodge

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending.ConstantFormProducts

variable {n : ℕ}

/-! ### Sums over permutations with marked slots -/

/-- Reindexing a permutation sum by a transposition moves the marked slot. -/
theorem sum_perm_apply_eq (f : Fin n → ℝ) (i₀ i : Fin n) :
    ∑ π : Equiv.Perm (Fin n), f (π i₀) = ∑ π : Equiv.Perm (Fin n), f (π i) := by
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap i₀ i)) (fun π : Equiv.Perm (Fin n) => f (π i))]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_right]

/-- `∑_{π ∈ S_n} f(π i₀) = (n-1)! ∑_k f k`. -/
theorem sum_perm_apply (f : Fin n → ℝ) (i₀ : Fin n) :
    ∑ π : Equiv.Perm (Fin n), f (π i₀) = ((n - 1).factorial : ℝ) * ∑ k, f k := by
  have hn : n ≠ 0 := by have := i₀.pos; omega
  have key : (n : ℝ) * ∑ π : Equiv.Perm (Fin n), f (π i₀) =
      (n.factorial : ℝ) * ∑ k, f k := by
    calc (n : ℝ) * ∑ π : Equiv.Perm (Fin n), f (π i₀)
        = ∑ i : Fin n, ∑ π : Equiv.Perm (Fin n), f (π i) := by
          rw [Finset.sum_congr rfl fun i _ => (sum_perm_apply_eq f i₀ i).symm]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ π : Equiv.Perm (Fin n), ∑ i, f (π i) := Finset.sum_comm
      _ = ∑ π : Equiv.Perm (Fin n), ∑ k, f k :=
          Finset.sum_congr rfl fun π _ => Equiv.sum_comp π f
      _ = (n.factorial : ℝ) * ∑ k, f k := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  have hfac : (n.factorial : ℝ) = n * (n - 1).factorial := by
    rw [← Nat.mul_factorial_pred hn]; push_cast; ring
  rw [hfac, mul_assoc] at key
  exact mul_left_cancel₀ (by exact_mod_cast hn) key

/-- `∑_{π ∈ S_n} f(π i₀) g(π i₁) = (n-2)! ((∑ f)(∑ g) - ∑ f g)` for distinct slots. -/
theorem sum_perm_apply_mul (f g : Fin n → ℝ) {i₀ i₁ : Fin n} (h : i₀ ≠ i₁) :
    ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i₁) =
      ((n - 2).factorial : ℝ) * ((∑ k, f k) * (∑ k, g k) - ∑ k, f k * g k) := by
  have hn : 2 ≤ n := by
    by_contra hlt
    exact h (Fin.ext (by have := i₀.isLt; have := i₁.isLt; omega))
  have hswap : ∀ i, i ≠ i₀ → ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i) =
      ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i₁) := by
    intro i hi
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap i₁ i))
      (fun π : Equiv.Perm (Fin n) => f (π i₀) * g (π i))]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne h hi.symm]
  have htot : ∑ i : Fin n, ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i) =
      ((n - 1).factorial : ℝ) * (∑ k, f k) * ∑ k, g k := by
    calc ∑ i : Fin n, ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i)
        = ∑ π : Equiv.Perm (Fin n), f (π i₀) * ∑ i, g (π i) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ π : Equiv.Perm (Fin n), f (π i₀) * ∑ k, g k :=
          Finset.sum_congr rfl fun π _ => by rw [Equiv.sum_comp π g]
      _ = (∑ π : Equiv.Perm (Fin n), f (π i₀)) * ∑ k, g k := (Finset.sum_mul _ _ _).symm
      _ = _ := by rw [sum_perm_apply f i₀]
  have hsplit : ∑ i : Fin n, ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i) =
      ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i₀) +
        ((n - 1 : ℕ) : ℝ) * ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i₁) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    congr 1
    rw [Finset.sum_congr rfl fun i hi => hswap i (Finset.ne_of_mem_erase hi), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hdiag : ∑ π : Equiv.Perm (Fin n), f (π i₀) * g (π i₀) =
      ((n - 1).factorial : ℝ) * ∑ k, f k * g k :=
    sum_perm_apply (fun k => f k * g k) i₀
  have hfac : ((n - 1).factorial : ℝ) = ((n - 1 : ℕ) : ℝ) * (n - 2).factorial := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have hne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  rw [hsplit, hdiag, hfac] at htot
  apply mul_left_cancel₀ hne
  linear_combination htot

/-! ### Pairing sums of block-diagonal families -/

theorem perm_fin_two_cases : ∀ τ : Equiv.Perm (Fin 2), τ = 1 ∨ τ = Equiv.swap 0 1 := by
  decide

theorem fin_two_eq_or {t t' : Fin 2} (h : t' ≠ t) (r : Fin 2) : r = t ∨ r = t' := by
  revert t t' r
  decide

theorem exists_fin_two_ne (t : Fin 2) : ∃ t' : Fin 2, t' ≠ t := by
  revert t
  decide

/-- Antisymmetry of a two-form, in the `![u, v]` notation. -/
theorem twoForm_apply_swap (A : CoordinateRealTwoForm n) (u v : ComplexModel n) :
    A ![v, u] = -A ![u, v] := by
  have h := A.toAlternatingMap.map_swap ![u, v] (i := 0) (j := 1) (by decide)
  have hv : (![u, v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h

/-- The sign of a block permutation `(i, t) ↦ (π i, εᵢ t)` is the product of the block signs. -/
theorem sign_prodShear {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → Equiv.Perm (Fin 2)) :
    Equiv.Perm.sign (Equiv.prodShear π ε) = ∏ i, Equiv.Perm.sign (ε i) := by
  have h : (Equiv.prodShear π ε : Equiv.Perm (Fin k × Fin 2)) =
      Equiv.prodCongrLeft (fun _ : Fin 2 => π) * Equiv.prodCongrRight ε := by
    ext x <;> rfl
  rw [h, Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrLeft,
    Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two, Int.units_mul_self, one_mul]

/-- The term of a block permutation: the orientation of each block cancels its sign. -/
theorem prodShear_term (A : Fin n → CoordinateRealTwoForm n) (v : Fin n × Fin 2 → ComplexModel n)
    (π : Equiv.Perm (Fin n)) (ε : Fin n → Equiv.Perm (Fin 2)) :
    ((Equiv.Perm.sign (Equiv.prodShear π ε) : ℤ) : ℝ) *
        ∏ i, A i ![v ((Equiv.prodShear π ε) (i, 0)), v ((Equiv.prodShear π ε) (i, 1))] =
      ∏ i, A i ![v (π i, 0), v (π i, 1)] := by
  rw [sign_prodShear, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Equiv.prodShear_apply]
  rcases perm_fin_two_cases (ε i) with h | h
  · rw [h]
    simp
  · rw [h, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one]
    rw [twoForm_apply_swap]
    ring

/-- **Pairing sum of a family whose factors are all block diagonal but one.**  If every factor
`A i` with `i ≠ i₀` vanishes on pairs of frame vectors from different blocks, then only the block
permutations contribute to the Pfaffian-type sum, and each block permutation contributes the
product of the block values. -/
theorem pairingSum_eq_sum_perm_of_offBlock (A : Fin n → CoordinateRealTwoForm n) (i₀ : Fin n)
    (v : Fin n × Fin 2 → ComplexModel n)
    (hA : ∀ i, i ≠ i₀ → ∀ x y : Fin n × Fin 2, x.1 ≠ y.1 → A i ![v x, v y] = 0) :
    coordinatePairingSumFamily A (id : Fin n × Fin 2 → Fin n × Fin 2) v =
      2 ^ n * ∑ π : Equiv.Perm (Fin n), ∏ i, A i ![v (π i, 0), v (π i, 1)] := by
  classical
  unfold coordinatePairingSumFamily
  simp only [id]
  set Φ : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2)) →
      Equiv.Perm (Fin n × Fin 2) := fun x => Equiv.prodShear x.1 x.2 with hΦ
  have hΦinj : Function.Injective Φ := by
    rintro ⟨π, ε⟩ ⟨π', ε'⟩ hx
    have hx' : ∀ i b, (π i, ε i b) = (π' i, ε' i b) := fun i b =>
      congrArg (fun σ : Equiv.Perm (Fin n × Fin 2) => σ (i, b)) hx
    refine Prod.ext (Equiv.ext fun i => congrArg Prod.fst (hx' i 0)) ?_
    funext i
    exact Equiv.ext fun b => congrArg Prod.snd (hx' i b)
  set F : Equiv.Perm (Fin n) → ℝ := fun π => ∏ i, A i ![v (π i, 0), v (π i, 1)] with hF
  refine ((Finset.sum_of_injOn Φ hΦinj.injOn
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ (s := Finset.univ)
    (f := fun x => F x.1) ?_).symm).trans ?_
  · intro σ _ hσ
    by_contra hne
    apply hσ
    have hprod := right_ne_zero_of_mul hne
    rw [Finset.prod_ne_zero_iff] at hprod
    have hfst0 : ∀ i, i ≠ i₀ → (σ (i, 0)).1 = (σ (i, 1)).1 := by
      intro i hi
      by_contra hc
      exact hprod i (Finset.mem_univ _) (hA i hi _ _ hc)
    -- the marked slot: its two values lie in the one block left free by the other slots
    have hfst₀ : (σ (i₀, 0)).1 = (σ (i₀, 1)).1 := by
      obtain ⟨t', htt'⟩ := exists_fin_two_ne (σ (i₀, 0)).2
      set x := σ.symm ((σ (i₀, 0)).1, t') with hxdef
      have hx : σ x = ((σ (i₀, 0)).1, t') := σ.apply_symm_apply _
      have hx0 : x ≠ (i₀, 0) := by
        intro h
        rw [h] at hx
        exact htt' (congrArg Prod.snd hx).symm
      have hx1 : x.1 = i₀ := by
        by_contra hne'
        obtain ⟨s', hs'⟩ := exists_fin_two_ne x.2
        have hfx := hfst0 x.1 hne'
        have hall : ∀ s s'' : Fin 2, (σ (x.1, s)).1 = (σ (x.1, s'')).1 := by
          intro s s''
          fin_cases s <;> fin_cases s'' <;> simp [hfx]
        have h1 : (σ (x.1, s')).1 = (σ (i₀, 0)).1 := by
          rw [hall s' x.2]
          simp only [Prod.mk.eta, hx]
        rcases fin_two_eq_or htt' (σ (x.1, s')).2 with hr | hr
        · have heq : σ (x.1, s') = σ (i₀, 0) := Prod.ext h1 hr
          exact hne' (congrArg Prod.fst (σ.injective heq))
        · have heq : σ (x.1, s') = σ x := Prod.ext (by rw [h1, hx]) (by rw [hr, hx])
          exact hs' (congrArg Prod.snd (σ.injective heq))
      have hxeq : x = (i₀, 1) := by
        refine Prod.ext hx1 ?_
        have h2 : x.2 ≠ 0 := fun h => hx0 (Prod.ext hx1 h)
        have h01 : ∀ t : Fin 2, t ≠ 0 → t = 1 := by decide
        exact h01 _ h2
      rw [← hxeq, hx]
    have hfst : ∀ i, (σ (i, 0)).1 = (σ (i, 1)).1 := by
      intro i
      by_cases hi : i = i₀
      · subst hi; exact hfst₀
      · exact hfst0 i hi
    have hfst' : ∀ i b, (σ (i, b)).1 = (σ (i, 0)).1 := by
      intro i b
      fin_cases b
      · rfl
      · exact (hfst i).symm
    have hπ : Function.Injective fun i => (σ (i, 0)).1 := by
      intro i i' hii'
      simp only at hii'
      have hab : σ (i, 0) ≠ σ (i, 1) := fun h => by
        simpa using σ.injective h
      have hab2 : (σ (i, 0)).2 ≠ (σ (i, 1)).2 := fun h => hab (Prod.ext (hfst i) h)
      rcases fin_two_eq_or (Ne.symm hab2) (σ (i', 0)).2 with hc | hc
      · have := σ.injective (Prod.ext hii'.symm hc)
        exact (congrArg Prod.fst this).symm
      · have := σ.injective (Prod.ext ((hfst i).symm.trans hii').symm hc)
        simp at this
    have hε : ∀ i, Function.Injective fun b => (σ (i, b)).2 := by
      intro i b b' hbb'
      have := σ.injective (Prod.ext ((hfst' i b).trans (hfst' i b').symm) hbb')
      simpa using this
    refine ⟨(Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hπ),
      fun i => Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (hε i))),
      Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    ext x
    · obtain ⟨i, b⟩ := x
      simp [hΦ, Equiv.prodShear, hfst' i b]
    · obtain ⟨i, b⟩ := x
      simp [hΦ, Equiv.prodShear]
  · rintro ⟨π, ε⟩ _
    exact (prodShear_term A v π ε).symm
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_perm,
      Fintype.card_fin, Nat.factorial_two, Finset.prod_const, nsmul_eq_mul, Finset.mul_sum]
    push_cast
    rfl

/-! ### The standard frame -/

/-- The standard real frame vector `e_{(k,t)}` (`e_k` for `t = 0`, `i e_k` for `t = 1`). -/
abbrev frameVec (x : Fin n × Fin 2) : ComplexModel n := coordinateRealFrame (finProdFinEquiv x)

theorem pairingSum_frame (A : Fin n → CoordinateRealTwoForm n) :
    coordinatePairingSumFamily A (finProdFinEquiv : Fin n × Fin 2 → Fin (n * 2))
        coordinateRealFrame =
      coordinatePairingSumFamily A (id : Fin n × Fin 2 → Fin n × Fin 2) frameVec := by
  have h := coordinatePairingSumFamily_equiv A
    (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)) id coordinateRealFrame
  rw [Function.comp_id] at h
  exact h

/-- A two-form is block diagonal with weights `λ` on the standard frame. -/
def IsBlockDiagonal (D : CoordinateRealTwoForm n) (d : Fin n → ℝ) : Prop :=
  ∀ x y : Fin n × Fin 2, D ![frameVec x, frameVec y] =
    if x.1 = y.1 then d x.1 * (((y.2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) else 0

theorem IsBlockDiagonal.offBlock {D : CoordinateRealTwoForm n} {d : Fin n → ℝ}
    (hD : IsBlockDiagonal D d) {x y : Fin n × Fin 2} (h : x.1 ≠ y.1) :
    D ![frameVec x, frameVec y] = 0 := by
  rw [hD, if_neg h]

theorem IsBlockDiagonal.block {D : CoordinateRealTwoForm n} {d : Fin n → ℝ}
    (hD : IsBlockDiagonal D d) (k : Fin n) :
    D ![frameVec (k, 0), frameVec (k, 1)] = d k := by
  rw [hD, if_pos rfl]
  norm_num

/-- The standard Kähler form `∑ dxₖ ∧ dyₖ` is block diagonal with unit weights. -/
theorem standardHermitianTwoForm_isBlockDiagonal :
    IsBlockDiagonal (standardHermitianTwoForm n) (fun _ => 1) := by
  intro x y
  rw [apply_coordinateRealFrame_of_apply_eq_im _ standardHermitianTwoForm_apply x y]
  simp

/-- `ω^{∧m}` read as a pairing sum. -/
theorem coordinateWedgePower_apply_eq_pairingSumFamily (a : CoordinateRealTwoForm n) (m : ℕ)
    (u : Fin (m * 2) → ComplexModel n) :
    coordinateWedgePower a m u = ((2 : ℝ) ^ m)⁻¹ *
      coordinatePairingSumFamily (fun _ : Fin m => a)
        (finProdFinEquiv : Fin m × Fin 2 → Fin (m * 2)) u := by
  rw [← coordinateWedgeFamily_const, coordinateWedgeFamily_apply_eq_pairingSum]

/-- `ω^{∧m} ∧ B` read as a pairing sum. -/
theorem coordinateWedge_power_apply_eq_pairingSumFamily (a B : CoordinateRealTwoForm n) (m : ℕ)
    (v : Fin ((m + 1) * 2) → ComplexModel n) :
    coordinateWedge (coordinateWedgePower a m) B
        (v ∘ Fin.cast (show m * 2 + 2 = (m + 1) * 2 by ring)) =
      ((2 : ℝ) ^ (m + 1))⁻¹ *
        coordinatePairingSumFamily
          (Fin.snoc (α := fun _ => CoordinateRealTwoForm n) (fun _ => a) B)
          (finProdFinEquiv : Fin (m + 1) × Fin 2 → Fin ((m + 1) * 2)) v := by
  have h := coordinateWedgeFamily_step_eq_pairingSum
    (Fin.snoc (α := fun _ => CoordinateRealTwoForm n) (fun _ => a) B)
    (coordinateWedgePower a m) (fun u => by
      simp only [Fin.snoc_castSucc]
      exact coordinateWedgePower_apply_eq_pairingSumFamily a m u) v
  simpa only [Fin.snoc_last] using h

/-- **`(ω₀^{∧m} ∧ ξ)(e) = m! ∑ₖ ξ(e_k, i e_k)`** on `ℂ^{m+1}`, for an arbitrary two-form `ξ`. -/
theorem wedge_power_standard_apply (m : ℕ) (ξ : CoordinateRealTwoForm (m + 1)) :
    coordinateWedge (coordinateWedgePower (standardHermitianTwoForm (m + 1)) m) ξ
        (coordinateRealFrame ∘ Fin.cast (show m * 2 + 2 = (m + 1) * 2 by ring)) =
      (m.factorial : ℝ) * ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] := by
  have hω : ∀ k, standardHermitianTwoForm (m + 1) ![frameVec (k, 0), frameVec (k, 1)] = 1 :=
    fun k => standardHermitianTwoForm_isBlockDiagonal.block k
  set A := Fin.snoc (α := fun _ => CoordinateRealTwoForm (m + 1))
    (fun _ => standardHermitianTwoForm (m + 1)) ξ with hAdef
  rw [coordinateWedge_power_apply_eq_pairingSumFamily, pairingSum_frame]
  have hblock : ∀ i, i ≠ Fin.last m → ∀ x y : Fin (m + 1) × Fin 2, x.1 ≠ y.1 →
      A i ![frameVec x, frameVec y] = 0 := by
    intro i hi x y hxy
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [hAdef, Fin.snoc_castSucc]
    exact standardHermitianTwoForm_isBlockDiagonal.offBlock hxy
  rw [pairingSum_eq_sum_perm_of_offBlock A (Fin.last m) frameVec hblock]
  have hterm : ∀ π : Equiv.Perm (Fin (m + 1)),
      ∏ i, A i ![frameVec (π i, 0), frameVec (π i, 1)] =
        ξ ![frameVec (π (Fin.last m), 0), frameVec (π (Fin.last m), 1)] := by
    intro π
    rw [Fin.prod_univ_castSucc]
    simp only [hAdef, Fin.snoc_castSucc, Fin.snoc_last, hω, Finset.prod_const_one, one_mul]
  simp only [hterm]
  rw [sum_perm_apply (fun k => ξ ![frameVec (k, 0), frameVec (k, 1)]) (Fin.last m)]
  simp only [Nat.add_sub_cancel]
  field_simp

/-- **`(ω₀^{∧m} ∧ D ∧ ξ)(e) = m! ((∑ λ)(∑ ξₖ) - ∑ λₖ ξₖ)`** on `ℂ^{m+2}`, for a block-diagonal
`D` with weights `λ` and an arbitrary two-form `ξ`. -/
theorem wedge_power_wedge_standard_apply (m : ℕ) (D ξ : CoordinateRealTwoForm (m + 2))
    {d : Fin (m + 2) → ℝ} (hD : IsBlockDiagonal D d) :
    coordinateWedge (castForm (show m * 2 + 2 = (m + 1) * 2 by ring)
        (coordinateWedge (coordinateWedgePower (standardHermitianTwoForm (m + 2)) m) D)) ξ
        (coordinateRealFrame ∘ Fin.cast (show (m + 1) * 2 + 2 = (m + 2) * 2 by ring)) =
      (m.factorial : ℝ) * ((∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)]) * (∑ k, d k) -
        ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] * d k) := by
  have hω : ∀ k, standardHermitianTwoForm (m + 2) ![frameVec (k, 0), frameVec (k, 1)] = 1 :=
    fun k => standardHermitianTwoForm_isBlockDiagonal.block k
  set ω₀ := standardHermitianTwoForm (m + 2) with hω₀
  set B := Fin.snoc (α := fun _ => CoordinateRealTwoForm (m + 2)) (fun _ => ω₀) D with hBdef
  set A := Fin.snoc (α := fun _ => CoordinateRealTwoForm (m + 2)) B ξ with hAdef
  have h := coordinateWedgeFamily_step_eq_pairingSum A
    (castForm (show m * 2 + 2 = (m + 1) * 2 by ring)
      (coordinateWedge (coordinateWedgePower ω₀ m) D)) (fun u => by
        simp only [hAdef, Fin.snoc_castSucc]
        rw [castForm_apply]
        exact coordinateWedge_power_apply_eq_pairingSumFamily ω₀ D m u) coordinateRealFrame
  simp only [hAdef, Fin.snoc_last] at h
  rw [h, pairingSum_frame]
  have hblock : ∀ i, i ≠ Fin.last (m + 1) → ∀ x y : Fin (m + 2) × Fin 2, x.1 ≠ y.1 →
      A i ![frameVec x, frameVec y] = 0 := by
    intro i hi x y hxy
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    rw [hAdef, Fin.snoc_castSucc]
    by_cases hi' : i' = Fin.last m
    · subst hi'
      rw [hBdef, Fin.snoc_last]
      exact hD.offBlock hxy
    · obtain ⟨i'', rfl⟩ := Fin.eq_castSucc_of_ne_last hi'
      rw [hBdef, Fin.snoc_castSucc]
      exact standardHermitianTwoForm_isBlockDiagonal.offBlock hxy
  rw [pairingSum_eq_sum_perm_of_offBlock A (Fin.last (m + 1)) frameVec hblock]
  have hterm : ∀ π : Equiv.Perm (Fin (m + 2)),
      ∏ i, A i ![frameVec (π i, 0), frameVec (π i, 1)] =
        ξ ![frameVec (π (Fin.last (m + 1)), 0), frameVec (π (Fin.last (m + 1)), 1)] *
          d (π (Fin.castSucc (Fin.last m))) := by
    intro π
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [hAdef, hBdef, Fin.snoc_castSucc, Fin.snoc_last, hω, hD.block,
      Finset.prod_const_one, one_mul]
    ring
  simp only [hterm]
  rw [sum_perm_apply_mul (fun k => ξ ![frameVec (k, 0), frameVec (k, 1)]) d
    (Fin.castSucc_lt_last (Fin.last m)).ne']
  simp only [show m + 2 - 2 = m by omega]
  field_simp

/-- `wedge_power_standard_apply` in a dimension `N = m + 1` given by an equation. -/
theorem wedge_power_standard_apply_of_eq {N : ℕ} (m : ℕ) (hN : N = m + 1)
    (ξ : CoordinateRealTwoForm N) :
    coordinateWedge (coordinateWedgePower (standardHermitianTwoForm N) m) ξ
        (coordinateRealFrame ∘ Fin.cast (show m * 2 + 2 = N * 2 by subst hN; ring)) =
      (m.factorial : ℝ) * ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] := by
  subst hN
  exact wedge_power_standard_apply m ξ

/-- `wedge_power_wedge_standard_apply` in a dimension `N = m + 2` given by an equation. -/
theorem wedge_power_wedge_standard_apply_of_eq {N : ℕ} (m : ℕ) (hN : N = m + 2)
    (D ξ : CoordinateRealTwoForm N) {d : Fin N → ℝ} (hD : IsBlockDiagonal D d) :
    coordinateWedge (castForm (show m * 2 + 2 = (m + 1) * 2 by ring)
        (coordinateWedge (coordinateWedgePower (standardHermitianTwoForm N) m) D)) ξ
        (coordinateRealFrame ∘ Fin.cast (show (m + 1) * 2 + 2 = N * 2 by subst hN; ring)) =
      (m.factorial : ℝ) * ((∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)]) * (∑ k, d k) -
        ∑ k, ξ ![frameVec (k, 0), frameVec (k, 1)] * d k) := by
  subst hN
  exact wedge_power_wedge_standard_apply m D ξ hD
