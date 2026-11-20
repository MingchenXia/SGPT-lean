import SGPT.Foundations.Analysis.Pending.LinearEllipticRegularity

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Schauder estimate of every order on the whole space

Let `E` be a finite-dimensional real inner product space with an orthonormal basis `b`, `0 < r < 1`, `k ∈ ℕ`, and
`L v = a : D²v + Dv(β) + c v` (`SchauderWholeSpace.ellipticOp`) a second-order operator whose coefficients lie in
`C^{k,r}_b` (`a` symmetric and `λ`-elliptic at every point).

**Main result** `exists_norm_le` (blueprint `bou:schauder-whole-space-higher`; Gilbarg--Trudinger Problem 6.1, Székelyhidi
Theorem 2.8 for every `k`): there is `C` such that every `u ∈ C^{k+2,r}_b(E)` with `|u| ≤ S` and `L u = g ∈ C^{k,r}_b(E)`
satisfies

`‖u‖_{C^{k+2,r}_b} ≤ C (‖g‖_{C^{k,r}_b} + S)`.

Proof, by induction on `k`.  For `k = 0` it is `SchauderWholeSpace.exists_schauder_estimate`.  For `k + 1`: the case `k`
applied to `u` bounds `‖u‖_{C^{k+2,r}_b}`; each directional derivative `w_i = ∂_{b_i} u` solves
`L w_i = ∂_{b_i} g̃ - (∂_{b_i} a) : D²u + Dw_i(β) + c w_i` with `g̃ = g - Du(β) - c u`
(`LinearRegularity.hessTrace_fderiv_apply_eq`, symmetry of third derivatives), whose right-hand side is bounded in
`C^{k,r}_b` by `‖g‖_{C^{k+1,r}_b} + ‖u‖_{C^{k+2,r}_b}` (products and derivatives in `C^{k,r}_b`); the case `k` applied to
`w_i` bounds `‖w_i‖_{C^{k+2,r}_b}`, and `Du = ∑ᵢ w_i ⟪b_i, ·⟫` gives `‖u‖_{C^{k+3,r}_b}`.  No interpolation is needed
beyond the case `k = 0`.

## Main definitions and results

* `BoundedContDiffHolderMap.lowerMap` (`C^{k+1,r}_b ⊆ C^{k,r}_b`), `constMap`, `clmMap` (composition with a continuous
  linear map), `dirMap` (a directional derivative), with norm bounds;
* `hessTraceBil` (`(A, Q) ↦ A : Q` as a continuous bilinear map);
* **`exists_norm_le`**.

TN.5, blueprint `bou:schauder-global` (the estimate for every `k`; the case `k = 0` is `ManifoldSchauder`).
-/

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ContDiff RealInnerProductSpace

namespace SGPT.Foundations.Analysis.Pending

namespace BoundedContDiffHolderMap

variable {k : ℕ} {r : ℝ≥0} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Lowering the order, constants, linear maps, directional derivatives -/

/-- The inclusion `C^{k+1,r}_b(E, F) ⊆ C^{k,r}_b(E, F)` (`r ≤ 1`). -/
def lowerMap (hr : r ≤ 1) (f : BoundedContDiffHolderMap (k + 1) r E F) : BoundedContDiffHolderMap k r E F :=
  ofContDiff hr f f.contDiff (M := ‖f‖) fun _ hi x => f.norm_iteratedFDeriv_apply_le hi x

@[simp]
theorem coe_lowerMap (hr : r ≤ 1) (f : BoundedContDiffHolderMap (k + 1) r E F) : ⇑(lowerMap hr f) = f :=
  rfl

/-- `‖f‖_{k,r} ≤ (k + 3) ‖f‖_{k+1,r}`. -/
theorem norm_lowerMap_le (hr : r ≤ 1) (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ‖lowerMap hr f‖ ≤ (k + 3) * ‖f‖ :=
  norm_ofContDiff_le hr _ _ _

/-- A constant map as an element of `C^{k,r}_b` (`r ≤ 1`). -/
def constMap (hr : r ≤ 1) (c : F) : BoundedContDiffHolderMap k r E F :=
  ofContDiff hr (fun _ : E => c) contDiff_const (M := ‖c‖) fun i _ x => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [norm_iteratedFDeriv_zero]
    · rw [iteratedFDeriv_const_of_ne hi.ne' c]
      simp

@[simp]
theorem coe_constMap (hr : r ≤ 1) (c : F) : ⇑(constMap (k := k) (E := E) hr c) = fun _ => c :=
  rfl

theorem norm_constMap_le (hr : r ≤ 1) (c : F) : ‖constMap (k := k) (E := E) hr c‖ ≤ (k + 3) * ‖c‖ :=
  norm_ofContDiff_le hr _ _ _

/-- Composition with a continuous linear map, `x ↦ L (f x)`, in `C^{k,r}_b` (`r ≤ 1`). -/
def clmMap (hr : r ≤ 1) (L : F →L[ℝ] G) (f : BoundedContDiffHolderMap k r E F) :
    BoundedContDiffHolderMap k r E G :=
  bilinear hr ((ContinuousLinearMap.lsmul ℝ ℝ).flip L) (constMap hr (1 : ℝ)) f

@[simp]
theorem coe_clmMap (hr : r ≤ 1) (L : F →L[ℝ] G) (f : BoundedContDiffHolderMap k r E F) :
    ⇑(clmMap hr L f) = fun x => L (f x) := by
  funext x
  simp [clmMap]

theorem norm_clmMap_le (hr : r ≤ 1) (L : F →L[ℝ] G) (f : BoundedContDiffHolderMap k r E F) :
    ‖clmMap hr L f‖ ≤ 2 ^ (k + 3) * (k + 3) * ‖L‖ * ‖f‖ := by
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ).flip L‖ ≤ ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun t => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    change ‖t • L v‖ ≤ _
    rw [norm_smul]
    calc ‖t‖ * ‖L v‖ ≤ ‖t‖ * (‖L‖ * ‖v‖) := by gcongr; exact L.le_opNorm v
      _ = ‖L‖ * ‖t‖ * ‖v‖ := by ring
  have h1 := norm_bilinear_le hr ((ContinuousLinearMap.lsmul ℝ ℝ).flip L) (constMap (k := k) (E := E) hr (1 : ℝ)) f
  have h2 := norm_constMap_le (k := k) (E := E) hr (1 : ℝ)
  rw [norm_one, mul_one] at h2
  calc ‖clmMap hr L f‖ ≤ 2 ^ (k + 3) * ‖(ContinuousLinearMap.lsmul ℝ ℝ).flip L‖ *
        ‖constMap (k := k) (E := E) hr (1 : ℝ)‖ * ‖f‖ := h1
    _ ≤ 2 ^ (k + 3) * ‖L‖ * (k + 3) * ‖f‖ := by gcongr
    _ = 2 ^ (k + 3) * (k + 3) * ‖L‖ * ‖f‖ := by ring

/-- The directional derivative `x ↦ Df(x) ζ` of `f ∈ C^{k+1,r}_b`, in `C^{k,r}_b` (`r ≤ 1`). -/
def dirMap (hr : r ≤ 1) (ζ : E) (f : BoundedContDiffHolderMap (k + 1) r E F) : BoundedContDiffHolderMap k r E F :=
  clmMap hr (ContinuousLinearMap.apply ℝ F ζ) f.fderivMap

@[simp]
theorem coe_dirMap (hr : r ≤ 1) (ζ : E) (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ⇑(dirMap hr ζ f) = fun x => fderiv ℝ f x ζ := by
  funext x
  simp [dirMap]

theorem norm_dirMap_le (hr : r ≤ 1) (ζ : E) (f : BoundedContDiffHolderMap (k + 1) r E F) :
    ‖dirMap hr ζ f‖ ≤ 2 ^ (k + 3) * (k + 3) * ‖ζ‖ * ‖f‖ := by
  have hA : ‖ContinuousLinearMap.apply ℝ F ζ‖ ≤ ‖ζ‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact T.le_opNorm ζ
  calc ‖dirMap hr ζ f‖ ≤ 2 ^ (k + 3) * (k + 3) * ‖ContinuousLinearMap.apply ℝ F ζ‖ * ‖f.fderivMap‖ :=
        norm_clmMap_le hr _ _
    _ ≤ 2 ^ (k + 3) * (k + 3) * ‖ζ‖ * ‖f‖ := by
        gcongr
        exact norm_fderivMap_le f

end BoundedContDiffHolderMap

namespace SchauderHigherOrder

open BoundedContDiffHolderMap EllipticMeanValue SchauderBlowup SchauderWholeSpace WholeSpaceSolvability
  LinearRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-! ### `A : Q` as a continuous bilinear map -/

theorem abs_hessTrace_le (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] ℝ) :
    |hessTrace b A Q| ≤ Fintype.card ι * ‖A‖ * ‖Q‖ := by
  unfold hessTrace
  calc |∑ i, Q (b i) (A (b i))| ≤ ∑ i, |Q (b i) (A (b i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ‖A‖ * ‖Q‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.norm_eq_abs]
        calc ‖Q (b i) (A (b i))‖ ≤ ‖Q (b i)‖ * ‖A (b i)‖ := (Q (b i)).le_opNorm _
          _ ≤ (‖Q‖ * ‖b i‖) * (‖A‖ * ‖b i‖) := by
              gcongr
              · exact Q.le_opNorm _
              · exact A.le_opNorm _
          _ = ‖A‖ * ‖Q‖ := by rw [b.orthonormal.1 i]; ring
    _ = Fintype.card ι * ‖A‖ * ‖Q‖ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The evaluation pairing `(p, v) ↦ p v`. -/
abbrev pairBil : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)

/-- `‖apply v‖ ≤ ‖v‖` for the evaluation `T ↦ T v`. -/
theorem norm_apply_le' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (v : E) :
    ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact T.le_opNorm v

/-- `x ↦ A(x) : Q(x)` in `C^{k,r}_b` for `A ∈ C^{k,r}_b(E, E →L E)`, `Q ∈ C^{k,r}_b(E, E →L E →L ℝ)` (`r ≤ 1`),
as `∑ᵢ ⟨Q(·)(bᵢ), A(·) bᵢ⟩`. -/
def hessTraceMap {k : ℕ} {r : ℝ≥0} (hr : r ≤ 1) (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ)) : BoundedContDiffHolderMap k r E ℝ :=
  ∑ i, bilinear hr pairBil (clmMap hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q)
    (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)

theorem coe_hessTraceMap {k : ℕ} {r : ℝ≥0} (hr : r ≤ 1) (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ)) (x : E) :
    hessTraceMap b hr A Q x = hessTrace b (A x) (Q x) := by
  rw [hessTraceMap, show (∑ i, bilinear hr pairBil (clmMap hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q)
      (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)) x =
      (coeAddHom (∑ i, bilinear hr pairBil (clmMap hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q)
      (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A))) x from rfl, map_sum, Finset.sum_apply]
  simp [coeAddHom, hessTrace]

theorem norm_hessTraceMap_le {k : ℕ} {r : ℝ≥0} (hr : r ≤ 1) (A : BoundedContDiffHolderMap k r E (E →L[ℝ] E))
    (Q : BoundedContDiffHolderMap k r E (E →L[ℝ] E →L[ℝ] ℝ)) :
    ‖hessTraceMap b hr A Q‖ ≤ Fintype.card ι * 2 ^ (k + 3) * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖Q‖ := by
  rw [hessTraceMap]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i, ‖bilinear hr pairBil (clmMap hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q)
      (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)‖ ≤
        2 ^ (k + 3) * (2 ^ (k + 3) * (k + 3)) ^ 2 * ‖A‖ * ‖Q‖ := by
    intro i
    have h1 := norm_bilinear_le hr (pairBil (E := E)) (clmMap hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q)
      (clmMap hr (ContinuousLinearMap.apply ℝ E (b i)) A)
    have h2 := norm_clmMap_le hr (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)) Q
    have h3 := norm_clmMap_le hr (ContinuousLinearMap.apply ℝ E (b i)) A
    have h4 : ‖ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b i)‖ ≤ 1 :=
      (norm_apply_le' (b i)).trans (b.orthonormal.1 i).le
    have h5 : ‖ContinuousLinearMap.apply ℝ E (b i)‖ ≤ 1 := (norm_apply_le' (b i)).trans (b.orthonormal.1 i).le
    have h6 : ‖(pairBil (E := E))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hP : (0 : ℝ) ≤ 2 ^ (k + 3) * (k + 3) := by positivity
    calc _ ≤ 2 ^ (k + 3) * 1 * (2 ^ (k + 3) * (k + 3) * 1 * ‖Q‖) * (2 ^ (k + 3) * (k + 3) * 1 * ‖A‖) := by
          refine h1.trans ?_
          gcongr
          · exact h2.trans (by gcongr)
          · exact h3.trans (by gcongr)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ### A functional from its values on the basis -/

/-- `p = ∑ᵢ p(bᵢ) ⟪bᵢ, ·⟫` for a linear functional `p`. -/
theorem eq_sum_apply_smul (p : E →L[ℝ] ℝ) : p = ∑ i, p (b i) • innerSL ℝ (b i) := by
  ext v
  rw [_root_.sum_apply]
  conv_lhs => rw [← b.sum_repr' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  simp [innerSL_apply_apply]

/-! ### The right-hand sides of the principal and differentiated equations -/

section Rhs

variable {k : ℕ} {r : ℝ≥0} (hr : r ≤ 1)

/-- `g̃ = g - Du(β) - c u`, the right-hand side of `a : D²u = g̃` when `L u = g`. -/
def principalRhs (g : BoundedContDiffHolderMap (k + 1) r E ℝ) (β : BoundedContDiffHolderMap (k + 1) r E E)
    (c : BoundedContDiffHolderMap (k + 1) r E ℝ) (u : BoundedContDiffHolderMap (k + 2) r E ℝ) :
    BoundedContDiffHolderMap (k + 1) r E ℝ :=
  g - bilinear hr pairBil u.fderivMap β - bilinear hr (ContinuousLinearMap.mul ℝ ℝ) c (lowerMap hr u)

theorem coe_principalRhs (g : BoundedContDiffHolderMap (k + 1) r E ℝ) (β : BoundedContDiffHolderMap (k + 1) r E E)
    (c : BoundedContDiffHolderMap (k + 1) r E ℝ) (u : BoundedContDiffHolderMap (k + 2) r E ℝ) (x : E) :
    principalRhs hr g β c u x = g x - fderiv ℝ u x (β x) - c x * u x := by
  simp [principalRhs]

theorem norm_principalRhs_le (g : BoundedContDiffHolderMap (k + 1) r E ℝ)
    (β : BoundedContDiffHolderMap (k + 1) r E E) (c : BoundedContDiffHolderMap (k + 1) r E ℝ)
    (u : BoundedContDiffHolderMap (k + 2) r E ℝ) :
    ‖principalRhs hr g β c u‖ ≤ ‖g‖ + (2 ^ (k + 1 + 3) * ‖β‖ + 2 ^ (k + 1 + 3) * ‖c‖ * (k + 1 + 3)) * ‖u‖ := by
  have e1 := norm_bilinear_le hr (pairBil (E := E)) u.fderivMap β
  have e2 := norm_bilinear_le hr (ContinuousLinearMap.mul ℝ ℝ) c (lowerMap hr u)
  have e3 : ‖(pairBil (E := E))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have e4 : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  have e5 := norm_fderivMap_le u
  have e6 := norm_lowerMap_le hr u
  have t1 : ‖bilinear hr pairBil u.fderivMap β‖ ≤ 2 ^ (k + 1 + 3) * ‖β‖ * ‖u‖ := by
    refine e1.trans ?_
    calc 2 ^ (k + 1 + 3) * ‖(pairBil (E := E))‖ * ‖u.fderivMap‖ * ‖β‖ ≤ 2 ^ (k + 1 + 3) * 1 * ‖u‖ * ‖β‖ := by
          gcongr
      _ = _ := by ring
  have t2 : ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) c (lowerMap hr u)‖ ≤
      2 ^ (k + 1 + 3) * ‖c‖ * (k + 1 + 3) * ‖u‖ := by
    refine e2.trans ?_
    calc 2 ^ (k + 1 + 3) * ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖c‖ * ‖lowerMap hr u‖ ≤
          2 ^ (k + 1 + 3) * 1 * ‖c‖ * ((k + 1 + 3) * ‖u‖) := by
          gcongr
          exact_mod_cast e6
      _ = _ := by ring
  calc ‖principalRhs hr g β c u‖ ≤ ‖g - bilinear hr pairBil u.fderivMap β‖ +
        ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) c (lowerMap hr u)‖ := norm_sub_le _ _
    _ ≤ ‖g‖ + ‖bilinear hr pairBil u.fderivMap β‖ + ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) c (lowerMap hr u)‖ := by
        linarith [norm_sub_le g (bilinear hr pairBil u.fderivMap β)]
    _ ≤ _ := by linarith

/-- `∂_ζ g̃ - (∂_ζ a) : D²u + D(∂_ζ u)(β) + c ∂_ζ u`, the right-hand side of the equation `L (∂_ζ u) = ...`. -/
def diffRhs (ζ : E) (a : BoundedContDiffHolderMap (k + 1) r E (E →L[ℝ] E)) (β : BoundedContDiffHolderMap (k + 1) r E E)
    (c : BoundedContDiffHolderMap (k + 1) r E ℝ) (g₁ : BoundedContDiffHolderMap (k + 1) r E ℝ)
    (u : BoundedContDiffHolderMap (k + 2) r E ℝ) : BoundedContDiffHolderMap k r E ℝ :=
  dirMap hr ζ g₁ - hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap +
    bilinear hr pairBil (dirMap hr ζ u).fderivMap (lowerMap hr β) +
    bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr c) (lowerMap hr (dirMap hr ζ u))

theorem coe_diffRhs (ζ : E) (a : BoundedContDiffHolderMap (k + 1) r E (E →L[ℝ] E))
    (β : BoundedContDiffHolderMap (k + 1) r E E) (c : BoundedContDiffHolderMap (k + 1) r E ℝ)
    (g₁ : BoundedContDiffHolderMap (k + 1) r E ℝ) (u : BoundedContDiffHolderMap (k + 2) r E ℝ) (x : E) :
    diffRhs b hr ζ a β c g₁ u x = fderiv ℝ g₁ x ζ - hessTrace b (fderiv ℝ a x ζ) (fderiv ℝ (fderiv ℝ u) x) +
      fderiv ℝ (fun y => fderiv ℝ u y ζ) x (β x) + c x * fderiv ℝ u x ζ := by
  simp [diffRhs, coe_hessTraceMap]

theorem norm_diffRhs_le (ζ : E) (hζ : ‖ζ‖ = 1) (a : BoundedContDiffHolderMap (k + 1) r E (E →L[ℝ] E))
    (β : BoundedContDiffHolderMap (k + 1) r E E) (c : BoundedContDiffHolderMap (k + 1) r E ℝ)
    (g₁ : BoundedContDiffHolderMap (k + 1) r E ℝ) (u : BoundedContDiffHolderMap (k + 2) r E ℝ) :
    ‖diffRhs b hr ζ a β c g₁ u‖ ≤ 2 ^ (k + 3) * (k + 3) * ‖g₁‖ +
      (Fintype.card ι * 2 ^ (k + 3) * (2 ^ (k + 3) * (k + 3)) ^ 2 * (2 ^ (k + 3) * (k + 3) * ‖a‖) +
        2 ^ (k + 3) * (2 ^ (k + 1 + 3) * (k + 1 + 3)) * ((k + 3) * ‖β‖) +
        2 ^ (k + 3) * ((k + 3) * ‖c‖) * ((k + 3) * (2 ^ (k + 1 + 3) * (k + 1 + 3)))) * ‖u‖ := by
  set P₀ : ℝ := 2 ^ (k + 3) * (k + 3) with hP₀
  set P₁ : ℝ := 2 ^ (k + 1 + 3) * (k + 1 + 3) with hP₁
  have hu0 := norm_nonneg u
  have hw : ‖dirMap hr ζ u‖ ≤ P₁ * ‖u‖ := by
    refine (norm_dirMap_le hr ζ u).trans_eq ?_
    rw [hζ, hP₁]; push_cast; ring
  have e1 : ‖dirMap hr ζ g₁‖ ≤ P₀ * ‖g₁‖ := by
    refine (norm_dirMap_le hr ζ g₁).trans_eq ?_
    rw [hζ, hP₀]; ring
  have e2 : ‖hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap‖ ≤
      Fintype.card ι * 2 ^ (k + 3) * P₀ ^ 2 * (P₀ * ‖a‖) * ‖u‖ := by
    refine (norm_hessTraceMap_le b hr _ _).trans ?_
    have h1 : ‖dirMap hr ζ a‖ ≤ P₀ * ‖a‖ := by
      refine (norm_dirMap_le hr ζ a).trans_eq ?_
      rw [hζ, hP₀]; ring
    have h2 : ‖u.fderivMap.fderivMap‖ ≤ ‖u‖ := (norm_fderivMap_le _).trans (norm_fderivMap_le _)
    rw [← hP₀]
    gcongr
  have e3 : ‖bilinear hr pairBil (dirMap hr ζ u).fderivMap (lowerMap hr β)‖ ≤
      2 ^ (k + 3) * P₁ * ((k + 3) * ‖β‖) * ‖u‖ := by
    refine (norm_bilinear_le hr _ _ _).trans ?_
    have h1 : ‖(pairBil (E := E))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 : ‖(dirMap hr ζ u).fderivMap‖ ≤ P₁ * ‖u‖ := (norm_fderivMap_le _).trans hw
    have h3 := norm_lowerMap_le hr β
    calc 2 ^ (k + 3) * ‖(pairBil (E := E))‖ * ‖(dirMap hr ζ u).fderivMap‖ * ‖lowerMap hr β‖ ≤
          2 ^ (k + 3) * 1 * (P₁ * ‖u‖) * ((k + 3) * ‖β‖) := by gcongr
      _ = _ := by ring
  have e4 : ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr c) (lowerMap hr (dirMap hr ζ u))‖ ≤
      2 ^ (k + 3) * ((k + 3) * ‖c‖) * ((k + 3) * P₁) * ‖u‖ := by
    refine (norm_bilinear_le hr _ _ _).trans ?_
    have h1 : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    have h2 := norm_lowerMap_le hr c
    have h3 : ‖lowerMap hr (dirMap hr ζ u)‖ ≤ (k + 3) * (P₁ * ‖u‖) :=
      (norm_lowerMap_le hr (dirMap hr ζ u)).trans (by gcongr)
    calc 2 ^ (k + 3) * ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖lowerMap hr c‖ * ‖lowerMap hr (dirMap hr ζ u)‖ ≤
          2 ^ (k + 3) * 1 * ((k + 3) * ‖c‖) * ((k + 3) * (P₁ * ‖u‖)) := by gcongr
      _ = _ := by ring
  have hsum : ‖diffRhs b hr ζ a β c g₁ u‖ ≤ ‖dirMap hr ζ g₁‖ +
      ‖hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap‖ +
      ‖bilinear hr pairBil (dirMap hr ζ u).fderivMap (lowerMap hr β)‖ +
      ‖bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr c) (lowerMap hr (dirMap hr ζ u))‖ := by
    rw [diffRhs]
    have t1 := norm_add_le (dirMap hr ζ g₁ - hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap +
      bilinear hr pairBil (dirMap hr ζ u).fderivMap (lowerMap hr β))
      (bilinear hr (ContinuousLinearMap.mul ℝ ℝ) (lowerMap hr c) (lowerMap hr (dirMap hr ζ u)))
    have t2 := norm_add_le (dirMap hr ζ g₁ - hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap)
      (bilinear hr pairBil (dirMap hr ζ u).fderivMap (lowerMap hr β))
    have t3 := norm_sub_le (dirMap hr ζ g₁) (hessTraceMap b hr (dirMap hr ζ a) u.fderivMap.fderivMap)
    linarith
  linarith

end Rhs

/-! ### `C^{k+1,r}_b` norms through first derivatives -/

section FirstDerivatives

variable {k : ℕ} {r : ℝ≥0}

theorem coe_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*} (s : Finset κ)
    (f : κ → BoundedContDiffHolderMap k r E F) : ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) :=
  map_sum coeAddHom f s

/-- `‖u‖_{k+1,r} ≤ S + ‖Du‖_{k,r}` when `‖u‖ ≤ S`. -/
theorem norm_le_add_norm_fderivMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : BoundedContDiffHolderMap (k + 1) r E F) {S : ℝ} (hS : ∀ x, ‖u x‖ ≤ S) : ‖u‖ ≤ S + ‖u.fderivMap‖ := by
  have hd : Differentiable ℝ (⇑u) := u.contDiff.differentiable (by simp)
  have h := norm_ofFDeriv_le (⇑u) hd u.fderivMap rfl hS
  have he : ofFDeriv (⇑u) hd u.fderivMap rfl hS = u := ext fun _ => rfl
  rwa [he] at h

/-- `‖Du‖_{k,r} ≤ ∑ᵢ P ‖∂_{bᵢ} u‖_{k,r}`, `P = 2^(k+3) (k+3)`, for real-valued `u ∈ C^{k+1,r}_b` (`r ≤ 1`). -/
theorem norm_fderivMap_le_sum (hr : r ≤ 1) (u : BoundedContDiffHolderMap (k + 1) r E ℝ) :
    ‖u.fderivMap‖ ≤ ∑ i, 2 ^ (k + 3) * (k + 3) * ‖dirMap hr (b i) u‖ := by
  have hDu : u.fderivMap = ∑ i, clmMap hr (ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (b i)))
      (dirMap hr (b i) u) := by
    ext x : 1
    rw [coe_sum, Finset.sum_apply, coe_fderivMap]
    refine (eq_sum_apply_smul b (fderiv ℝ u x)).trans (Finset.sum_congr rfl fun i _ => ?_)
    simp
  rw [hDu]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hn : ‖ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (b i))‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_toSpanSingleton, innerSL_apply_norm, b.orthonormal.1 i]
  calc ‖clmMap hr (ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (b i))) (dirMap hr (b i) u)‖ ≤
        2 ^ (k + 3) * (k + 3) * ‖ContinuousLinearMap.toSpanSingleton ℝ (innerSL ℝ (b i))‖ *
          ‖dirMap hr (b i) u‖ := norm_clmMap_le hr _ _
    _ ≤ 2 ^ (k + 3) * (k + 3) * 1 * ‖dirMap hr (b i) u‖ := by gcongr
    _ = _ := by ring

end FirstDerivatives

/-! ### The estimate -/

variable {r : ℝ≥0}

/-- **The Schauder estimate of every order on the whole space**: for coefficients `a, β, c ∈ C^{k,r}_b` with `a`
symmetric and `λ`-elliptic at every point, there is `C` such that every `u ∈ C^{k+2,r}_b(E)` with `|u| ≤ S` and
`L u = g ∈ C^{k,r}_b(E)` satisfies `‖u‖_{C^{k+2,r}_b} ≤ C (‖g‖_{C^{k,r}_b} + S)`. -/
theorem exists_norm_le {lam : ℝ} (hlam : 0 < lam) (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ∀ (a : BoundedContDiffHolderMap k r E (E →L[ℝ] E)) (β : BoundedContDiffHolderMap k r E E)
      (c : BoundedContDiffHolderMap k r E ℝ),
      (∀ x u v, ⟪a x u, v⟫ = ⟪u, a x v⟫) → (∀ x v, lam * ‖v‖ ^ 2 ≤ ⟪a x v, v⟫) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : BoundedContDiffHolderMap (k + 2) r E ℝ) (g : BoundedContDiffHolderMap k r E ℝ)
        (S : ℝ), 0 ≤ S → (∀ x, |u x| ≤ S) → (∀ x, g x = ellipticOp b a β c u x) → ‖u‖ ≤ C * (‖g‖ + S) := by
  have hr1' : r ≤ 1 := hr1.le
  induction k with
  | zero =>
    intro a β c hsymm hell
    set Λ : ℝ := 2 * (‖a‖ + ‖β‖ + ‖c‖) with hΛ
    have ha : IsEllipticCoeff (⇑a) lam Λ r :=
      { symm := hsymm
        elliptic := hell
        bound := fun x => (a.norm_apply_le x).trans (by rw [hΛ]; linarith [norm_nonneg β, norm_nonneg c, norm_nonneg a])
        holder := fun x y => (norm_sub_le_of_zero hr1' a x y).trans (by
          gcongr
          rw [hΛ]; linarith [norm_nonneg β, norm_nonneg c]) }
    have hβc : IsLowerCoeff (⇑β) (⇑c) Λ r :=
      { bound_β := fun x => (β.norm_apply_le x).trans (by rw [hΛ]; linarith [norm_nonneg β, norm_nonneg c, norm_nonneg a])
        holder_β := fun x y => (norm_sub_le_of_zero hr1' β x y).trans (by
          gcongr
          rw [hΛ]; linarith [norm_nonneg a, norm_nonneg c])
        bound_c := fun x => by
          rw [← Real.norm_eq_abs]
          exact (c.norm_apply_le x).trans (by rw [hΛ]; linarith [norm_nonneg β, norm_nonneg c, norm_nonneg a])
        holder_c := fun x y => by
          rw [← Real.norm_eq_abs]
          refine (norm_sub_le_of_zero hr1' c x y).trans ?_
          gcongr
          rw [hΛ]; linarith [norm_nonneg a, norm_nonneg β] }
    obtain ⟨C₀, hC₀, hSch⟩ := exists_schauder_estimate (Λ := Λ) b hlam hr0 hr1
    refine ⟨1 + 6 * C₀, by positivity, fun u g S hS hu heq => ?_⟩
    have hg : ∀ x y, |ellipticOp b a β c u x - ellipticOp b a β c u y| ≤
        (2 * ‖g‖) * ‖x - y‖ ^ (r : ℝ) := by
      intro x y
      rw [← heq, ← heq, ← Real.norm_eq_abs]
      exact norm_sub_le_of_zero hr1' g x y
    obtain ⟨s1, s2, s3⟩ := hSch a β c ha hβc u (contDiff_two u) ⟨‖u‖, norm_fderiv_fderiv_sub_le u⟩
      ⟨‖u‖, norm_fderiv_fderiv_le u⟩ S (2 * ‖g‖) (by positivity) hu hg
    have hn := norm_le_of_bounds u (by positivity) hu s3 s2 s1
    have hg0 := norm_nonneg g
    nlinarith
  | succ k ih =>
    intro a β c hsymm hell
    -- the case `k` for the lowered coefficients
    obtain ⟨C₁, hC₁, hk⟩ := ih (lowerMap hr1' a) (lowerMap hr1' β) (lowerMap hr1' c) hsymm hell
    have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    -- the norm factors of `clmMap` / `dirMap` at the levels `k`, `k + 1`, `k + 2`
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℝ, P₀ = 2 ^ (k + 3) * (k + 3) := ⟨_, rfl⟩
    obtain ⟨P₁, hP₁⟩ : ∃ P₁ : ℝ, P₁ = 2 ^ (k + 1 + 3) * (k + 1 + 3) := ⟨_, rfl⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P₂ : ℝ, P₂ = 2 ^ (k + 2 + 3) * (k + 2 + 3) := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Fintype.card ι : ℝ) := ⟨_, rfl⟩
    have hP₀0 : 0 ≤ P₀ := by rw [hP₀]; positivity
    have hP₁0 : 0 ≤ P₁ := by rw [hP₁]; positivity
    have hP₂0 : 0 ≤ P₂ := by rw [hP₂]; positivity
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    -- constants
    obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = 2 ^ (k + 1 + 3) * ‖β‖ + 2 ^ (k + 1 + 3) * ‖c‖ * (k + 1 + 3) := ⟨_, rfl⟩
    obtain ⟨A₃, hA₃⟩ : ∃ A₃ : ℝ, A₃ = d * 2 ^ (k + 3) * P₀ ^ 2 * (P₀ * ‖a‖) + 2 ^ (k + 3) * P₁ * ((k + 3) * ‖β‖) +
      2 ^ (k + 3) * ((k + 3) * ‖c‖) * ((k + 3) * P₁) := ⟨_, rfl⟩
    have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
    have hA₃0 : 0 ≤ A₃ := by
      rw [hA₃]
      have := mul_nonneg (mul_nonneg (mul_nonneg hd0 (by positivity : (0:ℝ) ≤ 2 ^ (k + 3))) (pow_nonneg hP₀0 2))
        (mul_nonneg hP₀0 (norm_nonneg a))
      have h2 : 0 ≤ (2 : ℝ) ^ (k + 3) * P₁ * ((k + 3) * ‖β‖) := by positivity
      have h3 : 0 ≤ (2 : ℝ) ^ (k + 3) * ((k + 3) * ‖c‖) * ((k + 3) * P₁) := by positivity
      linarith
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = d * P₂ * C₁ := ⟨_, rfl⟩
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 1 + B * P₀ + B * (P₀ * K₁ + A₃ + 1) * C₁ * (k + 4) + B * (P₀ * K₁ + A₃ + 1) * C₁ := ⟨_, rfl⟩
    have hD0 : 0 ≤ P₀ * K₁ + A₃ + 1 := by positivity
    have hC0 : 0 ≤ C := by rw [hC]; positivity
    refine ⟨C, hC0, fun u g S hS hu heq => ?_⟩
    have hg0 := norm_nonneg g
    -- `u` as an element of `C^{k+2,r}_b` and the case `k`
    obtain ⟨u₂, hu₂⟩ : ∃ u₂ : BoundedContDiffHolderMap (k + 2) r E ℝ, u₂ = lowerMap hr1' u := ⟨_, rfl⟩
    have hu₂c : ⇑u₂ = ⇑u := by rw [hu₂]; rfl
    have hu₂0 := norm_nonneg u₂
    have hu₂n' : ‖u₂‖ ≤ C₁ * ((k + 4) * ‖g‖ + S) := by
      refine (hk u₂ (lowerMap hr1' g) S hS (by rw [hu₂c]; exact hu) (fun x => by
        rw [hu₂c]; exact heq x)).trans (mul_le_mul_of_nonneg_left ?_ hC₁)
      have := norm_lowerMap_le hr1' g
      linarith
    -- the principal part of the equation: `a : D²u = g̃`
    have hg₁n := norm_principalRhs_le hr1' g β c u₂
    have hprin : ∀ x ∈ (univ : Set E), hessTrace b (a x) (fderiv ℝ (fderiv ℝ u) x) =
        principalRhs hr1' g β c u₂ x := by
      intro x _
      rw [coe_principalRhs, heq x, hu₂c]
      simp only [ellipticOp]
      ring
    -- the equations of the directional derivatives
    have hGeq : ∀ i x, diffRhs b hr1' (b i) a β c (principalRhs hr1' g β c u₂) u₂ x =
        ellipticOp b (lowerMap hr1' a) (lowerMap hr1' β) (lowerMap hr1' c) (dirMap hr1' (b i) u) x := by
      intro i x
      have had : DifferentiableAt ℝ (⇑a) x := (a.contDiff.differentiable (by simp)).differentiableAt
      have hu3 : ContDiffAt ℝ 3 (⇑u) x :=
        (u.contDiff.of_le (by exact_mod_cast (by omega : 3 ≤ k + 1 + 2))).contDiffAt
      have key := hessTrace_fderiv_apply_eq b isOpen_univ (mem_univ x) had hu3 hprin (b i)
      rw [coe_diffRhs, hu₂c]
      simp only [ellipticOp, coe_lowerMap, coe_dirMap]
      rw [key]
    have hGn : ∀ i, ‖diffRhs b hr1' (b i) a β c (principalRhs hr1' g β c u₂) u₂‖ ≤
        P₀ * ‖g‖ + (P₀ * K₁ + A₃) * ‖u₂‖ := by
      intro i
      have h1 := norm_diffRhs_le b hr1' (b i) (hb1 i) a β c (principalRhs hr1' g β c u₂) u₂
      have h2 := mul_le_mul_of_nonneg_left hg₁n hP₀0
      have h3 : P₀ * (‖g‖ + (2 ^ (k + 1 + 3) * ‖β‖ + 2 ^ (k + 1 + 3) * ‖c‖ * (↑k + 1 + 3)) * ‖u₂‖) =
          P₀ * ‖g‖ + P₀ * K₁ * ‖u₂‖ := by rw [hK₁]; ring
      have h4 : (↑(Fintype.card ι) * 2 ^ (k + 3) * (2 ^ (k + 3) * (↑k + 3)) ^ 2 * (2 ^ (k + 3) * (↑k + 3) * ‖a‖) +
          2 ^ (k + 3) * (2 ^ (k + 1 + 3) * (↑k + 1 + 3)) * ((↑k + 3) * ‖β‖) +
          2 ^ (k + 3) * ((↑k + 3) * ‖c‖) * ((↑k + 3) * (2 ^ (k + 1 + 3) * (↑k + 1 + 3)))) = A₃ := by
        rw [hA₃, hd, hP₀, hP₁]
      rw [h4] at h1
      rw [h3] at h2
      have h5 : 2 ^ (k + 3) * ((k : ℝ) + 3) = P₀ := by rw [hP₀]
      rw [h5] at h1
      nlinarith
    -- the case `k` for each directional derivative
    have hwn : ∀ i, ‖dirMap hr1' (b i) u‖ ≤
        C₁ * (‖diffRhs b hr1' (b i) a β c (principalRhs hr1' g β c u₂) u₂‖ + ‖u₂‖) := by
      intro i
      refine hk (dirMap hr1' (b i) u) _ ‖u₂‖ hu₂0 (fun x => ?_) (fun x => hGeq i x)
      have hwf : (dirMap hr1' (b i) u) x = fderiv ℝ u₂ x (b i) := by simp [hu₂c]
      rw [hwf, ← Real.norm_eq_abs]
      calc ‖fderiv ℝ u₂ x (b i)‖ ≤ ‖fderiv ℝ u₂ x‖ * ‖b i‖ := (fderiv ℝ u₂ x).le_opNorm _
        _ ≤ ‖u₂‖ * 1 := by
            rw [hb1]
            gcongr
            exact (u₂.fderivMap.norm_apply_le x).trans (norm_fderivMap_le u₂)
        _ = ‖u₂‖ := mul_one _
    -- `Du = ∑ᵢ (∂ᵢ u) ⟪bᵢ, ·⟫` and `‖u‖ ≤ S + ‖Du‖`
    have hDun : ‖u.fderivMap‖ ≤ ∑ i, P₂ * ‖dirMap hr1' (b i) u‖ := by
      refine (norm_fderivMap_le_sum b hr1' u).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
      rw [hP₂]; push_cast; ring
    have hun : ‖u‖ ≤ S + ‖u.fderivMap‖ :=
      norm_le_add_norm_fderivMap u (fun x => by rw [Real.norm_eq_abs]; exact hu x)
    -- assembling
    have hterm : ∀ i, P₂ * ‖dirMap hr1' (b i) u‖ ≤ P₂ * C₁ * (P₀ * ‖g‖ + (P₀ * K₁ + A₃ + 1) * ‖u₂‖) := by
      intro i
      calc P₂ * ‖dirMap hr1' (b i) u‖ ≤
            P₂ * (C₁ * (‖diffRhs b hr1' (b i) a β c (principalRhs hr1' g β c u₂) u₂‖ + ‖u₂‖)) :=
            mul_le_mul_of_nonneg_left (hwn i) hP₂0
        _ ≤ P₂ * (C₁ * (P₀ * ‖g‖ + (P₀ * K₁ + A₃) * ‖u₂‖ + ‖u₂‖)) := by gcongr; exact hGn i
        _ = P₂ * C₁ * (P₀ * ‖g‖ + (P₀ * K₁ + A₃ + 1) * ‖u₂‖) := by ring
    have hsumw : ∑ i, P₂ * ‖dirMap hr1' (b i) u‖ ≤ d * P₂ * C₁ * (P₀ * ‖g‖ + (P₀ * K₁ + A₃ + 1) * ‖u₂‖) := by
      refine (Finset.sum_le_sum fun i _ => hterm i).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]
      ring
    have hfin : ‖u‖ ≤ S + B * (P₀ * ‖g‖ + (P₀ * K₁ + A₃ + 1) * ‖u₂‖) := by
      rw [hB]; linarith
    have hstep : B * ((P₀ * K₁ + A₃ + 1) * ‖u₂‖) ≤ B * ((P₀ * K₁ + A₃ + 1) * (C₁ * ((k + 4) * ‖g‖ + S))) := by
      gcongr
    have h1 : 0 ≤ B * P₀ := by positivity
    have h2 : 0 ≤ B * (P₀ * K₁ + A₃ + 1) * C₁ * (k + 4) := by positivity
    have h3 : 0 ≤ B * (P₀ * K₁ + A₃ + 1) * C₁ := by positivity
    calc ‖u‖ ≤ S + B * (P₀ * ‖g‖ + (P₀ * K₁ + A₃ + 1) * ‖u₂‖) := hfin
      _ ≤ S + B * P₀ * ‖g‖ + B * ((P₀ * K₁ + A₃ + 1) * (C₁ * ((k + 4) * ‖g‖ + S))) := by linarith [hstep]
      _ = (1 + B * (P₀ * K₁ + A₃ + 1) * C₁) * S +
            (B * P₀ + B * (P₀ * K₁ + A₃ + 1) * C₁ * (k + 4)) * ‖g‖ := by ring
      _ ≤ C * (‖g‖ + S) := by
          rw [hC]
          linarith [mul_nonneg h1 hS, mul_nonneg h2 hS, mul_nonneg h3 hg0]

end SchauderHigherOrder

end SGPT.Foundations.Analysis.Pending
