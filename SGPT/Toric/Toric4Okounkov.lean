import SGPT.Toric.Toric3OkounkovBody
import SGPT.Toric.Toric4Surfaces

/-!
# Okounkov bodies of the toric examples

Source `chapter_toric_big.tex`, `ex:OkounP2` and `ex:toric-big:L532`, computed from
`prop:toricusualOko` (`toricOkounkovBody_eq`: `Δ_{Y•}(L) = Φ_ℝ(P_D)`).

The toric flag `Y_i = D_{ρ_1} ∩ ⋯ ∩ D_{ρ_i}` of a maximal cone `σ_v` is `toricFlag hs v e`,
where the ordering `e` of the chart basis puts `ρ_{l+1} = u_{e(l)}(v)`.  Since the chart basis
is chosen, we quantify over all orderings `e` realising the rays prescribed by the source
(`ρ_1 = σ_5, ρ_2 = σ_6` for `ℙ²`, `ρ_1 = σ_5, ρ_2 = σ_7` for `Bl₀ℙ²`) and prove that such an `e`
exists (`exists_flagOrder_of_vertexCone`).

* `simplex_okounkovBody`: for `X_{Δ_N}`, the cone `σ_0` and `ρ_l = e_l`, `Φ = id` and
  `Δ_{Y•}(L) = P_D = Δ_N` (`ex:OkounP2` is `N = 2`);
* `blowup_okounkovBody`: for `Bl₀ℙ²`, `σ_1'` and `ρ_1 = σ_5`, `ρ_2 = σ_7`,
  `Φ(m) = (m_1, m_1 + m_2)` and `Δ_{Y•}(π^*O(1)) = {0 ≤ y_1 ≤ y_2 ≤ 1}`, which differs from the
  body of `ex:OkounP2`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

section General
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K] {γ : K → Fin n → ℤ}
  (hs : latticePolytopeEdgeSmooth γ)

/-- For a vertex-cone basis `c` at `v` there is an ordering `e` of the chart basis with
`u_{e(l)}(v) = u_l(c)`: the flag `Y•` with rays `ρ_{l+1}` = the dual vectors of `c` exists. -/
theorem exists_flagOrder_of_vertexCone (v : latticePolytopeVertices γ)
    {c : Module.Basis (Fin n) ℤ (Fin n → ℤ)} (h : IsVertexConeBasis γ v.val c) :
    ∃ e : Fin n ≃ Fin n, ∀ l, polytopeToricRayGenerator γ hs v (e l) = vertexConeRay c l := by
  obtain ⟨τ, hτ⟩ := exists_perm_originalPolytopeNativeBasis_eq hs v h
  exact ⟨τ.symm, fun l => by
    rw [polytopeToricRayGenerator_eq_vertexConeRay hs v hτ, Equiv.apply_symm_apply]⟩

variable {hs}

theorem toricFlagRealMap_eq_of_rays (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) {u : Fin n → Fin n → ℤ}
    (hu : ∀ l, polytopeToricRayGenerator γ hs v (e l) = u l) (x : EuclideanSpace ℝ (Fin n)) :
    toricFlagRealMap hs v e D x =
      fun l => latticeFunctional (u l) x - (intPairing (toricCartierDatum D v) (u l) : ℝ) := by
  funext l
  simp only [toricFlagRealMap, hu l]

theorem toricFlagLatticeMap_eq_of_rays (v : latticePolytopeVertices γ) (e : Fin n ≃ Fin n)
    (D : ToricDivisor γ hs) {u : Fin n → Fin n → ℤ}
    (hu : ∀ l, polytopeToricRayGenerator γ hs v (e l) = u l) (m : Fin n → ℤ) :
    toricFlagLatticeMap hs v e D m = fun l => intPairing (m - toricCartierDatum D v) (u l) := by
  funext l
  simp only [toricFlagLatticeMap, hu l]

end General

/-! ### `ℙ^N` and `ex:OkounP2` -/

section Simplex
variable {N : ℕ} (hs : latticePolytopeEdgeSmooth (simplexGenerator N))

/-- The flag of `σ_0` with `ρ_l = e_l` exists. -/
theorem simplex_exists_flagOrder :
    ∃ e : Fin N ≃ Fin N, ∀ l, polytopeToricRayGenerator (simplexGenerator N) hs
      (simplexVertex none) (e l) = Pi.single l 1 := by
  obtain ⟨e, he⟩ := exists_flagOrder_of_vertexCone hs (simplexVertex none)
    (simplex_isVertexConeBasis none)
  exact ⟨e, fun l => by rw [he, simplex_vertexConeRay_none]⟩

/-- Source `ex:OkounP2` (for `N = 2`), from `prop:toricusualOko`: for the reference cone
`σ_0 = σ_1` and the rays `ρ_l = e_l` (`ρ_1 = σ_5`, `ρ_2 = σ_6`), `Φ(m) = m` and
`Δ_{Y•}(O(1)) = P_D`, the simplex `{y ≥ 0, ∑ y ≤ 1}`. -/
theorem simplex_okounkovBody [NeZero N] (e : Fin N ≃ Fin N)
    (he : ∀ l, polytopeToricRayGenerator (simplexGenerator N) hs (simplexVertex none) (e l) =
      Pi.single l 1) :
    (∀ m, toricFlagLatticeMap hs (simplexVertex none) e (simplexHyperplaneDivisor hs) m = m) ∧
    toricOkounkovBody (simplexVertex none) e (simplexHyperplaneDivisor hs) =
      EuclideanSpace.equiv (Fin N) ℝ '' toricDivisorPolytope (simplexHyperplaneDivisor hs) ∧
    toricOkounkovBody (simplexVertex none) e (simplexHyperplaneDivisor hs) =
      {y | (∀ k, 0 ≤ y k) ∧ ∑ k, y k ≤ 1} := by
  have hm0 := toricCartierDatum_simplexHyperplaneDivisor hs none
  simp only [simplexGenerator_none] at hm0
  have hΦ : ∀ x, toricFlagRealMap hs (simplexVertex none) e (simplexHyperplaneDivisor hs) x =
      EuclideanSpace.equiv (Fin N) ℝ x := by
    intro x
    rw [toricFlagRealMap_eq_of_rays _ e _ he, hm0]
    funext l
    simp [latticeFunctional_apply, intPairing, Pi.single_apply]
  have hbody : toricOkounkovBody (simplexVertex none) e (simplexHyperplaneDivisor hs) =
      EuclideanSpace.equiv (Fin N) ℝ '' toricDivisorPolytope (simplexHyperplaneDivisor hs) := by
    rw [toricOkounkovBody_eq]
    exact image_congr fun x _ => hΦ x
  refine ⟨fun m => ?_, hbody, ?_⟩
  · rw [toricFlagLatticeMap_eq_of_rays _ e _ he, hm0]
    funext l
    simp [intPairing, Pi.single_apply]
  · rw [hbody, toricDivisorPolytope_simplexHyperplaneDivisor]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨(EuclideanSpace.equiv (Fin N) ℝ).symm y, hy, rfl⟩

end Simplex

/-! ### `Bl₀ℙ²` and `ex:toric-big:L532` -/

section Blowup
variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The flag of `σ_1'` (the vertex `(0,1)` of `P'`) with `ρ_1 = σ_5`, `ρ_2 = σ_7` exists. -/
theorem blowup_exists_flagOrder :
    ∃ e : Fin 2 ≃ Fin 2,
      polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 0) = blowupRay5 ∧
      polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 1) = blowupRay7 := by
  obtain ⟨e, he⟩ := exists_flagOrder_of_vertexCone hs (blowupVertex 3)
    (blowup_isVertexConeBasis 3)
  obtain ⟨-, -, -, ⟨h30, h31⟩⟩ := blowup_vertexConeRays
  exact ⟨e, by rw [he, h30], by rw [he, h31]⟩

/-- Source `ex:toric-big:L532`, from `prop:toricusualOko`: for the reference cone `σ_1'` and
`ρ_1 = σ_5`, `ρ_2 = σ_7`, `Φ(m_1, m_2) = (m_1, m_1 + m_2)` and
`Δ_{Y•}(Bl₀ℙ², π^*O(1)) = {y : 0 ≤ y_1 ≤ y_2 ≤ 1}` (the triangle with vertices
`(0,0), (1,1), (0,1)`, figure `fig:P2b1pOkoun`). -/
theorem blowup_okounkovBody (e : Fin 2 ≃ Fin 2)
    (he0 : polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 0) = blowupRay5)
    (he1 : polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 1) = blowupRay7) :
    (∀ m, toricFlagLatticeMap hs (blowupVertex 3) e (blowupHyperplaneDivisor hs) m =
      ![m 0, m 0 + m 1]) ∧
    toricOkounkovBody (blowupVertex 3) e (blowupHyperplaneDivisor hs) =
      {y | 0 ≤ y 0 ∧ y 0 ≤ y 1 ∧ y 1 ≤ 1} := by
  have he : ∀ l, polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e l) =
      ![blowupRay5, blowupRay7] l := by
    intro l; fin_cases l
    · exact he0
    · exact he1
  have hm0 := (toricCartierDatum_blowupHyperplaneDivisor hs).2.1
  refine ⟨fun m => ?_, ?_⟩
  · rw [toricFlagLatticeMap_eq_of_rays _ e _ he, hm0]
    funext l; fin_cases l <;> simp [intPairing, blowupRay5, blowupRay7, Fin.sum_univ_two]
  · rw [toricOkounkovBody_eq, toricDivisorPolytope_blowupHyperplaneDivisor]
    have hΦ : ∀ x, toricFlagRealMap hs (blowupVertex 3) e (blowupHyperplaneDivisor hs) x =
        ![x 0, x 0 + x 1] := by
      intro x
      rw [toricFlagRealMap_eq_of_rays _ e _ he, hm0]
      funext l; fin_cases l <;> simp [latticeFunctional_two, intPairing, blowupRay5, blowupRay7]
    ext y
    simp only [mem_image, mem_ofPred_eq, hΦ]
    constructor
    · rintro ⟨x, ⟨h0, h1, h2⟩, rfl⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine ⟨h0, ?_, ?_⟩ <;> linarith
    · rintro ⟨h0, h1, h2⟩
      refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm ![y 0, y 1 - y 0], ?_, ?_⟩
      · simp
        refine ⟨h0, ?_, ?_⟩ <;> linarith
      · funext l; fin_cases l <;> simp

/-- Source `ex:toric-big:L532` ("it differs from the polytope in `ex:OkounP2`"). -/
theorem blowup_okounkovBody_ne_simplex :
    {y : Fin 2 → ℝ | 0 ≤ y 0 ∧ y 0 ≤ y 1 ∧ y 1 ≤ 1} ≠ {y | (∀ k, 0 ≤ y k) ∧ ∑ k, y k ≤ 1} := by
  intro h
  have hmem : (![1, 0] : Fin 2 → ℝ) ∈ {y : Fin 2 → ℝ | (∀ k, 0 ≤ y k) ∧ ∑ k, y k ≤ 1} := by
    refine ⟨fun k => by fin_cases k <;> simp, by simp [Fin.sum_univ_two]⟩
  rw [← h] at hmem
  obtain ⟨-, h1, -⟩ := hmem
  norm_num at h1

/-- Source `ex:toric-big:L532`: the flag is `Y_1 = D_{σ_5}` and `Y_2 = Y_1 ∩ D_{σ_7}`
(`D_{σ_7}` is the exceptional divisor `E`). -/
theorem blowup_toricFlag (e : Fin 2 ≃ Fin 2)
    (he0 : polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 0) = blowupRay5)
    (he1 : polytopeToricRayGenerator blowupGenerator hs (blowupVertex 3) (e 1) = blowupRay7) :
    toricFlag hs (blowupVertex 3) e 1 =
        toricPrimeDivisor ⟨blowupRay5, he0 ▸ ⟨_, _, rfl⟩⟩ ∧
    toricFlag hs (blowupVertex 3) e 2 =
        toricPrimeDivisor ⟨blowupRay5, he0 ▸ ⟨_, _, rfl⟩⟩ ∩
          toricPrimeDivisor ⟨blowupRay7, he1 ▸ ⟨_, _, rfl⟩⟩ := by
  have h0 : polytopeToricRay blowupGenerator hs (blowupVertex 3) (e 0) =
      ⟨blowupRay5, he0 ▸ ⟨_, _, rfl⟩⟩ := Subtype.ext he0
  have h1 : polytopeToricRay blowupGenerator hs (blowupVertex 3) (e 1) =
      ⟨blowupRay7, he1 ▸ ⟨_, _, rfl⟩⟩ := Subtype.ext he1
  constructor
  · ext p
    simp only [toricFlag, toricOrbitClosure, toricFlagRays, mem_iInter, mem_image, mem_ofPred_eq]
    constructor
    · intro hp
      rw [← h0]
      exact hp _ ⟨0, by simp, rfl⟩
    · rintro hp ρ ⟨l, hl, rfl⟩
      have hl0 : l = 0 := by ext; simp at hl ⊢; omega
      subst hl0
      rw [h0]; exact hp
  · ext p
    simp only [toricFlag, toricOrbitClosure, toricFlagRays, mem_iInter, mem_image, mem_ofPred_eq,
      mem_inter_iff]
    constructor
    · intro hp
      rw [← h0, ← h1]
      exact ⟨hp _ ⟨0, by simp, rfl⟩, hp _ ⟨1, by simp, rfl⟩⟩
    · rintro ⟨hp0, hp1⟩ ρ ⟨l, -, rfl⟩
      fin_cases l
      · rw [show ((⟨0, by omega⟩ : Fin 2)) = 0 from rfl, h0]; exact hp0
      · rw [show ((⟨1, by omega⟩ : Fin 2)) = 1 from rfl, h1]; exact hp1

end Blowup

end SGPT.Toric
