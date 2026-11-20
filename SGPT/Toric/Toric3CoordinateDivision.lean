import SGPT.Foundations.Analysis.Pending.DivisorialMultiplierOrder

/-!
# Division by coordinates of holomorphic functions on `ℂ^n`

A function holomorphic near a point `p` of `ℂ^n` which vanishes near `p` on the coordinate
hyperplane `{z_j = 0}` (through `p`) is `z_j` times a function holomorphic near `p`
(`exists_eq_coord_mul_of_eq_zero`, from the case of the last coordinate,
`DivisorialMultiplierOrder.exists_eq_last_mul_of_eq_zero`, by a coordinate permutation).
Iterating, a function holomorphic near `0` vanishing near `0` on the coordinate subspace
`{z_{c(s)} = 0, s ∈ S}` is a holomorphic combination `∑_{s ∈ S} z_{c(s)} A_s`
(`exists_eq_sum_coord_mul`).

These are the local algebraic facts behind the computation of flag valuations in adapted
coordinates (proof of `prop:toricusualOko`, chapter `chapter_toric_big.tex`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators

/-- The coordinate permutation `z ↦ (z_{σ i})_i` of `ℂ^n`, as a continuous linear map. -/
def coordPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : ComplexModel n →L[ℂ] ComplexModel n :=
  (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (EuclideanSpace.proj (σ i) : ComplexModel n →L[ℂ] ℂ))

@[simp] theorem coordPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : ComplexModel n) (i : Fin n) :
    coordPerm σ z i = z (σ i) := rfl

/-- The linear map `z ↦ z - z_j e_j` setting the `j`-th coordinate to `0`. -/
def coordZero {n : ℕ} (j : Fin n) : ComplexModel n →L[ℂ] ComplexModel n :=
  ContinuousLinearMap.id ℂ (ComplexModel n) -
    (EuclideanSpace.proj j : ComplexModel n →L[ℂ] ℂ).smulRight (EuclideanSpace.single j (1 : ℂ))

theorem coordZero_apply {n : ℕ} (j : Fin n) (z : ComplexModel n) (i : Fin n) :
    coordZero j z i = if i = j then 0 else z i := by
  simp only [coordZero, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.sub_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp

theorem coordZero_of_eq_zero {n : ℕ} (j : Fin n) {z : ComplexModel n} (hz : z j = 0) :
    coordZero j z = z := by
  ext i
  rw [coordZero_apply]
  split_ifs with h
  · subst h; exact hz.symm
  · rfl

/-- Division by a coordinate: a function holomorphic near `p` vanishing near `p` on
`{z_j = 0}` (with `p_j = 0`) is `z_j H` with `H` holomorphic near `p`. -/
theorem exists_eq_coord_mul_of_eq_zero {n : ℕ} (j : Fin n) {p : ComplexModel n} (hp : p j = 0)
    {G : ComplexModel n → ℂ} (hG : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ G z)
    (h0 : ∀ᶠ z in 𝓝 p, z j = 0 → G z = 0) :
    ∃ H : ComplexModel n → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ H z) ∧
      G =ᶠ[𝓝 p] fun z => z j * H z := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m)
    have hσσ : ∀ z, coordPerm σ (coordPerm σ z) = z := by
      intro z; ext i; simp [σ, Equiv.swap_apply_self]
    set p' := coordPerm σ p
    have hp' : p' (Fin.last m) = 0 := by simp [p', σ, hp]
    have hT : Tendsto (coordPerm σ) (𝓝 p') (𝓝 p) := by
      have := (coordPerm σ).continuous.tendsto p'
      rwa [show coordPerm σ p' = p from hσσ p] at this
    have hT' : Tendsto (coordPerm σ) (𝓝 p) (𝓝 p') := (coordPerm σ).continuous.tendsto p
    have hG' : ∀ᶠ w in 𝓝 p', DifferentiableAt ℂ (fun w => G (coordPerm σ w)) w := by
      filter_upwards [hT.eventually hG] with w hw
      exact hw.comp w (coordPerm σ).differentiableAt
    have h0' : ∀ᶠ w in 𝓝 p', w (Fin.last m) = 0 → G (coordPerm σ w) = 0 := by
      filter_upwards [hT.eventually h0] with w hw hwl
      apply hw
      simpa [σ] using hwl
    obtain ⟨H', hH', heq⟩ :=
      Pending.DivisorialMultiplierOrder.exists_eq_last_mul_of_eq_zero hp' hG' h0'
    refine ⟨fun z => H' (coordPerm σ z), ?_, ?_⟩
    · filter_upwards [hT'.eventually hH'] with z hz
      exact hz.comp z (coordPerm σ).differentiableAt
    · filter_upwards [hT'.eventually heq] with z hz
      have h1 : G z = G (coordPerm σ (coordPerm σ z)) := by rw [hσσ]
      rw [h1, hz]
      simp [σ]

/-- Iterated division by coordinates: a function holomorphic near `0` vanishing near `0` on
`{z_{c(s)} = 0 : s ∈ S}` is, near `0`, `∑_{s ∈ S} z_{c(s)} A_s` with `A_s` holomorphic. -/
theorem exists_eq_sum_coord_mul {n : ℕ} {ι : Type*} (S : Finset ι) (c : ι → Fin n)
    {G : ComplexModel n → ℂ} (hG : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ G z)
    (h0 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ s ∈ S, z (c s) = 0) → G z = 0) :
    ∃ A : ι → ComplexModel n → ℂ, (∀ s, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (A s) z) ∧
      G =ᶠ[𝓝 0] fun z => ∑ s ∈ S, z (c s) * A s z := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    refine ⟨fun _ _ => 0, fun _ => Eventually.of_forall fun _ => differentiableAt_const _, ?_⟩
    filter_upwards [h0] with z hz
    simpa using hz (fun s hs => absurd hs (Finset.notMem_empty s))
  | insert a S ha ih =>
    set Z := coordZero (c a)
    have hZ0 : Z 0 = 0 := map_zero Z
    have hZT : Tendsto Z (𝓝 0) (𝓝 0) := by
      have := Z.continuous.tendsto 0
      rwa [hZ0] at this
    -- `G ∘ Z` vanishes on the smaller coordinate subspace
    have hG1 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z => G (Z z)) z := by
      filter_upwards [hZT.eventually hG] with z hz
      exact hz.comp z Z.differentiableAt
    have h01 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), (∀ s ∈ S, z (c s) = 0) → G (Z z) = 0 := by
      filter_upwards [hZT.eventually h0] with z hz hzS
      apply hz
      intro s hs
      rw [coordZero_apply]
      split_ifs with h
      · rfl
      · rcases Finset.mem_insert.mp hs with rfl | hs'
        · exact absurd rfl h
        · exact hzS s hs'
    obtain ⟨A1, hA1, heq1⟩ := ih hG1 h01
    -- `G - G ∘ Z` vanishes on `{z_{c a} = 0}`
    have hG2 : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
        DifferentiableAt ℂ (fun z => G z - G (Z z)) z := by
      filter_upwards [hG, hG1] with z hz hz1
      exact hz.sub hz1
    have h02 : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z (c a) = 0 → G z - G (Z z) = 0 := by
      filter_upwards with z hz
      rw [coordZero_of_eq_zero (c a) hz, sub_self]
    obtain ⟨H, hH, heq2⟩ := exists_eq_coord_mul_of_eq_zero (c a) (by simp) hG2 h02
    refine ⟨fun s => if s = a then H else A1 s, fun s => ?_, ?_⟩
    · by_cases hs : s = a
      · simp only [hs, if_true]; exact hH
      · simp only [hs, if_false]; exact hA1 s
    · filter_upwards [heq1, heq2] with z hz1 hz2
      rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ s ∈ S, z (c s) * (if s = a then H else A1 s) z = ∑ s ∈ S, z (c s) * A1 s z := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have : s ≠ a := fun h => ha (h ▸ hs)
        simp [this]
      rw [hS, ← hz1]
      have : G z = (G z - G (Z z)) + G (Z z) := by ring
      rw [this, hz2]

end SGPT.Toric
