import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthonormal bases adapted to a filtration

Infrastructure for `rmk:PhongSturm` (chapter *Test curves*), following Ross–Witt Nyström
[RWN14, §9]: *"if `V` is a vector space with a scalar product, and `𝓕` is a filtration of `V`,
there is a unique decomposition of `V` into a direct sum of mutually orthogonal subspaces
`V_{λ_i}` such that `𝓕_λ V = ⊕_{λ_i ≥ λ} V_{λ_i}`. Furthermore we allow for `λ_i` to be equal
to `λ_j` even when `i ≠ j`, so we can assume that all the subspaces `V_{λ_i}` are one
dimensional."* Choosing a unit vector `s_i` in each line gives an orthonormal basis `(s_i)` of
`V` with weights `λ_i` such that `𝓕_λ V = span {s_i : λ_i ≥ λ}` for every `λ`.

## Main results

* `exists_orthonormal_adapted`: for a decreasing, left-continuous, eventually zero family
  `(G λ)_{λ ∈ ℝ}` of subspaces of a finite-dimensional inner product space there is an
  orthonormal family `(b_i)` with weights `(w_i)` such that `G λ = span {b_i : λ ≤ w_i}` for
  every `λ`.
* `AdaptedONBasis`, `exists_adaptedONBasis`: if moreover the family is exhaustive, the family is
  an orthonormal basis adapted to the filtration.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.TestConfig

open Module Submodule

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A filtration of a vector space indexed by `ℝ`: decreasing, left-continuous and eventually
zero. -/
structure IsLeftContFiltration (G : ℝ → Submodule ℂ V) : Prop where
  antitone : Antitone G
  leftContinuous : ∀ μ : ℝ, ∀ x : V, (∀ μ' : ℝ, μ' < μ → x ∈ G μ') → x ∈ G μ
  eventually_bot : ∃ μ : ℝ, G μ = ⊥

/-- In finite dimension, a nonzero left-continuous filtration has a largest index with nonzero
piece: `G λ* ≠ 0` and `G λ = 0` for `λ > λ*`. -/
theorem IsLeftContFiltration.exists_top_weight [FiniteDimensional ℂ V] {G : ℝ → Submodule ℂ V}
    (hG : IsLeftContFiltration G) (hne : ∃ μ, G μ ≠ ⊥) :
    ∃ μs : ℝ, G μs ≠ ⊥ ∧ ∀ μ, μs < μ → G μ = ⊥ := by
  classical
  set S : Set ℝ := {μ | G μ ≠ ⊥} with hSdef
  obtain ⟨μb, hμb⟩ := hG.eventually_bot
  have hbot : ∀ μ, μb ≤ μ → G μ = ⊥ := fun μ h =>
    le_bot_iff.mp ((hG.antitone h).trans hμb.le)
  have hbdd : BddAbove S := ⟨μb, fun μ hμ => by
    by_contra h
    exact hμ (hbot μ (le_of_lt (lt_of_not_ge h)))⟩
  have hSne : S.Nonempty := hne
  set μs := sSup S with hμs
  refine ⟨μs, ?_, fun μ hμ => ?_⟩
  · -- minimal dimension below `μs`
    let g : ℝ → ℕ := fun μ => finrank ℂ (G μ)
    have hne' : (g '' Set.Iio μs).Nonempty := by
      obtain ⟨μ₀, hμ₀⟩ := hSne
      refine ⟨g (μs - 1), μs - 1, by simp, rfl⟩
    obtain ⟨μ₀, hμ₀, hgμ₀⟩ := Nat.sInf_mem hne'
    have hmin : ∀ μ : ℝ, μ < μs → g μ₀ ≤ g μ := fun μ hμ => by
      rw [hgμ₀]
      exact Nat.sInf_le ⟨μ, hμ, rfl⟩
    -- `G μ₀ ≠ 0`
    have hμ₀ne : G μ₀ ≠ ⊥ := by
      obtain ⟨μ₁, hμ₁S, hμ₁⟩ := exists_lt_of_lt_csSup hSne (show μ₀ < sSup S from hμ₀)
      intro h
      exact hμ₁S (le_bot_iff.mp ((hG.antitone hμ₁.le).trans h.le))
    -- `G μs ⊇ G μ₀`
    intro hμsbot
    apply hμ₀ne
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ G μs := by
      refine hG.leftContinuous μs x fun μ' hμ' => ?_
      rcases le_total μ' μ₀ with h | h
      · exact hG.antitone h hx
      · have hsub : G μ' ≤ G μ₀ := hG.antitone h
        have heq := Submodule.eq_of_le_of_finrank_le hsub (hmin μ' hμ')
        rw [heq]
        exact hx
    rw [hμsbot] at this
    exact this
  · by_contra h
    exact absurd (le_csSup hbdd (show μ ∈ S from h)) (not_le.mpr hμ)

/-- An orthonormal family adapted to a left-continuous filtration. -/
def IsAdaptedFamily (G : ℝ → Submodule ℂ V) {ι : Type} (b : ι → V) (w : ι → ℝ) : Prop :=
  Orthonormal ℂ b ∧ ∀ μ : ℝ, G μ = span ℂ (b '' {i | μ ≤ w i})

theorem orthonormal_emptyElim : Orthonormal ℂ (Empty.elim : Empty → V) := by
  classical
  rw [orthonormal_iff_ite]
  intro i
  exact i.elim

theorem orthonormal_sum_elim {ι ι' : Type} {b : ι → V} {b' : ι' → V} (hb : Orthonormal ℂ b)
    (hb' : Orthonormal ℂ b') (horth : ∀ i j, inner ℂ (b i) (b' j) = 0) :
    Orthonormal ℂ (Sum.elim b b') := by
  classical
  rw [orthonormal_iff_ite] at hb hb' ⊢
  rintro (i | i) (j | j)
  · simp [hb i j]
  · simp [horth i j]
  · simp only [Sum.elim_inr, Sum.elim_inl, reduceCtorEq, if_false]
    rw [← inner_conj_symm, horth j i, map_zero]
  · simp [hb' i j]

/-- **Existence of adapted orthonormal families** ([RWN14, §9]). -/
theorem exists_orthonormal_adapted [FiniteDimensional ℂ V] (G : ℝ → Submodule ℂ V)
    (hG : IsLeftContFiltration G) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → V) (w : ι → ℝ), IsAdaptedFamily G b w := by
  classical
  -- strong induction on the dimension of the union of the pieces
  suffices key : ∀ d : ℕ, ∀ G : ℝ → Submodule ℂ V, IsLeftContFiltration G →
      finrank ℂ (⨆ μ, G μ : Submodule ℂ V) ≤ d →
      ∃ (ι : Type) (_ : Fintype ι) (b : ι → V) (w : ι → ℝ), IsAdaptedFamily G b w from
    key _ G hG le_rfl
  intro d
  induction d with
  | zero =>
    intro G hG hd
    have htop : (⨆ μ, G μ) = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hd)
    refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ⟨orthonormal_emptyElim, fun μ => ?_⟩⟩
    rw [show (Empty.elim : Empty → V) '' {i | μ ≤ (Empty.elim : Empty → ℝ) i} = ∅ by
      ext x; simp, Submodule.span_empty]
    exact le_bot_iff.mp (htop ▸ le_iSup G μ)
  | succ d ih =>
    intro G hG hd
    by_cases hne : ∃ μ, G μ ≠ ⊥
    swap
    · push Not at hne
      refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, ⟨orthonormal_emptyElim, fun μ => ?_⟩⟩
      rw [show (Empty.elim : Empty → V) '' {i | μ ≤ (Empty.elim : Empty → ℝ) i} = ∅ by
        ext x; simp, Submodule.span_empty]
      exact hne μ
    obtain ⟨μs, hUne, hUtop⟩ := hG.exists_top_weight hne
    set U := G μs with hU
    let G' : ℝ → Submodule ℂ V := fun μ => G μ ⊓ Uᗮ
    have hG' : IsLeftContFiltration G' := by
      refine ⟨fun μ μ' h => inf_le_inf_right _ (hG.antitone h), fun μ x hx => ?_, ?_⟩
      · refine ⟨hG.leftContinuous μ x fun μ' hμ' => (hx μ' hμ').1, (hx (μ - 1) (by linarith)).2⟩
      · obtain ⟨μb, hμb⟩ := hG.eventually_bot
        exact ⟨μb, by simp [G', hμb]⟩
    have hUle : U ≤ ⨆ μ, G μ := le_iSup G μs
    have hdim : finrank ℂ (⨆ μ, G' μ : Submodule ℂ V) ≤ d := by
      have h1 : (⨆ μ, G' μ) ≤ Uᗮ ⊓ (⨆ μ, G μ) :=
        iSup_le fun μ => le_inf inf_le_right (inf_le_left.trans (le_iSup G μ))
      have h2 := Submodule.finrank_add_inf_finrank_orthogonal hUle
      have h3 : 0 < finrank ℂ U := by
        rw [Module.finrank_pos_iff]
        exact Submodule.nontrivial_iff_ne_bot.mpr hUne
      have h4 := Submodule.finrank_mono h1
      omega
    obtain ⟨ι', hι', b', w', hon', had'⟩ := ih G' hG' hdim
    let e := stdOrthonormalBasis ℂ U
    let bU : Fin (finrank ℂ U) → V := fun i => (e i : V)
    have honU : Orthonormal ℂ bU := e.orthonormal.comp_linearIsometry U.subtypeₗᵢ
    have hspanU : span ℂ (Set.range bU) = U := by
      change span ℂ (Set.range (U.subtype ∘ e)) = U
      rw [Set.range_comp, Submodule.span_image, ← e.coe_toBasis, e.toBasis.span_eq,
        Submodule.map_subtype_top]
    -- each `b' j` lies in `Uᗮ`
    have hb'perp : ∀ j, b' j ∈ Uᗮ := by
      intro j
      have hmem : b' j ∈ G' (w' j) := by
        rw [had' (w' j)]
        exact Submodule.subset_span ⟨j, le_refl (w' j), rfl⟩
      exact hmem.2
    refine ⟨Fin (finrank ℂ U) ⊕ ι', inferInstance, Sum.elim bU b', Sum.elim (fun _ => μs) w',
      ⟨orthonormal_sum_elim honU hon' fun i j => ?_, fun μ => ?_⟩⟩
    · exact Submodule.inner_right_of_mem_orthogonal (Submodule.coe_mem (e i)) (hb'perp j)
    · have himg : Sum.elim bU b' '' {x | μ ≤ Sum.elim (fun _ => μs) w' x} =
          bU '' {i | μ ≤ μs} ∪ b' '' {j | μ ≤ w' j} := by
        ext v
        simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_union, Sum.exists, Sum.elim_inl,
          Sum.elim_inr]
      rw [himg, Submodule.span_union, ← had' μ]
      by_cases hμ : μ ≤ μs
      · have hall : {i : Fin (finrank ℂ U) | μ ≤ μs} = Set.univ := Set.eq_univ_of_forall fun _ => hμ
        rw [hall, Set.image_univ, hspanU]
        have hUG : U ≤ G μ := hG.antitone hμ
        change G μ = U ⊔ (G μ ⊓ Uᗮ)
        rw [inf_comm]
        exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hUG).symm
      · have hnone : {i : Fin (finrank ℂ U) | μ ≤ μs} = ∅ := Set.eq_empty_of_forall_notMem
          fun _ h => hμ h
        rw [hnone, Set.image_empty, Submodule.span_empty, bot_sup_eq]
        have hb : G μ = ⊥ := hUtop μ (lt_of_not_ge hμ)
        change G μ = G μ ⊓ Uᗮ
        rw [hb, bot_inf_eq]

/-- An orthonormal basis `(s_i)` of `V` with weights `(λ_i)` adapted to a filtration `G`:
`G λ = span {s_i : λ_i ≥ λ}` for every `λ` ([RWN14, §9]). -/
structure AdaptedONBasis (G : ℝ → Submodule ℂ V) where
  /-- The index type. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The orthonormal basis. -/
  basis : OrthonormalBasis ι ℂ V
  /-- The weights. -/
  weight : ι → ℝ
  adapted : ∀ μ : ℝ, G μ = span ℂ (basis '' {i | μ ≤ weight i})

attribute [instance] AdaptedONBasis.fintype

/-- **Existence of adapted orthonormal bases** for an exhaustive filtration. -/
theorem exists_adaptedONBasis [FiniteDimensional ℂ V] (G : ℝ → Submodule ℂ V)
    (hG : IsLeftContFiltration G) (hex : ∃ μ, G μ = ⊤) : Nonempty (AdaptedONBasis G) := by
  obtain ⟨ι, hι, b, w, hon, had⟩ := exists_orthonormal_adapted G hG
  obtain ⟨μt, hμt⟩ := hex
  have hsp : ⊤ ≤ span ℂ (Set.range b) := by
    rw [← hμt, had μt]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  let B := OrthonormalBasis.mk hon hsp
  refine ⟨⟨ι, B, w, fun μ => ?_⟩⟩
  rw [had μ]
  congr 1
  ext v
  simp [B, OrthonormalBasis.coe_mk]

end SGPT.TestCurve.TestConfig
