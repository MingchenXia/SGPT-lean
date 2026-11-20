import SGPT.Checks.Comparison.BJIntersectPositivity

/-!
# The Hodge-type inequality for vertical divisors (lane BJ-INTERSECT, R7 core)

[BHJ17, Lemma 6.14] = [BJ22, `lem:Hodge`]: on a test configuration, a `ℚ`-Cartier divisor `D`
supported on the central fibre satisfies `(D² · L₁ ⋯ L_{n-1}) ≤ 0` for relatively nef `Lᵢ`.

We prove it on any integral projective scheme `X` (of dimension `≤ m + 2`, `n = m + 1`) whose
"central fibre" has Cartier components: an invertible `P` (the fibre class `𝒪(𝒳₀) = π^*𝒪(1)`)
with a nonzero section `s_∞` (vanishing on the fibre at infinity), invertible `E_j` with nonzero
sections `σ_j` whose zero schemes `Z_j` are integral (the components of `𝒳₀`), with
`[P] = ∑ b_j [E_j]`, `b_j > 0`, each `E_j` trivial on the zero scheme of `s_∞`, and the restriction
of `σ_j` to `Z_i` nonzero for `i ≠ j`. Then every `D = ∑ x_j [E_j]` has
`(D · D · N₁ ⋯ N_m) ≤ 0` for invertible `N_k` that are nef on a closed set containing all `Z_j`
(`interFormQ_sq_nonpos_of_components`), and also for nonnegative rational multiples of them
(`interFormQ_sq_nonpos_of_components_smul`).

The proof is Zariski's lemma (`MultisetForm.sq_nonpos_of_offDiag_nonneg`): the matrix
`M_ij = (E_i · E_j · N)` has nonnegative off-diagonal entries (`mixedEulerDifference_effective_nonneg`
on `Z_i`) and kills `b` (`mixedEulerDifference_eq_zero_of_trivial_on_zero`).

The reduction of the general case (central fibre with non-`ℚ`-Cartier components) to this one by
an alteration and the projection formula is planned in `claude-bj-intersect.tex`
(`claude-bj-intersect:plan-hodge`). Blueprint: `claude-bj-intersect:hodge-cartier`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
open scoped TensorProduct

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.SeshadriAmplenessCriterion

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The restriction of a section `σ` of `E` along a morphism `i`: a section of `i^* E`. -/
def restrictSection {X Y : Scheme.{u}} (i : Y ⟶ X) {E : X.Modules} (σ : unitObj X ⟶ E) :
    unitObj Y ⟶ (Scheme.Modules.pullback i).obj E :=
  (Scheme.Modules.pullbackUnitIso i).inv ≫ (Scheme.Modules.pullback i).map σ

variable {k : Type u} [Field k]

/-- The off-diagonal intersection numbers of two components are nonnegative. -/
theorem mixedEulerDifference_components_nonneg (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (E₁ : X.Modules) (hE₁ : IsInvertible E₁) (σ₁ : unitObj X ⟶ E₁) (hσ₁ : σ₁ ≠ 0)
    (hint : IsIntegral (LineSectionZeroIdeal.zeroIdeal E₁ hE₁ σ₁).subscheme)
    (E₂ : X.Modules) (hE₂ : IsInvertible E₂) (σ₂ : unitObj X ⟶ E₂)
    (hσ₂ : restrictSection (LineSectionZeroIdeal.zeroIdeal E₁ hE₁ σ₁).subschemeι σ₂ ≠ 0)
    (W : Set X) (hW : ((LineSectionZeroIdeal.zeroIdeal E₁ hE₁ σ₁).support : Set X) ⊆ W)
    (Ns : List {N : X.Modules // IsInvertible N}) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1 W) :
    0 ≤ mixedEulerDifference p (E₁ :: E₂ :: Ns.map Subtype.val) (unitObj X) := by
  let D := LineSectionZeroIdeal.zeroIdeal E₁ hE₁ σ₁
  let i := D.subschemeι
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : D.subscheme.IsSeparated := isSeparated_of_closed i
  let : IsProjective (i ≫ p) := isProjective_closed_comp i p
  let : IsIntegral D.subscheme := hint
  have hinv : ∀ K ∈ E₂ :: Ns.map Subtype.val, IsInvertible K := by
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact hE₂
    · obtain ⟨N, -, rfl⟩ := List.mem_map.mp hK
      exact N.2
  rw [mixedEulerDifference_sectionDifference p E₁ hE₁ σ₁ hσ₁ _ hinv (unitObj X) isInvertible_unit,
    List.map_cons]
  have hdimD : topologicalKrullDim D.subscheme ≤ (m + 1 : ℕ) :=
    sectionZero_dimension_drop (m + 1) hdim E₁ hE₁ σ₁ hσ₁
  have hTE : IsInvertible (unitObj X ⊗ E₁) :=
    (isInvertible_unit.tensorObj hE₁).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso _ E₁)
  let Ns' : List {N : D.subscheme.Modules // IsInvertible N} :=
    Ns.map fun N => ⟨(Scheme.Modules.pullback i).obj N.1, N.2.pullback i⟩
  have h := mixedEulerDifference_effective_nonneg m (i ≫ p) hdimD
    ((Scheme.Modules.pullback i).obj E₂) (hE₂.pullback i) (restrictSection i σ₂) hσ₂ Ns'
    (by simpa [Ns'] using hNs)
    (by
      intro N' hN'
      obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hN'
      refine ((hnef N hN).pullback i).mono ?_
      intro x _
      apply hW
      change i x ∈ (D.support : Set X)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩)
    ((Scheme.Modules.pullback i).obj (unitObj X ⊗ E₁)) (hTE.pullback i)
  simpa [Ns', List.map_map, Function.comp_def] using h

/-- **The Hodge-type inequality when the components of the central fibre are Cartier**
([BHJ17, Lemma 6.14], [BJ22, `lem:Hodge`], on a model whose central fibre has Cartier
components). -/
theorem interFormQ_sq_nonpos_of_components (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (sInf : unitObj X ⟶ P) (hsInf : sInf ≠ 0)
    {ι : Type*} [Fintype ι] (E : ι → {E : X.Modules // IsInvertible E})
    (σ : ∀ j, unitObj X ⟶ (E j).1) (hσ : ∀ j, σ j ≠ 0)
    (hint : ∀ j, IsIntegral (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subscheme)
    (hres : ∀ i j, i ≠ j → restrictSection
      (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι (σ j) ≠ 0)
    (b : ι → ℕ) (hb : ∀ j, 0 < b j) (hfib : ∑ j, b j • lineCls (E j) = lineCls ⟨P, hP⟩)
    (htriv : ∀ j, Nonempty ((Scheme.Modules.pullback
      (LineSectionZeroIdeal.zeroIdeal P hP sInf).subschemeι).obj (E j).1 ≅
        unitObj (LineSectionZeroIdeal.zeroIdeal P hP sInf).subscheme))
    (W : Set X) (hW : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support :
      Set X) ⊆ W)
    (Ns : List {N : X.Modules // IsInvertible N}) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1 W) (x : ι → ℚ) :
    interFormQ p (m + 2) hdim (unitObj X)
      ((∑ j, x j • picQ (E j)) ::ₘ (∑ j, x j • picQ (E j)) ::ₘ
        ((Ns.map picQ : List (PicQ X)) : Multiset (PicQ X))) ≤ 0 := by
  classical
  set Φ := interFormQ p (m + 2) hdim (unitObj X) with hΦ
  set t : Multiset (PicQ X) := ((Ns.map picQ : List (PicQ X)) : Multiset (PicQ X)) with ht
  -- the intersection numbers `(E_i · E_j · N)` and `(E_i · P · N)`
  have hval : ∀ A B : {E : X.Modules // IsInvertible E},
      Φ (picQ A ::ₘ picQ B ::ₘ t) =
        mixedEulerDifference p (A.1 :: B.1 :: Ns.map Subtype.val) (unitObj X) := by
    intro A B
    have := interFormQ_picQ p (m + 2) hdim (unitObj X) (A :: B :: Ns) (by simp [hNs])
    simpa [ht] using this
  have hP' : picQ ⟨P, hP⟩ = ∑ j, ((b j : ℚ)) • picQ (E j) := by
    unfold picQ
    rw [← hfib, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.tmul_smul, ← Nat.cast_smul_eq_nsmul ℚ]
  refine Φ.sq_nonpos_of_offDiag_nonneg (fun j => picQ (E j)) t (fun j => (b j : ℚ))
    (fun j => by exact_mod_cast hb j) (fun i j hij => ?_) (fun i => ?_) x
  · rw [hval]
    have := mixedEulerDifference_components_nonneg m p hdim (E i).1 (E i).2 (σ i) (hσ i)
      (hint i) (E j).1 (E j).2 (σ j) (hres i j hij) W (hW i) Ns hNs hnef
    exact_mod_cast this
  · rw [← hP', hval]
    have hinv : ∀ K ∈ Ns.map Subtype.val, IsInvertible K := by
      intro K hK
      obtain ⟨N, -, rfl⟩ := List.mem_map.mp hK
      exact N.2
    rw [mixedEulerDifference_swap p (E i).1 P, mixedEulerDifference_eq_zero_of_trivial_on_zero
      p P hP sInf hsInf (E i).1 (htriv i) (E i).2 _ hinv (unitObj X) isInvertible_unit]
    rfl

/-- The Hodge-type inequality against nonnegative rational multiples of relatively nef
invertible sheaves (i.e. against relatively nef `ℚ`-line bundles). -/
theorem interFormQ_sq_nonpos_of_components_smul (m : ℕ) {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated] (p : X ⟶ Spec (.of k)) [IsProjective p]
    (hdim : topologicalKrullDim X ≤ (m + 2 : ℕ))
    (P : X.Modules) (hP : IsInvertible P) (sInf : unitObj X ⟶ P) (hsInf : sInf ≠ 0)
    {ι : Type*} [Fintype ι] (E : ι → {E : X.Modules // IsInvertible E})
    (σ : ∀ j, unitObj X ⟶ (E j).1) (hσ : ∀ j, σ j ≠ 0)
    (hint : ∀ j, IsIntegral (LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).subscheme)
    (hres : ∀ i j, i ≠ j → restrictSection
      (LineSectionZeroIdeal.zeroIdeal (E i).1 (E i).2 (σ i)).subschemeι (σ j) ≠ 0)
    (b : ι → ℕ) (hb : ∀ j, 0 < b j) (hfib : ∑ j, b j • lineCls (E j) = lineCls ⟨P, hP⟩)
    (htriv : ∀ j, Nonempty ((Scheme.Modules.pullback
      (LineSectionZeroIdeal.zeroIdeal P hP sInf).subschemeι).obj (E j).1 ≅
        unitObj (LineSectionZeroIdeal.zeroIdeal P hP sInf).subscheme))
    (W : Set X) (hW : ∀ j, ((LineSectionZeroIdeal.zeroIdeal (E j).1 (E j).2 (σ j)).support :
      Set X) ⊆ W)
    (Ns : List ({N : X.Modules // IsInvertible N} × ℚ)) (hNs : Ns.length = m)
    (hnef : ∀ N ∈ Ns, IsNefOn p N.1.1 W) (hc : ∀ N ∈ Ns, 0 ≤ N.2) (x : ι → ℚ) :
    interFormQ p (m + 2) hdim (unitObj X)
      ((∑ j, x j • picQ (E j)) ::ₘ (∑ j, x j • picQ (E j)) ::ₘ
        ((Ns.map fun N => N.2 • picQ N.1 : List (PicQ X)) : Multiset (PicQ X))) ≤ 0 := by
  have h := (interFormQ p (m + 2) hdim (unitObj X)).map_smul_list Prod.snd (fun N => picQ N.1) Ns
    {∑ j, x j • picQ (E j), ∑ j, x j • picQ (E j)}
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add] at h
  rw [h]
  refine mul_nonpos_of_nonneg_of_nonpos (List.prod_nonneg fun c hc' => ?_) ?_
  · obtain ⟨N, hN, rfl⟩ := List.mem_map.mp hc'
    exact hc N hN
  · have := interFormQ_sq_nonpos_of_components m p hdim P hP sInf hsInf E σ hσ hint hres b hb
      hfib htriv W hW (Ns.map Prod.fst) (by simpa using hNs)
      (by
        intro N hN
        obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hN
        exact hnef M hM) x
    simpa [List.map_map, Function.comp_def] using this

end SGPT.NAPotential.BJIntersect
