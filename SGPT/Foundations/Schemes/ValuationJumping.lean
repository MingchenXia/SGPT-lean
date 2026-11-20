import SGPT.Foundations.Schemes.ValuationFiltration
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Tactic

/-! # Actual valuation jumping weights

An adapted basis is constructed along the actual strict threshold subspaces by
finite-dimensional induction and genuine quotient complements. Its weights
are the actual finite values of its nonzero basis vectors. Global sections and
linear growth in the degree are separate geometric producers.
-/

open Set Module
open scoped Classical BigOperators

namespace SGPT.Foundations.Schemes

variable {K F V : Type*} [Field K] [Field F] [Algebra K F]
  [AddCommGroup V] [Module K V]

/-- The strict threshold subspace used to split a finite valuation filtration. -/
def strictValuationFiltration (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (a : ℝ) : Submodule K V where
  carrier := {x | (a : WithTop ℝ) < v (ι x)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (a : WithTop ℝ) < v (ι (x + y))
    rw [map_add]
    exact (lt_min hx hy).trans_le (v.map_add _ _)
  smul_mem' := by
    intro c x hx
    by_cases hc : c = 0
    · subst c
      simp
    · change (a : WithTop ℝ) < v (ι (c • x))
      rw [show ι (c • x) = algebraMap K F c * ι x by simp [Algebra.smul_def],
        v.map_mul, htrivial c hc, zero_add]
      exact hx

@[simp]
theorem mem_strictValuationFiltration (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (a : ℝ) (x : V) : x ∈ strictValuationFiltration v ι htrivial a ↔
      (a : WithTop ℝ) < v (ι x) := Iff.rfl

/-- The minimum is produced by the finite set of actual nonzero-vector values. -/
theorem exists_minimum_valuation [FiniteDimensional K V]
    (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)
    (hne : ∃ x : V, x ≠ 0) :
    ∃ a : ℝ, (∃ x : V, x ≠ 0 ∧ v (ι x) = (a : WithTop ℝ)) ∧
      ∀ x : V, (a : WithTop ℝ) ≤ v (ι x) := by
  have hfinite := valuationValues_finite v ι hι htrivial
  have hnonempty : (valuationValues v ι).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    let a := (v (ι x)).untop (valuation_ne_top_of_injective v ι hι hx)
    exact ⟨a, x, hx, (WithTop.coe_untop _ _).symm⟩
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image (valuationValues v ι) id hfinite hnonempty
  refine ⟨a, ha, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · let b := (v (ι x)).untop (valuation_ne_top_of_injective v ι hι hx)
    have hb : b ∈ valuationValues v ι := ⟨x, hx, (WithTop.coe_untop _ _).symm⟩
    have hab : a ≤ b := hmin b hb
    exact (WithTop.coe_le_coe.mpr hab).trans (WithTop.coe_untop _ _).le

/-- Coordinate formulation of an adapted basis for the actual filtration. -/
def IsValuationAdapted {I : Type*} (v : AddValuation F (WithTop ℝ))
    (ι : V →ₗ[K] F) (b : Basis I K V) : Prop :=
  ∀ (a : ℝ) (x : V) (i : I), (a : WithTop ℝ) ≤ v (ι x) →
    b.repr x i ≠ 0 → (a : WithTop ℝ) ≤ v (ι (b i))

/-- The adapted basis is obtained by splitting actual threshold subspaces,
with a strictly smaller-dimensional subspace at every recursive step. -/
theorem exists_valuationAdapted_basis [FiniteDimensional K V]
    (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) (hι : Function.Injective ι)
    (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0) :
    ∃ b : Basis (Fin (Module.finrank K V)) K V, IsValuationAdapted v ι b := by
  classical
  have aux : ∀ d : ℕ, ∀ W : Submodule K V, Module.finrank K W = d →
      ∃ b : Basis (Fin (Module.finrank K W)) K W,
        IsValuationAdapted v (ι.comp W.subtype) b := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro W hd
      by_cases hW : W = ⊥
      · refine ⟨Module.finBasis K W, ?_⟩
        intro a x i hx hcoord
        have hxzero : x = 0 := by
          apply Subtype.ext
          simpa [hW] using x.property
        simp [hxzero] at hcoord
      · have hιW : Function.Injective (ι.comp W.subtype) := hι.comp Subtype.val_injective
        have hWnonzero : ∃ x : W, x ≠ 0 := by
          obtain ⟨x, hx, hxzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
          exact ⟨⟨x, hx⟩, by simpa using hxzero⟩
        obtain ⟨q, ⟨xq, hxq, hvalueq⟩, hminimum⟩ :=
          exists_minimum_valuation v (ι.comp W.subtype) hιW htrivial hWnonzero
        let S : Submodule K V := W ⊓ strictValuationFiltration v ι htrivial q
        have hSW : S ≤ W := inf_le_left
        have hSlt : S < W := by
          apply lt_of_le_of_ne hSW
          intro heq
          have hxs : (xq : V) ∈ S :=
            Eq.mp (congrArg (fun P : Submodule K V => (xq : V) ∈ P) heq.symm) xq.property
          have hstrict : (q : WithTop ℝ) < v (ι (xq : V)) := hxs.2
          change (q : WithTop ℝ) < v ((ι.comp W.subtype) xq) at hstrict
          rw [hvalueq] at hstrict
          exact (lt_irrefl (q : WithTop ℝ)) hstrict
        obtain ⟨bS, hbS⟩ := ih (Module.finrank K S)
          ((Submodule.finrank_lt_finrank_of_lt hSlt).trans_eq hd) S rfl
        let S' : Submodule K W := S.comap W.subtype
        let eS : S' ≃ₗ[K] S := Submodule.comapSubtypeEquivOfLe hSW
        let bS' := bS.map eS.symm
        obtain ⟨C, hcompl⟩ := Submodule.exists_isCompl S'
        let bC := Module.finBasis K C
        let e : (S' × C) ≃ₗ[K] W := S'.prodEquivOfIsCompl C hcompl
        let B := (bS'.prod bC).map e
        have hB : IsValuationAdapted v (ι.comp W.subtype) B := by
          intro a x j hx hcoord
          by_cases haq : a ≤ q
          · exact (WithTop.coe_le_coe.mpr haq).trans (hminimum (B j))
          · have hqa : q < a := lt_of_not_ge haq
            have hxS : x ∈ S' := by
              exact ⟨x.property, (WithTop.coe_lt_coe.mpr hqa).trans_le hx⟩
            let xs : S' := ⟨x, hxS⟩
            have hsplit : e.symm x = (xs, 0) :=
              S'.prodEquivOfIsCompl_symm_apply_left C hcompl xs
            cases j with
            | inl i =>
              have hcoordS : bS.repr (eS xs) i ≠ 0 := by
                simpa [B, Basis.map_repr, hsplit, bS', Basis.prod_repr_inl] using hcoord
              have hthreshold := hbS a (eS xs) i hx hcoordS
              have hBi : ((B (Sum.inl i) : W) : V) = (bS i : V) := by
                simp [B, bS', Basis.map_apply, Basis.prod_apply,
                  Submodule.coe_prodEquivOfIsCompl', e, eS,
                  Submodule.comapSubtypeEquivOfLe]
              change (a : WithTop ℝ) ≤ v (ι ((B (Sum.inl i) : W) : V))
              rw [hBi]
              exact hthreshold
            | inr i =>
              exfalso
              apply hcoord
              simp [B, Basis.map_repr, hsplit, Basis.prod_repr_inr]
        let eI := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
        refine ⟨B.reindex eI, ?_⟩
        intro a x i hx hcoord
        simpa only [Basis.reindex_apply] using
          hB a x (eI.symm i) hx (by simpa [Basis.repr_reindex_apply] using hcoord)
  obtain ⟨b, hb⟩ := aux (Module.finrank K (⊤ : Submodule K V)) ⊤ rfl
  let e : (⊤ : Submodule K V) ≃ₗ[K] V := LinearEquiv.ofTop (⊤ : Submodule K V) rfl
  let B := b.map e
  let eI := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex eI, ?_⟩
  intro a x i hx hcoord
  have hcoordb : b.repr (e.symm x) (eI.symm i) ≠ 0 := by
    simpa [B, Basis.repr_reindex_apply, Basis.map_repr] using hcoord
  have hthreshold := hb a (e.symm x) (eI.symm i) hx hcoordb
  simpa [B, Basis.reindex_apply, Basis.map_apply, e, LinearEquiv.ofTop] using hthreshold

section JumpingWeights

variable [FiniteDimensional K V]
variable (v : AddValuation F (WithTop ℝ)) (ι : V →ₗ[K] F) (hι : Function.Injective ι)
variable (htrivial : ∀ c : K, c ≠ 0 → v (algebraMap K F c) = 0)

/-- A basis selected from the proved quotient-complement construction. -/
noncomputable def valuationAdaptedBasis : Basis (Fin (Module.finrank K V)) K V :=
  Classical.choose (exists_valuationAdapted_basis v ι hι htrivial)

theorem valuationAdaptedBasis_isAdapted :
    IsValuationAdapted v ι (valuationAdaptedBasis v ι hι htrivial) :=
  Classical.choose_spec (exists_valuationAdapted_basis v ι hι htrivial)

/-- The actual jumping weights, retaining one entry for every basis vector. -/
noncomputable def valuationJumpingWeights : Fin (Module.finrank K V) → ℝ := fun i =>
  (v (ι (valuationAdaptedBasis v ι hι htrivial i))).untop
    (valuation_ne_top_of_injective v ι hι ((valuationAdaptedBasis v ι hι htrivial).ne_zero i))

/-- Each defined real weight is exactly the valuation of its nonzero vector. -/
theorem coe_valuationJumpingWeights (i : Fin (Module.finrank K V)) :
    ((valuationJumpingWeights v ι hι htrivial i : ℝ) : WithTop ℝ) =
      v (ι (valuationAdaptedBasis v ι hι htrivial i)) :=
  WithTop.coe_untop _ _

/-- The actual threshold subspace is spanned by precisely the qualifying
basis vectors; adaptedness is supplied by the construction. -/
theorem valuationFiltration_eq_span_jumpingWeights (a : ℝ) :
    valuationFiltration v ι htrivial a = Submodule.span K
      (valuationAdaptedBasis v ι hι htrivial ''
        {i | a ≤ valuationJumpingWeights v ι hι htrivial i}) := by
  let b := valuationAdaptedBasis v ι hι htrivial
  have hb := valuationAdaptedBasis_isAdapted v ι hι htrivial
  apply le_antisymm
  · intro x hx
    have hsupp : ((b.repr x).support : Set (Fin (Module.finrank K V))) ⊆
        {i | a ≤ valuationJumpingWeights v ι hι htrivial i} := by
      intro i hi
      have hbi := hb a x i hx (Finsupp.mem_support_iff.mp hi)
      change a ≤ valuationJumpingWeights v ι hι htrivial i
      apply WithTop.coe_le_coe.mp
      rw [coe_valuationJumpingWeights]
      exact hbi
    exact Submodule.span_mono (Set.image_mono hsupp) (b.mem_span_repr_support x)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change (a : WithTop ℝ) ≤ v (ι (valuationAdaptedBasis v ι hι htrivial i))
    rw [← coe_valuationJumpingWeights v ι hι htrivial i]
    exact WithTop.coe_le_coe.mpr hi

/-- Threshold dimensions count the actual jumping weights with multiplicity. -/
theorem valuationFiltration_finrank_eq_count (a : ℝ) :
    Module.finrank K (valuationFiltration v ι htrivial a) =
      (Finset.univ.filter (fun i => a ≤ valuationJumpingWeights v ι hι htrivial i)).card := by
  classical
  let b := valuationAdaptedBasis v ι hι htrivial
  let s : Set (Fin (Module.finrank K V)) := {i | a ≤ valuationJumpingWeights v ι hι htrivial i}
  have hli : LinearIndependent K (fun i : s => b i) :=
    b.linearIndependent.comp ((↑) : s → Fin (Module.finrank K V)) Subtype.val_injective
  have hrange : Set.range (fun i : s => b i) = b '' s := by
    ext x
    simp
  rw [valuationFiltration_eq_span_jumpingWeights]
  change Module.finrank K (Submodule.span K (b '' s)) = _
  rw [← hrange, finrank_span_eq_card hli]
  exact Fintype.card_subtype _

/-- The actual finite weight multiset, retaining all repetitions. -/
noncomputable def valuationJumpingMultiset : Multiset ℝ :=
  Finset.univ.val.map (valuationJumpingWeights v ι hι htrivial)

/-- The total multiplicity of the actual weight list is the dimension. -/
theorem valuationJumpingWeights_total_multiplicity :
    Multiset.card (valuationJumpingMultiset v ι hι htrivial) = Module.finrank K V := by
  simp [valuationJumpingMultiset]

/-- A finite-dimensional filtration has finite real bounds in its individual
space, including the zero-dimensional case. This is not a degree-linear bound. -/
theorem valuationJumpingWeights_bounded :
    ∃ A B : ℝ, ∀ i, A ≤ valuationJumpingWeights v ι hι htrivial i ∧
      valuationJumpingWeights v ι hι htrivial i ≤ B := by
  classical
  let s := Finset.univ.image (valuationJumpingWeights v ι hι htrivial)
  by_cases hs : s.Nonempty
  · refine ⟨s.min' hs, s.max' hs, ?_⟩
    intro i
    have hi : valuationJumpingWeights v ι hι htrivial i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact ⟨Finset.min'_le s _ hi, Finset.le_max' s _ hi⟩
  · refine ⟨0, 0, ?_⟩
    intro i
    exact False.elim (hs ⟨valuationJumpingWeights v ι hι htrivial i,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)

/-- Centered nonnegative representative values give nonnegative jumping
weights; the local nonnegativity is an explicit geometric input. -/
theorem valuationJumpingWeights_nonneg
    (hcenter : ∀ x : V, (0 : WithTop ℝ) ≤ v (ι x)) (i : Fin (Module.finrank K V)) :
    0 ≤ valuationJumpingWeights v ι hι htrivial i := by
  apply WithTop.coe_le_coe.mp
  rw [coe_valuationJumpingWeights]
  exact hcenter _

/-- The quotient dimension is the number of weights strictly below threshold,
which is the colength counting convention of the manuscript. -/
theorem valuationFiltration_quotient_finrank_eq_count (a : ℝ) :
    Module.finrank K (V ⧸ valuationFiltration v ι htrivial a) =
      (Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i < a)).card := by
  classical
  have hdim := (valuationFiltration v ι htrivial a).finrank_quotient_add_finrank
  rw [valuationFiltration_finrank_eq_count v ι hι htrivial a] at hdim
  have hsplit :
      (Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i < a)).card +
      (Finset.univ.filter (fun i => a ≤ valuationJumpingWeights v ι hι htrivial i)).card =
      Module.finrank K V := by
    rw [← Finset.card_union_of_disjoint]
    · have hunion : Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i < a) ∪
          Finset.univ.filter (fun i => a ≤ valuationJumpingWeights v ι hι htrivial i) = Finset.univ := by
        ext i
        simp [lt_or_ge]
      rw [hunion, Finset.card_univ, Fintype.card_fin]
    · apply Finset.disjoint_left.mpr
      intro i hi₁ hi₂
      exact not_lt_of_ge (Finset.mem_filter.mp hi₂).2 (Finset.mem_filter.mp hi₁).2
  omega

omit [FiniteDimensional K V] in
/-- Strict thresholds are subspaces of the corresponding weak thresholds. -/
theorem strictValuationFiltration_le (a : ℝ) :
    strictValuationFiltration v ι htrivial a ≤ valuationFiltration v ι htrivial a := by
  intro x hx
  change (a : WithTop ℝ) < v (ι x) at hx
  exact hx.le

/-- The actual strict threshold subspace is spanned by the basis vectors
strictly above the threshold. -/
theorem strictValuationFiltration_eq_span_jumpingWeights (a : ℝ) :
    strictValuationFiltration v ι htrivial a = Submodule.span K
      (valuationAdaptedBasis v ι hι htrivial ''
        {i | a < valuationJumpingWeights v ι hι htrivial i}) := by
  let b := valuationAdaptedBasis v ι hι htrivial
  have hb := valuationAdaptedBasis_isAdapted v ι hι htrivial
  apply le_antisymm
  · intro x hx
    have hsupp : ((b.repr x).support : Set (Fin (Module.finrank K V))) ⊆
        {i | a < valuationJumpingWeights v ι hι htrivial i} := by
      intro i hi
      have hxnonzero : x ≠ 0 := by
        intro hzero
        subst x
        simp at hi
      have hfinite := valuation_ne_top_of_injective v ι hι hxnonzero
      have hbi := hb ((v (ι x)).untop hfinite) x i
        (WithTop.coe_untop _ _).le (Finsupp.mem_support_iff.mp hi)
      rw [WithTop.coe_untop] at hbi
      change a < valuationJumpingWeights v ι hι htrivial i
      apply WithTop.coe_lt_coe.mp
      rw [coe_valuationJumpingWeights]
      exact hx.trans_le hbi
    exact Submodule.span_mono (Set.image_mono hsupp) (b.mem_span_repr_support x)
  · apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change (a : WithTop ℝ) < v (ι (valuationAdaptedBasis v ι hι htrivial i))
    rw [← coe_valuationJumpingWeights v ι hι htrivial i]
    exact WithTop.coe_lt_coe.mpr hi

/-- Dimensions at strict thresholds count strictly higher weights. -/
theorem strictValuationFiltration_finrank_eq_count (a : ℝ) :
    Module.finrank K (strictValuationFiltration v ι htrivial a) =
      (Finset.univ.filter (fun i => a < valuationJumpingWeights v ι hι htrivial i)).card := by
  classical
  let b := valuationAdaptedBasis v ι hι htrivial
  let s : Set (Fin (Module.finrank K V)) := {i | a < valuationJumpingWeights v ι hι htrivial i}
  have hli : LinearIndependent K (fun i : s => b i) :=
    b.linearIndependent.comp ((↑) : s → Fin (Module.finrank K V)) Subtype.val_injective
  have hrange : Set.range (fun i : s => b i) = b '' s := by
    ext x
    simp
  rw [strictValuationFiltration_eq_span_jumpingWeights]
  change Module.finrank K (Submodule.span K (b '' s)) = _
  rw [← hrange, finrank_span_eq_card hli]
  exact Fintype.card_subtype _

/-- The multiplicity at an actual weight is intrinsic: it is the dimension
drop between the actual weak and strict threshold subspaces. -/
theorem valuationJumpingWeights_multiplicity_eq_finrank_difference (a : ℝ) :
    (Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i = a)).card =
      Module.finrank K (valuationFiltration v ι htrivial a) -
        Module.finrank K (strictValuationFiltration v ι htrivial a) := by
  classical
  rw [valuationFiltration_finrank_eq_count v ι hι htrivial a,
    strictValuationFiltration_finrank_eq_count v ι hι htrivial a]
  have hsplit :
      (Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i = a)).card +
      (Finset.univ.filter (fun i => a < valuationJumpingWeights v ι hι htrivial i)).card =
      (Finset.univ.filter (fun i => a ≤ valuationJumpingWeights v ι hι htrivial i)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp [eq_comm, le_iff_eq_or_lt]
    · apply Finset.disjoint_left.mpr
      intro i hi₁ hi₂
      have heq := (Finset.mem_filter.mp hi₁).2
      have hlt := (Finset.mem_filter.mp hi₂).2
      exact (lt_irrefl a) (heq ▸ hlt)
  omega

/-- Multiplicity is the dimension of the genuine graded quotient at the
threshold, making it independent of the chosen quotient complements. -/
theorem valuationJumpingWeights_multiplicity_eq_quotient_finrank (a : ℝ) :
    (Finset.univ.filter (fun i => valuationJumpingWeights v ι hι htrivial i = a)).card =
      Module.finrank K ((valuationFiltration v ι htrivial a) ⧸
        (strictValuationFiltration v ι htrivial a).comap
          (valuationFiltration v ι htrivial a).subtype) := by
  rw [valuationJumpingWeights_multiplicity_eq_finrank_difference]
  have hdim := ((strictValuationFiltration v ι htrivial a).comap
    (valuationFiltration v ι htrivial a).subtype).finrank_quotient_add_finrank
  have heq := (Submodule.comapSubtypeEquivOfLe
    (strictValuationFiltration_le v ι htrivial a)).finrank_eq
  rw [heq] at hdim
  omega

/-- The defined weight values are exactly all actual values of nonzero vectors,
not a larger or arbitrarily assigned finite spectrum. -/
theorem valuationValues_eq_range_jumpingWeights :
    valuationValues v ι = Set.range (valuationJumpingWeights v ι hι htrivial) := by
  classical
  let b := valuationAdaptedBasis v ι hι htrivial
  have hb := valuationAdaptedBasis_isAdapted v ι hι htrivial
  apply Set.Subset.antisymm
  · rintro a ⟨x, hxnonzero, hxvalue⟩
    by_contra hnot
    have hxstrict : x ∈ strictValuationFiltration v ι htrivial a := by
      have hspan : Submodule.span K (b '' ((b.repr x).support : Set (Fin (Module.finrank K V)))) ≤
          strictValuationFiltration v ι htrivial a := by
        apply Submodule.span_le.mpr
        intro y hy
        obtain ⟨i, hi, rfl⟩ := hy
        have hbi := hb a x i hxvalue.symm.le (Finsupp.mem_support_iff.mp hi)
        have hw : a ≤ valuationJumpingWeights v ι hι htrivial i := by
          apply WithTop.coe_le_coe.mp
          rw [coe_valuationJumpingWeights]
          exact hbi
        have hne : a ≠ valuationJumpingWeights v ι hι htrivial i := by
          intro heq
          exact hnot ⟨i, heq.symm⟩
        change (a : WithTop ℝ) < v (ι (b i))
        rw [← coe_valuationJumpingWeights v ι hι htrivial i]
        exact WithTop.coe_lt_coe.mpr (lt_of_le_of_ne hw hne)
      exact hspan (b.mem_span_repr_support x)
    change (a : WithTop ℝ) < v (ι x) at hxstrict
    rw [hxvalue] at hxstrict
    exact (lt_irrefl (a : WithTop ℝ)) hxstrict
  · rintro a ⟨i, rfl⟩
    exact ⟨b i, b.ne_zero i, (coe_valuationJumpingWeights v ι hι htrivial i).symm⟩

end JumpingWeights

end SGPT.Foundations.Schemes
