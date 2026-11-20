import SGPT.Checks.Comparison.BJRelAmplePositive
import SGPT.Checks.Comparison.BJCycleBound

/-!
# `thm:BJappseq`: approximating sequences of psh metrics

Source: `chapter_NApotential.tex`, `thm:BJappseq` (Boucksom–Jonsson, *Global pluripotential
theory over a trivially valued field*, Corollary 12.18): let `X` be an irreducible (unibranch)
complex projective variety, `S` an ample line bundle on `X` and `φ ∈ PSH(L^An)`. Then there are
rationals `ε_i ↘ 0` and a decreasing sequence `φ_i ∈ 𝓗^gf_ℚ((L + ε_i S)^An)` converging pointwise
to `φ`. Blueprint: `claude-bj-relample.tex`, node `claude-bj-relample:thm`.

The statement is the `AppSeq.BJAppSeqStatement p` (for all ample `S`, all rational
classes `L` and all psh metrics `φ` in the sense of `def:BJpshmetric`). For `dim X ≥ 1` it is
`BJCycle.bjAppSeq_of_relAmplePositive` (lane BJ-CYCLE: the cycle lower bound) with the hypothesis
`RelAmplePositive` discharged by `relAmplePositive` (this lane). For `dim X = 0` the space `X^An`
is a single point (every valuation of `κ(η) = ℂ` trivial on `ℂ` is trivial), so every defining
net has a convergent increasing subsequence of indices.

* `eq_genericPoint_of_topologicalKrullDim_eq_zero`, `exists_algebraMap_eq_of_dim_zero`,
  `berkovichPoint_subsingleton`: for `dim X = 0`, `X^An` is a single point;
* `exists_monotone_tendsto`: a convergent net in `EReal` over a directed index set converges along
  an increasing sequence of indices;
* `decreasingNetSelection_of_dim_zero`: countable selection when `dim X = 0`;
* `bjAppSeq_holds`: **`thm:BJappseq`** for every integral projective `X` over `ℂ`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory Filter Topology Order
open SGPT.NAPotential.Berkovich

/-! ### Selection along sequences -/

/-- **Countable selection in `EReal`**: a net in `EReal` over a nonempty directed index set
converging to `a` converges to `a` along some increasing sequence of indices. -/
theorem exists_monotone_tendsto {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {f : I → EReal} {a : EReal} (h : Tendsto f atTop (𝓝 a)) :
    ∃ j : ℕ → I, Monotone j ∧ Tendsto (f ∘ j) atTop (𝓝 a) := by
  obtain ⟨U, hU⟩ := (𝓝 a).exists_antitone_basis
  have hk : ∀ k, ∃ i, ∀ i' ≥ i, f i' ∈ U k := fun k =>
    Filter.mem_atTop_sets.mp (h (hU.mem k))
  choose i hi using hk
  let j : ℕ → I := fun k =>
    Nat.rec (i 0) (fun k jk => (exists_ge_ge jk (i (k + 1))).choose) k
  have hj1 : ∀ k, j k ≤ j (k + 1) := fun k =>
    (exists_ge_ge (j k) (i (k + 1))).choose_spec.1
  have hj2 : ∀ k, i k ≤ j k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => exact (exists_ge_ge (j k) (i (k + 1))).choose_spec.2
  exact ⟨j, monotone_nat_of_le_succ hj1, hU.tendsto fun k => hi k (j k) (hj2 k)⟩

/-! ### Zero-dimensional varieties -/

section dimZero

variable {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X]

local instance relAmpleAppSeq_isProper : IsProper p :=
  (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

omit [IsProjective p] in
/-- On a zero-dimensional integral scheme every point is the generic point. -/
theorem eq_genericPoint_of_topologicalKrullDim_eq_zero (hX : topologicalKrullDim X = 0)
    (x : X) : x = genericPoint X := by
  apply eq_genericPoint_of_coheight_eq_zero
  have h1 : (coheight x : WithBot ℕ∞) ≤ Order.krullDim X := Order.coheight_le_krullDim x
  have h2 : Order.krullDim X = topologicalKrullDim X := by
    change Order.krullDim X = Order.krullDim (TopologicalSpace.IrreducibleCloseds X)
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  rw [h2, hX] at h1
  have h3 : coheight x ≤ 0 := by exact_mod_cast h1
  exact nonpos_iff_eq_zero.mp h3

/-- **`κ(η) = ℂ` for a zero-dimensional variety**: the function field has transcendence degree
`0` over the algebraically closed field `ℂ`, so every element of the residue field at the
generic point is a constant. -/
theorem exists_algebraMap_eq_of_dim_zero (hX : topologicalKrullDim X = 0)
    (g : X.residueField (genericPoint X)) :
    letI := residueComplexAlgebra p (genericPoint X)
    ∃ c : ℂ, algebraMap ℂ (X.residueField (genericPoint X)) c = g := by
  let := p.stalkAlgebra (genericPoint X)
  let := residueComplexAlgebra p (genericPoint X)
  obtain ⟨d, htr, hd⟩ := exists_trdeg_eq_and_dim_eq p
  have hd0 : d = 0 := by
    rw [hX] at hd
    exact_mod_cast hd.symm
  subst hd0
  have : Algebra.IsAlgebraic ℂ X.functionField :=
    trdeg_eq_zero_iff.mp (by simpa using htr)
  let e : X.functionField ≃ₐ[ℂ] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective (X.residue (genericPoint X)).hom
        (residue_bijective_of_eq_genericPoint _ rfl) with
      commutes' := fun a => by
        have h := congrArg (fun φ => φ.hom a) (residueComplexHom_eq_stalkAlgebra p (genericPoint X))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h.symm }
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := X.functionField)).2 (e.symm g)
  exact ⟨c, by rw [← e.commutes, hc, AlgEquiv.apply_symm_apply]⟩

/-- **`X^An` is a single point for a zero-dimensional variety**: every semi-valuation is
supported at the generic point, and every valuation of `κ(η) = ℂ` trivial on `ℂ` is trivial. -/
theorem berkovichPoint_subsingleton (hX : topologicalKrullDim X = 0) :
    Subsingleton (BerkovichPoint p) := by
  constructor
  rintro ⟨s, w⟩ ⟨s', w'⟩
  obtain rfl := eq_genericPoint_of_topologicalKrullDim_eq_zero hX s
  obtain rfl := eq_genericPoint_of_topologicalKrullDim_eq_zero hX s'
  congr 1
  let := residueComplexAlgebra p (genericPoint X)
  apply SourceRealValuation.ext
  intro g
  by_cases hg : g = 0
  · subst hg
    rw [(w.eq_top_iff' 0).mpr rfl, (w'.eq_top_iff' 0).mpr rfl]
  · obtain ⟨c, rfl⟩ := exists_algebraMap_eq_of_dim_zero p hX g
    have hc : c ≠ 0 := by
      rintro rfl
      exact hg (map_zero _)
    change w.toFun _ = w'.toFun _
    rw [w.map_complex' c hc, w'.map_complex' c hc]

/-- **Countable selection for zero-dimensional varieties**: `X^An` is a point, so every defining
net of a psh metric converges along an increasing sequence of indices. -/
theorem decreasingNetSelection_of_dim_zero (hX : topologicalKrullDim X = 0) :
    AppSeq.DecreasingNetSelection.{u} p := by
  have := berkovichPoint_subsingleton p hX
  rintro L φ D ⟨v₀, -⟩ - hlim
  obtain ⟨j, hj, hjt⟩ := exists_monotone_tendsto (hlim v₀)
  refine ⟨j, hj, fun v => ?_⟩
  rw [Subsingleton.elim v v₀]
  exact hjt

end dimZero

/-! ### `thm:BJappseq` -/

/-- **`thm:BJappseq`** ([BJ22, Corollary 12.18]): for an integral (irreducible, reduced) projective
variety `X` over `ℂ`, every ample line bundle `S`, every rational class `L` and every psh metric
`φ ∈ PSH(L^An)` (`def:BJpshmetric`), there are rationals `ε_i ↘ 0` and a decreasing sequence
`φ_i ∈ 𝓗^gf_ℚ((L + ε_i S)^An)` converging pointwise to `φ` on `X^An`. The unibranch hypothesis of
the book is not needed. -/
theorem bjAppSeq_holds {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [IsProjective p] [IsIntegral X] :
    AppSeq.BJAppSeqStatement.{u} p := by
  let : IsProper p := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper
  obtain ⟨d, -, hd⟩ := exists_trdeg_eq_and_dim_eq p
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · exact AppSeq.bjAppSeq_of_selection p
      (decreasingNetSelection_of_dim_zero p (by simpa using hd))
  · exact BJCycle.bjAppSeq_of_relAmplePositive d hd hpos fun ω hω => relAmplePositive p d hd ω hω

end SGPT.NAPotential.BJ
