import SGPT.GAGA.PNSections
import SGPT.GAGA.SerreHomogeneous
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# `Ȟ⁰(ℙᴺ, 𝒪(n))` for the cover `(K_i)`: homogeneous polynomials

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), milestone M3.3 (degree `0`).

* `freeSubquotient ι`: the free sheaf `𝒪^ι` on the cone `X ∖ 0` (numerator `𝒪^ι`, denominator
  `0`); `structureSheaf N = 𝒪` on the cone over `ℙᴺ`. The zero and the free modules are
  invariant under `ℂ*` (`isConeInvariant_bot`, `isConeInvariant_top`), so `𝒪^ι` is an
  invariant subquotient.
* **Gluing** (`cechAug_free_bijective`): for `ρ ≥ 1`, the augmentation
  `Γ(ℂ^{N+1} ∖ 0, 𝒪^ι(n)) → Ž⁰` from global homogeneous sections to `0`-cocycles of the Čech
  complex of the cover `(K_i)` is bijective. A `0`-cocycle is a family of sections over the
  `K_i` that agree near the `K_i ∩ K_k`; they glue to a global homogeneous holomorphic tuple.
  No Theorem B is used.
* **`Ȟ⁰(ℙᴺ, 𝒪(n)) = ℂ[Z₀, …, Z_N]_n`** (`cechH_zero_structureSheaf`): for `n ≥ 0`, every class
  in `Ȟ⁰` of the Čech complex of `𝒪(n)` is the class of a unique homogeneous polynomial of
  degree `n` (by `SerreHomogeneous.exists_isHomogeneous_eq_of_homogeneous`).

Blueprint: `claude-serre-pn.tex`, nodes `claude-serre-pn:structure-sheaf`,
`claude-serre-pn:gluing`, `claude-serre-pn:H0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

namespace SGPT.GAGA.PN

/-! ### The free sheaves and their invariance -/

section Free

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {ι : Type} [Fintype ι]

theorem isConeInvariant_top : IsConeInvariant (GermModule.top X ι) := by
  intro y _ c hc a
  have hφ : ∀ x : X, DifferentiableAt ℂ (fun z : X => c⁻¹ • z) x :=
    fun _ => differentiableAt_id.const_smul c⁻¹
  have hψ : ∀ x : X, DifferentiableAt ℂ (fun z : X => c • z) x :=
    fun _ => differentiableAt_id.const_smul c
  constructor
  · intro ha j
    have h : HolAt (a j) ((fun z : X => c⁻¹ • z) (c • y)) := by
      simpa [inv_smul_smul₀ hc] using ha j
    exact h.comp (continuous_const_smul c⁻¹) hφ
  · intro ha j
    have h := HolAt.comp (ha j) (continuous_const_smul c) hψ
    refine h.congr (Eventually.of_forall fun z => ?_)
    simp [inv_smul_smul₀ hc]

theorem isConeInvariant_bot : IsConeInvariant (GermModule.bot X ι) := by
  intro y _ c hc a
  have hφ : Tendsto (fun z : X => c⁻¹ • z) (𝓝 (c • y)) (𝓝 y) := by
    have := (continuous_const_smul c⁻¹).tendsto (c • y)
    rwa [inv_smul_smul₀ hc] at this
  have hψ : Tendsto (fun z : X => c • z) (𝓝 y) (𝓝 (c • y)) :=
    (continuous_const_smul c).tendsto y
  constructor
  · intro ha j
    exact (ha j).comp_tendsto hφ
  · intro ha j
    have h := (ha j).comp_tendsto hψ
    refine EventuallyEq.trans (Eventually.of_forall fun z => ?_) h
    simp [inv_smul_smul₀ hc]

variable (X ι) in
/-- The free sheaf `𝒪^ι` on the cone `X ∖ 0`, as a subquotient `𝒪^ι/0`. -/
noncomputable def freeSubquotient [DecidableEq ι] : Subquotient X (puncture X) where
  ι := ι
  M := GermModule.top X ι
  N := GermModule.bot X ι
  coherent_M := GermModule.top_isCoherentOn _
  coherent_N := GermModule.bot_isCoherentOn _
  le := GermModule.bot_le (GermModule.top_isCoherentOn _)

theorem freeSubquotient_isInvariant [DecidableEq ι] :
    IsInvariantSubquotient (freeSubquotient X ι) :=
  ⟨isConeInvariant_top, isConeInvariant_bot⟩

/-- A section of `0` vanishes on its domain. -/
theorem IsHomSection.bot_eq_zero {n : ℤ} {K : Set X} {a : ι → X → ℂ}
    (h : IsHomSection (GermModule.bot X ι) n K a) :
    ∃ U : Set X, K ⊆ U ∧ IsHomOn U n a ∧ ∀ y ∈ U, ∀ j, a j y = 0 := by
  obtain ⟨U, hKU, hU, hbot⟩ := h
  exact ⟨U, hKU, hU, fun y hy j => (hbot y hy j).eq_of_nhds⟩

end Free

/-! ### Gluing `0`-cocycles of `𝒪^ι(n)` -/

section Gluing

variable {N : ℕ}

/-- The structure sheaf `𝒪` on the cone over `ℙᴺ`. -/
noncomputable abbrev structureSheaf (N : ℕ) :
    Subquotient (ConeSpace N) (puncture (ConeSpace N)) :=
  freeSubquotient (ConeSpace N) Unit

theorem mem_coverSet_pair {ρ : ℝ} {i k : Fin (N + 1)} {z : ConeSpace N} :
    z ∈ coverSet ρ {i, k} ↔ z ∈ coverSet ρ {i} ∧ z ∈ coverSet ρ {k} := by
  simp only [coverSet, mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  tauto

theorem isOpen_puncture_diff_coverSet (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    IsOpen (puncture (ConeSpace N) \ coverSet ρ s) := by
  obtain ⟨C, hC, hCs⟩ := isClosed_coverSet_inter ρ s
  have : puncture (ConeSpace N) \ coverSet ρ s = puncture _ ∩ Cᶜ := by
    rw [hCs]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  rw [this]
  exact isOpen_ne.inter hC.isOpen_compl

theorem isCone_puncture_diff_coverSet (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    IsCone (puncture (ConeSpace N) \ coverSet ρ s) := by
  rintro c hc z ⟨hz0, hzK⟩
  refine ⟨smul_ne_zero hc hz0, fun hcz => hzK ?_⟩
  have := isCone_coverSet ρ s c⁻¹ (inv_ne_zero hc) _ hcz
  rwa [inv_smul_smul₀ hc] at this

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Gluing**: for `ρ ≥ 1`, every `0`-cocycle of the Čech complex of `𝒪^ι(n)` for the cover
`(K_i)` is the family of restrictions of a global homogeneous section. -/
theorem cechAug_free_surjective {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) :
    Function.Surjective (cechAug (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ)) := by
  classical
  intro z
  -- representatives over the `K_i`
  have hrep : ∀ i : Fin (N + 1),
      ∃ a : secM (freeSubquotient (ConeSpace N) ι) n (coverSet ρ {i}) (coverSet_subset ρ {i}),
        sectionMk (freeSubquotient (ConeSpace N) ι) a = z.1.1 {i} :=
    fun i => Submodule.Quotient.mk_surjective _ _
  choose a ha using hrep
  -- their domains
  have hdom : ∀ i, ∃ U : Set (ConeSpace N), coverSet ρ {i} ⊆ U ∧ IsHomOn U n (a i).1 :=
    fun i => by
      obtain ⟨U, hKU, hU, -⟩ := (a i).2
      exact ⟨U, hKU, hU⟩
  choose U hKU hU using hdom
  -- the representatives agree near the `K_i ∩ K_k`
  have hagree : ∀ i k : Fin (N + 1), ∃ W : Set (ConeSpace N), IsOpen W ∧ IsCone W ∧
      coverSet ρ {i, k} ⊆ W ∧ ∀ w ∈ W, ∀ j, (a i).1 j w = (a k).1 j w := by
    intro i k
    by_cases hik : i = k
    · subst hik
      exact ⟨univ, isOpen_univ, fun _ _ _ _ => mem_univ _, subset_univ _, fun _ _ _ => rfl⟩
    have h := cechCocycle_zero_res (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ) z.2 hik
    rw [← ha i, ← ha k] at h
    change sectionMk (freeSubquotient (ConeSpace N) ι) ⟨(a i).1, IsHomSection.mono (a i).2
        fun z hz => (mem_coverSet_pair.1 hz).1⟩ =
      sectionMk (freeSubquotient (ConeSpace N) ι)
        ⟨(a k).1, IsHomSection.mono (a k).2 fun z hz => (mem_coverSet_pair.1 hz).2⟩
      at h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, sectionMk_eq_zero_iff] at h
    obtain ⟨W, hKW, hW, hzero⟩ := IsHomSection.bot_eq_zero h
    refine ⟨W, hW.isOpen, hW.isCone, hKW, fun w hw j => ?_⟩
    have := hzero w hw j
    simpa [sub_eq_zero] using this
  choose W hWo hWc hKW hWa using hagree
  -- the open cones `V_i ⊇ K_i` on which the glued tuple will agree with `a_i`
  set V : Fin (N + 1) → Set (ConeSpace N) := fun i =>
    U i ∩ ⋂ k, (W i k ∪ (puncture (ConeSpace N) \ coverSet ρ {k})) with hVdef
  have hVo : ∀ i, IsOpen (V i) := fun i =>
    (hU i).isOpen.inter (isOpen_iInter_of_finite fun k =>
      (hWo i k).union (isOpen_puncture_diff_coverSet ρ {k}))
  have hVc : ∀ i, IsCone (V i) := by
    intro i c hc w hw
    refine ⟨(hU i).isCone c hc w hw.1, mem_iInter.2 fun k => ?_⟩
    rcases mem_iInter.1 hw.2 k with h | h
    · exact Or.inl (hWc i k c hc w h)
    · exact Or.inr (isCone_puncture_diff_coverSet ρ {k} c hc w h)
  have hKV : ∀ i, coverSet ρ {i} ⊆ V i := by
    intro i w hw
    refine ⟨hKU i hw, mem_iInter.2 fun k => ?_⟩
    by_cases hwk : w ∈ coverSet ρ {k}
    · exact Or.inl (hKW i k (mem_coverSet_pair.2 ⟨hw, hwk⟩))
    · exact Or.inr ⟨hw.1, hwk⟩
  -- the glued tuple
  let g : (freeSubquotient (ConeSpace N) ι).ι → ConeSpace N → ℂ := fun j w =>
    if h : ∃ i, w ∈ coverSet ρ {i} then (a h.choose).1 j w else 0
  have hgV : ∀ i, ∀ w ∈ V i, ∀ j, g j w = (a i).1 j w := by
    intro i w hw j
    have hw0 : w ≠ 0 := (hU i).subset hw.1
    have hex : ∃ i, w ∈ coverSet ρ {i} := exists_mem_coverSet hρ hw0
    simp only [g, dif_pos hex]
    rcases mem_iInter.1 hw.2 hex.choose with h | h
    · exact (hWa i _ w h j).symm
    · exact absurd hex.choose_spec h.2
  -- `g` is holomorphic and homogeneous on `ℂ^{N+1} ∖ 0`
  have hg : IsHomOn (puncture (ConeSpace N)) n g := by
    refine ⟨isOpen_ne, isCone_ne_zero, subset_rfl, fun j w hw => ?_, fun w hw c hc j => ?_⟩
    · obtain ⟨i, hi⟩ := exists_mem_coverSet hρ hw
      have hev : (a i).1 j =ᶠ[𝓝 w] g j :=
        eventually_of_mem ((hVo i).mem_nhds (hKV i hi)) fun x hx => (hgV i x hx j).symm
      exact (((hU i).diff j).differentiableAt
        ((hU i).isOpen.mem_nhds (hKU i hi))).congr_of_eventuallyEq
        hev.symm |>.differentiableWithinAt
    · obtain ⟨i, hi⟩ := exists_mem_coverSet hρ hw
      have hci : c • w ∈ coverSet ρ {i} := isCone_coverSet ρ {i} c hc w hi
      rw [hgV i (c • w) (hKV i hci) j, hgV i w (hKV i hi) j, (hU i).hom w (hKU i hi) c hc j]
  have hgsec : IsHomSection (freeSubquotient (ConeSpace N) ι).M n (coverSet ρ ∅) g := by
    refine ⟨puncture _, coverSet_subset ρ ∅, hg, fun y hy j => ?_⟩
    exact holAt_of_differentiableOn isOpen_ne (hg.diff j) hy
  refine ⟨sectionMk (freeSubquotient (ConeSpace N) ι) ⟨g, mem_homSections.2 hgsec⟩,
    Subtype.ext (Subtype.ext (funext fun s => ?_))⟩
  refine (cechAug_coe_apply _ _ s).trans ?_
  split_ifs with hs
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    rw [← ha i]
    change sectionMk (freeSubquotient (ConeSpace N) ι) ⟨g, IsHomSection.mono hgsec
      (coverSet_anti ρ (Finset.empty_subset {i}))⟩ =
        sectionMk (freeSubquotient (ConeSpace N) ι) (a i)
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, sectionMk_eq_zero_iff]
    refine isHomSection_of_eqOn (freeSubquotient (ConeSpace N) ι).coherent_N
      (U := puncture _ ∩ U i) (fun w hw => ⟨hw.1, hKU i hw⟩)
      ((hg.inter (hU i).isOpen (hU i).isCone).sub ((hU i).inter_left isOpen_ne isCone_ne_zero))
      (isHomSection_zero (freeSubquotient (ConeSpace N) ι).coherent_N n (coverSet_subset ρ {i}))
      (hKV i) (hVo i) (hVc i)
      fun w hw j => ?_
    show g j w - (a i).1 j w = 0
    rw [hgV i w hw j, sub_self]
  · exact (z.1.2 s hs).symm

/-- The augmentation is injective: a global section of `𝒪^ι(n)` vanishing on every `K_i`
vanishes (`ρ ≥ 1`). -/
theorem cechAug_free_injective {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) :
    Function.Injective (cechAug (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
  refine (sectionMk_eq_zero_iff (freeSubquotient (ConeSpace N) ι) a).2 ?_
  have hi : ∀ i : Fin (N + 1),
      IsHomSection (freeSubquotient (ConeSpace N) ι).N n (coverSet ρ {i}) a.1 := by
    intro i
    have h := congrFun (congrArg (fun w => w.1.1) hx) {i}
    have h' := (cechAug_coe_apply _ _ {i}).symm.trans h
    rw [if_pos (Finset.card_singleton i)] at h'
    change sectionMk (freeSubquotient (ConeSpace N) ι) ⟨a.1, IsHomSection.mono a.2
      (coverSet_anti ρ (Finset.empty_subset {i}))⟩ = 0 at h'
    exact (sectionMk_eq_zero_iff (freeSubquotient (ConeSpace N) ι) _).1 h'
  obtain ⟨U, hKU, hU, -⟩ := a.2
  refine ⟨U, hKU, hU, fun y hy => ?_⟩
  obtain ⟨i, hyi⟩ := exists_mem_coverSet hρ (hU.subset hy)
  obtain ⟨V, hKV, -, hV⟩ := hi i
  exact hV y (hKV hyi)

theorem cechAug_free_bijective {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℤ) :
    Function.Bijective (cechAug (coverSystem (freeSubquotient (ConeSpace N) ι) n ρ)) :=
  ⟨cechAug_free_injective hρ n, cechAug_free_surjective hρ n⟩

end Gluing

/-! ### Global sections of `𝒪(n)` are homogeneous polynomials -/

section Polynomials

variable {N : ℕ}

theorem eval_smul_of_isHomogeneous {σ : Type*} [Fintype σ] {P : MvPolynomial σ ℂ} {n : ℕ}
    (hP : P.IsHomogeneous n) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (c • x) P = c ^ n * MvPolynomial.eval x P := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hP (MvPolynomial.mem_support_iff.1 hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem differentiable_eval_poly (P : MvPolynomial (Fin (N + 1)) ℂ) :
    Differentiable ℂ (fun z : ConeSpace N => MvPolynomial.eval (fun i => z i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add]
      exact hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable

/-- The tuple (of length one) given by a polynomial. -/
noncomputable def polyTuple (P : MvPolynomial (Fin (N + 1)) ℂ) : Unit → ConeSpace N → ℂ :=
  fun _ z => MvPolynomial.eval (fun i => z i) P

theorem isHomOn_polyTuple {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ} (hP : P.IsHomogeneous n) :
    IsHomOn (puncture (ConeSpace N)) (n : ℤ) (polyTuple P) := by
  refine ⟨isOpen_ne, isCone_ne_zero, subset_rfl,
    fun _ => (differentiable_eval_poly P).differentiableOn, fun z _ c _ _ => ?_⟩
  have h := eval_smul_of_isHomogeneous hP c (fun i => z i)
  have hz : (fun i => (c • z) i) = c • fun i => z i := funext fun i => by simp
  simp only [polyTuple, zpow_natCast]
  rw [hz]
  exact h

/-- A homogeneous polynomial of degree `n` is a global section of `𝒪(n)`. -/
theorem isHomSection_poly {ρ : ℝ} {n : ℕ} {P : MvPolynomial (Fin (N + 1)) ℂ}
    (hP : P.IsHomogeneous n) :
    IsHomSection (structureSheaf N).M (n : ℤ) (coverSet ρ ∅) (polyTuple P) :=
  ⟨puncture _, coverSet_subset ρ ∅, isHomOn_polyTuple hP, fun _ hy j =>
    holAt_of_differentiableOn isOpen_ne ((isHomOn_polyTuple hP).diff j) hy⟩

/-- The global section of `𝒪(n)` defined by a homogeneous polynomial of degree `n`. -/
noncomputable def polySection (ρ : ℝ) (n : ℕ)
    (P : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ n) :
    (coverSystem (structureSheaf N) (n : ℤ) ρ).obj ∅ :=
  sectionMk (structureSheaf N)
    ⟨polyTuple P.1, isHomSection_poly ((MvPolynomial.mem_homogeneousSubmodule n P.1).1 P.2)⟩

/-- **`H⁰(ℙᴺ, 𝒪(n))` is the space of homogeneous polynomials of degree `n`.** For `ρ ≥ 1` and
`n ≥ 0`, every class in `Ȟ⁰` of the Čech complex of `𝒪(n)` for the cover `(K_i)` is the
class of the restrictions of a unique homogeneous polynomial of degree `n`. -/
theorem cechH_zero_structureSheaf {ρ : ℝ} (hρ : 1 ≤ ρ) (n : ℕ)
    (x : cechH (coverSystem (structureSheaf N) (n : ℤ) ρ) 0) :
    ∃! P : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ n,
      cechClass _ 0 (cechAug _ (polySection ρ n P)) = x := by
  have hinj : Function.Injective (fun P : MvPolynomial.homogeneousSubmodule (Fin (N + 1)) ℂ n =>
      cechClass (coverSystem (structureSheaf N) (n : ℤ) ρ) 0
        (cechAug (coverSystem (structureSheaf N) (n : ℤ) ρ) (polySection ρ n P))) := by
    intro P Q hPQ
    have h1 := cechAug_free_injective hρ (n : ℤ)
      (cechClass_injective_zero (coverSystem (structureSheaf N) (n : ℤ) ρ) hPQ)
    simp only [polySection] at h1
    obtain ⟨U, hKU, hU, hzero⟩ := IsHomSection.bot_eq_zero ((sectionMk_eq_iff _ _ _).1 h1)
    have hval : ∀ z : ConeSpace N, z ≠ 0 →
        MvPolynomial.eval (fun i => z i) P.1 = MvPolynomial.eval (fun i => z i) Q.1 := by
      intro z hz
      have := hzero z (hKU (by rw [coverSet_empty]; exact hz)) ()
      change polyTuple P.1 () z - polyTuple Q.1 () z = 0 at this
      simpa [polyTuple, sub_eq_zero] using this
    have hcont : ∀ R : MvPolynomial (Fin (N + 1)) ℂ,
        Continuous (fun z : ConeSpace N => MvPolynomial.eval (fun i => z i) R) :=
      fun R => (differentiable_eval_poly R).continuous
    have hall : (fun z : ConeSpace N => MvPolynomial.eval (fun i => z i) P.1) =
        fun z => MvPolynomial.eval (fun i => z i) Q.1 :=
      (hcont P.1).ext_on (dense_compl_singleton (0 : ConeSpace N)) (hcont Q.1)
        fun z hz => hval z hz
    refine Subtype.ext (MvPolynomial.funext fun v => ?_)
    have := congrFun hall (WithLp.toLp 2 v)
    simpa using this
  refine existsUnique_of_exists_of_unique ?_ fun P Q hP hQ => hinj (hP.trans hQ.symm)
  obtain ⟨ζ, rfl⟩ := cechClass_surjective (coverSystem (structureSheaf N) (n : ℤ) ρ) 0 x
  obtain ⟨g, rfl⟩ := cechAug_free_surjective hρ (n : ℤ) ζ
  induction g using Submodule.Quotient.induction_on with
  | _ a =>
  obtain ⟨U, hKU, hU, -⟩ := a.2
  rw [coverSet_empty] at hKU
  have hUeq : ∀ z : ConeSpace N, z ≠ 0 → z ∈ U := fun z hz => hKU hz
  obtain ⟨P, hPh, hPF⟩ := exists_isHomogeneous_eq_of_homogeneous (m := n)
    (F := a.1 ()) (fun z hz => (hU.diff () z (hUeq z hz)).mono fun w hw => hUeq w hw)
    (fun c z hc hz => by
      have := hU.hom z (hUeq z hz) c hc ()
      rwa [zpow_natCast] at this)
  refine ⟨⟨P, (MvPolynomial.mem_homogeneousSubmodule n P).2 hPh⟩, ?_⟩
  congr 2
  simp only [polySection]
  refine (sectionMk_eq_iff (structureSheaf N) _ a).2 ?_
  have hK : coverSet ρ (∅ : Finset (Fin (N + 1))) ⊆ puncture _ ∩ U := fun w hw => by
    rw [coverSet_empty] at hw
    exact ⟨hw, hKU hw⟩
  refine isHomSection_of_eqOn (structureSheaf N).coherent_N hK
    (((isHomOn_polyTuple hPh).inter hU.isOpen hU.isCone).sub
      (hU.inter_left isOpen_ne isCone_ne_zero))
    (isHomSection_zero (structureSheaf N).coherent_N _ (coverSet_subset ρ ∅))
    (coverSet_subset ρ ∅) isOpen_ne isCone_ne_zero fun w hw j => ?_
  show polyTuple P j w - a.1 j w = 0
  rw [sub_eq_zero]
  exact (hPF w hw).symm

end Polynomials

end SGPT.GAGA.PN
