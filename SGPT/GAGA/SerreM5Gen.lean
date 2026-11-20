import SGPT.GAGA.SerreM4Chain

/-!
# Serre's theorems on `ℙᴺ`: generation by global sections

Towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), milestone M4.2
(Serre's Theorem A on `ℙᴺ`).

For germ modules `I ⊆ M ⊆ 𝒪^ι` on `ℂ^{N+1} ∖ 0`:

* `GlobSec M m σ`: the tuples `σ_k` are global sections of `M(m)`: holomorphic and homogeneous of
  degree `m` on `ℂ^{N+1} ∖ 0`, with germs in `M` at every point.
* `GenAt M I σ y`: every member of `M_y` is `∑ c_k σ_k` modulo `I_y` (`c_k` holomorphic at `y`).
* `GenOn M I m U`: finitely many global sections of `M(m)` generate `M_y` modulo `I_y` at every
  point `y ∈ U`.

Generation is open (`GenAt.eventually`, using coherence), increasing in the degree
(`GenOn.of_le`: multiply by the coordinates), stable under finite unions (`GenOn.biUnion`) and,
for `ℂ*`-invariant `M, I`, transported along `ℂ*` (`GenAt.smul`). Hence generation near every
point of the unit sphere, in all large degrees, gives generation on `ℂ^{N+1} ∖ 0` in all large
degrees (`exists_genOn_puncture`, compactness of the sphere). With `I = I_{L_d} 𝒪^ι`, points off
`L_d` are trivial (`genAt_of_not_mem_planeL`), so Theorem A for the class `𝒮_d` reduces to
generation at one point of `L_d ∖ 0` in one degree (`serreA_of_ptGen`).

Blueprint: `claude-serre-m5.tex`, node `claude-serre-m5:generation`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-- Combinations at a point are combinations at all nearby points. -/
theorem IsCombinationAt.eventually' {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {ι μ : Type} [Fintype ι] [Fintype μ] {σ : μ → ι → X → ℂ} {x : X} {a : ι → X → ℂ}
    (h : IsCombinationAt σ x a) : ∀ᶠ y in 𝓝 x, IsCombinationAt σ y a := by
  obtain ⟨c, hc, hca⟩ := h
  filter_upwards [eventually_all.2 fun k => (hc k).eventually,
    eventually_all.2 fun j => (hca j).eventuallyEq_nhds] with y h1 h2
  exact ⟨c, h1, h2⟩

variable {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Definitions -/

/-- The tuples `σ_k` are global sections of `M(m)`. -/
def GlobSec (M : GermModule (ConeSpace N) ι) (m : ℤ) {μ : Type}
    (σ : μ → ι → ConeSpace N → ℂ) : Prop :=
  (∀ k, IsHomOn (puncture (ConeSpace N)) m (σ k)) ∧ ∀ k (y : ConeSpace N), y ≠ 0 → M.mem y (σ k)

/-- The `σ_k` generate `M_y` modulo `I_y`. -/
def GenAt (M I : GermModule (ConeSpace N) ι) {μ : Type} [Fintype μ]
    (σ : μ → ι → ConeSpace N → ℂ) (y : ConeSpace N) : Prop :=
  ∀ a, M.mem y a → ∃ c : μ → ConeSpace N → ℂ, (∀ k, HolAt (c k) y) ∧
    I.mem y (fun j z => a j z - ∑ k, c k z * σ k j z)

/-- Finitely many global sections of `M(m)` generate `M` modulo `I` at every point of `U`. -/
def GenOn (M I : GermModule (ConeSpace N) ι) (m : ℤ) (U : Set (ConeSpace N)) : Prop :=
  ∃ (μ : Type) (_ : Fintype μ) (σ : μ → ι → ConeSpace N → ℂ), GlobSec M m σ ∧
    ∀ y ∈ U, GenAt M I σ y

variable {M I : GermModule (ConeSpace N) ι}

/-! ### Elementary properties -/

theorem GenOn.mono_set {m : ℤ} {U V : Set (ConeSpace N)} (h : GenOn M I m U) (hVU : V ⊆ U) :
    GenOn M I m V := by
  obtain ⟨μ, _, σ, hσ, hgen⟩ := h
  exact ⟨μ, inferInstance, σ, hσ, fun y hy => hgen y (hVU hy)⟩

theorem genOn_empty (m : ℤ) : GenOn M I m ∅ :=
  ⟨Empty, inferInstance, fun k => k.elim, ⟨fun k => k.elim, fun k => k.elim⟩,
    fun _ hy => hy.elim⟩

theorem GenOn.union {m : ℤ} {U V : Set (ConeSpace N)} (h₁ : GenOn M I m U)
    (h₂ : GenOn M I m V) : GenOn M I m (U ∪ V) := by
  obtain ⟨μ, _, σ, ⟨hσh, hσM⟩, hσg⟩ := h₁
  obtain ⟨ν, _, τ, ⟨hτh, hτM⟩, hτg⟩ := h₂
  refine ⟨μ ⊕ ν, inferInstance, Sum.elim σ τ, ⟨fun k => ?_, fun k => ?_⟩, fun y hy => ?_⟩
  · rcases k with k | k
    · exact hσh k
    · exact hτh k
  · rcases k with k | k
    · exact hσM k
    · exact hτM k
  · intro a ha
    rcases hy with hy | hy
    · obtain ⟨c, hc, hca⟩ := hσg y hy a ha
      refine ⟨Sum.elim c 0, fun k => ?_, ?_⟩
      · rcases k with k | k
        · exact hc k
        · exact holAt_const 0 y
      · simpa [Fintype.sum_sum_type] using hca
    · obtain ⟨c, hc, hca⟩ := hτg y hy a ha
      refine ⟨Sum.elim 0 c, fun k => ?_, ?_⟩
      · rcases k with k | k
        · exact holAt_const 0 y
        · exact hc k
      · simpa [Fintype.sum_sum_type] using hca

theorem GenOn.biUnion {α : Type*} {m : ℤ} (t : Finset α) (U : α → Set (ConeSpace N))
    (h : ∀ i ∈ t, GenOn M I m (U i)) : GenOn M I m (⋃ i ∈ t, U i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using genOn_empty m
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (Finset.mem_insert_self a t)).union
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Openness -/

/-- **Generation is open**: generation of `M_x` modulo `I_x` by the `σ_k` propagates to nearby
points, `M` and `I` being coherent at `x`. -/
theorem GenAt.eventually {μ : Type} [Fintype μ] {σ : μ → ι → ConeSpace N → ℂ}
    {x : ConeSpace N} (hM : M.CoherentAt x) (hI : I.CoherentAt x) (h : GenAt M I σ x) :
    ∀ᶠ y in 𝓝 x, GenAt M I σ y := by
  classical
  obtain ⟨U₁, hU₁, hxU₁, μ₁, _, τ, hτ⟩ := hM
  obtain ⟨U₂, hU₂, hxU₂, ν, _, ρ, hρ⟩ := hI
  have hcomb : ∀ l, IsCombinationAt (Sum.elim σ ρ) x (τ l) := by
    intro l
    obtain ⟨c, hc, hca⟩ := h _ ((hτ.2 x hxU₁ _).2 (isCombinationAt_gen τ x l))
    refine GermModule.isCombinationAt_sumElim_iff.2 ⟨fun j z => ∑ k, c k z * σ k j z,
      fun j z => τ l j z - ∑ k, c k z * σ k j z, ⟨c, hc, fun _ => EventuallyEq.rfl⟩,
      (hρ.2 x hxU₂ _).1 hca, fun j => Eventually.of_forall fun z => ?_⟩
    simp only
    ring
  filter_upwards [hU₁.mem_nhds hxU₁, hU₂.mem_nhds hxU₂,
    eventually_all.2 fun l => IsCombinationAt.eventually' (hcomb l)] with y hy₁ hy₂ hy
  intro a ha
  obtain ⟨b, e, ⟨c, hc, hcb⟩, he, hbe⟩ :=
    GermModule.isCombinationAt_sumElim_iff.1 (Core.IsCombinationAt.trans ((hτ.2 y hy₁ a).1 ha) hy)
  refine ⟨c, hc, (hρ.2 y hy₂ _).2 (Core.IsCombinationAt.congr he fun j => ?_)⟩
  filter_upwards [hbe j, hcb j] with z h1 h2
  rw [h1, h2]
  ring

/-! ### Raising the degree -/

/-- Multiplying the generators by all coordinates raises the degree by one. -/
theorem sum_coord_mul {μ : Type} [Fintype μ] (l : Fin (N + 1)) (c : μ → ConeSpace N → ℂ)
    (σ : μ → ι → ConeSpace N → ℂ) {z : ConeSpace N} (hz : z l ≠ 0) (j : ι) :
    ∑ p : Fin (N + 1) × μ, (if p.1 = l then c p.2 z * (z l)⁻¹ else 0) * (z p.1 * σ p.2 j z) =
      ∑ k, c k z * σ k j z := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single l]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    field_simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun k _ => by rw [if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem GenOn.succ (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hI : I.IsCoherentOn (puncture (ConeSpace N))) {m : ℤ} {U : Set (ConeSpace N)}
    (hU : U ⊆ puncture (ConeSpace N)) (h : GenOn M I m U) : GenOn M I (m + 1) U := by
  classical
  obtain ⟨μ, _, σ, ⟨hσh, hσM⟩, hgen⟩ := h
  refine ⟨Fin (N + 1) × μ, inferInstance, fun p j z => z p.1 * σ p.2 j z,
    ⟨fun p => ?_, fun p y hy => ?_⟩, fun y hy => ?_⟩
  · have := (hσh p.2).matApply (isHomMatrix_scalMat (ι := ι) p.1)
    rwa [matApply_scalMat] at this
  · exact (hM y hy).smul_mem (Eventually.of_forall fun z => differentiable_coord p.1 z)
      (hσM p.2 y hy)
  · obtain ⟨l, hyl⟩ := exists_mem_coverSet le_rfl (hU hy)
    have hl : y l ≠ 0 := coord_ne_zero_of_mem_coverSet (Finset.mem_singleton_self l) hyl
    intro a ha
    obtain ⟨c, hc, hca⟩ := hgen y hy a ha
    have hzl : HolAt (fun z : ConeSpace N => z l) y :=
      Eventually.of_forall fun z => differentiable_coord l z
    refine ⟨fun p z => if p.1 = l then c p.2 z * (z l)⁻¹ else 0, fun p => ?_, ?_⟩
    · by_cases hp : p.1 = l
      · simp only [hp, if_true]
        exact (hc p.2).mul (hzl.inv hl)
      · simp only [hp, if_false]
        exact holAt_const 0 y
    · refine (hI y (hU hy)).congr_mem hca fun j => ?_
      filter_upwards [hzl.continuousAt.eventually_ne hl] with z hz
      rw [sum_coord_mul l c σ hz j]

theorem GenOn.of_le (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hI : I.IsCoherentOn (puncture (ConeSpace N))) {U : Set (ConeSpace N)}
    (hU : U ⊆ puncture (ConeSpace N)) {m m' : ℤ} (hmm : m ≤ m') (h : GenOn M I m U) :
    GenOn M I m' U := by
  induction m', hmm using Int.leInduction with
  | base => exact h
  | succ n _ ih => exact ih.succ hM hI hU

/-- Generation in one degree at a point gives generation near the point in all larger
degrees. -/
theorem exists_nhds_genOn (hM : M.IsCoherentOn (puncture (ConeSpace N)))
    (hI : I.IsCoherentOn (puncture (ConeSpace N))) {x : ConeSpace N} (hx : x ≠ 0) {m₀ : ℤ}
    (h : GenOn M I m₀ {x}) : ∃ U ∈ 𝓝 x, ∀ m ≥ m₀, GenOn M I m U := by
  obtain ⟨μ, _, σ, hσ, hgen⟩ := h
  have hev := GenAt.eventually (hM x hx) (hI x hx) (hgen x (Set.mem_singleton x))
  exact ⟨{y | GenAt M I σ y ∧ y ≠ 0}, hev.and (isOpen_ne.mem_nhds hx), fun m hm =>
    GenOn.of_le hM hI (fun y hy => hy.2) hm ⟨μ, inferInstance, σ, hσ, fun y hy => hy.1⟩⟩

/-! ### Transport along `ℂ*` and compactness -/

/-- Generation is transported along `ℂ*` for invariant `M` and `I`. -/
theorem GenAt.smul (hMi : IsConeInvariant M) (hIi : IsConeInvariant I)
    (hIc : I.IsCoherentOn (puncture (ConeSpace N))) {m : ℤ} {μ : Type} [Fintype μ]
    {σ : μ → ι → ConeSpace N → ℂ} (hσ : ∀ k, IsHomOn (puncture (ConeSpace N)) m (σ k))
    {y : ConeSpace N} (hy : y ≠ 0) {c : ℂ} (hc : c ≠ 0) (h : GenAt M I σ y) :
    GenAt M I σ (c • y) := by
  intro a ha
  have ha' : M.mem y (fun j z => a j (c • z)) := by
    rw [hMi y hy c hc]
    have e : (fun j z => (fun j z => a j (c • z)) j (c⁻¹ • z)) = a := by
      funext j z
      simp only [smul_inv_smul₀ hc]
    rw [e]
    exact ha
  obtain ⟨e, he, hea⟩ := h _ ha'
  have h1 := (hIi y hy c hc _).1 hea
  have hcy : c • y ≠ 0 := smul_ne_zero hc hy
  refine ⟨fun k z => e k (c⁻¹ • z) * (c⁻¹) ^ m, fun k => ?_, (hIc _ hcy).congr_mem h1 fun j => ?_⟩
  · have h2 : HolAt (e k) (c⁻¹ • (c • y)) := by
      rw [inv_smul_smul₀ hc]
      exact he k
    exact (h2.comp (continuous_const_smul c⁻¹) fun _ => differentiableAt_id.const_smul c⁻¹).mul
      (holAt_const _ _)
  · filter_upwards [isOpen_ne.mem_nhds hcy] with z hz
    simp only [smul_inv_smul₀ hc]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hσ k).hom z hz c⁻¹ (inv_ne_zero hc) j]
    ring

theorem GenOn.puncture_of_sphere (hMi : IsConeInvariant M) (hIi : IsConeInvariant I)
    (hIc : I.IsCoherentOn (puncture (ConeSpace N))) {m : ℤ}
    (h : GenOn M I m (sphere (0 : ConeSpace N) 1)) : GenOn M I m (puncture (ConeSpace N)) := by
  obtain ⟨μ, _, σ, hσ, hgen⟩ := h
  refine ⟨μ, inferInstance, σ, hσ, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := hy
  have hn : ((‖y‖ : ℂ)) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hy0
  have hy1 : ((‖y‖ : ℂ))⁻¹ • y ∈ sphere (0 : ConeSpace N) 1 :=
    mem_sphere_zero_iff_norm.2 (norm_normalize hy0)
  have := GenAt.smul hMi hIi hIc hσ.1 (smul_ne_zero (inv_ne_zero hn) hy0) hn (hgen _ hy1)
  rwa [smul_inv_smul₀ hn] at this

/-- **Compactness**: generation near every point of the unit sphere in all large degrees gives
generation on `ℂ^{N+1} ∖ 0` in all large degrees. -/
theorem exists_genOn_puncture (hMi : IsConeInvariant M) (hIi : IsConeInvariant I)
    (hIc : I.IsCoherentOn (puncture (ConeSpace N)))
    (h : ∀ x ∈ sphere (0 : ConeSpace N) 1, ∃ m₀ : ℤ, ∃ U ∈ 𝓝 x, ∀ m ≥ m₀, GenOn M I m U) :
    ∃ m₀ : ℤ, ∀ m ≥ m₀, GenOn M I m (puncture (ConeSpace N)) := by
  classical
  choose! m₀ U hU hgen using h
  obtain ⟨t, hts, ht⟩ := (isCompact_sphere (0 : ConeSpace N) 1).elim_nhds_subcover U hU
  obtain ⟨B, hB⟩ := (t.image m₀).exists_le
  refine ⟨B, fun m hm => GenOn.puncture_of_sphere hMi hIi hIc
    ((GenOn.biUnion t U fun x hx => hgen x (hts x hx) m ?_).mono_set ht)⟩
  exact le_trans (hB _ (Finset.mem_image_of_mem _ hx)) hm

/-! ### Points off `L_d` and the reduction to one point -/

/-- Off `L_d` every germ lies in `I_{L_d} 𝒪^ι`. -/
theorem genAt_of_not_mem_planeL {d : ℕ} {y : ConeSpace N} (hM : M.CoherentAt y)
    (hy : y ∉ planeL d) {μ : Type} [Fintype μ] (σ : μ → ι → ConeSpace N → ℂ) :
    GenAt M (Idm d ι) σ y := by
  intro a ha
  refine ⟨fun _ _ => 0, fun _ => holAt_const 0 y, ?_⟩
  rw [mem_Idm_iff]
  refine ⟨fun j => ?_, ?_⟩
  · simpa using hM.holTupleAt_of_mem ha j
  · have hy' : ¬ ∀ l : Fin (N + 1), d < l.1 → y l = 0 := hy
    push Not at hy'
    obtain ⟨l, hl, hyl⟩ := hy'
    have hc : HolAt (fun z : ConeSpace N => z l) y :=
      Eventually.of_forall fun z => differentiable_coord l z
    filter_upwards [hc.continuousAt.eventually_ne hyl] with z hz hzL
    exact absurd (hzL l hl) hz

/-- Generation at the point `x` in some degree, for every member of `𝒮_d`. -/
def PtGen (N d : ℕ) (x : ConeSpace N) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : GermModule (ConeSpace N) ι), InS d M →
    ∃ m₀ : ℤ, GenOn M (Idm d ι) m₀ {x}

/-- **Theorem A for the class `𝒮_d`**: every invariant subsheaf `M/I_{L_d}` of `𝒪_{L_d}^ι` has
`M(m)` generated modulo `I_{L_d}` by global sections for all `m ≫ 0`. -/
def SerreA (N d : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : GermModule (ConeSpace N) ι), InS d M →
    ∃ m₀ : ℤ, ∀ m ≥ m₀, GenOn M (Idm d ι) m (puncture (ConeSpace N))

/-- **Reduction to points of `L_d`**: pointwise generation at the points of `L_d ∖ 0` gives
Theorem A for `𝒮_d`. -/
theorem serreA_of_ptGen {d : ℕ} (h : ∀ x : ConeSpace N, x ∈ planeL d → x ≠ 0 → PtGen N d x) :
    SerreA N d := by
  intro ι _ _ M hS
  refine exists_genOn_puncture hS.inv (isConeInvariant_Idm d) (Idm_isCoherentOn_puncture d)
    fun x hx => ?_
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  have hgen : ∃ m₀ : ℤ, GenOn M (Idm d ι) m₀ {x} := by
    by_cases hxL : x ∈ planeL d
    · exact h x hxL hx0 ι M hS
    · refine ⟨0, Empty, inferInstance, fun k => k.elim, ⟨fun k => k.elim, fun k => k.elim⟩,
        fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.1 hy]
      exact genAt_of_not_mem_planeL (hS.coh x hx0) hxL _
  obtain ⟨m₀, hm₀⟩ := hgen
  obtain ⟨U, hU, hgen⟩ := exists_nhds_genOn hS.coh (Idm_isCoherentOn_puncture d) hx0 hm₀
  exact ⟨m₀, U, hU, hgen⟩

end SGPT.GAGA.PN
