import SGPT.GAGA.CoreCTheoremB
import SGPT.GAGA.CoreCGraph
import SGPT.GAGA.PNSections

/-!
# Theorem B on compact Reinhardt Laurent polyhedra

Infrastructure of lane SERRE-CORE3 (Serre's GAGA, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), step M2.6 of the plan in
`blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core3.tex`), delivering the
statement `AffineSectionsDecompose` requested by lane SERRE-PN (`claude-serre-pn.tex`, paragraph
"Interface with SERRE-CORE2"; stated as `SGPT.GAGA.PN.AffineSectionsDecompose` by lane SERRE-PN2,
the wrapper is `CoreCPN2Bridge`).
Sources: Oka's embedding of analytic polyhedra (Gunning--Rossi, *Analytic functions of several
complex variables*, I.D, VII.A; Hörmander, *An introduction to complex analysis in several
variables*, 7.2--7.4).

Let `D ⊆ ℂᴺ` be open, `g : D → ℂᵐ` holomorphic with closed graph `Φ(D)`, `Φ(w) = (w, g(w))`, and
`C` a box in `ℂ^{N+m}`. On the compact set `K = slice D g C = {w ∈ D : Φ(w) ∈ ∏ C_l}`:

* `exists_extend`: holomorphic functions near `K` are restrictions `F ∘ Φ` of holomorphic
  functions `F` near the box (Theorem B in degree one on the box for the push-forward of the zero
  module, `TheoremB.exists_lift`);
* `exists_decompose_slice`: Theorem B for surjections `P ⊕ Q ↠ P + A(Q)` on `K` (extend `b` and
  `A`, decompose on the box for the push-forwards `push P`, `push Q`, pull back by `Φ`).

The compact Reinhardt Laurent polyhedra of lane SERRE-PN,
`lpoly ρ s = {w : |w_j| ≤ ρ, 1 ≤ ρ|w_k|, |w_j| ≤ ρ|w_k| (k ∈ s)}`, are such slices for
`g(w) = (w_j/w_k, 1/w_k)_{k ∈ s}` and the closed polydisc of radius `ρ` (`slice_lpoly`), whence
`exists_decompose_lpoly`. In the chart `z_i = 1` (`i ∈ s`, `ρ ≥ 1`) the cone sets `coverSet ρ s`
of lane SERRE-PN become `lpoly ρ {m : i.succAbove m ∈ s}` (`preimage_coverSet_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf

namespace SGPT.GAGA.Core.Laurent

open Box TheoremB Graph GermModule

/-! ### Slices of graphs -/

variable {N m : ℕ} {D : Set (EuclideanSpace ℂ (Fin N))}
  {g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ} {C : Fin (N + m) → Set ℂ}

/-- The slice `{w ∈ D : Φ(w) ∈ ∏ C_l}` of the graph `Φ(w) = (w, g(w))` by a box. -/
def slice (D : Set (EuclideanSpace ℂ (Fin N))) (g : Fin m → EuclideanSpace ℂ (Fin N) → ℂ)
    (C : Fin (N + m) → Set ℂ) : Set (EuclideanSpace ℂ (Fin N)) :=
  D ∩ graphMap g ⁻¹' boxSet C

theorem differentiableOn_graphMap (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D) :
    DifferentiableOn ℂ (graphMap g) D := fun _ hw =>
  (differentiableAt_graphMap fun r =>
    (hg r).differentiableAt (hD.mem_nhds hw)).differentiableWithinAt

/-- Preimages under `Φ` of open sets, intersected with an open subset of `D`, are open. -/
theorem isOpen_inter_preimage_graphMap (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    {V : Set (EuclideanSpace ℂ (Fin N))} (hV : IsOpen V) (hVD : V ⊆ D)
    {U : Set (EuclideanSpace ℂ (Fin (N + m)))} (hU : IsOpen U) : IsOpen (V ∩ graphMap g ⁻¹' U) :=
  ((differentiableOn_graphMap hD hg).mono hVD).continuousOn.isOpen_inter_preimage hV hU

/-- The box lies in the open set where `push P` is coherent. -/
theorem box_subset_push_domain {W : Set (EuclideanSpace ℂ (Fin N))} (hKW : slice D g C ⊆ W) :
    boxSet C ⊆ proj ⁻¹' (W ∩ D) ∪ (graphMap g '' D)ᶜ := by
  intro y hy
  by_cases hZ : y ∈ graphMap g '' D
  · obtain ⟨w, hw, rfl⟩ := hZ
    left
    rw [mem_preimage, proj_graphMap]
    exact ⟨hKW ⟨hw, hy⟩, hw⟩
  · exact Or.inr hZ

/-- **Extension from a slice to the box.** Holomorphic functions near `K = slice D g C` are, near
`K`, of the form `F ∘ Φ` with `F` holomorphic near the box. -/
theorem exists_extend (hC : IsBox C) (hD : IsOpen D) (hg : ∀ r, DifferentiableOn ℂ (g r) D)
    (hcl : IsClosed (graphMap g '' D)) {ι : Type} [Fintype ι]
    {f : ι → EuclideanSpace ℂ (Fin N) → ℂ} {V : Set (EuclideanSpace ℂ (Fin N))} (hV : IsOpen V)
    (hKV : slice D g C ⊆ V) (hf : ∀ j, DifferentiableOn ℂ (f j) V) :
    ∃ U : Set (EuclideanSpace ℂ (Fin (N + m))), IsOpen U ∧ boxSet C ⊆ U ∧
      ∃ F : ι → EuclideanSpace ℂ (Fin (N + m)) → ℂ, (∀ j, DifferentiableOn ℂ (F j) U) ∧
        ∃ V' : Set (EuclideanSpace ℂ (Fin N)), IsOpen V' ∧ slice D g C ⊆ V' ∧
          ∀ w ∈ V', ∀ j, F j (graphMap g w) = f j w := by
  classical
  set Z := graphMap g '' D with hZdef
  set Ω := proj ⁻¹' (univ ∩ D) ∪ Zᶜ with hΩdef
  have hM : (push D g (bot (EuclideanSpace ℂ (Fin N)) ι)).IsCoherentOn Ω :=
    push_isCoherentOn hD hg hcl isOpen_univ (bot_isCoherentOn univ)
  have hΩ : IsOpen Ω :=
    ((isOpen_univ.inter hD).preimage continuous_proj).union hcl.isOpen_compl
  have hCΩ : boxSet C ⊆ Ω := box_subset_push_domain fun _ _ => mem_univ _
  set U : Bool → Set (EuclideanSpace ℂ (Fin (N + m))) := fun a =>
    cond a (proj ⁻¹' (V ∩ D)) Zᶜ with hUdef
  set s : Bool → ι → EuclideanSpace ℂ (Fin (N + m)) → ℂ := fun a =>
    cond a (fun j y => f j (proj y)) fun _ _ => 0 with hsdef
  have hU : ∀ a, IsOpen (U a) := by
    intro a
    cases a
    · exact hcl.isOpen_compl
    · exact (hV.inter hD).preimage continuous_proj
  have hcov : boxSet C ⊆ ⋃ a, U a := by
    intro y hy
    by_cases hZ : y ∈ Z
    · obtain ⟨w, hw, rfl⟩ := hZ
      refine mem_iUnion.2 ⟨true, ?_⟩
      show proj (graphMap g w) ∈ V ∩ D
      rw [proj_graphMap]
      exact ⟨hKV ⟨hw, hy⟩, hw⟩
    · exact mem_iUnion.2 ⟨false, hZ⟩
  have hs : ∀ a j, DifferentiableOn ℂ (s a j) (U a) := by
    intro a j
    cases a
    · exact differentiableOn_const _
    · exact (hf j).comp differentiable_proj.differentiableOn fun y hy => hy.1
  have hcoc : ∀ a b, ∀ y ∈ U a ∩ U b,
      (push D g (bot (EuclideanSpace ℂ (Fin N)) ι)).mem y (fun j z => s a j z - s b j z) := by
    intro a b y hy
    refine ⟨fun j => (holAt_of_differentiableOn (hU a) (hs a j) hy.1).sub
      (holAt_of_differentiableOn (hU b) (hs b j) hy.2), fun hyZ => ?_⟩
    cases a <;> cases b
    · exact fun j => Eventually.of_forall fun w => by simp
    · exact absurd hyZ hy.1
    · exact absurd hyZ hy.2
    · exact fun j => Eventually.of_forall fun w => by simp
  obtain ⟨V₁, hV₁, hCV₁, G, hG, hGs⟩ := exists_lift hC hΩ hCΩ hM U hU hcov s hs hcoc
  refine ⟨V₁, hV₁, hCV₁, G, hG, (V ∩ D) ∩ graphMap g ⁻¹' V₁,
    isOpen_inter_preimage_graphMap hD hg (hV.inter hD) inter_subset_right hV₁,
    fun w hw => ⟨⟨hKV hw, hw.1⟩, hCV₁ hw.2⟩, fun w hw j => ?_⟩
  have hmem : graphMap g w ∈ V₁ ∩ U true := by
    refine ⟨hw.2, ?_⟩
    show proj (graphMap g w) ∈ V ∩ D
    rw [proj_graphMap]
    exact hw.1
  have h := (hGs true (graphMap g w) hmem).2 (mem_image_of_mem _ hw.1.2) j
  have h' := h.eq_of_nhds
  simp only [hsdef, cond_true, proj_graphMap] at h'
  exact sub_eq_zero.1 h'

/-- **Theorem B for surjections on slices of graphs.** -/
theorem exists_decompose_slice (hC : IsBox C) (hD : IsOpen D)
    (hg : ∀ r, DifferentiableOn ℂ (g r) D) (hcl : IsClosed (graphMap g '' D)) {κ ι : Type}
    [Fintype κ] [Fintype ι] {P : GermModule (EuclideanSpace ℂ (Fin N)) κ}
    {Q : GermModule (EuclideanSpace ℂ (Fin N)) ι} {W : Set (EuclideanSpace ℂ (Fin N))}
    (hW : IsOpen W) (hKW : slice D g C ⊆ W) (hP : P.IsCoherentOn W) (hQ : Q.IsCoherentOn W)
    {A : κ → ι → EuclideanSpace ℂ (Fin N) → ℂ} (hA : ∀ i j, DifferentiableOn ℂ (A i j) W)
    {b : κ → EuclideanSpace ℂ (Fin N) → ℂ} {V₀ : Set (EuclideanSpace ℂ (Fin N))}
    (hV₀ : IsOpen V₀) (hKV₀ : slice D g C ⊆ V₀) (hb : ∀ y ∈ V₀, (P.sup (Q.map A)).mem y b) :
    ∃ V : Set (EuclideanSpace ℂ (Fin N)), IsOpen V ∧ slice D g C ⊆ V ∧
      ∃ (p : κ → EuclideanSpace ℂ (Fin N) → ℂ) (a : ι → EuclideanSpace ℂ (Fin N) → ℂ),
        (∀ j, DifferentiableOn ℂ (p j) V) ∧ (∀ j, DifferentiableOn ℂ (a j) V) ∧
        (∀ y ∈ V, P.mem y p) ∧ (∀ y ∈ V, Q.mem y a) ∧
        ∀ z ∈ V, ∀ j, b j z = p j z + matApply A a j z := by
  classical
  set K := slice D g C with hKdef
  set W₁ := W ∩ V₀ ∩ D with hW₁def
  have hW₁ : IsOpen W₁ := (hW.inter hV₀).inter hD
  have hKW₁ : K ⊆ W₁ := fun w hw => ⟨⟨hKW hw, hKV₀ hw⟩, hw.1⟩
  have hNc : (P.sup (Q.map A)).IsCoherentOn W :=
    hP.sup (hQ.map fun x hx i j => holAt_of_differentiableOn hW (hA i j) hx)
  have hbd : ∀ j, DifferentiableOn ℂ (b j) W₁ := fun j z hz =>
    ((hNc z hz.1.1).holTupleAt_of_mem (hb z hz.1.2) j).differentiableAt.differentiableWithinAt
  -- extend `b` and `A` to the box
  obtain ⟨Ub, hUb, hCUb, bt, hbt, Vb, hVb, hKVb, hbteq⟩ :=
    exists_extend hC hD hg hcl hW₁ hKW₁ hbd
  obtain ⟨UA, hUA, hCUA, At', hAt', VA, hVA, hKVA, hAteq⟩ :=
    exists_extend (ι := κ × ι) (f := fun q => A q.1 q.2) hC hD hg hcl hW₁ hKW₁
      fun q => (hA q.1 q.2).mono fun z hz => hz.1.1
  set At : κ → ι → EuclideanSpace ℂ (Fin (N + m)) → ℂ := fun i j => At' (i, j) with hAtdef
  set V₁ := W₁ ∩ Vb ∩ VA with hV₁def
  have hV₁ : IsOpen V₁ := (hW₁.inter hVb).inter hVA
  have hKV₁ : K ⊆ V₁ := fun w hw => ⟨⟨hKW₁ hw, hKVb hw⟩, hKVA hw⟩
  have hV₁W : V₁ ⊆ W := fun z hz => hz.1.1.1.1
  set Ω := (proj ⁻¹' (V₁ ∩ D) ∪ (graphMap g '' D)ᶜ) ∩ Ub ∩ UA with hΩdef
  have hΩ : IsOpen Ω :=
    ((((hV₁.inter hD).preimage continuous_proj).union hcl.isOpen_compl).inter hUb).inter hUA
  have hCΩ : boxSet C ⊆ Ω := fun y hy =>
    ⟨⟨box_subset_push_domain hKV₁ hy, hCUb hy⟩, hCUA hy⟩
  have hPt : (push D g P).IsCoherentOn Ω :=
    (push_isCoherentOn hD hg hcl hV₁ (hP.mono hV₁W)).mono fun y hy => hy.1.1
  have hQt : (push D g Q).IsCoherentOn Ω :=
    (push_isCoherentOn hD hg hcl hV₁ (hQ.mono hV₁W)).mono fun y hy => hy.1.1
  have hAth : ∀ i j, DifferentiableOn ℂ (At i j) Ω := fun i j =>
    (hAt' (i, j)).mono fun y hy => hy.2
  -- the extension of `b` is a section of `push P + At (push Q)` near the box
  have hbtm : ∀ y ∈ Ω, ((push D g P).sup ((push D g Q).map At)).mem y bt := by
    intro y hy
    have hbty : HolTupleAt bt y := fun j => holAt_of_differentiableOn hUb (hbt j) hy.1.2
    have hAty : ∀ i j, HolAt (At i j) y := fun i j =>
      holAt_of_differentiableOn hUA (hAt' (i, j)) hy.2
    by_cases hZ : y ∈ graphMap g '' D
    · obtain ⟨w, hwD, rfl⟩ := hZ
      have hwV₁ : w ∈ V₁ := by
        rcases hy.1.1 with h | h
        · rw [mem_preimage, proj_graphMap] at h; exact h.1
        · exact absurd (mem_image_of_mem _ hwD) h
      obtain ⟨p, q', hp, ⟨a, ha, haq⟩, hpq⟩ := hb w hwV₁.1.1.1.2
      have hah : HolTupleAt a w := (hQ w (hV₁W hwV₁)).holTupleAt_of_mem ha
      have hpw : HolTupleAt (fun j z => a j (proj z)) (graphMap g w) := fun i =>
        holAt_comp (by rw [proj_graphMap]; exact hah i)
          (Eventually.of_forall fun z => differentiable_proj z)
      refine ⟨fun j z => bt j z - matApply At (fun i z => a i (proj z)) j z,
        fun j z => matApply At (fun i z => a i (proj z)) j z, ⟨fun j => ?_, fun _ => ?_⟩,
        ⟨fun i z => a i (proj z), ⟨hpw, fun _ => ?_⟩, fun j => EventuallyEq.rfl⟩,
        fun j => Eventually.of_forall fun z => (sub_add_cancel _ _).symm⟩
      · exact (hbty j).sub (HolAt.fintype_sum fun i => (hAty j i).mul (hpw i))
      · rw [proj_graphMap]
        refine (hP w (hV₁W hwV₁)).congr_mem hp fun j => ?_
        have hnear : ∀ᶠ w' in 𝓝 w, w' ∈ Vb ∩ VA := (hVb.inter hVA).mem_nhds ⟨hwV₁.1.2, hwV₁.2⟩
        filter_upwards [hnear, hpq j, haq j] with w' hw' h1 h2
        have h1' : b j w' = p j w' + q' j w' := h1
        have h2' : q' j w' = matApply A a j w' := h2
        have hS : ∑ i, At' (j, i) (graphMap g w') * a i w' = ∑ i, A j i w' * a i w' :=
          Finset.sum_congr rfl fun i _ => by rw [hAteq w' hw'.2 (j, i)]
        simp only [proj_graphMap, matApply, hAtdef]
        rw [hbteq w' hw'.1 j, h1', h2']
        simp only [matApply]
        rw [hS, add_sub_cancel_right]
      · simpa only [proj_graphMap] using ha
    · refine ⟨bt, fun _ _ => 0, ⟨hbty, fun h => absurd h hZ⟩,
        ⟨fun _ _ => 0, ⟨fun _ => holAt_const 0 y, fun h => absurd h hZ⟩,
          fun i => Eventually.of_forall fun z => by simp [matApply]⟩,
        fun j => Eventually.of_forall fun z => by simp⟩
  obtain ⟨V₂, hV₂, hCV₂, pt, at', hptd, hatd, hptm, hatm, hdec⟩ :=
    exists_decompose hC hΩ hCΩ hPt hQt hAth hΩ hCΩ hbtm
  -- pull back along `Φ`
  have hV : IsOpen (V₁ ∩ graphMap g ⁻¹' V₂) :=
    isOpen_inter_preimage_graphMap hD hg hV₁ (fun z hz => hz.1.1.2) hV₂
  have hΦ : DifferentiableOn ℂ (graphMap g) (V₁ ∩ graphMap g ⁻¹' V₂) :=
    (differentiableOn_graphMap hD hg).mono fun z hz => hz.1.1.1.2
  refine ⟨V₁ ∩ graphMap g ⁻¹' V₂, hV, fun w hw => ⟨hKV₁ hw, hCV₂ hw.2⟩,
    fun j w => pt j (graphMap g w), fun i w => at' i (graphMap g w),
    fun j => (hptd j).comp hΦ fun z hz => hz.2, fun i => (hatd i).comp hΦ fun z hz => hz.2,
    fun w hw => ?_, fun w hw => ?_, fun w hw j => ?_⟩
  · have h := (hptm (graphMap g w) hw.2).2 (mem_image_of_mem _ hw.1.1.1.2)
    rwa [proj_graphMap] at h
  · have h := (hatm (graphMap g w) hw.2).2 (mem_image_of_mem _ hw.1.1.1.2)
    rwa [proj_graphMap] at h
  · have h := hdec (graphMap g w) hw.2 j
    rw [hbteq w hw.1.1.2 j] at h
    rw [h]
    simp only [matApply, hAtdef]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hAteq w hw.1.2 (j, i)]

/-! ### Compact Reinhardt Laurent polyhedra -/

/-- The compact Reinhardt Laurent polyhedron
`{w ∈ ℂᴺ : |w_j| ≤ ρ ∀ j, and 1 ≤ ρ|w_k|, |w_j| ≤ ρ|w_k| ∀ j, for k ∈ s}`. For `s ∋ i` the set
`K_s = {[z] : |z_j| ≤ ρ|z_k|, k ∈ s}` of lane SERRE-PN is, in the chart `z_i = 1`, of this form
(with `s \ {i}`). -/
def lpoly {N : ℕ} (ρ : ℝ) (s : Finset (Fin N)) : Set (EuclideanSpace ℂ (Fin N)) :=
  {w | (∀ j, ‖w j‖ ≤ ρ) ∧ ∀ k ∈ s, 1 ≤ ρ * ‖w k‖ ∧ ∀ j, ‖w j‖ ≤ ρ * ‖w k‖}

/-- Index set of the extra coordinates `w_j / w_k` and `1 / w_k`. -/
abbrev LIdx (N : ℕ) : Type := (Fin N × Fin N) ⊕ Fin N

/-- The extra coordinates: `w_j / w_k` and `1 / w_k` for `k ∈ s`, zero otherwise. -/
noncomputable def lgIdx {N : ℕ} (s : Finset (Fin N)) : LIdx N → EuclideanSpace ℂ (Fin N) → ℂ
  | Sum.inl jk => fun w => if jk.2 ∈ s then w jk.1 / w jk.2 else 0
  | Sum.inr k => fun w => if k ∈ s then (w k)⁻¹ else 0

/-- The equations of the graph of `lgIdx`. -/
def lEqn {N : ℕ} (s : Finset (Fin N)) : LIdx N → EuclideanSpace ℂ (Fin N) → ℂ → Prop
  | Sum.inl jk => fun w u => if jk.2 ∈ s then u * w jk.2 = w jk.1 else u = 0
  | Sum.inr k => fun w u => if k ∈ s then u * w k = 1 else u = 0

/-- The number of extra coordinates. -/
abbrev lm (N : ℕ) : ℕ := Fintype.card (LIdx N)

/-- An enumeration of the extra coordinates. -/
noncomputable def lidx (N : ℕ) : Fin (lm N) ≃ LIdx N :=
  (Fintype.equivFin (LIdx N)).symm

/-- The map `g = (w_j / w_k, 1 / w_k)` of the graph embedding. -/
noncomputable def lg {N : ℕ} (s : Finset (Fin N)) : Fin (lm N) → EuclideanSpace ℂ (Fin N) → ℂ :=
  fun r => lgIdx s (lidx N r)

/-- Its domain `{w : w_k ≠ 0, k ∈ s}`. -/
def lD {N : ℕ} (s : Finset (Fin N)) : Set (EuclideanSpace ℂ (Fin N)) :=
  {w | ∀ k ∈ s, w k ≠ 0}

/-- The closed polydisc of radius `ρ` in `ℂ^{N+m}`. -/
def lC (N : ℕ) (ρ : ℝ) : Fin (N + lm N) → Set ℂ :=
  fun _ => closedBall 0 ρ

theorem isBox_lC (N : ℕ) (ρ : ℝ) : IsBox (lC N ρ) :=
  ⟨fun _ => isCompact_closedBall 0 ρ, fun _ => convex_closedBall 0 ρ⟩

theorem isOpen_lD {N : ℕ} (s : Finset (Fin N)) : IsOpen (lD s) := by
  have : lD s = ⋂ k ∈ s, {w : EuclideanSpace ℂ (Fin N) | w k ≠ 0} := by
    ext w; simp [lD]
  rw [this]
  exact isOpen_biInter_finset fun k _ =>
    isOpen_ne_fun (Cousin.continuous_coord k) continuous_const

theorem differentiableOn_lg {N : ℕ} (s : Finset (Fin N)) (r : Fin (lm N)) :
    DifferentiableOn ℂ (lg s r) (lD s) := by
  intro w hw
  have hc : ∀ l : Fin N, DifferentiableAt ℂ (fun x : EuclideanSpace ℂ (Fin N) => x l) w :=
    fun l => (EuclideanSpace.proj l : EuclideanSpace ℂ (Fin N) →L[ℂ] ℂ).differentiableAt
  unfold lg
  rcases lidx N r with ⟨j, k⟩ | k
  · by_cases hk : k ∈ s
    · simp only [lgIdx, if_pos hk, div_eq_mul_inv]
      exact ((hc j).fun_mul ((hc k).fun_inv (hw k hk))).differentiableWithinAt
    · simp only [lgIdx, if_neg hk]
      exact differentiableWithinAt_const _
  · by_cases hk : k ∈ s
    · simp only [lgIdx, if_pos hk]
      exact ((hc k).inv (hw k hk)).differentiableWithinAt
    · simp only [lgIdx, if_neg hk]
      exact differentiableWithinAt_const _

theorem lEqn_lgIdx {N : ℕ} {s : Finset (Fin N)} {w : EuclideanSpace ℂ (Fin N)} (hw : w ∈ lD s)
    (x : LIdx N) : lEqn s x w (lgIdx s x w) := by
  rcases x with ⟨j, k⟩ | k
  · by_cases hk : k ∈ s
    · simp only [lEqn, lgIdx, if_pos hk]
      exact div_mul_cancel₀ _ (hw k hk)
    · simp only [lEqn, lgIdx, if_neg hk]
  · by_cases hk : k ∈ s
    · simp only [lEqn, lgIdx, if_pos hk]
      exact inv_mul_cancel₀ (hw k hk)
    · simp only [lEqn, lgIdx, if_neg hk]

theorem mem_lD_of_lEqn {N : ℕ} {s : Finset (Fin N)} {w : EuclideanSpace ℂ (Fin N)}
    {u : LIdx N → ℂ} (h : ∀ x, lEqn s x w (u x)) : w ∈ lD s := by
  intro k hk hwk
  have := h (Sum.inr k)
  simp [lEqn, hk, hwk] at this

theorem eq_lgIdx_of_lEqn {N : ℕ} {s : Finset (Fin N)} {w : EuclideanSpace ℂ (Fin N)}
    (hw : w ∈ lD s) {x : LIdx N} {u : ℂ} (h : lEqn s x w u) : u = lgIdx s x w := by
  rcases x with ⟨j, k⟩ | k
  · by_cases hk : k ∈ s
    · simp only [lEqn, lgIdx, if_pos hk] at h ⊢
      exact eq_div_of_mul_eq (hw k hk) h
    · simp only [lEqn, lgIdx, if_neg hk] at h ⊢
      exact h
  · by_cases hk : k ∈ s
    · simp only [lEqn, lgIdx, if_pos hk] at h ⊢
      exact eq_inv_of_mul_eq_one_left h
    · simp only [lEqn, lgIdx, if_neg hk] at h ⊢
      exact h

/-- The graph of `lg` is the closed algebraic set given by the equations `lEqn`. -/
theorem graph_lg_eq {N : ℕ} (s : Finset (Fin N)) :
    graphMap (lg s) '' lD s =
      {y | ∀ r : Fin (lm N), lEqn s (lidx N r) (proj y) (y (Fin.natAdd N r))} := by
  ext y
  rw [mem_graph_iff]
  constructor
  · rintro ⟨hD, hdef⟩ r
    have := hdef r
    rw [graphDef, sub_eq_zero] at this
    rw [this]
    exact lEqn_lgIdx hD _
  · intro h
    have hD : proj y ∈ lD s := by
      refine mem_lD_of_lEqn (u := fun x => y (Fin.natAdd N ((lidx N).symm x))) fun x => ?_
      simpa using h ((lidx N).symm x)
    refine ⟨hD, fun r => ?_⟩
    rw [graphDef, sub_eq_zero]
    exact eq_lgIdx_of_lEqn hD (h r)

theorem isClosed_graph_lg {N : ℕ} (s : Finset (Fin N)) : IsClosed (graphMap (lg s) '' lD s) := by
  rw [graph_lg_eq, ofPred_forall]
  refine isClosed_iInter fun r => ?_
  have hu : Continuous fun y : EuclideanSpace ℂ (Fin (N + lm N)) => y (Fin.natAdd N r) :=
    Cousin.continuous_coord _
  have hc : ∀ k : Fin N, Continuous fun y : EuclideanSpace ℂ (Fin (N + lm N)) => proj y k :=
    fun k => (Cousin.continuous_coord k).comp continuous_proj
  rcases lidx N r with ⟨j, k⟩ | k
  · by_cases hk : k ∈ s
    · simp only [lEqn, hk, if_true]
      exact isClosed_eq (hu.mul (hc k)) (hc j)
    · simp only [lEqn, hk, if_false]
      exact isClosed_eq hu continuous_const
  · by_cases hk : k ∈ s
    · simp only [lEqn, hk, if_true]
      exact isClosed_eq (hu.mul (hc k)) continuous_const
    · simp only [lEqn, hk, if_false]
      exact isClosed_eq hu continuous_const

/-- **The Laurent polyhedron is a slice of the graph of `(w_j/w_k, 1/w_k)` by a closed
polydisc.** -/
theorem slice_lpoly {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (s : Finset (Fin N)) :
    slice (lD s) (lg s) (lC N ρ) = lpoly ρ s := by
  ext w
  simp only [slice, mem_inter_iff, mem_preimage, mem_boxSet, lC, mem_closedBall, dist_zero_right,
    Fin.forall_fin_add, graphMap_castAdd, graphMap_natAdd, lg, lpoly, mem_ofPred_eq]
  simp only [(lidx N).symm.surjective.forall]
  simp only [Equiv.apply_symm_apply, Sum.forall, Prod.forall, lgIdx]
  constructor
  · rintro ⟨hD, hj, hjk, hk⟩
    refine ⟨hj, fun k hks => ⟨?_, fun j => ?_⟩⟩
    · have := hk k
      rw [if_pos hks, norm_inv, inv_le_iff_one_le_mul₀ (norm_pos_iff.2 (hD k hks))] at this
      linarith [mul_comm ρ ‖w k‖]
    · have := hjk j k
      rw [if_pos hks, norm_div, div_le_iff₀ (norm_pos_iff.2 (hD k hks))] at this
      linarith [mul_comm ρ ‖w k‖]
  · rintro ⟨hj, hk⟩
    have hD : w ∈ lD s := fun k hks hwk => by
      have := (hk k hks).1
      rw [hwk, norm_zero, mul_zero] at this
      linarith
    refine ⟨hD, hj, fun j k => ?_, fun k => ?_⟩
    · split_ifs with hks
      · rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (hD k hks))]
        linarith [(hk k hks).2 j, mul_comm ρ ‖w k‖]
      · simpa using hρ
    · split_ifs with hks
      · rw [norm_inv, inv_le_iff_one_le_mul₀ (norm_pos_iff.2 (hD k hks))]
        linarith [(hk k hks).1, mul_comm ρ ‖w k‖]
      · simpa using hρ

/-- **Theorem B for surjections on compact Reinhardt Laurent polyhedra** (the statement
`AffineSectionsDecompose (lpoly ρ s)` requested by lane SERRE-PN, see
`SGPT.GAGA.PN.AffineSectionsDecompose` of lane SERRE-PN2 and `CoreCPN2Bridge`). Let `ρ ≥ 0`,
`P ⊆ 𝒪^κ`, `Q ⊆ 𝒪^ι` coherent on an open `W ⊇ L = lpoly ρ s` and `A` a `κ × ι` matrix
holomorphic on `W`. Every section `b` of `P + A(Q)` on an open `U ⊇ L` is `p + A a` on an open
`V ⊇ L`, with `p`, `a` holomorphic sections of `P`, `Q` on `V`. -/
theorem exists_decompose_lpoly {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (s : Finset (Fin N)) {κ ι : Type}
    [Fintype κ] [Fintype ι] {P : GermModule (EuclideanSpace ℂ (Fin N)) κ}
    {Q : GermModule (EuclideanSpace ℂ (Fin N)) ι} {W : Set (EuclideanSpace ℂ (Fin N))}
    (hW : IsOpen W) (hLW : lpoly ρ s ⊆ W) (hP : P.IsCoherentOn W) (hQ : Q.IsCoherentOn W)
    {A : κ → ι → EuclideanSpace ℂ (Fin N) → ℂ} (hA : ∀ i j, DifferentiableOn ℂ (A i j) W)
    {b : κ → EuclideanSpace ℂ (Fin N) → ℂ} {U : Set (EuclideanSpace ℂ (Fin N))}
    (hU : IsOpen U) (hLU : lpoly ρ s ⊆ U) (hb : ∀ y ∈ U, (P.sup (Q.map A)).mem y b) :
    ∃ V : Set (EuclideanSpace ℂ (Fin N)), IsOpen V ∧ lpoly ρ s ⊆ V ∧
      ∃ (p : κ → EuclideanSpace ℂ (Fin N) → ℂ) (a : ι → EuclideanSpace ℂ (Fin N) → ℂ),
        (∀ j, DifferentiableOn ℂ (p j) V) ∧ (∀ j, DifferentiableOn ℂ (a j) V) ∧
        (∀ y ∈ V, P.mem y p) ∧ (∀ y ∈ V, Q.mem y a) ∧
        ∀ z ∈ V, ∀ j, b j z = p j z + matApply A a j z := by
  rw [← slice_lpoly hρ s] at hLW hLU ⊢
  exact exists_decompose_slice (isBox_lC N ρ) (isOpen_lD s) (differentiableOn_lg s)
    (isClosed_graph_lg s) hW hLW hP hQ hA hU hLU hb

/-! ### The sets `K_s` of lane SERRE-PN in an affine chart -/

/-- **`K_s` in the chart `z_i = 1` is a Laurent polyhedron.** For `i ∈ s` and `ρ ≥ 1`, the
points `w ∈ ℂᴺ` whose image `(w_0, …, 1, …, w_{N-1})` (`1` in place `i`) lies in the cone
`coverSet ρ s = {z ≠ 0 : |z_j| ≤ ρ |z_k|, k ∈ s}` of lane SERRE-PN form `lpoly ρ s'` with
`s' = {m : i.succAbove m ∈ s}`. (The map is SERRE-PN2's `chart i`.) -/
theorem preimage_coverSet_eq {N : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) {s : Finset (Fin (N + 1))}
    {i : Fin (N + 1)} (hi : i ∈ s) :
    (fun w : EuclideanSpace ℂ (Fin N) =>
        (WithLp.toLp 2 (Fin.insertNth i (1 : ℂ) fun m => w m) : PN.ConeSpace N)) ⁻¹'
      PN.coverSet ρ s = lpoly ρ (Finset.univ.filter fun m => i.succAbove m ∈ s) := by
  ext w
  simp only [mem_preimage, PN.coverSet, lpoly, mem_ofPred_eq, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun m => ?_, fun k hk => ⟨?_, fun m => ?_⟩⟩
    · have := h i hi (i.succAbove m)
      simpa using this
    · have := h _ hk i
      simpa using this
    · have := h _ hk (i.succAbove m)
      simpa using this
  · rintro ⟨hj, hk⟩
    refine ⟨fun h0 => ?_, fun k hks j => ?_⟩
    · have := congrArg (fun z : PN.ConeSpace N => z i) h0
      simp at this
    · induction k using Fin.succAboveCases i with
      | x =>
        induction j using Fin.succAboveCases i with
        | x => simpa using hρ
        | p m => simpa using hj m
      | p k =>
        have hk' := hk k hks
        induction j using Fin.succAboveCases i with
        | x => simpa using hk'.1
        | p m => simpa using hk'.2 m

/-- The same set is empty for `ρ < 1` and `i ∈ s`. -/
theorem preimage_coverSet_eq_empty {N : ℕ} {ρ : ℝ} (hρ : ρ < 1) {s : Finset (Fin (N + 1))}
    {i : Fin (N + 1)} (hi : i ∈ s) :
    (fun w : EuclideanSpace ℂ (Fin N) =>
        (WithLp.toLp 2 (Fin.insertNth i (1 : ℂ) fun m => w m) : PN.ConeSpace N)) ⁻¹'
      PN.coverSet ρ s = ∅ := by
  ext w
  simp only [mem_preimage, PN.coverSet, mem_ofPred_eq, mem_empty_iff_false, iff_false,
    not_and]
  intro _ h
  have := h i hi i
  simp at this
  linarith

end SGPT.GAGA.Core.Laurent
