import SGPT.GAGA.CoreCPN2Bridge

/-!
# Serre's theorems on `ℙᴺ`, part 1: growing `0`-cocycles

Infrastructure towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145), plan
node PN7/M3.4 of `blueprint/src/claude-serre-pn.tex` and milestone M4 of
`blueprint/src/claude-serre-core.tex`; blueprint `claude-serre-m34.tex`.

A `0`-cocycle of a coherent sheaf `𝓕 = M/N` on `ℙᴺ` for the closed cover
`K_i(ρ) = {|z_j| ≤ ρ |z_i|}` (sections `g_i` of `M(n)` near `K_i(ρ)` with `g_k - g_i ∈ N` near
`K_i(ρ) ∩ K_k(ρ)`) is, modulo `N`, the restriction of a `0`-cocycle for the larger cover
`K(ρ')`, `ρ ≤ ρ'` (`exists_grow_zero`). In the chart `z_j = 1` the set `K_j(ρ')` is the closed
polydisc of radius `ρ'` (`chart_preimage_coverSet_self`), a box of lane SERRE-CORE3; the `g_k`
restricted to the pieces `K_j(ρ') ∩ K_k(ρ)` form a section of `𝒪^ι/N` over it, which lifts by
Theorem B in degree one on boxes (`Core.TheoremB.exists_lift`) after shrinking the closed cover
to an open one (`exists_open_shrink`). The lift is rehomogenized (`rehom`, `mem_rehom`).

This is the cover comparison in degree `0` which the Cartan--Serre finiteness argument needs
(`SerreM1Banach`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Shrinking a finite closed cover -/

/-- **Shrinking.** Let `A_k` be finitely many compact sets in a Hausdorff space, `O_k ⊇ A_k`
open, and `P_{kl} ⊇ A_k ∩ A_l` open. Then there are open `U_k` with `A_k ⊆ U_k ⊆ O_k` and
`U_k ∩ U_l ⊆ P_{kl}`. -/
theorem exists_open_shrink {X : Type*} [TopologicalSpace X] [T2Space X] {α : Type*} [Finite α]
    {A O : α → Set X} {P : α → α → Set X} (hA : ∀ k, IsCompact (A k)) (hO : ∀ k, IsOpen (O k))
    (hAO : ∀ k, A k ⊆ O k) (hP : ∀ k l, IsOpen (P k l)) (hAP : ∀ k l, A k ∩ A l ⊆ P k l) :
    ∃ U : α → Set X, (∀ k, IsOpen (U k)) ∧ (∀ k, A k ⊆ U k) ∧ (∀ k, U k ⊆ O k) ∧
      ∀ k l, U k ∩ U l ⊆ P k l := by
  have hsep : ∀ k l, SeparatedNhds (A k \ P k l) (A l) := fun k l =>
    SeparatedNhds.of_isCompact_isCompact ((hA k).diff (hP k l)) (hA l)
      (Set.disjoint_left.2 fun x hx hxl => hx.2 (hAP k l ⟨hx.1, hxl⟩))
  choose G H hG hH hAG hAH hGH using hsep
  refine ⟨fun k => (O k ∩ ⋂ l, (P k l ∪ G k l)) ∩ ⋂ l, H l k, fun k => ?_, fun k x hx => ?_,
    fun k _ hx => hx.1.1, fun k l x hx => ?_⟩
  · exact ((hO k).inter (isOpen_iInter_of_finite fun l => (hP k l).union (hG k l))).inter
      (isOpen_iInter_of_finite fun l => hH l k)
  · refine ⟨⟨hAO k hx, mem_iInter.2 fun l => ?_⟩, mem_iInter.2 fun l => hAH l k hx⟩
    by_cases hxP : x ∈ P k l
    · exact Or.inl hxP
    · exact Or.inr (hAG k l ⟨hx, hxP⟩)
  · rcases mem_iInter.1 hx.1.1.2 l with h1 | h1
    · exact h1
    · exact absurd (mem_iInter.1 hx.2.2 k) (Set.disjoint_left.1 (hGH k l) h1)

variable {N : ℕ}

/-! ### The cover sets in a chart -/

theorem coverSet_mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') (s : Finset (Fin (N + 1))) :
    coverSet ρ s ⊆ coverSet ρ' s :=
  fun _ hz => ⟨hz.1, fun i hi j => (hz.2 i hi j).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg _))⟩

theorem coord_ne_zero_of_mem_coverSet {ρ : ℝ} {s : Finset (Fin (N + 1))} {i : Fin (N + 1)}
    (hi : i ∈ s) {z : ConeSpace N} (hz : z ∈ coverSet ρ s) : z i ≠ 0 := by
  intro h0
  apply hz.1
  ext j
  have := hz.2 i hi j
  rw [h0, norm_zero, mul_zero] at this
  simpa using norm_le_zero_iff.1 this

theorem isClosed_chart_preimage_coverSet (i : Fin (N + 1)) (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    IsClosed (chart i ⁻¹' coverSet ρ s) := by
  obtain ⟨C, hC, hCs⟩ := isClosed_coverSet_inter ρ s
  have : chart i ⁻¹' coverSet ρ s = chart i ⁻¹' C := by
    ext w
    simp only [mem_preimage, hCs, mem_inter_iff]
    exact and_iff_left (chart_ne_zero i w)
  rw [this]
  exact hC.preimage (continuous_chart i)

/-- In the chart `z_i = 1`, `K_i(ρ)` is the closed polydisc of radius `ρ` (`ρ ≥ 1`). -/
theorem chart_preimage_coverSet_self {ρ : ℝ} (hρ : 1 ≤ ρ) (i : Fin (N + 1)) :
    chart i ⁻¹' coverSet ρ {i} = Box.boxSet fun _ => closedBall (0 : ℂ) ρ := by
  ext w
  simp only [mem_preimage, coverSet, mem_ofPred_eq, Finset.mem_singleton, forall_eq,
    chart_apply_self, norm_one, mul_one, Box.mem_boxSet, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨-, h⟩ m
    simpa using h (i.succAbove m)
  · intro h
    refine ⟨chart_ne_zero i w, fun j => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨m, rfl⟩
    · simpa using hρ
    · simpa using h m

theorem isBox_closedBall (n : ℕ) (ρ : ℝ) :
    Box.IsBox (fun _ : Fin n => closedBall (0 : ℂ) ρ) :=
  ⟨fun _ => isCompact_closedBall 0 ρ, fun _ => convex_closedBall 0 ρ⟩

/-! ### Rehomogenization -/

section Rehom

variable {τ : Type} [Fintype τ]

/-- The homogeneous function of degree `m` on `{z_i ≠ 0}` with chart representative `f`:
`z ↦ z_i^m f(z / z_i)`. -/
def rehom (i : Fin (N + 1)) (m : ℤ) (f : τ → EuclideanSpace ℂ (Fin N) → ℂ) :
    τ → ConeSpace N → ℂ :=
  fun j z => z i ^ m * f j (dehom i z)

/-- The cone over `V ⊆ ℂ^N` in the chart `z_i ≠ 0`. -/
def chartCone (i : Fin (N + 1)) (V : Set (EuclideanSpace ℂ (Fin N))) : Set (ConeSpace N) :=
  {z | z i ≠ 0} ∩ dehom i ⁻¹' V

variable (i : Fin (N + 1)) {V : Set (EuclideanSpace ℂ (Fin N))}

theorem isOpen_chartCone (hV : IsOpen V) : IsOpen (chartCone i V) :=
  ContinuousOn.isOpen_inter_preimage (fun _ hz => (differentiableAt_dehom i hz).continuousAt
    |>.continuousWithinAt) (isOpen_coord_ne_zero i) hV

theorem isCone_chartCone : IsCone (chartCone i V) := by
  intro c hc z hz
  refine ⟨?_, ?_⟩
  · simp only [mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hz.1
  · show dehom i (c • z) ∈ V
    rw [dehom_smul i hc]
    exact hz.2

theorem chartCone_subset : chartCone i V ⊆ {z | z ≠ 0} := fun z hz h0 => hz.1 (by simp [h0])

theorem chartCone_mono {V' : Set (EuclideanSpace ℂ (Fin N))} (h : V ⊆ V') :
    chartCone i V ⊆ chartCone i V' :=
  fun _ hz => ⟨hz.1, h hz.2⟩

/-- A cone `K ⊆ {z_i ≠ 0}` whose chart trace lies in `V` lies in the cone over `V`. -/
theorem subset_chartCone {K : Set (ConeSpace N)} (hKc : IsCone K) (hKi : ∀ z ∈ K, z i ≠ 0)
    (hKV : chart i ⁻¹' K ⊆ V) : K ⊆ chartCone i V := by
  intro z hz
  refine ⟨hKi z hz, hKV ?_⟩
  show chart i (dehom i z) ∈ K
  rw [chart_dehom i (hKi z hz)]
  exact hKc _ (inv_ne_zero (hKi z hz)) z hz

theorem differentiableAt_zpow_coord (m : ℤ) {z : ConeSpace N} (hz : z i ≠ 0) :
    DifferentiableAt ℂ (fun z : ConeSpace N => z i ^ m) z :=
  ((EuclideanSpace.proj i : ConeSpace N →L[ℂ] ℂ).differentiableAt).zpow (Or.inl hz)

theorem isHomOn_rehom (hV : IsOpen V) {m : ℤ} {f : τ → EuclideanSpace ℂ (Fin N) → ℂ}
    (hf : ∀ j, DifferentiableOn ℂ (f j) V) : IsHomOn (chartCone i V) m (rehom i m f) := by
  refine ⟨isOpen_chartCone i hV, isCone_chartCone i, chartCone_subset i, fun j z hz => ?_,
    fun z hz c hc j => ?_⟩
  · exact ((differentiableAt_zpow_coord i m hz.1).mul
      (((hf j).differentiableAt (hV.mem_nhds hz.2)).comp z
        (differentiableAt_dehom i hz.1))).differentiableWithinAt
  · simp only [rehom, PiLp.smul_apply, smul_eq_mul, dehom_smul i hc, mul_zpow]
    ring

/-- **Rehomogenization preserves membership**: if `f ∈ (pullChart i R)_w` for `w ∈ V`, then
`rehom i m f ∈ R_y` at every point of the cone over `V` (`R` invariant and coherent). -/
theorem mem_rehom {R : GermModule (ConeSpace N) τ}
    (hR : R.IsCoherentOn (puncture (ConeSpace N))) (hRi : IsConeInvariant R) (m : ℤ)
    {f : τ → EuclideanSpace ℂ (Fin N) → ℂ} (hfm : ∀ y ∈ V, (pullChart i R).mem y f)
    {y : ConeSpace N} (hy : y ∈ chartCone i V) : R.mem y (rehom i m f) := by
  have h1 := hfm _ hy.2
  have hy0 : y ≠ 0 := chartCone_subset i hy
  have hyi := hy.1
  have h2 : R.mem ((y i)⁻¹ • y) fun j z => f j (dehom i z) := by
    have h1' : R.mem (chart i (dehom i y)) fun j z => f j (dehom i z) := h1
    rwa [chart_dehom i hyi] at h1'
  have h3 := (hRi ((y i)⁻¹ • y) (smul_ne_zero (inv_ne_zero hyi) hy0) (y i) hyi _).1 h2
  rw [smul_inv_smul₀ hyi] at h3
  have h4 : R.mem y fun j z => f j (dehom i z) := by
    refine (hR y hy0).congr_mem h3 fun j => Eventually.of_forall fun z => ?_
    simp only [dehom_smul i (inv_ne_zero hyi)]
  have hhol : HolAt (fun z : ConeSpace N => z i ^ m) y :=
    (eventually_coord_ne_zero i hyi).mono fun z hz => differentiableAt_zpow_coord i m hz
  exact (hR y hy0).smul_mem hhol h4

/-- A homogeneous tuple of degree `m` equals the rehomogenization of its chart restriction. -/
theorem eq_rehom_of_isHomOn {U : Set (ConeSpace N)} {m : ℤ} {a : τ → ConeSpace N → ℂ}
    (ha : IsHomOn U m a) {z : ConeSpace N} (hz : z ∈ U) (hzi : z i ≠ 0) (j : τ) :
    a j z = rehom i m (fun j v => a j (chart i v)) j z := by
  have h := ha.hom ((z i)⁻¹ • z) (ha.isCone _ (inv_ne_zero hzi) z hz) (z i) hzi j
  rw [smul_inv_smul₀ hzi] at h
  simp only [rehom, chart_dehom i hzi]
  exact h

end Rehom

/-! ### Sections from pointwise membership -/

section Pointwise

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {τ : Type} [Fintype τ]

/-- A homogeneous tuple on an open cone `U ⊇ K` whose germs at the points of `K` lie in an
invariant coherent `P` is a section of `P` over `K`. -/
theorem isHomSection_of_forall_mem {P : GermModule X τ} (hP : P.IsCoherentOn {z | z ≠ 0})
    (hPi : IsConeInvariant P) {n : ℤ} {K U : Set X} {a : τ → X → ℂ} (hKU : K ⊆ U)
    (ha : IsHomOn U n a) (hmem : ∀ y ∈ K, P.mem y a) : IsHomSection P n K a := by
  set U' : Set X := {y | y ∈ U ∧ P.mem y a} with hU'def
  have hU'o : IsOpen U' := by
    refine isOpen_iff_mem_nhds.2 fun y hy => ?_
    filter_upwards [eventually_mem_of_coherentAt (hP y (ha.subset hy.1)) hy.2,
      ha.isOpen.mem_nhds hy.1] with y' h1 h2
    exact ⟨h2, h1⟩
  have hU'c : IsCone U' := by
    intro c hc y hy
    have hcy : c • y ∈ U := ha.isCone c hc y hy.1
    refine ⟨hcy, ?_⟩
    have h1 := (hPi y (ha.subset hy.1) c hc a).1 hy.2
    have h2 : P.mem (c • y) fun j z => c⁻¹ ^ n * a j z := by
      refine (hP _ (ha.subset hcy)).congr_mem h1 fun j => ?_
      filter_upwards [ha.isOpen.mem_nhds hcy] with z hz
      exact ha.hom z hz c⁻¹ (inv_ne_zero hc) j
    have h3 := (hP _ (ha.subset hcy)).smul_mem (holAt_const ((c⁻¹ ^ n)⁻¹) (c • y)) h2
    have hcn : (c⁻¹ ^ n) ≠ 0 := zpow_ne_zero n (inv_ne_zero hc)
    exact (hP _ (ha.subset hcy)).congr_mem h3 fun j => Eventually.of_forall fun z =>
      inv_mul_cancel_left₀ hcn (a j z)
  refine ⟨U', fun y hy => ⟨hKU hy, hmem y hy⟩, ⟨hU'o, hU'c, fun y hy => ha.subset hy.1,
    fun j => (ha.diff j).mono fun y hy => hy.1, fun z hz => ha.hom z hz.1⟩, fun y hy => hy.2⟩

end Pointwise

/-! ### Growing a `0`-cocycle -/

section Grow

variable {F : Subquotient (ConeSpace N) (puncture (ConeSpace N))}

/-- **One chart of the growth.** Given a `0`-cocycle `g` of `F(n)` for the cover `K(ρ)`, there
is a section `g'` of `M(n)` near `K_j(ρ')` congruent to `g_k` modulo `N` at every point of
`K_j(ρ') ∩ K_k(ρ)`. -/
theorem exists_grow_zero_one (hF : IsInvariantSubquotient F) {ρ ρ' : ℝ} (hρ : 1 ≤ ρ)
    (hρρ' : ρ ≤ ρ') (n : ℤ) (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)) (j : Fin (N + 1)) :
    ∃ g' : F.ι → ConeSpace N → ℂ, IsHomSection F.M n (coverSet ρ' {j}) g' ∧
      ∀ k, ∀ y ∈ coverSet ρ' {j} ∩ coverSet ρ {k}, F.N.mem y (g' - g k) := by
  classical
  choose U hKU hUh hUM using hg
  choose W hKW hWh hWN using hcoc
  have hρ' : 1 ≤ ρ' := hρ.trans hρρ'
  set D : Set (EuclideanSpace ℂ (Fin N)) := Box.boxSet fun _ => closedBall (0 : ℂ) ρ' with hDdef
  have hDK : chart j ⁻¹' coverSet ρ' {j} = D := chart_preimage_coverSet_self hρ' j
  set A : Fin (N + 1) → Set (EuclideanSpace ℂ (Fin N)) :=
    fun k => chart j ⁻¹' coverSet ρ {k} ∩ D with hAdef
  have hAc : ∀ k, IsCompact (A k) := fun k =>
    (isBox_closedBall N ρ').isCompact_boxSet.inter_left (isClosed_chart_preimage_coverSet j ρ {k})
  set O : Fin (N + 1) → Set (EuclideanSpace ℂ (Fin N)) := fun k => chart j ⁻¹' U k with hOdef
  have hOo : ∀ k, IsOpen (O k) := fun k => (hUh k).isOpen.preimage (continuous_chart j)
  set P : Fin (N + 1) → Fin (N + 1) → Set (EuclideanSpace ℂ (Fin N)) :=
    fun a b => chart j ⁻¹' W b a with hPdef
  have hPo : ∀ a b, IsOpen (P a b) := fun a b => (hWh b a).isOpen.preimage (continuous_chart j)
  have hAP : ∀ a b, A a ∩ A b ⊆ P a b := by
    intro a b w hw
    exact hKW b a ((mem_coverSet_pair).2 ⟨hw.2.1, hw.1.1⟩)
  obtain ⟨U', hU'o, hAU', hU'O, hU'P⟩ :=
    exists_open_shrink hAc hOo (fun k w hw => hKU k hw.1) hPo hAP
  set s : Fin (N + 1) → F.ι → EuclideanSpace ℂ (Fin N) → ℂ :=
    fun a c v => g a c (chart j v) with hsdef
  have hsd : ∀ a c, DifferentiableOn ℂ (s a c) (U' a) := fun a c =>
    ((hUh a).diff c).comp (differentiable_chart j).differentiableOn fun v hv => hU'O a hv
  have hNc := isCoherentOn_pullChart F.coherent_N hF.2 j
  have hMc := isCoherentOn_pullChart F.coherent_M hF.1 j
  have hcov : D ⊆ ⋃ a, U' a := by
    intro w hw
    obtain ⟨k, hk⟩ := exists_mem_coverSet hρ (chart_ne_zero j w)
    exact mem_iUnion.2 ⟨k, hAU' k ⟨hk, hw⟩⟩
  have hscoc : ∀ a b, ∀ y ∈ U' a ∩ U' b,
      (pullChart j F.N).mem y (fun c z => s a c z - s b c z) := by
    intro a b y hy
    have h := hWN b a (chart j y) (hU'P a b hy)
    exact mem_pullChart_comp_chart F.coherent_N hF.2 j h
  obtain ⟨V, hVo, hDV, g'', hg''d, hg''m⟩ :=
    TheoremB.exists_lift (isBox_closedBall N ρ') isOpen_univ (subset_univ _)
      (hNc.mono (subset_univ _)) U' hU'o hcov s hsd hscoc
  set V' : Set (EuclideanSpace ℂ (Fin N)) := V ∩ ⋃ a, U' a with hV'def
  have hV'o : IsOpen V' := hVo.inter (isOpen_iUnion hU'o)
  have hDV' : D ⊆ V' := fun w hw => ⟨hDV hw, hcov hw⟩
  -- the lift is a section of `M` on the chart
  have hg''M : ∀ y ∈ V', (pullChart j F.M).mem y g'' := by
    intro y hy
    obtain ⟨a, ha⟩ := mem_iUnion.1 hy.2
    have h1 : (pullChart j F.N).mem y (fun c z => g'' c z - s a c z) := hg''m a y ⟨hy.1, ha⟩
    have h1' : (pullChart j F.M).mem y (fun c z => g'' c z - s a c z) :=
      F.le _ (chart_ne_zero j y) _ h1
    have h2 : (pullChart j F.M).mem y (s a) :=
      mem_pullChart_comp_chart F.coherent_M hF.1 j (hUM a (chart j y) (hU'O a ha))
    refine (hMc y (mem_univ y)).congr_mem ((hMc y (mem_univ y)).add_mem h1' h2) fun c => ?_
    exact Eventually.of_forall fun z => by simp
  refine ⟨rehom j n g'', ⟨chartCone j V', ?_, isHomOn_rehom j hV'o fun c =>
    (hg''d c).mono inter_subset_left, fun y hy => mem_rehom j F.coherent_M hF.1 n hg''M hy⟩, ?_⟩
  · refine subset_chartCone j (isCone_coverSet ρ' {j})
      (fun z hz => coord_ne_zero_of_mem_coverSet (Finset.mem_singleton_self j) hz) ?_
    rw [hDK]
    exact hDV'
  · intro k y hy
    have hyj : y j ≠ 0 := coord_ne_zero_of_mem_coverSet (Finset.mem_singleton_self j) hy.1
    set Z : Set (ConeSpace N) := chartCone j (V ∩ U' k) ∩ U k with hZdef
    have hZo : IsOpen Z := (isOpen_chartCone j (hVo.inter (hU'o k))).inter (hUh k).isOpen
    have hyD : dehom j y ∈ D := by
      rw [← hDK]
      show chart j (dehom j y) ∈ coverSet ρ' {j}
      rw [chart_dehom j hyj]
      exact isCone_coverSet ρ' {j} _ (inv_ne_zero hyj) y hy.1
    have hyZ : y ∈ Z := by
      refine ⟨⟨hyj, hDV hyD, hAU' k ⟨?_, hyD⟩⟩, hKU k hy.2⟩
      show chart j (dehom j y) ∈ coverSet ρ {k}
      rw [chart_dehom j hyj]
      exact isCone_coverSet ρ {k} _ (inv_ne_zero hyj) y hy.2
    have hmem : F.N.mem y (rehom j n fun c z => g'' c z - s k c z) :=
      mem_rehom j F.coherent_N hF.2 n (fun w hw => hg''m k w hw) hyZ.1
    refine (F.coherent_N y (chartCone_subset j hyZ.1)).congr_mem hmem fun c => ?_
    filter_upwards [hZo.mem_nhds hyZ] with z hz
    have hzj : z j ≠ 0 := hz.1.1
    have h1 := eq_rehom_of_isHomOn j (hUh k) hz.2 hzj c
    simp only [rehom, Pi.sub_apply] at h1 ⊢
    rw [h1]
    ring

/-- **Growing `0`-cocycles** (cover comparison in degree `0`). Let `F = M/N` be an invariant
subquotient, `1 ≤ ρ ≤ ρ'`, and `g` a `0`-cocycle of `F(n)` for the cover `K(ρ)`: sections
`g_i` of `M(n)` over `K_i(ρ)` with `g_k - g_i` a section of `N(n)` over `K_i(ρ) ∩ K_k(ρ)`.
Then there is a `0`-cocycle `g'` of `F(n)` for the cover `K(ρ')` with `g'_i - g_i` a section of
`N(n)` over `K_i(ρ)`: the restriction `Ȟ⁰(K(ρ'), F(n)) → Ȟ⁰(K(ρ), F(n))` is onto. -/
theorem exists_grow_zero (hF : IsInvariantSubquotient F) {ρ ρ' : ℝ} (hρ : 1 ≤ ρ)
    (hρρ' : ρ ≤ ρ') (n : ℤ) (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)) :
    ∃ g' : Fin (N + 1) → F.ι → ConeSpace N → ℂ,
      (∀ i, IsHomSection F.M n (coverSet ρ' {i}) (g' i)) ∧
      (∀ i k, IsHomSection F.N n (coverSet ρ' {i, k}) (g' k - g' i)) ∧
      ∀ i, IsHomSection F.N n (coverSet ρ {i}) (g' i - g i) := by
  choose g' hg' hg'N using exists_grow_zero_one hF hρ hρρ' n g hg hcoc
  choose U hKU hUh hUM using hg'
  choose Ug hKUg hUgh hUgM using hg
  refine ⟨g', fun i => ⟨U i, hKU i, hUh i, hUM i⟩, fun i k => ?_, fun i => ?_⟩
  · refine isHomSection_of_forall_mem (U := U i ∩ U k) F.coherent_N hF.2
      (fun y hy => ⟨hKU i ((mem_coverSet_pair).1 hy).1, hKU k ((mem_coverSet_pair).1 hy).2⟩)
      ((hUh k).inter_left (hUh i).isOpen (hUh i).isCone |>.sub
        ((hUh i).inter (hUh k).isOpen (hUh k).isCone)) fun y hy => ?_
    obtain ⟨l, hl⟩ := exists_mem_coverSet hρ hy.1
    have h1 := hg'N k l y ⟨((mem_coverSet_pair).1 hy).2, hl⟩
    have h2 := hg'N i l y ⟨((mem_coverSet_pair).1 hy).1, hl⟩
    refine (F.coherent_N y hy.1).congr_mem ((F.coherent_N y hy.1).sub_mem h1 h2) fun c => ?_
    exact Eventually.of_forall fun z => by simp
  · refine isHomSection_of_forall_mem (U := U i ∩ Ug i) F.coherent_N hF.2
      (fun y hy => ⟨hKU i (coverSet_mono hρρ' {i} hy), hKUg i hy⟩)
      ((hUh i).inter (hUgh i).isOpen (hUgh i).isCone |>.sub
        ((hUgh i).inter_left (hUh i).isOpen (hUh i).isCone)) fun y hy =>
      hg'N i i y ⟨coverSet_mono hρρ' {i} hy, hy⟩

end Grow

end SGPT.GAGA.PN
