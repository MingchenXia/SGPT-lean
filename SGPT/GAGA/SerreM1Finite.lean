import SGPT.GAGA.SerreM1Banach

/-!
# Serre's theorems on `ℙᴺ`, part 4: `dim Ȟ⁰(ℙᴺ, 𝓕(n)) < ∞`

Infrastructure towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145).

**`finiteDimensional_cechH_zero`**: for every `ℂ*`-invariant subquotient `F = M/N` on the cone
`ℂ^{N+1} ∖ 0` (a coherent sheaf on `ℙᴺ` in the model of lane SERRE-PN), every `n ∈ ℤ` and every
`ρ ≥ 1`, the Čech cohomology `Ȟ⁰` of `F(n)` for the closed cover `K(ρ)` is finite-dimensional.
The proof is the Cartan--Serre argument of `SerreM1Banach` (Schwartz's theorem, compact
restriction between levels, and the growth of `0`-cocycles `exists_grow_zero`).

**`finiteDimensional_cechH_one_submodule`**: for an invariant coherent submodule `M ⊆ 𝒪^ι`
(the subquotient `M/0`), `Ȟ¹(K(ρ), M(n))` is finite-dimensional. It sits in the exact sequence
`Ȟ⁰(𝒪^ι/M (n)) → Ȟ¹(M(n)) → Ȟ¹(𝒪^ι(n))` of lane SERRE-PN (`coverSystem_les`, Theorem B of
SERRE-CORE3), whose outer terms are finite-dimensional (the first by `finiteDimensional_cechH_zero`,
the last by SERRE-PN2's `finiteDimensional_cechH_free`).

Blueprint: `claude-serre-m34.tex`, nodes `claude-serre-m34:finite-H0`,
`claude-serre-m34:finite-H1-sub`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core
open scoped BoundedContinuousFunction

noncomputable section

namespace SGPT.GAGA.PN

variable {N : ℕ}

theorem openCover_subset_coverSet (ρ : ℝ) (s : Finset (Fin (N + 1))) :
    openCover ρ s ⊆ coverSet ρ s :=
  fun _ hz => ⟨hz.1, fun i hi j => (hz.2 i hi j).le⟩

theorem mem_openCover_pair {r : ℝ} {i k : Fin (N + 1)} {z : ConeSpace N}
    (hi : z ∈ openCover r {i}) (hk : z ∈ openCover r {k}) : z ∈ openCover r {i, k} := by
  refine ⟨hi.1, fun i' hi' j => ?_⟩
  rcases Finset.mem_insert.1 hi' with rfl | hi'
  · exact hi.2 i' (Finset.mem_singleton_self _) j
  · rw [Finset.mem_singleton.1 hi']
    exact hk.2 k (Finset.mem_singleton_self _) j

theorem extendTuple_sub {ι : Type} [Fintype ι] {U : Set (ConeSpace N)} (f g : U →ᵇ (ι → ℂ)) :
    extendTuple (f - g) = fun j x => extendTuple f j x - extendTuple g j x := by
  funext j x
  unfold extendTuple
  split_ifs <;> simp

theorem hext_sub {τ : Type} [Fintype τ] (n : ℤ) (f g : τ → ConeSpace N → ℂ) :
    hext n (f - g) = hext n f - hext n g := by
  funext j z
  simp only [hext, Pi.sub_apply]
  ring

section Finite

variable {F : Subquotient (ConeSpace N) (puncture (ConeSpace N))} {n : ℤ}

/-! ### From cocycles of the closed cover to the Banach spaces and back -/

/-- **Restriction of a `0`-cocycle of `K(ρ')` to the pieces at a level `(r, t)`, `r < ρ'`.** -/
theorem exists_cocE_of_cocycle {r ρ' t : ℝ} (hr : r < ρ') (ht : 1 < t)
    (g : Fin (N + 1) → F.ι → ConeSpace N → ℂ)
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ' {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ' {i, k}) (g k - g i)) :
    ∃ e : cocE F n r t, ∀ i, ∀ z ∈ piece r t {i}, ∀ j, extendTuple (e.1 i) j z = g i j z := by
  choose U hKU hUh hUM using hg
  choose W hKW hWh hWN using hcoc
  choose K hK h1 h2 using fun i : Fin (N + 1) =>
    exists_isCompact_between hr ht (lt_add_one t) ({i} : Finset (Fin (N + 1)))
  have hKU' : ∀ i, K i ⊆ U i := fun i z hz =>
    hKU i (openCover_subset_coverSet ρ' {i} (h2 i hz).1)
  set e : Amb F r t := fun i => bcfOn (hK i) (h1 i) (g i) fun j =>
    ((hUh i).diff j).continuousOn.mono (hKU' i) with hedef
  have hee : ∀ i, ∀ z ∈ piece r t {i}, ∀ j, extendTuple (e i) j z = g i j z := fun i z hz j =>
    extendTuple_bcfOn (hK i) (h1 i) (g i) _ hz j
  have hpU : ∀ i, piece r t {i} ⊆ U i := fun i z hz => hKU' i (h1 i hz)
  refine ⟨⟨e, mem_cocE.2 ⟨fun i => ⟨fun j => ?_, fun y hy => ?_⟩, fun i z hz c hc j => ?_,
    fun i k => ⟨fun j => ?_, fun y hy => ?_⟩⟩⟩, hee⟩
  · exact ((hUh i).diff j).mono (hpU i) |>.congr fun z hz => hee i z hz j
  · refine (coherent_M_piece F r t {i} y hy).congr_mem (hUM i y (hpU i hy)) fun j => ?_
    filter_upwards [(isOpen_piece r t {i}).mem_nhds hy] with z hz
    exact (hee i z hz j).symm
  · rw [hee i _ hc, hee i z hz]
    exact (hUh i).hom z (hpU i hz) c (by rintro rfl; simpa using piece_subset_puncture r t _ hc) j
  · have hsub : piece r t {i, k} ⊆ W i k := fun z hz =>
      hKW i k (coverSet_mono hr.le _ (openCover_subset_coverSet r _ hz.1))
    refine (((hWh i k).diff j).mono hsub).congr fun z hz => ?_
    rw [extendTuple_diffPair F r t i k e hz,
      hee k z (piece_subset_of_subset (by simp) hz) j,
      hee i z (piece_subset_of_subset (by simp) hz) j]
    rfl
  · have hyW : y ∈ W i k :=
      hKW i k (coverSet_mono hr.le _ (openCover_subset_coverSet r _ hy.1))
    refine (coherent_N_piece F r t {i, k} y hy).congr_mem (hWN i k y hyW) fun j => ?_
    filter_upwards [(isOpen_piece r t {i, k}).mem_nhds hy] with z hz
    rw [extendTuple_diffPair F r t i k e hz,
      hee k z (piece_subset_of_subset (by simp) hz) j,
      hee i z (piece_subset_of_subset (by simp) hz) j]
    rfl

/-- The extension of the restriction of a homogeneous section is the section. -/
theorem hext_eq_of_restrict {r t : ℝ} (ht : 1 < t) {τ : Type} [Fintype τ]
    {f a : τ → ConeSpace N → ℂ} {U : Set (ConeSpace N)} (ha : IsHomOn U n a) {i : Fin (N + 1)}
    (hU : openCover r {i} ⊆ U) (hfa : ∀ z ∈ piece r t {i}, ∀ j, f j z = a j z) {z : ConeSpace N}
    (hz : z ∈ openCover r {i}) (j : τ) : hext n f j z = a j z := by
  rw [← hext_eq_of_isHomOn ha (hU hz) j]
  simp only [hext]
  rw [hfa _ (normalize_mem_piece ht hz) j]

variable (F n) in
/-- The homogeneous extension of the `i`-th component of a bounded cocycle. -/
def hextComp {r t : ℝ} (e : cocE F n r t) (i : Fin (N + 1)) : F.ι → ConeSpace N → ℂ :=
  hext n (extendTuple (e.1 i))

theorem isHomOn_hextComp {r t : ℝ} (ht : 1 < t) (e : cocE F n r t) (i : Fin (N + 1)) :
    IsHomOn (openCover r {i}) n (hextComp F n e i) :=
  isHomOn_hext ht ((mem_cocE.1 e.2).2.1 i) ((mem_cocE.1 e.2).1 i).1

theorem hextComp_isHomSection {ρ₀ r t : ℝ} (hF : IsInvariantSubquotient F) (ht : 1 < t)
    (hρr : ρ₀ < r) (e : cocE F n r t) (i : Fin (N + 1)) :
    IsHomSection F.M n (coverSet ρ₀ {i}) (hextComp F n e i) :=
  ⟨openCover r {i}, coverSet_subset_openCover hρr {i}, isHomOn_hextComp ht e i, fun _ hy =>
    mem_hext F.coherent_M hF.1 ht ((mem_cocE.1 e.2).2.1 i) le_rfl ht
      (fun y' hy' => ((mem_cocE.1 e.2).1 i).2 y' hy') hy⟩

theorem hextComp_cocycle {ρ₀ r t : ℝ} (hF : IsInvariantSubquotient F) (ht : 1 < t)
    (hρr : ρ₀ < r) (e : cocE F n r t) (i k : Fin (N + 1)) :
    IsHomSection F.N n (coverSet ρ₀ {i, k}) (hextComp F n e k - hextComp F n e i) := by
  obtain ⟨ha, hb, hc⟩ := mem_cocE.1 e.2
  have hUo : IsOpen (openCover r {i} ∩ openCover r {k}) :=
    (isOpen_openCover r {i}).inter (isOpen_openCover r {k})
  refine ⟨openCover r {i} ∩ openCover r {k}, fun z hz => ⟨coverSet_subset_openCover hρr {i}
    (coverSet_anti ρ₀ (by simp) hz), coverSet_subset_openCover hρr {k}
    (coverSet_anti ρ₀ (by simp) hz)⟩, ((isHomOn_hextComp ht e k).inter_left
      (isOpen_openCover r {i}) (isCone_openCover r {i})).sub ((isHomOn_hextComp ht e i).inter
      (isOpen_openCover r {k}) (isCone_openCover r {k})), fun y hy => ?_⟩
  have hhom : IsHomShell (extendTuple (e.1 k) - extendTuple (e.1 i)) (piece r t {i, k}) n := by
    intro z hz c hc j
    simp only [Pi.sub_apply]
    rw [hb k z (piece_subset_of_subset (by simp) hz) c (piece_subset_of_subset (by simp) hc) j,
      hb i z (piece_subset_of_subset (by simp) hz) c (piece_subset_of_subset (by simp) hc) j]
    ring
  have hmem : ∀ y' ∈ piece r t {i, k}, F.N.mem y' (extendTuple (e.1 k) - extendTuple (e.1 i)) := by
    intro y' hy'
    refine (coherent_N_piece F r t {i, k} y' hy').congr_mem ((hc i k).2 y' hy') fun j => ?_
    filter_upwards [(isOpen_piece r t {i, k}).mem_nhds hy'] with z hz
    rw [extendTuple_diffPair F r t i k e.1 hz]
    rfl
  have h := mem_hext F.coherent_N hF.2 ht hhom le_rfl ht hmem (mem_openCover_pair hy.1 hy.2)
  rw [hext_sub] at h
  exact h

/-! ### The surjection onto the `0`-cocycles -/

variable (F n) in
/-- The linear map from bounded cocycles at level `(r, t)` to the `0`-cocycles of `K(ρ₀)`. -/
def toZeroCocycle (hF : IsInvariantSubquotient F) {ρ₀ r t : ℝ} (ht : 1 < t) (hρr : ρ₀ < r) :
    cocE F n r t →ₗ[ℂ] LinearMap.ker (cechDq (coverSystem F n ρ₀) 0) where
  toFun e := zeroCocycle (hextComp F n e) (hextComp_isHomSection hF ht hρr e)
    (hextComp_cocycle hF ht hρr e)
  map_add' e e' := by
    have h : hextComp F n (e + e') = hextComp F n e + hextComp F n e' := by
      funext i j z
      simp only [hextComp, hext, Pi.add_apply, Submodule.coe_add, extendTuple_add]
      ring
    have h1 := zeroCocycle_congr (F := F) (ρ := ρ₀) (hg := hextComp_isHomSection hF ht hρr (e + e'))
      (hcoc := hextComp_cocycle hF ht hρr (e + e')) (hg' := h ▸ hextComp_isHomSection hF ht hρr
        (e + e')) (hcoc' := h ▸ hextComp_cocycle hF ht hρr (e + e')) h
    rw [h1, zeroCocycle_add]
  map_smul' c e := by
    have h : hextComp F n (c • e) = c • hextComp F n e := by
      funext i j z
      simp only [hextComp, hext, Pi.smul_apply, Submodule.coe_smul, extendTuple_smul,
        smul_eq_mul]
      ring
    have h1 := zeroCocycle_congr (F := F) (ρ := ρ₀) (hg := hextComp_isHomSection hF ht hρr (c • e))
      (hcoc := hextComp_cocycle hF ht hρr (c • e)) (hg' := h ▸ hextComp_isHomSection hF ht hρr
        (c • e)) (hcoc' := h ▸ hextComp_cocycle hF ht hρr (c • e)) h
    rw [RingHom.id_apply, h1, zeroCocycle_smul]

theorem toZeroCocycle_apply (hF : IsInvariantSubquotient F) {ρ₀ r t : ℝ} (ht : 1 < t)
    (hρr : ρ₀ < r) (e : cocE F n r t) :
    toZeroCocycle F n hF ht hρr e = zeroCocycle (hextComp F n e)
      (hextComp_isHomSection hF ht hρr e) (hextComp_cocycle hF ht hρr e) :=
  rfl

theorem zeroCocycle_zero {ρ : ℝ} (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i})
      ((0 : Fin (N + 1) → F.ι → ConeSpace N → ℂ) i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k})
      ((0 : Fin (N + 1) → F.ι → ConeSpace N → ℂ) k - (0 : Fin (N + 1) → F.ι → ConeSpace N → ℂ) i)) :
    zeroCocycle 0 hg hcoc = 0 := by
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    change zeroCochain 0 hg {i} = 0
    rw [zeroCochain_singleton]
    exact (sectionMk_eq_zero_iff F _).2 (isHomSection_zero F.coherent_N n (coverSet_subset ρ _))
  · change zeroCochain 0 hg s = 0
    unfold zeroCochain
    split_ifs
    rfl

/-! ### The main theorem -/

/-- **The decomposition step**: every bounded cocycle at level `(ρ+2, 3)` is, modulo `N` on the
level `(ρ+1, 2)`, the restriction of a bounded cocycle at level `(ρ+3, 4)`. -/
theorem exists_decomp (hF : IsInvariantSubquotient F) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (e : cocE F n (ρ + 2) 3) :
    ∃ z : cocE F n (ρ + 3) 4, ∀ i, ∀ y ∈ piece (ρ + 1) 2 {i},
      F.N.mem y (extendTuple ((e - resCocE F n (show ρ + 2 ≤ ρ + 3 by linarith)
        (show (3 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) < 3 by norm_num) z).1 i)) := by
  have ht2 : (1 : ℝ) < 3 := by norm_num
  have hρ' : ρ + 3 / 2 < ρ + 2 := by linarith
  obtain ⟨g', hg', hcoc', hgg'⟩ := exists_grow_zero (ρ' := ρ + 4) hF
    (show 1 ≤ ρ + 3 / 2 by linarith) (by linarith) n (hextComp F n e)
    (hextComp_isHomSection hF ht2 hρ' e) (hextComp_cocycle hF ht2 hρ' e)
  obtain ⟨z, hz⟩ := exists_cocE_of_cocycle (r := ρ + 3) (t := 4) (by linarith) (by norm_num)
    g' hg' hcoc'
  refine ⟨z, fun i y hy => ?_⟩
  have hy2 : y ∈ piece (ρ + 2) 3 {i} := piece_anti (by linarith) (by norm_num) (by norm_num)
    (subset_refl _) hy
  obtain ⟨V, hKV, hVh, hVN⟩ := hgg' i
  have hyV : y ∈ V := hKV (coverSet_mono (show ρ + 1 ≤ ρ + 3 / 2 by linarith) _
    (openCover_subset_coverSet _ _ hy.1))
  have h1 := (F.coherent_N y (hVh.subset hyV)).neg_mem (hVN y hyV)
  refine (coherent_N_piece F (ρ + 1) 2 {i} y hy).congr_mem h1 fun j => ?_
  filter_upwards [(isOpen_piece (ρ + 2) 3 {i}).mem_nhds hy2] with w hw
  have hw3 : w ∈ piece (ρ + 3) 4 {i} := piece_anti (by linarith) (by norm_num) (by norm_num)
    (subset_refl _) hw
  have hzr' : extendTuple ((resCocE F n (show ρ + 2 ≤ ρ + 3 by linarith)
      (show (3 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) < 3 by norm_num) z).1 i) j w = g' i j w := by
    rw [← hz i w hw3 j]
    exact extendTuple_resLevel F (show ρ + 2 ≤ ρ + 3 by linarith) (show (3 : ℝ) ≤ 4 by norm_num)
      (show (0 : ℝ) < 3 by norm_num) z.1 i hw j
  have he' : extendTuple (e.1 i) j w = hextComp F n e i j w :=
    (hext_eq ht2 ((mem_cocE.1 e.2).2.1 i) hw j).symm
  change -(g' i j w - hextComp F n e i j w) = extendTuple (e.1 i - _) j w
  rw [extendTuple_sub]
  simp only [he', hzr']
  ring

/-- **Finiteness of `Ȟ⁰`** (Cartan--Serre, degree `0`): for an invariant subquotient `F = M/N`
on `ℂ^{N+1} ∖ 0`, every `n` and `ρ ≥ 1`, the space of `0`-cocycles of `F(n)` for the closed cover
`K(ρ)` is finite-dimensional. -/
theorem finiteDimensional_zeroCocycles (hF : IsInvariantSubquotient F) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    FiniteDimensional ℂ (LinearMap.ker (cechDq (coverSystem F n ρ) 0)) := by
  classical
  have ht2 : (1 : ℝ) < 3 := by norm_num
  have hρr₂ : ρ < ρ + 2 := by linarith
  have h12 : ρ + 1 ≤ ρ + 2 := by linarith
  -- the closed subspace of cocycles vanishing modulo `N` on the lowest level
  let R : (i : Fin (N + 1)) →
      (Amb F (ρ + 2) 3 →L[ℂ] (piece (N := N) (ρ + 1) 2 {i} →ᵇ (F.ι → ℂ))) :=
    fun i => (BoundedContinuousFunction.compContinuousCLM (F.ι → ℂ) ℂ
      ⟨Set.inclusion (piece_anti h12 (show (2 : ℝ) ≤ 3 by norm_num)
        (show (0 : ℝ) < 2 by norm_num) (subset_refl {i})), continuous_inclusion _⟩).comp
      (ContinuousLinearMap.proj i)
  let Wamb : Submodule ℂ (Amb F (ρ + 2) 3) := cocE F n (ρ + 2) 3 ⊓
    ⨅ i, (boundedSections F.N (piece (ρ + 1) 2 {i}) (coherent_N_piece F (ρ + 1) 2 {i})).comap
      (R i).toLinearMap
  have hWclosed : IsClosed (Wamb : Set (Amb F (ρ + 2) 3)) := by
    simp only [Wamb, Submodule.coe_inf, Submodule.coe_iInf]
    exact (isClosed_cocE F n (ρ + 2) 3).inter (isClosed_iInter fun i =>
      (isClosed_boundedSections (M := F.N) (isOpen_piece (ρ + 1) 2 {i})
        (coherent_N_piece F (ρ + 1) 2 {i})).preimage (R i).continuous)
  have : CompleteSpace Wamb := hWclosed.completeSpace_coe
  let jW : Wamb →L[ℂ] cocE F n (ρ + 2) 3 :=
    Wamb.subtypeL.codRestrict (cocE F n (ρ + 2) 3) fun w => (Submodule.mem_inf.1 w.2).1
  have hRapp : ∀ (a : Amb F (ρ + 2) 3) i, ∀ z ∈ piece (ρ + 1) 2 {i}, ∀ j,
      extendTuple (R i a) j z = extendTuple (a i) j z := by
    intro a i z hz j
    rw [extendTuple_of_mem _ hz, extendTuple_of_mem _ (piece_anti h12
      (show (2 : ℝ) ≤ 3 by norm_num) (show (0 : ℝ) < 2 by norm_num) (subset_refl {i}) hz)]
    rfl
  refine finiteDimensional_of_compact_decomposition (E := cocE F n (ρ + 2) 3) (W := Wamb)
    (Z' := cocE F n (ρ + 3) 4) (toZeroCocycle F n hF ht2 hρr₂) ?_ jW ?_
    (resCocE F n (show ρ + 2 ≤ ρ + 3 by linarith) (show (3 : ℝ) ≤ 4 by norm_num)
      (show (0 : ℝ) < 3 by norm_num))
    (isCompactOperator_resCocE F n (show ρ + 2 < ρ + 3 by linarith) ht2
      (show (3 : ℝ) < 4 by norm_num)) ?_
  · -- surjectivity
    intro z
    obtain ⟨g, hg, hcoc, rfl⟩ := exists_eq_zeroCocycle z
    obtain ⟨g', hg', hcoc', hgg'⟩ := exists_grow_zero hF hρ (show ρ ≤ ρ + 4 by linarith) n g hg hcoc
    obtain ⟨e, he⟩ := exists_cocE_of_cocycle (r := ρ + 2) (t := 3)
      (show ρ + 2 < ρ + 4 by linarith) ht2 g' hg' hcoc'
    refine ⟨e, ?_⟩
    rw [toZeroCocycle_apply]
    refine zeroCocycle_eq fun i => ?_
    obtain ⟨U, hKU, hUh, -⟩ := hg' i
    obtain ⟨V, hKV, hVh, -⟩ := hg i
    have hrU : openCover (ρ + 2) {i} ⊆ U := fun z hz =>
      hKU (coverSet_mono (show ρ + 2 ≤ ρ + 4 by linarith) _ (openCover_subset_coverSet _ _ hz))
    have hKo : coverSet ρ {i} ⊆ openCover (ρ + 2) {i} ∩ V := fun z hz =>
      ⟨coverSet_subset_openCover hρr₂ {i} hz, hKV hz⟩
    refine isHomSection_of_eqOn F.coherent_N hKo (((isHomOn_hextComp ht2 e i).inter hVh.isOpen
      hVh.isCone).sub (hVh.inter_left (isOpen_openCover (ρ + 2) {i})
        (isCone_openCover (ρ + 2) {i})))
      (hgg' i) (coverSet_subset_openCover hρr₂ {i}) (isOpen_openCover (ρ + 2) {i})
      (isCone_openCover (ρ + 2) {i}) fun z hz j => ?_
    simp only [Pi.sub_apply]
    rw [hextComp, hext_eq_of_restrict ht2 hUh hrU (fun w hw j => he i w hw j) hz j]
  · -- `Ψ` kills the cocycles vanishing modulo `N` on the lowest level
    intro w
    rw [toZeroCocycle_apply]
    have hw : ∀ i, ∀ y ∈ piece (ρ + 1) 2 {i}, F.N.mem y (extendTuple ((jW w).1 i)) := by
      intro i y hy
      have h1 := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 w.2).2 i
      refine (coherent_N_piece F (ρ + 1) 2 {i} y hy).congr_mem (h1.2 y hy) fun j => ?_
      filter_upwards [(isOpen_piece (ρ + 1) 2 {i}).mem_nhds hy] with z hz
      exact hRapp _ i z hz j
    refine (zeroCocycle_eq (g' := (0 : Fin (N + 1) → F.ι → ConeSpace N → ℂ))
      (hg' := fun i => isHomSection_zero F.coherent_M n (coverSet_subset ρ _))
      (hcoc' := fun i k => by
        simp only [Pi.zero_apply, sub_self]
        exact isHomSection_zero F.coherent_N n (coverSet_subset ρ _)) fun i => ?_).trans
      (zeroCocycle_zero _ _)
    rw [Pi.zero_apply, sub_zero]
    refine ⟨openCover (ρ + 1) {i}, coverSet_subset_openCover (by linarith) {i}, ?_,
      fun y hy => ?_⟩
    · have h := (isHomOn_hextComp ht2 (jW w) i).inter (isOpen_openCover (ρ + 1) {i})
        (isCone_openCover (ρ + 1) {i})
      rwa [Set.inter_eq_right.2 (openCover_anti h12 (subset_refl _))] at h
    · exact mem_hext F.coherent_N hF.2 ht2 ((mem_cocE.1 (jW w).2).2.1 i) h12 (by norm_num)
        (hw i) hy
  · -- every cocycle at level `(ρ+2, 3)` is a restriction modulo `Wamb`
    intro e
    refine (exists_decomp hF hρ e).elim fun z hz => ?_
    have hmemW : (e - resCocE F n (show ρ + 2 ≤ ρ + 3 by linarith)
        (show (3 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) < 3 by norm_num) z).1 ∈ Wamb := by
      refine Submodule.mem_inf.2 ⟨Submodule.coe_mem _, (Submodule.mem_iInf _).2 fun i =>
        ⟨fun j => ?_, fun y hy => ?_⟩⟩
      · exact (((mem_cocE.1 (Submodule.coe_mem (e - _))).1 i).1 j).mono (piece_anti h12
          (by norm_num) (by norm_num) (subset_refl _)) |>.congr fun w hw => hRapp _ i w hw j
      · refine (coherent_N_piece F (ρ + 1) 2 {i} y hy).congr_mem (hz i y hy) fun j => ?_
        filter_upwards [(isOpen_piece (ρ + 1) 2 {i}).mem_nhds hy] with w hw
        exact (hRapp _ i w hw j).symm
    refine ⟨z, ⟨_, hmemW⟩, ?_⟩
    have hj : jW ⟨_, hmemW⟩ = e - resCocE F n (show ρ + 2 ≤ ρ + 3 by linarith)
        (show (3 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) < 3 by norm_num) z := rfl
    rw [hj]
    abel

/-- **`dim Ȟ⁰(ℙᴺ, 𝓕(n)) < ∞`** for every invariant subquotient (coherent sheaf) `𝓕`, every `n`
and every `ρ ≥ 1` (Čech cohomology of the closed cover `K(ρ)`). -/
theorem finiteDimensional_cechH_zero (hF : IsInvariantSubquotient F) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    FiniteDimensional ℂ (cechH (coverSystem F n ρ) 0) := by
  have := finiteDimensional_zeroCocycles (n := n) hF hρ
  exact Module.Finite.of_surjective (cechClass (coverSystem F n ρ) 0)
    (cechClass_surjective (coverSystem F n ρ) 0)

end Finite

end SGPT.GAGA.PN
