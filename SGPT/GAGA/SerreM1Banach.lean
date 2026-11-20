import SGPT.GAGA.SerreM1Shell

/-!
# Serre's theorems on `ℙᴺ`, part 3: finiteness of `Ȟ⁰(ℙᴺ, 𝓕(n))`

Infrastructure towards source `lma:GAGA` (`chapter_NApotential.tex`, lines 1143--1145): the
Cartan--Serre finiteness theorem in degree `0` for every coherent sheaf `𝓕 = M/N` on `ℙᴺ`
(an invariant subquotient in the cone model of lane SERRE-PN), for the Čech complex of the
closed cover `K(ρ)`, `ρ ≥ 1`: `finiteDimensional_cechH_zero`. Blueprint
`claude-serre-m34.tex`, node `claude-serre-m34:finite-H0`.

**Banach spaces.** At a level `(r, t)` (`r > 0`, `t > 1`) let `cocE F n r t` be the space of
families `e_i` of bounded holomorphic tuples on the pieces `V_i(r) ∩ {1/t < ‖z‖ < t}` with germs in
`M`, homogeneous of degree `n` as far as the piece allows, and with `e_k - e_i` having germs in
`N` on the piece of `V_i(r) ∩ V_k(r)`. It is a closed subspace of a finite product of spaces of
bounded continuous tuples (`isClosed_cocE`), hence a Banach space; restriction from a higher
level is a compact operator (Montel, `PNBanach`; `isCompactOperator_resLevel`).

**The argument.** Fix `ρ ≥ 1` and the levels `(ρ+1, 2) < (ρ+2, 3) < (ρ+3, 4)`. The homogeneous
extension (`hext`) maps `cocE` at level `(ρ+2, 3)` linearly onto the `0`-cocycles of the cover
`K(ρ)`; onto because every `0`-cocycle grows to the cover `K(ρ+4)` (`exists_grow_zero`). Every
element of `cocE` at level `(ρ+2,3)` is, up to an element vanishing modulo `N` on the level
`(ρ+1,2)`, the restriction of an element at level `(ρ+3,4)` (growth from `K(ρ+3/2)` to
`K(ρ+4)` again). Schwartz's theorem (`finiteDimensional_of_compact_decomposition`) gives the
finiteness.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Topology Metric
open SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core
open scoped BoundedContinuousFunction

noncomputable section

namespace SGPT.GAGA.PN

/-! ### Compact operators into finite products -/

theorem isCompactOperator_pi {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] {ι : Type}
    [Fintype ι] [DecidableEq ι] {φ : ι → Type*} [∀ i, NormedAddCommGroup (φ i)]
    [∀ i, NormedSpace ℂ (φ i)] (f : ∀ i, M →L[ℂ] φ i) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  have h : (ContinuousLinearMap.pi f : M → ∀ i, φ i) =
      fun x => ∑ i, ContinuousLinearMap.single ℂ φ i (f i x) := by
    funext x
    simp only [ContinuousLinearMap.single_apply, Finset.univ_sum_single,
      ContinuousLinearMap.coe_pi']
  rw [h]
  have key : ∀ s : Finset ι,
      IsCompactOperator fun x => ∑ i ∈ s, ContinuousLinearMap.single ℂ φ i (f i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        exact isCompactOperator_zero
    | insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact ((hf i).clm_comp (ContinuousLinearMap.single ℂ φ i)).add ih
  exact key Finset.univ

variable {N : ℕ}

/-! ### Bounded continuous tuples from continuous ones -/

section Bcf

variable {X : Type*} [TopologicalSpace X] {τ : Type} [Fintype τ]

/-- A tuple continuous on a compact `K ⊇ S`, as a bounded continuous tuple on `S`. -/
def bcfOn {S K : Set X} (hK : IsCompact K) (hSK : S ⊆ K) (g : τ → X → ℂ)
    (hg : ∀ j, ContinuousOn (g j) K) : S →ᵇ (τ → ℂ) :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x j => g j x, continuous_pi fun j => ((hg j).mono hSK).domRestrict⟩
    (2 * Classical.choose (hK.exists_bound_of_continuousOn (continuousOn_pi.2 hg)))
    fun x y => by
      have h := Classical.choose_spec (hK.exists_bound_of_continuousOn (continuousOn_pi.2 hg))
      refine (dist_le_norm_add_norm _ _).trans ?_
      have hx := h x (hSK x.2)
      have hy := h y (hSK y.2)
      change ‖fun j => g j x‖ + ‖fun j => g j y‖ ≤ _
      linarith

theorem bcfOn_apply {S K : Set X} (hK : IsCompact K) (hSK : S ⊆ K) (g : τ → X → ℂ)
    (hg : ∀ j, ContinuousOn (g j) K) (x : S) (j : τ) : bcfOn hK hSK g hg x j = g j x :=
  rfl

end Bcf

theorem extendTuple_bcfOn {τ : Type} [Fintype τ] {S K : Set (ConeSpace N)} (hK : IsCompact K)
    (hSK : S ⊆ K) (g : τ → ConeSpace N → ℂ) (hg : ∀ j, ContinuousOn (g j) K) {z : ConeSpace N}
    (hz : z ∈ S) (j : τ) : extendTuple (bcfOn hK hSK g hg) j z = g j z := by
  rw [extendTuple_of_mem _ hz]
  rfl

/-! ### Sums of `0`-cocycles -/

section CocycleAlg

variable {F : Subquotient (ConeSpace N) (puncture (ConeSpace N))} {n : ℤ} {ρ : ℝ}

theorem zeroCocycle_add {g g' : Fin (N + 1) → F.ι → ConeSpace N → ℂ}
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i))
    (hg' : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g' i))
    (hcoc' : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g' k - g' i))
    (hgg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) ((g + g') i))
    (hcocg : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) ((g + g') k - (g + g') i)) :
    zeroCocycle (g + g') hgg hcocg = zeroCocycle g hg hcoc + zeroCocycle g' hg' hcoc' := by
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    change zeroCochain (g + g') hgg {i} = zeroCochain g hg {i} + zeroCochain g' hg' {i}
    rw [zeroCochain_singleton, zeroCochain_singleton, zeroCochain_singleton]
    rfl
  · change zeroCochain (g + g') hgg s = zeroCochain g hg s + zeroCochain g' hg' s
    unfold zeroCochain
    split_ifs
    exact (add_zero 0).symm

theorem zeroCocycle_smul (c : ℂ) {g : Fin (N + 1) → F.ι → ConeSpace N → ℂ}
    (hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i))
    (hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i))
    (hgc : ∀ i, IsHomSection F.M n (coverSet ρ {i}) ((c • g) i))
    (hcocc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) ((c • g) k - (c • g) i)) :
    zeroCocycle (c • g) hgc hcocc = c • zeroCocycle g hg hcoc := by
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hs
    change zeroCochain (c • g) hgc {i} = c • zeroCochain g hg {i}
    rw [zeroCochain_singleton, zeroCochain_singleton]
    rfl
  · change zeroCochain (c • g) hgc s = c • zeroCochain g hg s
    unfold zeroCochain
    split_ifs
    exact (smul_zero c).symm

/-- `zeroCocycle` only depends on the functions. -/
theorem zeroCocycle_congr {g g' : Fin (N + 1) → F.ι → ConeSpace N → ℂ}
    {hg : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g i)}
    {hcoc : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g k - g i)}
    {hg' : ∀ i, IsHomSection F.M n (coverSet ρ {i}) (g' i)}
    {hcoc' : ∀ i k, IsHomSection F.N n (coverSet ρ {i, k}) (g' k - g' i)} (h : g = g') :
    zeroCocycle g hg hcoc = zeroCocycle g' hg' hcoc' := by
  subst h
  rfl

end CocycleAlg

/-! ### The Banach spaces of bounded `0`-cocycles -/

section Spaces

variable (F : Subquotient (ConeSpace N) (puncture (ConeSpace N))) (n : ℤ)

theorem piece_subset_of_subset {r t : ℝ} {s s' : Finset (Fin (N + 1))} (h : s ⊆ s') :
    piece r t s' ⊆ piece r t s :=
  fun _ hz => ⟨openCover_anti le_rfl h hz.1, hz.2⟩

theorem coherent_M_piece (r t : ℝ) (s : Finset (Fin (N + 1))) :
    F.M.IsCoherentOn (piece r t s) :=
  F.coherent_M.mono (piece_subset_puncture r t s)

theorem coherent_N_piece (r t : ℝ) (s : Finset (Fin (N + 1))) :
    F.N.IsCoherentOn (piece r t s) :=
  F.coherent_N.mono (piece_subset_puncture r t s)

/-- The ambient Banach space at level `(r, t)`: one bounded continuous tuple on each piece
`V_i(r) ∩ shell(t)`. -/
abbrev Amb (r t : ℝ) : Type :=
  (i : Fin (N + 1)) → (piece (N := N) r t {i} →ᵇ (F.ι → ℂ))

/-- Holomorphic with germs in `M` on the piece `i`. -/
def secSub (r t : ℝ) (i : Fin (N + 1)) : Submodule ℂ (Amb F r t) :=
  (boundedSections F.M (piece r t {i}) (coherent_M_piece F r t {i})).comap (LinearMap.proj i)

/-- Homogeneous of degree `n` on the piece `i`. -/
def homSub (r t : ℝ) (i : Fin (N + 1)) : Submodule ℂ (Amb F r t) where
  carrier := {e | IsHomShell (extendTuple (e i)) (piece r t {i}) n}
  add_mem' := by
    intro e e' he he' z hz c hc j
    simp only [Pi.add_apply, extendTuple_add]
    rw [he z hz c hc j, he' z hz c hc j]
    ring
  zero_mem' := by
    intro z _ c _ j
    simp [extendTuple_zero]
  smul_mem' := by
    intro a e he z hz c hc j
    simp only [Pi.smul_apply, extendTuple_smul]
    rw [he z hz c hc j]
    ring

/-- Restriction to a smaller piece. -/
def resPiece (r t : ℝ) {s s' : Finset (Fin (N + 1))} (h : s ⊆ s') :
    (piece (N := N) r t s →ᵇ (F.ι → ℂ)) →L[ℂ] (piece r t s' →ᵇ (F.ι → ℂ)) :=
  BoundedContinuousFunction.compContinuousCLM (F.ι → ℂ) ℂ
    ⟨Set.inclusion (piece_subset_of_subset h), continuous_inclusion _⟩

theorem extendTuple_resPiece (r t : ℝ) {s s' : Finset (Fin (N + 1))} (h : s ⊆ s')
    (f : piece (N := N) r t s →ᵇ (F.ι → ℂ)) {z : ConeSpace N} (hz : z ∈ piece r t s') (j : F.ι) :
    extendTuple (resPiece F r t h f) j z = extendTuple f j z :=
  extendTuple_compContinuous (piece_subset_of_subset h) f hz j

/-- `e_k - e_i` on the piece of `{i, k}`. -/
def diffPair (r t : ℝ) (i k : Fin (N + 1)) :
    Amb F r t →L[ℂ] (piece (N := N) r t {i, k} →ᵇ (F.ι → ℂ)) :=
  (resPiece F r t (s := {k}) (s' := {i, k}) (by simp)).comp (ContinuousLinearMap.proj k) -
    (resPiece F r t (s := {i}) (s' := {i, k}) (by simp)).comp (ContinuousLinearMap.proj i)

theorem extendTuple_diffPair (r t : ℝ) (i k : Fin (N + 1)) (e : Amb F r t) {z : ConeSpace N}
    (hz : z ∈ piece r t {i, k}) (j : F.ι) :
    extendTuple (diffPair F r t i k e) j z = extendTuple (e k) j z - extendTuple (e i) j z := by
  rw [extendTuple_of_mem _ hz, extendTuple_of_mem _ (piece_subset_of_subset (by simp) hz),
    extendTuple_of_mem _ (piece_subset_of_subset (by simp) hz)]
  rfl

/-- The cocycle condition on the pair `{i, k}`. -/
def cocSub (r t : ℝ) (i k : Fin (N + 1)) : Submodule ℂ (Amb F r t) :=
  (boundedSections F.N (piece r t {i, k}) (coherent_N_piece F r t {i, k})).comap
    (diffPair F r t i k).toLinearMap

/-- **The Banach space of bounded homogeneous `0`-cocycles** at level `(r, t)`. -/
def cocE (r t : ℝ) : Submodule ℂ (Amb F r t) :=
  ((⨅ i, secSub F r t i) ⊓ ⨅ i, homSub F n r t i) ⊓ ⨅ i, ⨅ k, cocSub F r t i k

variable {F n}

theorem mem_cocE {r t : ℝ} {e : Amb F r t} :
    e ∈ cocE F n r t ↔
      (∀ i, e i ∈ boundedSections F.M (piece r t {i}) (coherent_M_piece F r t {i})) ∧
      (∀ i, IsHomShell (extendTuple (e i)) (piece r t {i}) n) ∧
      ∀ i k, diffPair F r t i k e ∈
        boundedSections F.N (piece r t {i, k}) (coherent_N_piece F r t {i, k}) := by
  simp only [cocE, Submodule.mem_inf, Submodule.mem_iInf, and_assoc]
  exact Iff.rfl

variable (F n)

theorem isClosed_homSub (r t : ℝ) (i : Fin (N + 1)) :
    IsClosed (homSub F n r t i : Set (Amb F r t)) := by
  have h : (homSub F n r t i : Set (Amb F r t)) =
      ⋂ (z : piece (N := N) r t {i}) (c : ℂ) (hc : c • (z : ConeSpace N) ∈ piece r t {i})
        (j : F.ι), {e | e i ⟨c • (z : ConeSpace N), hc⟩ j = c ^ n * e i z j} := by
    ext e
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro he z c hc j
      have := he z z.2 c hc j
      rwa [extendTuple_of_mem _ hc, extendTuple_of_mem _ z.2] at this
    · intro he z hz c hc j
      have := he ⟨z, hz⟩ c hc j
      rw [extendTuple_of_mem _ hc, extendTuple_of_mem _ hz]
      exact this
  rw [h]
  refine isClosed_iInter fun z => isClosed_iInter fun c => isClosed_iInter fun hc =>
    isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact (continuous_apply j).comp ((continuous_eval_const _).comp
      (continuous_apply i))
  · exact continuous_const.mul ((continuous_apply j).comp
      ((continuous_eval_const _).comp (continuous_apply i)))

theorem isClosed_cocE (r t : ℝ) : IsClosed (cocE F n r t : Set (Amb F r t)) := by
  simp only [cocE, Submodule.coe_inf, Submodule.coe_iInf]
  refine ((isClosed_iInter fun i => ?_).inter (isClosed_iInter fun i => isClosed_homSub F n r t i)
    ).inter (isClosed_iInter fun i => isClosed_iInter fun k => ?_)
  · exact (isClosed_boundedSections (M := F.M) (isOpen_piece r t {i})
      (coherent_M_piece F r t {i})).preimage
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun i => piece (N := N) r t {i} →ᵇ (F.ι → ℂ))
        i).continuous
  · exact (isClosed_boundedSections (M := F.N) (isOpen_piece r t {i, k})
      (coherent_N_piece F r t {i, k})).preimage (diffPair F r t i k).continuous

instance completeSpace_cocE (r t : ℝ) : CompleteSpace (cocE F n r t) :=
  (isClosed_cocE F n r t).completeSpace_coe

/-! #### Restriction between levels -/

/-- Restriction from level `(r', t')` to a lower level `(r, t)`. -/
def resLevel {r r' t t' : ℝ} (hr : r ≤ r') (ht : t ≤ t') (ht0 : 0 < t) :
    Amb F r' t' →L[ℂ] Amb F r t :=
  ContinuousLinearMap.pi fun i =>
    (BoundedContinuousFunction.compContinuousCLM (F.ι → ℂ) ℂ
      ⟨Set.inclusion (piece_anti hr ht ht0 (subset_refl {i})), continuous_inclusion _⟩).comp
    (ContinuousLinearMap.proj i)

theorem extendTuple_resLevel {r r' t t' : ℝ} (hr : r ≤ r') (ht : t ≤ t') (ht0 : 0 < t)
    (e : Amb F r' t') (i : Fin (N + 1)) {z : ConeSpace N} (hz : z ∈ piece r t {i}) (j : F.ι) :
    extendTuple (resLevel F hr ht ht0 e i) j z = extendTuple (e i) j z := by
  rw [extendTuple_of_mem _ hz, extendTuple_of_mem _ (piece_anti hr ht ht0 (subset_refl {i}) hz)]
  rfl

variable {F n}

theorem resLevel_mem {r r' t t' : ℝ} (hr : r ≤ r') (ht : t ≤ t') (ht0 : 0 < t)
    {e : Amb F r' t'} (he : e ∈ cocE F n r' t') : resLevel F hr ht ht0 e ∈ cocE F n r t := by
  obtain ⟨ha, hb, hc⟩ := mem_cocE.1 he
  have hsub : ∀ s : Finset (Fin (N + 1)), piece r t s ⊆ piece r' t' s := fun s =>
    piece_anti hr ht ht0 (subset_refl s)
  refine mem_cocE.2 ⟨fun i => ⟨fun j => ((ha i).1 j).mono (hsub {i}) |>.congr fun z hz =>
    extendTuple_resLevel F hr ht ht0 e i hz j, fun y hy => ?_⟩, fun i z hz c hc j => ?_,
    fun i k => ⟨fun j => ?_, fun y hy => ?_⟩⟩
  · refine (coherent_M_piece F r t {i} y hy).congr_mem ((ha i).2 y (hsub {i} hy)) fun j => ?_
    filter_upwards [(isOpen_piece r t {i}).mem_nhds hy] with z hz
    exact (extendTuple_resLevel F hr ht ht0 e i hz j).symm
  · rw [extendTuple_resLevel F hr ht ht0 e i hc, extendTuple_resLevel F hr ht ht0 e i hz]
    exact hb i z (hsub {i} hz) c (hsub {i} hc) j
  · refine (((hc i k).1 j).mono (hsub {i, k})).congr fun z hz => ?_
    rw [extendTuple_diffPair F r t i k _ hz, extendTuple_diffPair F r' t' i k _ (hsub _ hz),
      extendTuple_resLevel F hr ht ht0 e k (piece_subset_of_subset (by simp) hz),
      extendTuple_resLevel F hr ht ht0 e i (piece_subset_of_subset (by simp) hz)]
  · refine (coherent_N_piece F r t {i, k} y hy).congr_mem ((hc i k).2 y (hsub _ hy)) fun j => ?_
    filter_upwards [(isOpen_piece r t {i, k}).mem_nhds hy] with z hz
    rw [extendTuple_diffPair F r t i k _ hz, extendTuple_diffPair F r' t' i k _ (hsub _ hz),
      extendTuple_resLevel F hr ht ht0 e k (piece_subset_of_subset (by simp) hz),
      extendTuple_resLevel F hr ht ht0 e i (piece_subset_of_subset (by simp) hz)]

variable (F n)

/-- The restriction as a map of Banach spaces of cocycles. -/
def resCocE {r r' t t' : ℝ} (hr : r ≤ r') (ht : t ≤ t') (ht0 : 0 < t) :
    cocE F n r' t' →L[ℂ] cocE F n r t :=
  ((resLevel F hr ht ht0).comp (cocE F n r' t').subtypeL).codRestrict _ fun e =>
    resLevel_mem hr ht ht0 e.2

/-- The `i`-th component of a cocycle as a bounded section of `M`. -/
def compSec (r t : ℝ) (i : Fin (N + 1)) :
    cocE F n r t →L[ℂ] boundedSections F.M (piece r t {i}) (coherent_M_piece F r t {i}) :=
  ((ContinuousLinearMap.proj i).comp (cocE F n r t).subtypeL).codRestrict _ fun e =>
    (mem_cocE.1 e.2).1 i

/-- **Compactness of restriction** (Montel): from level `(r', t')` to a level `(r, t)` with
`r < r'`, `1 < t < t'`. -/
theorem isCompactOperator_resCocE {r r' t t' : ℝ} (hr : r < r') (ht1 : 1 < t) (ht : t < t') :
    IsCompactOperator (resCocE F n hr.le ht.le (by linarith)) := by
  classical
  have h0 : (0 : ℝ) < t := by linarith
  have hcomp : IsCompactOperator ((resLevel F hr.le ht.le h0).comp (cocE F n r' t').subtypeL) := by
    have hfac : (resLevel F hr.le ht.le h0).comp (cocE F n r' t').subtypeL =
        ContinuousLinearMap.pi fun i =>
          (boundedSections F.M (piece r t {i}) (coherent_M_piece F r t {i})).subtypeL.comp
            ((restrictSections (coherent_M_piece F r' t' {i}) (isOpen_piece r t {i})
              (piece_anti hr.le ht.le h0 (subset_refl {i}))).comp (compSec F n r' t' i)) :=
      ContinuousLinearMap.ext fun e => rfl
    rw [hfac]
    refine isCompactOperator_pi (M := cocE F n r' t')
      (φ := fun i => piece (N := N) r t {i} →ᵇ (F.ι → ℂ)) _ fun i => ?_
    obtain ⟨K, hK, h1, h2⟩ := exists_isCompact_between hr ht1 ht {i}
    exact ((isCompactOperator_restrictSections (isOpen_piece r' t' {i}) (isOpen_piece r t {i})
      hK h1 h2 (coherent_M_piece F r' t' {i})).comp_clm (compSec F n r' t' i)).clm_comp
      (boundedSections F.M (piece r t {i}) (coherent_M_piece F r t {i})).subtypeL
  exact hcomp.codRestrict (fun e => resLevel_mem hr.le ht.le h0 e.2) (isClosed_cocE F n r t)

end Spaces

end SGPT.GAGA.PN
