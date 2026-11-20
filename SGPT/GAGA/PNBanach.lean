import SGPT.GAGA.CoreClosure
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Banach spaces of bounded sections of a coherent module and compact restrictions

Infrastructure of lane SERRE-PN (Serre's GAGA on `ℙᴺ`, towards source `lma:GAGA`,
`chapter_NApotential.tex` lines 1143--1145), milestone M3.4 of the plan in
`blueprint/src/claude-serre-core.tex`: the functional-analytic objects of the Cartan--Serre
proof of `dim H¹(ℙᴺ, 𝓕) < ∞`. Source for the mathematics: Cartan--Serre, *Un théorème de
finitude concernant les variétés analytiques compactes* (1953); Grauert--Remmert, *Coherent
analytic sheaves*, Ch. 6.

Let `M ⊆ 𝒪^ι` be a coherent germ module on an open set `U ⊆ ℂⁿ`.

* `boundedSections M U hM`: the bounded holomorphic tuples on `U` whose germs lie in `M` at
  every point of `U`, a subspace of the Banach space `U →ᵇ (ι → ℂ)` (sup norm).
* `isClosed_boundedSections`, `completeSpace_boundedSections`: it is closed, hence a Banach
  space. Holomorphy passes to uniform limits by Montel's theorem (TN), and membership in `M`
  by the closure theorem of lane SERRE-CORE (`GermModule.CoherentAt.mem_of_tendstoUniformlyOn`,
  Krull).
* `exists_subseq_uniformCauchySeqOn`: Montel's theorem for finitely many uniformly bounded
  sequences of holomorphic functions on `U`, in the form "a common subsequence is uniformly
  Cauchy on a given compact `K ⊆ U`".
* `restrictSections`, `isCompactOperator_restrictSections`: for open `U' ⊆ K ⊆ U` with `K`
  compact, the restriction `boundedSections M U → boundedSections M U'` is a compact operator.

Together with `PNSchwartz` (Schwartz's theorem) these are the analytic tools of the
finiteness theorem.

Blueprint: `claude-serre-pn.tex`, nodes `claude-serre-pn:banach`, `claude-serre-pn:montel`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set Metric
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
open SGPT.GAGA.Core
open scoped BoundedContinuousFunction

namespace SGPT.GAGA.PN

/-! ### Totally bounded sets via Cauchy subsequences -/

/-- A set in which every sequence has a Cauchy subsequence is totally bounded. -/
theorem totallyBounded_of_forall_subseq_cauchySeq {X : Type*} [UniformSpace X] {s : Set X}
    (h : ∀ u : ℕ → X, (∀ n, u n ∈ s) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (u ∘ φ)) :
    TotallyBounded s := by
  intro V V_in
  by_contra! hcon
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧
      ∀ n m, m < n → u m ∉ UniformSpace.ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at hcon
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists hcon
  obtain ⟨φ, hφ, huφ⟩ := h u u_in
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    huφ.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| Nat.lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)

variable {n : ℕ} {ι : Type} [Fintype ι]

/-! ### Montel's theorem for tuples -/

/-- Uniform Cauchy sequences stay uniformly Cauchy along a strictly monotone reindexing. -/
theorem uniformCauchySeqOn_comp_strictMono {α β : Type*} [UniformSpace β] {F : ℕ → α → β}
    {s : Set α} (h : UniformCauchySeqOn F atTop s) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    UniformCauchySeqOn (fun m => F (ψ m)) atTop s :=
  fun u hu => (hψ.tendsto_atTop.prodMap hψ.tendsto_atTop).eventually (h u hu)

/-- **Montel's theorem for tuples, uniform form.** Uniformly bounded sequences `F · j`
(`j ∈ ι`) of functions holomorphic on an open `U ⊆ ℂⁿ` have a common subsequence which is
uniformly Cauchy on every given compact `K ⊆ U`. -/
theorem exists_subseq_uniformCauchySeqOn {U K : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (F : ℕ → ι → EuclideanSpace ℂ (Fin n) → ℂ) (hF : ∀ m j, DifferentiableOn ℂ (F m j) U)
    {C : ℝ} (hC : ∀ m j, ∀ x ∈ U, ‖F m j x‖ ≤ C) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, UniformCauchySeqOn (fun m => F (ψ m) j) atTop K := by
  classical
  suffices h : ∀ s : Finset ι, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ j ∈ s, UniformCauchySeqOn (fun m => F (ψ m) j) atTop K by
    obtain ⟨ψ, hψ, h⟩ := h Finset.univ
    exact ⟨ψ, hψ, fun j => h j (Finset.mem_univ j)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert j₀ s _ ih =>
    obtain ⟨ψ₁, hψ₁, h₁⟩ := ih
    obtain ⟨ψ₂, G, hψ₂, -, hconv⟩ := exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded
      hU (fun m => F (ψ₁ m) j₀) fun x hx => by
        obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
        exact ⟨r, hr, C, Eventually.of_forall fun m =>
          ⟨(hF _ j₀).mono hrU, fun y hy => hC _ j₀ y (hrU hy)⟩⟩
    have hK₀ : UniformCauchySeqOn (fun m => F (ψ₁ (ψ₂ m)) j₀) atTop K :=
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hKU hK).uniformCauchySeqOn
    refine ⟨ψ₁ ∘ ψ₂, hψ₁.comp hψ₂, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hK₀
    · exact uniformCauchySeqOn_comp_strictMono (h₁ j hj) hψ₂

/-! ### Bounded sections -/

section Bounded

variable {U U' : Set (EuclideanSpace ℂ (Fin n))}

open Classical in
/-- A bounded continuous tuple on `U`, extended by `0` outside `U`. -/
noncomputable def extendTuple (f : U →ᵇ (ι → ℂ)) : ι → EuclideanSpace ℂ (Fin n) → ℂ :=
  fun j x => if h : x ∈ U then f ⟨x, h⟩ j else 0

theorem extendTuple_of_mem (f : U →ᵇ (ι → ℂ)) {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U)
    (j : ι) : extendTuple f j x = f ⟨x, hx⟩ j :=
  dif_pos hx

theorem extendTuple_add (f g : U →ᵇ (ι → ℂ)) :
    extendTuple (f + g) = fun j x => extendTuple f j x + extendTuple g j x := by
  funext j x
  unfold extendTuple
  split_ifs <;> simp

theorem extendTuple_smul (c : ℂ) (f : U →ᵇ (ι → ℂ)) :
    extendTuple (c • f) = fun j x => c * extendTuple f j x := by
  funext j x
  unfold extendTuple
  split_ifs <;> simp

theorem extendTuple_zero : extendTuple (0 : U →ᵇ (ι → ℂ)) = fun _ _ => 0 := by
  funext j x
  unfold extendTuple
  split_ifs <;> simp

theorem norm_extendTuple_le (f : U →ᵇ (ι → ℂ)) {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U)
    (j : ι) : ‖extendTuple f j x‖ ≤ ‖f‖ := by
  rw [extendTuple_of_mem f hx]
  exact (norm_le_pi_norm _ j).trans (f.norm_coe_le_norm _)

/-- **Bounded sections.** The bounded tuples on `U`, holomorphic on `U`, with germs in `M` at
every point of `U`: a subspace of `U →ᵇ (ι → ℂ)` with the sup norm. -/
def boundedSections (M : GermModule (EuclideanSpace ℂ (Fin n)) ι)
    (U : Set (EuclideanSpace ℂ (Fin n)))
    (hM : M.IsCoherentOn U) : Submodule ℂ (U →ᵇ (ι → ℂ)) where
  carrier := {f | (∀ j, DifferentiableOn ℂ (extendTuple f j) U) ∧
    ∀ y ∈ U, M.mem y (extendTuple f)}
  add_mem' := by
    rintro f g ⟨hf, hfM⟩ ⟨hg, hgM⟩
    refine ⟨fun j => ?_, fun y hy => ?_⟩
    · rw [extendTuple_add]
      exact (hf j).add (hg j)
    · rw [extendTuple_add]
      exact (hM y hy).add_mem (hfM y hy) (hgM y hy)
  zero_mem' := by
    refine ⟨fun j => ?_, fun y hy => ?_⟩
    · rw [extendTuple_zero]
      exact differentiableOn_const 0
    · rw [extendTuple_zero]
      exact (hM y hy).zero_mem
  smul_mem' := by
    rintro c f ⟨hf, hfM⟩
    refine ⟨fun j => ?_, fun y hy => ?_⟩
    · rw [extendTuple_smul]
      exact (differentiableOn_const c).mul (hf j)
    · rw [extendTuple_smul]
      exact (hM y hy).smul_mem (holAt_const c y) (hfM y hy)

variable {M : GermModule (EuclideanSpace ℂ (Fin n)) ι}

/-- **The bounded sections form a closed subspace**: holomorphy and membership in `M` pass to
uniform limits. -/
theorem isClosed_boundedSections (hU : IsOpen U) (hM : M.IsCoherentOn U) :
    IsClosed (boundedSections M U hM : Set (U →ᵇ (ι → ℂ))) := by
  refine IsSeqClosed.isClosed fun f g hf hfg => ?_
  have hunif : ∀ j, TendstoUniformlyOn (fun m => extendTuple (f m) j) (extendTuple g j)
      atTop U := by
    intro j
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 hfg ε hε] with m hm x hx
    rw [extendTuple_of_mem g hx, extendTuple_of_mem (f m) hx, dist_eq_norm]
    calc ‖g ⟨x, hx⟩ j - f m ⟨x, hx⟩ j‖ ≤ ‖g ⟨x, hx⟩ - f m ⟨x, hx⟩‖ :=
          norm_le_pi_norm (g ⟨x, hx⟩ - f m ⟨x, hx⟩) j
      _ = dist (g ⟨x, hx⟩) (f m ⟨x, hx⟩) := (dist_eq_norm _ _).symm
      _ ≤ dist g (f m) := BoundedContinuousFunction.dist_coe_le_dist _
      _ < ε := by rw [dist_comm]; exact hm
  have hdiff : ∀ j, DifferentiableOn ℂ (extendTuple g j) U := by
    intro j
    obtain ⟨ψ, G, hψ, hG, hconv⟩ :=
      exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded hU
        (fun m => extendTuple (f m) j) fun x hx => by
          obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
          refine ⟨r, hr, ‖g‖ + 1, ?_⟩
          filter_upwards [Metric.tendsto_nhds.1 hfg 1 one_pos] with m hm
          refine ⟨((hf m).1 j).mono hrU, fun y hy => ?_⟩
          refine (norm_extendTuple_le (f m) (hrU hy) j).trans ?_
          calc ‖f m‖ ≤ ‖g‖ + ‖f m - g‖ := norm_le_norm_add_norm_sub' _ _
            _ ≤ ‖g‖ + 1 := by rw [← dist_eq_norm]; linarith
    refine hG.congr fun y hy => ?_
    exact tendsto_nhds_unique (((hunif j).tendsto_at hy).comp hψ.tendsto_atTop)
      (hconv.tendsto_at hy)
  refine ⟨hdiff, fun y hy => ?_⟩
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hy
  exact (hM y hy).mem_of_tendstoUniformlyOn hr (fun m j => ((hf m).1 j).mono hrU)
    (fun j => (hdiff j).mono hrU) (fun m => (hf m).2 y hy) fun j => (hunif j).mono hrU

/-- **The bounded sections of a coherent module form a Banach space.** -/
theorem completeSpace_boundedSections (hU : IsOpen U) (hM : M.IsCoherentOn U) :
    CompleteSpace (boundedSections M U hM) :=
  (isClosed_boundedSections hU hM).completeSpace_coe

theorem extendTuple_compContinuous (h : U' ⊆ U) (f : U →ᵇ (ι → ℂ))
    {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U') (j : ι) :
    extendTuple (f.compContinuous ⟨Set.inclusion h, continuous_inclusion h⟩) j x =
      extendTuple f j x := by
  rw [extendTuple_of_mem _ hx, extendTuple_of_mem _ (h hx)]
  rfl

/-- **Restriction** of bounded sections from `U` to an open `U' ⊆ U`. -/
noncomputable def restrictSections (hM : M.IsCoherentOn U) (hU' : IsOpen U') (h : U' ⊆ U) :
    boundedSections M U hM →L[ℂ] boundedSections M U' (hM.mono h) :=
  ((BoundedContinuousFunction.compContinuousCLM (ι → ℂ) ℂ
      ⟨Set.inclusion h, continuous_inclusion h⟩).comp
    (boundedSections M U hM).subtypeL).codRestrict _ fun f => by
    refine ⟨fun j => ((f.2.1 j).mono h).congr fun x hx => ?_, fun y hy => ?_⟩
    · exact extendTuple_compContinuous h f.1 hx j
    · refine (hM y (h hy)).congr_mem (f.2.2 y (h hy)) fun j => ?_
      exact eventually_of_mem (hU'.mem_nhds hy) fun x hx =>
        (extendTuple_compContinuous h f.1 hx j).symm

theorem restrictSections_apply (hM : M.IsCoherentOn U) (hU' : IsOpen U') (h : U' ⊆ U)
    (f : boundedSections M U hM) {x : EuclideanSpace ℂ (Fin n)} (hx : x ∈ U') (j : ι) :
    extendTuple (restrictSections hM hU' h f).1 j x = extendTuple f.1 j x :=
  extendTuple_compContinuous h f.1 hx j

/-- **Compactness of restriction (Montel).** If `U' ⊆ K ⊆ U` with `U, U'` open and `K`
compact, the restriction of bounded sections of a coherent module from `U` to `U'` is a
compact operator. -/
theorem isCompactOperator_restrictSections {K : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hU' : IsOpen U') (hK : IsCompact K) (hU'K : U' ⊆ K) (hKU : K ⊆ U)
    (hM : M.IsCoherentOn U) :
    IsCompactOperator (restrictSections hM hU' (hU'K.trans hKU)) := by
  have hc : CompleteSpace (boundedSections M U' (hM.mono (hU'K.trans hKU))) :=
    completeSpace_boundedSections hU' _
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image]
  refine ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, ?_⟩
  refine (TotallyBounded.closure ?_).isCompact_of_isClosed isClosed_closure
  refine totallyBounded_of_forall_subseq_cauchySeq fun u hu => ?_
  choose f hfB hfu using hu
  obtain ⟨ψ, hψ, hcauchy⟩ := exists_subseq_uniformCauchySeqOn hU hK hKU
    (fun m => extendTuple (f m).1) (fun m j => (f m).2.1 j) (C := 1) fun m j x hx =>
      (norm_extendTuple_le (f m).1 hx j).trans (mem_closedBall_zero_iff.1 (hfB m))
  refine ⟨ψ, hψ, Metric.cauchySeq_iff.2 fun ε hε => ?_⟩
  have hN : ∀ j, ∃ N, ∀ m ≥ N, ∀ k ≥ N, ∀ x ∈ K,
      dist (extendTuple (f (ψ m)).1 j x) (extendTuple (f (ψ k)).1 j x) < ε / 2 :=
    fun j => Metric.uniformCauchySeqOn_iff.1 (hcauchy j) (ε / 2) (half_pos hε)
  choose N hN using hN
  refine ⟨Finset.univ.sup N, fun m hm k hk => ?_⟩
  have hNj : ∀ j, N j ≤ Finset.univ.sup N := fun j => Finset.le_sup (Finset.mem_univ j)
  simp only [Function.comp_apply, ← hfu]
  rw [Subtype.dist_eq]
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x => ?_)
    (half_lt_self hε)
  rw [dist_pi_le_iff (half_pos hε).le]
  intro j
  have e : ∀ a : boundedSections M U hM,
      (restrictSections hM hU' (hU'K.trans hKU) a).1 x j = extendTuple a.1 j x := fun a => by
    rw [← restrictSections_apply hM hU' (hU'K.trans hKU) a x.2 j, extendTuple_of_mem _ x.2]
  rw [e, e]
  exact (hN j m ((hNj j).trans hm) k ((hNj j).trans hk) x (hU'K x.2)).le

end Bounded

end SGPT.GAGA.PN
