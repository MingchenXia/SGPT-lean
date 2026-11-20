import SGPT.GAGA.CoreOkaModules
import SGPT.Foundations.Analysis.Pending.OkaGermBridge
import SGPT.Foundations.Analysis.Pending.HironakaHolomorphicPointJets
import SGPT.Foundations.Analysis.Pending.HolomorphicAnalytic

/-!
# Stalks of coherent modules are closed: Krull's theorem and uniform limits

Infrastructure of lane SERRE-CORE (Serre's GAGA, towards source `lma:GAGA`). Source for the
mathematics: Cartan's closure theorem for submodules of `𝒪^p` in its stalkwise form
(Grauert--Remmert, *Coherent analytic sheaves*, Ch. 2 §1 and Ch. 5 §6; Gunning--Rossi, II.D),
proved here by Krull's intersection theorem.

* `germTuple y a`: the tuple of germs at the origin of `x ↦ a_j (y + x)` (TN `germAt`), an
  element of the free module `(𝒪_{X,0})^ι` over TN's germ ring `HolGerm X`;
  `isCombinationAt_iff_germTuple_mem`: `a` is a combination of the `σ_k` at `y` iff `a` is
  holomorphic at `y` and its germ lies in the submodule spanned by the germs of the `σ_k`.
  So the stalk of a coherent germ module is a finitely generated `𝒪_{X,0}`-submodule.
* `CoherentAt.mem_of_jets` (**Krull**): on `ℂⁿ`, if for every `q` some member of `M_y` has the
  same derivatives of order `< q` at `y` as `b`, then `b ∈ M_y`. (The stalk is the intersection
  of the submodules `M_y + 𝔪^q 𝒪^ι`, and `𝔪^q` is the kernel of the `q`-jet, TN
  `mem_maximalIdeal_pow_iff_iteratedFDeriv`.)
* `CoherentAt.mem_of_tendstoUniformlyOn` (**closure theorem**): a uniform limit, on a ball
  around `y`, of members of `M_y` holomorphic on that ball is a member of `M_y`. The jets of
  members form a finite-dimensional, hence closed, subspace, and jets converge by the Cauchy
  estimates (TN `norm_factorial_inv_smul_iteratedFDeriv_le`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Filter Topology Set Metric
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.OkaRelationSheaf
  SGPT.Foundations.Analysis.Pending.OkaGermBridge

namespace SGPT.GAGA.Core

/-! ### Germs of tuples -/

section Germs

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {ι μ : Type} [Fintype ι]
  [Fintype μ]

/-- The germs at the origin of the translates `x ↦ a_j (y + x)`. -/
noncomputable def germTuple (y : X) (a : ι → X → ℂ) : ι → HolGerm X :=
  fun j => germAt y (a j)

/-- The submodule of `(𝒪_{X,0})^ι` spanned by the germs at `y` of finitely many tuples. -/
noncomputable def germSpan (y : X) (σ : μ → ι → X → ℂ) :
    Submodule (HolGerm X) (ι → HolGerm X) :=
  Submodule.span (HolGerm X) (Set.range fun k => germTuple y (σ k))

theorem germAt_sub' {f g : X → ℂ} {y : X} (hf : HolAt f y) (hg : HolAt g y) :
    germAt y (fun x => f x - g x) = germAt y f - germAt y g := by
  have h := germAt_add hf hg.neg
  rw [germAt_neg hg] at h
  simpa only [sub_eq_add_neg] using h

/-- Germs of combinations are combinations of germs. -/
theorem germTuple_combination {σ : μ → ι → X → ℂ} {y : X} (hσ : ∀ k j, HolAt (σ k j) y)
    {c : μ → X → ℂ} (hc : ∀ k, HolAt (c k) y) :
    germTuple y (fun j x => ∑ k, c k x * σ k j x) =
      ∑ k, germAt y (c k) • germTuple y (σ k) := by
  funext j
  simp only [germTuple, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [germAt_sum _ fun k _ => (hc k).mul (hσ k j)]
  exact Finset.sum_congr rfl fun k _ => germAt_mul (hc k) (hσ k j)

/-- **Combinations are membership in the span of the germs.** -/
theorem isCombinationAt_iff_germTuple_mem {σ : μ → ι → X → ℂ} {y : X}
    (hσ : ∀ k j, HolAt (σ k j) y) {a : ι → X → ℂ} :
    IsCombinationAt σ y a ↔ HolTupleAt a y ∧ germTuple y a ∈ germSpan y σ := by
  constructor
  · intro ha
    have hah := IsCombinationAt.holTupleAt hσ ha
    refine ⟨hah, ?_⟩
    obtain ⟨c, hc, hca⟩ := ha
    have hsum : ∀ j, HolAt (fun x => ∑ k, c k x * σ k j x) y := fun j =>
      HolAt.fintype_sum fun k => (hc k).mul (hσ k j)
    have heq : germTuple y a = germTuple y (fun j x => ∑ k, c k x * σ k j x) := by
      funext j
      exact (germAt_eq_germAt_iff (hah j) (hsum j)).2 (hca j)
    rw [heq, germTuple_combination hσ hc]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro ⟨ha, hmem⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    choose c' hc' hcc' using fun k => exists_germAt_eq (c k) y
    refine ⟨c', hc', fun j => ?_⟩
    have hsum : HolAt (fun x => ∑ k, c' k x * σ k j x) y :=
      HolAt.fintype_sum fun k => (hc' k).mul (hσ k j)
    rw [← germAt_eq_germAt_iff (ha j) hsum]
    have h1 := congrFun (germTuple_combination hσ hc') j
    have h2 := congrFun hc j
    simp only [hcc'] at h1
    rw [show germAt y (fun x => ∑ k, c' k x * σ k j x) =
      germTuple y (fun j x => ∑ k, c' k x * σ k j x) j from rfl, h1, h2]
    rfl

/-- At a point of a generating set, membership is membership of the germ in the span of the
germs of the generators: the stalk is a finitely generated `𝒪_{X,0}`-module. -/
theorem GermModule.GeneratedOn.mem_iff_germTuple {M : GermModule X ι} {U : Set X}
    {σ : μ → ι → X → ℂ} (h : M.GeneratedOn U σ) (hU : IsOpen U) {y : X} (hy : y ∈ U)
    (a : ι → X → ℂ) : M.mem y a ↔ HolTupleAt a y ∧ germTuple y a ∈ germSpan y σ :=
  (h.2 y hy a).trans (isCombinationAt_iff_germTuple_mem (h.holAt hU hy))

/-- A function holomorphic near a point of a finite-dimensional space is smooth there. -/
theorem contDiffAt_of_holAt [FiniteDimensional ℂ X] {f : X → ℂ} {y : X} (hf : HolAt f y)
    {m : WithTop ℕ∞} : ContDiffAt ℂ m f y := by
  obtain ⟨V, hV, hyV, hfV⟩ := hf.exists_isOpen
  exact (HolomorphicAnalytic.analyticAt_of_differentiableOn hV hfV hyV).contDiffAt

end Germs

/-! ### Krull's theorem: membership is detected by finite jets -/

section Krull

variable {n : ℕ} {ι : Type} [Fintype ι]

/-- `𝔪^q` is the kernel of the `q`-jet at `y`. -/
theorem germAt_mem_maximalIdeal_pow_iff {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hf : HolAt f y) (q : ℕ) :
    germAt y f ∈ IsLocalRing.maximalIdeal (HolGerm (EuclideanSpace ℂ (Fin n))) ^ q ↔
      ∀ k < q, iteratedFDeriv ℂ k f y = 0 := by
  rw [germAt_of_holAt hf,
    HironakaHolomorphicPointJets.mem_maximalIdeal_pow_iff_iteratedFDeriv]
  simp only [iteratedFDeriv_comp_add_left, add_zero]

/-- **Krull's theorem for coherent modules.** If `M` is coherent at `y ∈ ℂⁿ` and, for every
`q`, some member of `M_y` has the same derivatives of order `< q` at `y` as the holomorphic
tuple `b`, then `b ∈ M_y`. -/
theorem GermModule.CoherentAt.mem_of_jets {M : GermModule (EuclideanSpace ℂ (Fin n)) ι}
    {y : EuclideanSpace ℂ (Fin n)} (hM : M.CoherentAt y) {b : ι → EuclideanSpace ℂ (Fin n) → ℂ}
    (hb : HolTupleAt b y)
    (h : ∀ q : ℕ, ∃ a, M.mem y a ∧
      ∀ j, ∀ k < q, iteratedFDeriv ℂ k (a j) y = iteratedFDeriv ℂ k (b j) y) :
    M.mem y b := by
  classical
  have := isNoetherianRing_holGerm_euclidean n
  obtain ⟨U, hU, hyU, μ', _, σ, hσ⟩ := hM
  rw [hσ.mem_iff_germTuple hU hyU]
  refine ⟨hb, ?_⟩
  set R := HolGerm (EuclideanSpace ℂ (Fin n))
  set S := germSpan y σ
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := (ι → R) ⧸ S)
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hmem : S.mkQ (germTuple y b) ∈
      (⨅ q : ℕ, (IsLocalRing.maximalIdeal R) ^ q • ⊤ : Submodule R ((ι → R) ⧸ S)) := by
    rw [Submodule.mem_iInf]
    intro q
    obtain ⟨a, haM, hjet⟩ := h q
    have ha : HolTupleAt a y := hσ.holTupleAt hU hyU haM
    have haS : germTuple y a ∈ S := ((hσ.mem_iff_germTuple hU hyU a).1 haM).2
    have hdiff : ∀ j, germAt y (fun x => b j x - a j x) ∈
        IsLocalRing.maximalIdeal R ^ q := by
      intro j
      rw [germAt_mem_maximalIdeal_pow_iff ((hb j).sub (ha j))]
      intro k hk
      have hs := iteratedFDeriv_sub_apply (𝕜 := ℂ) (i := k) (x := y)
        (contDiffAt_of_holAt (hb j)) (contDiffAt_of_holAt (ha j))
      rw [show (fun x => b j x - a j x) = b j - a j from rfl, hs, hjet j k hk, sub_self]
    have hsplit : germTuple y b = germTuple y a +
        ∑ j, germAt y (fun x => b j x - a j x) • Pi.single j (1 : R) := by
      funext j'
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, germTuple]
      rw [germAt_sub' (hb j') (ha j')]
      ring
    rw [hsplit, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero S).2 haS, zero_add,
      map_sum]
    exact Submodule.sum_mem _ fun j _ => by
      rw [map_smul]
      exact Submodule.smul_mem_smul (hdiff j) Submodule.mem_top
  rw [hK, Submodule.mem_bot, Submodule.mkQ_apply] at hmem
  exact (Submodule.Quotient.mk_eq_zero S).1 hmem

end Krull

/-! ### The closure theorem -/

section Closure

variable {n : ℕ} {ι : Type} [Fintype ι]

instance finiteDimensional_continuousMultilinearMap (k : ℕ) :
    FiniteDimensional ℂ
      (ContinuousMultilinearMap ℂ (fun _ : Fin k => EuclideanSpace ℂ (Fin n)) ℂ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℂ))
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- The space of `q`-jets of `ι`-tuples of functions on `ℂⁿ`. -/
abbrev JetSpace (n : ℕ) (ι : Type) (q : ℕ) : Type :=
  (k : Fin q) → ι → ContinuousMultilinearMap ℂ (fun _ : Fin k => EuclideanSpace ℂ (Fin n)) ℂ

/-- The `q`-jet of a tuple at `y`. -/
noncomputable def jet (y : EuclideanSpace ℂ (Fin n)) (q : ℕ)
    (a : ι → EuclideanSpace ℂ (Fin n) → ℂ) : JetSpace n ι q :=
  fun k j => iteratedFDeriv ℂ k (a j) y

/-- Derivatives at the centre of a ball converge under uniform convergence on the ball. -/
theorem tendsto_iteratedFDeriv_of_tendstoUniformlyOn {y : EuclideanSpace ℂ (Fin n)} {r : ℝ}
    (hr : 0 < r) {f : ℕ → EuclideanSpace ℂ (Fin n) → ℂ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ∀ m, DifferentiableOn ℂ (f m) (ball y r)) (hg : DifferentiableOn ℂ g (ball y r))
    (hlim : TendstoUniformlyOn f g atTop (ball y r)) (k : ℕ) :
    Tendsto (fun m => iteratedFDeriv ℂ k (f m) y) atTop (𝓝 (iteratedFDeriv ℂ k g y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := (k.factorial : ℝ) * Real.exp 1 * (Real.exp 1 / r) ^ k + 1 with hC
  have hC0 : 0 < C := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hlim (ε / C) (div_pos hε hC0)).exists_forall_of_atTop
  refine ⟨N, fun m hm => ?_⟩
  have hyball : ball y r ∈ 𝓝 y := isOpen_ball.mem_nhds (mem_ball_self hr)
  have hdiff : DifferentiableOn ℂ (fun w => f m w - g w) (ball y r) := (hf m).sub hg
  have hbound : ∀ w ∈ ball y r, ‖f m w - g w‖ ≤ ε / C := fun w hw => by
    rw [← dist_eq_norm, dist_comm]
    exact (hN m hm w hw).le
  have hest := HolomorphicAnalytic.norm_factorial_inv_smul_iteratedFDeriv_le hr hdiff hbound k
  have hsub : iteratedFDeriv ℂ k (fun w => f m w - g w) y =
      iteratedFDeriv ℂ k (f m) y - iteratedFDeriv ℂ k g y :=
    iteratedFDeriv_sub_apply
      (contDiffAt_of_holAt (holAt_of_differentiableOn isOpen_ball (hf m) (mem_ball_self hr)))
      (contDiffAt_of_holAt (holAt_of_differentiableOn isOpen_ball hg (mem_ball_self hr)))
  rw [hsub, norm_smul, norm_inv, Complex.norm_natCast] at hest
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [dist_eq_norm]
  have h1 : ‖iteratedFDeriv ℂ k (f m) y - iteratedFDeriv ℂ k g y‖ ≤
      k.factorial * (ε / C * Real.exp 1 * (Real.exp 1 / r) ^ k) := by
    rw [inv_mul_le_iff₀ hfac] at hest
    exact hest
  calc ‖iteratedFDeriv ℂ k (f m) y - iteratedFDeriv ℂ k g y‖
      ≤ k.factorial * (ε / C * Real.exp 1 * (Real.exp 1 / r) ^ k) := h1
    _ = ε / C * (C - 1) := by rw [hC]; ring
    _ < ε / C * C := by
        have : 0 < ε / C := div_pos hε hC0
        nlinarith
    _ = ε := by field_simp

/-- **Closure theorem.** Let `M` be coherent at `y ∈ ℂⁿ`. If tuples `a_m`, holomorphic on a ball
around `y` with germs in `M_y`, converge uniformly on that ball to a holomorphic `b`, then
`b ∈ M_y`. -/
theorem GermModule.CoherentAt.mem_of_tendstoUniformlyOn
    {M : GermModule (EuclideanSpace ℂ (Fin n)) ι} {y : EuclideanSpace ℂ (Fin n)}
    (hM : M.CoherentAt y) {r : ℝ} (hr : 0 < r) {a : ℕ → ι → EuclideanSpace ℂ (Fin n) → ℂ}
    {b : ι → EuclideanSpace ℂ (Fin n) → ℂ}
    (ha : ∀ m j, DifferentiableOn ℂ (a m j) (ball y r))
    (hb : ∀ j, DifferentiableOn ℂ (b j) (ball y r)) (hmem : ∀ m, M.mem y (a m))
    (hlim : ∀ j, TendstoUniformlyOn (fun m => a m j) (b j) atTop (ball y r)) :
    M.mem y b := by
  classical
  have hby : HolTupleAt b y := fun j =>
    holAt_of_differentiableOn isOpen_ball (hb j) (mem_ball_self hr)
  refine hM.mem_of_jets hby fun q => ?_
  -- the jets of members of `M_y` form a subspace
  let T : Set (JetSpace n ι q) := {v | ∃ a', M.mem y a' ∧ jet y q a' = v}
  have hTspan : ((Submodule.span ℂ T : Submodule ℂ (JetSpace n ι q)) : Set (JetSpace n ι q)) ⊆
      T := by
    intro v hv
    refine Submodule.span_induction (fun v hv => hv) ?_ ?_ ?_ hv
    · refine ⟨fun _ _ => 0, hM.zero_mem, ?_⟩
      funext k j
      simp [jet]
    · rintro v w - - ⟨a₁, ha₁, rfl⟩ ⟨a₂, ha₂, rfl⟩
      refine ⟨fun j x => a₁ j x + a₂ j x, hM.add_mem ha₁ ha₂, ?_⟩
      funext k j
      exact iteratedFDeriv_add_apply (contDiffAt_of_holAt (hM.holTupleAt_of_mem ha₁ j))
        (contDiffAt_of_holAt (hM.holTupleAt_of_mem ha₂ j))
    · rintro c v - ⟨a₁, ha₁, rfl⟩
      refine ⟨fun j x => c * a₁ j x, hM.smul_mem (holAt_const c y) ha₁, ?_⟩
      funext k j
      show iteratedFDeriv ℂ k (fun x => c • a₁ j x) y = c • iteratedFDeriv ℂ k (a₁ j) y
      exact iteratedFDeriv_const_smul_apply' (contDiffAt_of_holAt (hM.holTupleAt_of_mem ha₁ j))
  have hclosed : IsClosed ((Submodule.span ℂ T : Submodule ℂ (JetSpace n ι q)) :
      Set (JetSpace n ι q)) :=
    Submodule.closed_of_finiteDimensional _
  have hlimjet : Tendsto (fun m => jet y q (a m)) atTop (𝓝 (jet y q b)) := by
    refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
    exact tendsto_iteratedFDeriv_of_tendstoUniformlyOn hr (fun m => ha m j) (hb j) (hlim j) k
  have hbT : jet y q b ∈ ((Submodule.span ℂ T : Submodule ℂ (JetSpace n ι q)) :
      Set (JetSpace n ι q)) :=
    hclosed.mem_of_tendsto hlimjet (Eventually.of_forall fun m =>
      Submodule.subset_span ⟨a m, hmem m, rfl⟩)
  obtain ⟨a', ha', hjet⟩ := hTspan hbT
  exact ⟨a', ha', fun j k hk => congrFun (congrFun hjet ⟨k, hk⟩) j⟩

end Closure

end SGPT.GAGA.Core
