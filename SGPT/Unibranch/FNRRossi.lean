import SGPT.Unibranch.FNRPshHull

/-!
# Rossi's local maximum modulus principle

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proofs of Lemma 5.2 and Theorems 5.3.1, 5.4 ("By Rossi's local maximum
principle [16], we have `p₀ ∈ F̂`" with `F = K̂ ∩ ∂B(p₀, r)`); ingredient of `thm:FN` (2) ⇒ (1)
(`appendix_unibranch.tex`). Reference [16]: H. Rossi, *The local maximum modulus principle*,
Ann. of Math. 72 (1960).

* `rossi_local_maximum`: for `K ⊆ ℂⁿ` compact and `U ⊆ ℂⁿ` open,
  `K̂ ∩ Ū ⊆ ((K̂ ∩ ∂U) ∪ (K ∩ Ū))^`.
* `rossi_local_maximum_ball`, `mem_polyHull_inter_sphere`: the form used by FN80: if
  `p ∈ K̂` and `B̄(p, r) ∩ K = ∅` (`r > 0`), then `K̂ ∩ B̄(p, r) ⊆ (K̂ ∩ ∂B(p, r))^`; in particular
  `p ∈ (K̂ ∩ ∂B(p, r))^`.
* `norm_le_on_polyHull_inter_closure`: the maximum modulus form: a polynomial is bounded on
  `K̂ ∩ Ū` by its supremum on `(K̂ ∩ ∂U) ∪ (K ∩ Ū)`.

Proof (via the maximum principle for plurisubharmonic functions on polynomial hulls,
`psh_le_on_polyHull`, instead of Rossi's Banach-algebra argument): let `L = (K̂ ∩ ∂U) ∪ (K ∩ Ū)`
and `z ∈ K̂ ∩ Ū \ L̂`. A polynomial `P` has `|P| < 1` on `L̂` and `|P(z)| > 1`. The function
`u = max(|P|², 1)` on `U`, `u = 1` off `U`, is plurisubharmonic on the open set
`ℂⁿ \ (∂U ∩ {|P| ≥ 1}) ⊇ K̂` (near `∂U ∩ {|P| < 1}` it is identically `1`), `u ≤ 1` on `K` and
`u(z) > 1`, contradicting `psh_le_on_polyHull`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNR

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum

variable {n : ℕ}

/-- **Rossi's local maximum modulus principle** for polynomial hulls: for `K ⊆ ℂⁿ` compact and
`U ⊆ ℂⁿ` open, `K̂ ∩ Ū ⊆ ((K̂ ∩ ∂U) ∪ (K ∩ Ū))^`. -/
theorem rossi_local_maximum {K U : Set (ComplexModel n)} (hK : IsCompact K) (hU : IsOpen U) :
    polyHull K ∩ closure U ⊆ polyHull ((polyHull K ∩ frontier U) ∪ (K ∩ closure U)) := by
  classical
  have h1top : (1 : EReal) ≠ ⊤ := by rw [← EReal.coe_one]; exact EReal.coe_ne_top 1
  rintro z ⟨hzK, hzcl⟩
  by_contra hz
  set L : Set (ComplexModel n) := (polyHull K ∩ frontier U) ∪ (K ∩ closure U) with hL_def
  obtain ⟨P, hPL, hPz⟩ := exists_normalized_separator hz
  set V : Set (ComplexModel n) := {x | ‖polyEval P x‖ < 1} with hV_def
  have hV : IsOpen V := isOpen_lt (continuous_polyEval P).norm continuous_const
  have hLV : L ⊆ V := fun x hx => hPL x (subset_polyHull L hx)
  have hzU : z ∈ U := by
    by_contra hzU
    have hzF : z ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hzcl, hzU⟩
    have : z ∈ V := hLV (Or.inl ⟨hzK, hzF⟩)
    exact absurd (this.trans hPz) (lt_irrefl _)
  set D : Set (ComplexModel n) := (frontier U ∩ Vᶜ)ᶜ with hD_def
  have hD : IsOpen D := (isClosed_frontier.inter hV.isClosed_compl).isOpen_compl
  have hKD : polyHull K ⊆ D := fun x hx ⟨hxF, hxV⟩ => hxV (hLV (Or.inl ⟨hx, hxF⟩))
  set f : ComplexModel n → EReal := fun x => ((‖polyEval P x‖ ^ 2 : ℝ) : EReal) with hf_def
  have hfpsh : PlurisubharmonicOn f univ := plurisubharmonicOn_normSq_polyEval P
  have hmaxpsh : PlurisubharmonicOn (fun x => max (f x) (1 : EReal)) univ :=
    hfpsh.max fun x _ => plurisubharmonicAt_const _ h1top x
  set u : ComplexModel n → EReal := fun x => if x ∈ U then max (f x) 1 else 1 with hu_def
  have hfV : ∀ x ∈ V, f x ≤ 1 := by
    intro x hx
    have h1 : ‖polyEval P x‖ ^ 2 ≤ 1 := by
      have := norm_nonneg (polyEval P x)
      have h := (show ‖polyEval P x‖ < 1 from hx)
      nlinarith
    simp only [hf_def]
    exact_mod_cast h1
  have huV : ∀ x ∈ V, u x = 1 := by
    intro x hx
    simp only [hu_def]
    split_ifs
    · exact max_eq_right (hfV x hx)
    · rfl
  have hconst : ∀ x, PlurisubharmonicAt (fun _ : ComplexModel n => (1 : EReal)) x :=
    fun x => plurisubharmonicAt_const _ h1top x
  have hu : PlurisubharmonicOn u D := by
    intro x hxD
    by_cases hxU : x ∈ U
    · refine (hmaxpsh x (mem_univ x)).congr ?_
      filter_upwards [hU.mem_nhds hxU] with y hy
      simp only [hu_def, if_pos hy]
    by_cases hxcl : x ∈ closure U
    · have hxF : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hxcl, hxU⟩
      have hxV : x ∈ V := by
        by_contra hxV
        exact hxD ⟨hxF, hxV⟩
      refine (hconst x).congr ?_
      filter_upwards [hV.mem_nhds hxV] with y hy
      exact (huV y hy).symm
    · refine (hconst x).congr ?_
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
      have hyU : y ∉ U := fun h => hy (subset_closure h)
      simp only [hu_def, if_neg hyU]
  have hcK : ∀ x ∈ K, u x ≤ (1 : EReal) := by
    intro x hx
    by_cases hxU : x ∈ U
    · rw [huV x (hLV (Or.inr ⟨hx, subset_closure hxU⟩))]
    · simp only [hu_def, if_neg hxU, le_refl]
  have key := psh_le_on_polyHull hK hD hKD hu hcK hzK
  simp only [hu_def, if_pos hzU] at key
  have h1 : f z ≤ 1 := (le_max_left _ _).trans key
  simp only [hf_def] at h1
  have h2 : ‖polyEval P z‖ ^ 2 ≤ 1 := by exact_mod_cast h1
  nlinarith

/-- Maximum modulus form of `rossi_local_maximum`: a polynomial bounded by `C` on
`(K̂ ∩ ∂U) ∪ (K ∩ Ū)` is bounded by `C` on `K̂ ∩ Ū`. -/
theorem norm_le_on_polyHull_inter_closure {K U : Set (ComplexModel n)} (hK : IsCompact K)
    (hU : IsOpen U) (p : Poly n) (C : ℝ)
    (hC : ∀ x ∈ (polyHull K ∩ frontier U) ∪ (K ∩ closure U), ‖polyEval p x‖ ≤ C) :
    ∀ z ∈ polyHull K ∩ closure U, ‖polyEval p z‖ ≤ C :=
  fun _ hz => rossi_local_maximum hK hU hz p C hC

/-- **Rossi's local maximum principle, ball form** (FN80, Lemma 5.2 and Theorem 5.3.1): if the
closed ball `B̄(p, r)`, `r > 0`, does not meet `K`, then `K̂ ∩ B̄(p, r) ⊆ (K̂ ∩ ∂B(p, r))^`. -/
theorem rossi_local_maximum_ball {K : Set (ComplexModel n)} (hK : IsCompact K)
    {p : ComplexModel n} {r : ℝ} (hr : 0 < r) (hKr : Disjoint K (closedBall p r)) :
    polyHull K ∩ closedBall p r ⊆ polyHull (polyHull K ∩ sphere p r) := by
  have h := rossi_local_maximum (U := ball p r) hK isOpen_ball
  rw [closure_ball p hr.ne', frontier_ball p hr.ne', hKr.inter_eq, union_empty] at h
  exact h

/-- FN80's use of Rossi's principle: for `p ∈ K̂ \ K` and `0 < r < dist(p, K)`,
`p ∈ (K̂ ∩ ∂B(p, r))^`. -/
theorem mem_polyHull_inter_sphere {K : Set (ComplexModel n)} (hK : IsCompact K)
    {p : ComplexModel n} (hp : p ∈ polyHull K) {r : ℝ} (hr : 0 < r)
    (hKr : Disjoint K (closedBall p r)) : p ∈ polyHull (polyHull K ∩ sphere p r) :=
  rossi_local_maximum_ball hK hr hKr ⟨hp, mem_closedBall_self hr.le⟩

/-- The hull in FN80's Lemma 5.2 stays local: `(K̂ ∩ ∂B(p, r))^ ⊆ B̄(p, r)`. -/
theorem polyHull_inter_sphere_subset_closedBall (K : Set (ComplexModel n)) (p : ComplexModel n)
    (r : ℝ) : polyHull (polyHull K ∩ sphere p r) ⊆ closedBall p r :=
  polyHull_subset_closedBall fun _ hx => sphere_subset_closedBall hx.2

end SGPT.Unibranch.FNR
