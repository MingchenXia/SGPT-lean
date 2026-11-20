import SGPT.Unibranch.FNRRossi
import SGPT.Unibranch.FNRAnalyticHull

/-!
# Rossi's principle inside an analytic subset of a polydisc

Source: Fornæss–Narasimhan, *The Levi problem on complex spaces with singularities*,
Math. Ann. 248 (1980), proof of Lemma 5.2 (and of Theorem 5.3.1): "Let `F = K̂ ∩ ∂B(p₀, r)`, where
`0 < r < 1` is sufficiently small. By Rossi's local maximum principle we have `p₀ ∈ F̂`. ... if we
replace `X` by `X' = X ∩ Δ'ⁿ` with a small polydisc `Δ'ⁿ` centered at `p₀` [and `r` so small that
`B(p₀, r) ⊂⊂ Δ'ⁿ`] ...". Ingredient of `thm:FN` (2) ⇒ (1) (`appendix_unibranch.tex`).

`rossi_step_polydisc`: for `X` with local equations on a polydisc `Δ`, `K ⊆ X ∩ Δ` compact,
`p ∈ K̂` and `0 < r` with `B̄(p, r) ∩ K = ∅`, the set `F = K̂ ∩ ∂B(p, r)` is a compact subset of
`X ∩ Δ`, `p ∈ F̂`, and `F̂ ⊆ X ∩ Δ ∩ B̄(p, r)`; in particular `F̂` lies in every polydisc
containing `B̄(p, r)`, i.e. the hull of `F` in `X' = X ∩ Δ'` is `F̂`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open SGPT.Foundations.Analysis.FirstPass

namespace SGPT.Unibranch.FNR

open E2Nov16FNPolynomialPolyhedron E2Nov16FNHolomorphicHullMaximum

variable {n : ℕ}

/-- **FN80's Rossi step in an analytic subset of a polydisc.** -/
theorem rossi_step_polydisc {X K : Set (ComplexModel n)} {a : ComplexModel n} {r : Fin n → ℝ}
    (hX : HasLocalEquationsOn X {z | ∀ i, ‖z i - a i‖ < r i}) (hK : IsCompact K) (hKX : K ⊆ X)
    (hKΔ : ∀ x ∈ K, ∀ i, ‖x i - a i‖ < r i) {p : ComplexModel n} (hp : p ∈ polyHull K)
    {ρ : ℝ} (hρ : 0 < ρ) (hKρ : Disjoint K (closedBall p ρ)) :
    IsCompact (polyHull K ∩ sphere p ρ) ∧
      polyHull K ∩ sphere p ρ ⊆ X ∩ {z | ∀ i, ‖z i - a i‖ < r i} ∧
      p ∈ polyHull (polyHull K ∩ sphere p ρ) ∧
      polyHull (polyHull K ∩ sphere p ρ) ⊆
        X ∩ {z | ∀ i, ‖z i - a i‖ < r i} ∩ closedBall p ρ := by
  have hKH := polyHull_subset_of_localEquations_polydisc hX hK hKX hKΔ
  have hFH : polyHull (polyHull K ∩ sphere p ρ) ⊆ polyHull K := by
    have := polyHull_mono (inter_subset_left : polyHull K ∩ sphere p ρ ⊆ polyHull K)
    rwa [polyHull_polyHull] at this
  refine ⟨(isCompact_polyHull hK).inter_right isClosed_sphere,
    inter_subset_left.trans hKH, mem_polyHull_inter_sphere hK hp hρ hKρ, ?_⟩
  exact subset_inter (hFH.trans hKH) (polyHull_inter_sphere_subset_closedBall K p ρ)

/-- A polydisc containing `B̄(p, ρ)` contains the hull of `K̂ ∩ ∂B(p, ρ)`: the hull of `F` in the
localized space `X' = X ∩ Δ'` (FN80) is `F̂`. -/
theorem polyHull_inter_sphere_subset_polydisc (K : Set (ComplexModel n)) {p : ComplexModel n}
    {ρ : ℝ} {a' : ComplexModel n} {r' : Fin n → ℝ}
    (hball : closedBall p ρ ⊆ {z | ∀ i, ‖z i - a' i‖ < r' i}) :
    polyHull (polyHull K ∩ sphere p ρ) ⊆ {z | ∀ i, ‖z i - a' i‖ < r' i} :=
  (polyHull_inter_sphere_subset_closedBall K p ρ).trans hball

/-- **Local maximum principle for plurisubharmonic functions on hulls** (the combination of
Rossi's principle with `psh_le_on_polyHull` used at the end of FN80's Lemma 5.2 and in Theorem
5.4): if `p ∈ K̂`, `B̄(p, r) ∩ K = ∅` (`r > 0`) and `u` is plurisubharmonic on an open
`D ⊇ B̄(p, r)`, then `u(p) ≤ sup_{K̂ ∩ ∂B(p, r)} u`. -/
theorem psh_le_on_sphere_of_mem_polyHull {K D : Set (ComplexModel n)} (hK : IsCompact K)
    {p : ComplexModel n} (hp : p ∈ polyHull K) {r : ℝ} (hr : 0 < r)
    (hKr : Disjoint K (closedBall p r)) (hD : IsOpen D) (hBD : closedBall p r ⊆ D)
    {u : ComplexModel n → EReal} (hu : SGPT.Foundations.Analysis.PlurisubharmonicOn u D)
    {c : EReal} (hc : ∀ x ∈ polyHull K ∩ sphere p r, u x ≤ c) : u p ≤ c :=
  psh_le_on_polyHull ((isCompact_polyHull hK).inter_right isClosed_sphere) hD
    ((polyHull_inter_sphere_subset_closedBall K p r).trans hBD) hu hc
    (mem_polyHull_inter_sphere hK hp hr hKr)

/-- The same, with the supremum attained: some `q ∈ K̂ ∩ ∂B(p, r)` has `u(p) ≤ u(q)`. In
particular a plurisubharmonic function cannot have a strict local maximum on `K̂` at a point of
`K̂ \ K` (FN80, end of Lemma 5.2). -/
theorem exists_mem_sphere_le_of_mem_polyHull {K D : Set (ComplexModel n)} (hK : IsCompact K)
    {p : ComplexModel n} (hp : p ∈ polyHull K) {r : ℝ} (hr : 0 < r)
    (hKr : Disjoint K (closedBall p r)) (hD : IsOpen D) (hBD : closedBall p r ⊆ D)
    {u : ComplexModel n → EReal} (hu : SGPT.Foundations.Analysis.PlurisubharmonicOn u D) :
    ∃ q ∈ polyHull K ∩ sphere p r, u p ≤ u q := by
  have hF : IsCompact (polyHull K ∩ sphere p r) :=
    (isCompact_polyHull hK).inter_right isClosed_sphere
  have hne : (polyHull K ∩ sphere p r).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := mem_polyHull_inter_sphere hK hp hr hKr
    rw [h, polyHull_empty] at this
    exact this
  have husc : UpperSemicontinuousOn u (polyHull K ∩ sphere p r) := fun y hy =>
    ((hu y (hBD (sphere_subset_closedBall hy.2))).upperSemicontinuousAt
      ).upperSemicontinuousWithinAt _
  obtain ⟨q, hq, hqmax⟩ := husc.exists_isMaxOn hne hF
  exact ⟨q, hq, psh_le_on_sphere_of_mem_polyHull hK hp hr hKr hD hBD hu fun x hx =>
    (hqmax hx : u x ≤ u q)⟩

/-- **Sublevel sets of restrictions of ambient plurisubharmonic functions are Runge in `X`**
(FN80, Theorem 5.4 for `X` a closed analytic subset of a polydisc `Δ` and `φ = ρ|_X` with `ρ`
plurisubharmonic on `Δ`): the hull of a compact `K ⊆ X ∩ Δ ∩ {ρ < c}` lies in
`X ∩ Δ ∩ {ρ < c}`. -/
theorem analytic_sublevel_runge {X K : Set (ComplexModel n)} {a : ComplexModel n}
    {r : Fin n → ℝ} (hX : HasLocalEquationsOn X {z | ∀ i, ‖z i - a i‖ < r i})
    {ρ : ComplexModel n → EReal}
    (hρ : SGPT.Foundations.Analysis.PlurisubharmonicOn ρ {z | ∀ i, ‖z i - a i‖ < r i}) {c : EReal}
    (hK : IsCompact K) (hKX : K ⊆ X) (hKΔ : ∀ x ∈ K, ∀ i, ‖x i - a i‖ < r i)
    (hKc : ∀ x ∈ K, ρ x < c) :
    polyHull K ⊆ X ∩ {z | ∀ i, ‖z i - a i‖ < r i} ∩ {z | ρ z < c} :=
  subset_inter (polyHull_subset_of_localEquations_polydisc hX hK hKX hKΔ)
    fun _ hz => (polydisc_sublevel_runge hρ hK (fun x hx => hKΔ x hx) hKc hz).2

end SGPT.Unibranch.FNR
