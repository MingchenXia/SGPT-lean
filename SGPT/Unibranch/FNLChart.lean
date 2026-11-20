import SGPT.Unibranch.FNLLemma52

/-!
# FN80 §5.3: local branched-covering charts (statement of the local parametrization)

Source: `[FN80]` Theorem 5.3.1, proof: "In a small neighborhood of `p`, we can represent
`S_j × ℂ` as a branched covering of `Δ^{j+1}` relative to suitable coordinates in `ℂ^{n+1}`
(as in Lemma 5.2)"; this is the local parametrization theorem for pure-dimensional analytic
sets (Grauert–Remmert, Gunning–Rossi III.B; Demailly, CADG II.4).

* `HasCoveringChartAt Y p O`: after a complex-linear automorphism `T` of `ℂᴺ`, `T(Y)` is, on a
  polydisc centred at `T p` inside `T(O)`, a closed analytic set (local holomorphic equations)
  which is a finite branched covering of an open set `D ⊇ π(polydisc)` of `ℂᵈ` under the
  projection `π` to the first `d` coordinates — exactly the hypotheses of `runge_sublevel`.
* `LocalCoveringCharts`: the local parametrization theorem in this form, for sets which are
  closed analytic (local equations) and of pure dimension `d` on an open set `Ω`, at every point
  of `Y ∩ Ω` and inside every neighbourhood.  (Stated here as a proposition; its proof is the
  remaining FNL task, see `notes.md`.)
-/

set_option autoImplicit false

open Set Filter Metric TopologicalSpace
open scoped Topology

noncomputable section

namespace SGPT.Unibranch.FNL

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Unibranch.FNR

/-- A local branched-covering chart of `Y` at `p` inside `O` (`[FN80]` §5.3). -/
def HasCoveringChartAt {N : ℕ} (Y : Set (ComplexModel N)) (p : ComplexModel N)
    (O : Set (ComplexModel N)) : Prop :=
  ∃ (T : ComplexModel N ≃L[ℂ] ComplexModel N) (d : ℕ) (_ : d ≤ N) (r : Fin N → ℝ)
    (D : Set (ComplexModel d)) (deg : ℕ) (δ : ComplexModel d → ℂ),
    (∀ i, 0 < r i) ∧ pdisc (T p) r ⊆ T '' O ∧
    MapsTo (coordinateProjection N d) (pdisc (T p) r) D ∧
    IsBranchedCovering (T '' Y ∩ pdisc (T p) r) (coordinateProjection N d) D deg δ ∧
    HasLocalEquationsOn (T '' Y ∩ pdisc (T p) r) (pdisc (T p) r)

/-- **The local parametrization theorem** in the form used by `[FN80]` §5: a set `Y ⊆ ℂᴺ` with
local holomorphic equations on an open set `Ω`, of pure dimension `d` there, has local
branched-covering charts at every point of `Y ∩ Ω`, inside every neighbourhood. -/
def LocalCoveringCharts : Prop :=
  ∀ (N d : ℕ) (Y Ω : Set (ComplexModel N)) (p : ComplexModel N), IsOpen Ω → p ∈ Y → p ∈ Ω →
    HasLocalEquationsOn Y Ω →
    AnalyticDimensionBasics.IsPureDim (n := N) (M := ComplexModel N) (Y ∩ Ω) d →
    ∀ O : Set (ComplexModel N), IsOpen O → p ∈ O → HasCoveringChartAt Y p O

end SGPT.Unibranch.FNL
