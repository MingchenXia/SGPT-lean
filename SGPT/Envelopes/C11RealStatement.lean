import SGPT.Okounkov.TranscendentalWNRegStatement

/-!
# `C^{1,1}(X)` and the statement of `thm:Tos_C11`

Lane C11-REAL (`claude-c11-real`, nodes `c11r:c11-class`, `c11r:tos-statement`).  Source:
`references/sgpt-d3f272c3/source/author/chapter_npp.tex`, `thm:Tos_C11` (Tosatti, Chu–Zhou):

> Let `X` be a compact Kähler manifold with a Kähler form `ω` and let `f ∈ C^{1,1}(X)`.  Then
> `P_ω(f) ∈ C^{1,1}(X)`, and there is a constant `C = C(X, ω, ‖f‖_{C^{1,1}})` such that
> `‖P_ω(f)‖_{C^{1,1}} ≤ C`.

This file only fixes the objects and the **statement** (`TosattiChuZhouStatement`); it proves
no part of the theorem (see the plan in `blueprint/src/claude-c11-real.tex`).

* `IsCOneOne f` — `f ∈ C^{1,1}(X)`: in every chart of the atlas, `f ∘ e⁻¹` is `C¹` on the chart
  target and its derivative is Lipschitz on every compact subset (`C¹` with locally Lipschitz
  first derivatives, the usual definition; chart-independent since transition maps are smooth).
* `C11ChartData` — finitely many charts with compact pieces covering `X`; `C11Bound D f B` is
  `‖f‖_{C^{1,1}} ≤ B` for the norm `sup|f| + max_i (sup_{K_i} |D(f ∘ e_i⁻¹)| + Lip_{K_i} D(f ∘ e_i⁻¹))`
  attached to `D`.  All such norms are equivalent; the statement quantifies over every `D`, so it
  holds for whichever fixed norm one chooses.
* `IsCOneOne.of_chartSmooth`, `exists_c11ChartData` — sanity checks: smooth functions are
  `C^{1,1}`, and chart data exist on every compact manifold, so the statement is not vacuous.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

universe u

namespace SGPT.Envelopes.C11Real

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Okounkov.TranscendentalWNReg

section Defs

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]

/-- **`C^{1,1}(X)`**: in every chart `e` of the atlas, `f ∘ e⁻¹` is `C¹` on the chart target and its
derivative is Lipschitz on every compact subset of the target. -/
def IsCOneOne (f : Y → ℝ) : Prop :=
  ∀ e : ComplexChart N Y, ContDiffOn ℝ 1 (fun z => f (e.val.symm z)) e.val.target ∧
    ∀ K : Set (ComplexModel N), IsCompact K → K ⊆ e.val.target →
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (fun z => f (e.val.symm z))) K

/-- **Chart data for a `C^{1,1}` norm**: finitely many charts of the atlas with compact pieces of
their targets whose preimages cover `X`. -/
structure C11ChartData (N : ℕ) (Y : Type*) [TopologicalSpace Y]
    [ChartedSpace (ComplexModel N) Y] where
  /-- The number of pieces. -/
  card : ℕ
  /-- The charts. -/
  chart : Fin card → ComplexChart N Y
  /-- The compact pieces of the chart targets. -/
  piece : Fin card → Set (ComplexModel N)
  isCompact_piece : ∀ i, IsCompact (piece i)
  piece_subset : ∀ i, piece i ⊆ (chart i).val.target
  cover : ∀ x : Y, ∃ i, x ∈ (chart i).val.symm '' piece i

/-- **`‖f‖_{C^{1,1}} ≤ B`** for the norm attached to the chart data `D`: `|f| ≤ B`, and on every
piece `K_i` the derivative of `f ∘ e_i⁻¹` is bounded by `B` and `B`-Lipschitz. -/
def C11Bound (D : C11ChartData N Y) (f : Y → ℝ) (B : ℝ) : Prop :=
  (∀ x, |f x| ≤ B) ∧ ∀ i,
    (∀ z ∈ D.piece i, ‖fderiv ℝ (fun z => f ((D.chart i).val.symm z)) z‖ ≤ B) ∧
    ∀ z ∈ D.piece i, ∀ z' ∈ D.piece i,
      ‖fderiv ℝ (fun z => f ((D.chart i).val.symm z)) z -
        fderiv ℝ (fun z => f ((D.chart i).val.symm z)) z'‖ ≤ B * ‖z - z'‖

end Defs

/-- **Source `thm:Tos_C11` (statement only)**: for a compact complex manifold `X` with a Kähler form
`ω`, chart data `D` and a bound `B`, there is `C` such that for every `f ∈ C^{1,1}(X)` with
`‖f‖_{C^{1,1}, D} ≤ B` the envelope `P_ω(f)` is real-valued (`rooftopEnvelope`, the envelope of
`def:Pthetaf`, equals its real part `envelopeReal`), belongs to `C^{1,1}(X)` and has
`‖P_ω(f)‖_{C^{1,1}, D} ≤ C`. -/
def TosattiChuZhouStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] (A : KahlerBackground N Y) (D : C11ChartData N Y)
    (B : ℝ), ∃ C : ℝ, ∀ f : Y → ℝ, IsCOneOne (N := N) f → C11Bound D f B →
      (∀ x, rooftopEnvelope A.form.val (fun y => ((f y : ℝ) : EReal)) x =
        ((envelopeReal A.form f x : ℝ) : EReal)) ∧
      IsCOneOne (N := N) (envelopeReal A.form f) ∧ C11Bound D (envelopeReal A.form f) C

section Sanity

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]

/-- Chart-smooth functions are `C^{1,1}`. -/
theorem IsCOneOne.of_chartSmooth [IsComplexManifold N Y] {f : Y → ℝ}
    (hf : ChartSmooth (n := N) f) : IsCOneOne (N := N) f := by
  intro e
  have hU := e.val.open_target
  refine ⟨(hf e).of_le (by exact_mod_cast le_top), fun K hK hKU => ?_⟩
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun z => f (e.val.symm z))) e.val.target :=
    (hf e).fderiv_of_isOpen hU (by simp)
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun x hx => ?_
  have hx' : ContDiffAt ℝ 1 (fderiv ℝ (fun z => f (e.val.symm z))) x :=
    ((hD x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx))).of_le (by exact_mod_cast le_top)
  obtain ⟨L, t, ht, hL⟩ := hx'.exists_lipschitzOnWith
  exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩

/-- **Chart data exist** on every compact manifold. -/
theorem exists_c11ChartData [CompactSpace Y] : Nonempty (C11ChartData N Y) := by
  -- around every point, a closed ball inside the target of the preferred chart
  have hloc : ∀ x : Y, ∃ r : ℝ, 0 < r ∧
      closedBall ((complexChartAt (n := N) x).val x) r ⊆ (complexChartAt (n := N) x).val.target := by
    intro x
    have hmem : (complexChartAt (n := N) x).val x ∈ (complexChartAt (n := N) x).val.target :=
      (complexChartAt (n := N) x).val.map_source (mem_complexChartAt_source x)
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp (complexChartAt (n := N) x).val.open_target _ hmem
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hrU⟩
  choose r hr hrU using hloc
  -- the open sets `e_x⁻¹(B(e_x x, r_x))`, an open cover of `X`
  set V : Y → Set Y := fun x => (complexChartAt (n := N) x).val.source ∩
    (complexChartAt (n := N) x).val ⁻¹' ball ((complexChartAt (n := N) x).val x) (r x) with hV
  have hVo : ∀ x, IsOpen (V x) := fun x =>
    (complexChartAt (n := N) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := N) x).val.open_source isOpen_ball
  have hVx : ∀ x, x ∈ V x := fun x => ⟨mem_complexChartAt_source x, mem_ball_self (hr x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => mem_iUnion.mpr ⟨x, hVx x⟩)
  let pts : Fin t.card → Y := fun i => (t.equivFin.symm i : Y)
  refine ⟨{ card := t.card
            chart := fun i => complexChartAt (n := N) (pts i)
            piece := fun i => closedBall ((complexChartAt (n := N) (pts i)).val (pts i)) (r (pts i))
            isCompact_piece := fun i => isCompact_closedBall _ _
            piece_subset := fun i => hrU (pts i)
            cover := fun y => ?_ }⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
  have hpts : pts (t.equivFin ⟨x, hxt⟩) = x := by simp [pts]
  rw [hpts]
  refine ⟨(complexChartAt (n := N) x).val y, ball_subset_closedBall hyx.2, ?_⟩
  exact (complexChartAt (n := N) x).val.left_inv hyx.1

end Sanity

end SGPT.Envelopes.C11Real
