import SGPT.Envelopes.TosC11cSmoothing
import SGPT.Envelopes.TosC11bGradient
import SGPT.Okounkov.TranscendentalWNRegEnvelope
import SGPT.Envelopes.DNTRegRooftop

/-!
# `thm:Tos_C11` from the penalized real-Hessian estimate

Lane TOS-C11c (`claude-tos-c11c`, nodes `tos-c11c:estimate`, `tos-c11c:assembly`).  Source: SGPT
`thm:Tos_C11` (`references/sgpt-d3f272c3/source/author/chapter_npp.tex:1202`, Tosatti, Chu–Zhou), with
the proof of Xia, *Foundations of pluripotential theory*, `thm:kahler-real-c11-envelope` (case of one
obstacle).

The remaining analytic core of `thm:Tos_C11` is FPT `lem:penalized-real-hessian`: uniform bounds for the
full real Hessian of the solutions `u_β` of the penalized equations
`(A + ddᶜu_β)^N = e^{β(u_β - F)} A^N` (`BetaSolution`) for smooth obstacles `F` with bounded values, first
derivatives and Hessians.  It is stated here, in the charts of chart data `D`, as
`PenalizedHessianEstimate` (a `def … : Prop`, **not proved here**), and everything else of the proof of
`thm:Tos_C11` is carried out:

* `tosattiChuZhou_of_penalizedHessianEstimate` — for a compact connected complex manifold with a Kähler
  background `A` and chart data `D`: if the estimate holds for `D` (with some `δ`), then for every `B`
  there is `C` such that every `f ∈ C^{1,1}(Y)` with `‖f‖_{C^{1,1}, D} ≤ B` has a real-valued envelope
  `P_A(f) ∈ C^{1,1}(Y)` with `‖P_A(f)‖_{C^{1,1}, D} ≤ C`.  Proof: smooth `f` (`exists_smoothing`), solve
  the penalized equations (`exists_betaSolution`, Aubin–Yau), squeeze the envelopes
  (`envelope_bounds`, Berman; `envelope_sandwich`), apply the estimate along a diagonal sequence, and
  pass to the limit (`exists_c11Bound_of_tendsto`, `isCOneOne_of_tendsto`, `exists_hessian_transfer`).
* `TosattiChuZhouConnectedStatement` — the statement of `thm:Tos_C11` for connected `X` (the section of
  the book containing `thm:Tos_C11` begins "Let `X` be a connected compact Kähler manifold"); and
  `tosattiChuZhouConnected_of_penalizedHessianEstimate`: it follows from
  `PenalizedHessianEstimateStatement`.

Nothing in this file assumes `thm:Tos_C11` or its conclusion: the only open input is the a priori estimate
for smooth solutions of the penalized equations.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

universe u

namespace SGPT.Envelopes.TosC11c

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.C11Real

section Statements

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **FPT `lem:penalized-real-hessian`, in the charts of chart data `D`** (statement only): for every
`B` there are `β₀` and `C` such that for `β ≥ β₀`, every chart-smooth obstacle `F` with `|F| ≤ B`,
`‖D(F ∘ e_i⁻¹)‖ ≤ B` and `‖D²(F ∘ e_i⁻¹)‖ ≤ B` on the pieces `K_i` and `ddᶜF ≤ B·A` on complex lines,
and every solution `u` of `(A + ddᶜu)^N = e^{β(u - F)} A^N`, the chart Hessians of `u` are bounded by
`C` on the closed `δ`-thickenings of the pieces.  (FPT bounds `|u| + |∇u| + |∇²u|` for a fixed metric;
on the compact `δ`-thickenings this is equivalent to the chart bound.) -/
def PenalizedHessianEstimate (A : KahlerBackground N Y) (D : C11ChartData N Y) (δ : ℝ) : Prop :=
  ∀ B : ℝ, ∃ β₀ C : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ (F : Y → ℝ) (hF : ChartSmooth (n := N) F),
    (∀ y, |F y| ≤ B) →
    (∀ i, ∀ z ∈ D.piece i, ‖fderiv ℝ (fun z => F ((D.chart i).val.symm z)) z‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => F ((D.chart i).val.symm z))) z‖ ≤ B) →
    (∀ (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target → ∀ v : ComplexModel N,
      (ddcClosedForm F hF).val.coeff e z ![v, Complex.I • v] ≤
        B * A.form.val.coeff e z ![v, Complex.I • v]) →
    ∀ (U : BetaSolution A β F) (i : Fin D.card), ∀ z ∈ cthickening δ (D.piece i),
      ‖fderiv ℝ (fderiv ℝ (fun z => U.u ((D.chart i).val.symm z))) z‖ ≤ C

end Statements

/-- **`PenalizedHessianEstimate` for all compact connected Kähler manifolds** (statement only; FPT
`lem:penalized-real-hessian`, the remaining analytic input of `thm:Tos_C11`). -/
def PenalizedHessianEstimateStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y)
    (D : C11ChartData N Y) (δ : ℝ), 0 < δ →
    (∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target) → PenalizedHessianEstimate A D δ

/-- **Source `thm:Tos_C11` for connected `X`** (statement): the book's section containing
`thm:Tos_C11` assumes `X` connected.  Same conclusion as `C11Real.TosattiChuZhouStatement`, with
`[ConnectedSpace Y]` added. -/
def TosattiChuZhouConnectedStatement : Prop :=
  ∀ (N : ℕ) (Y : Type u) [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
    [IsComplexManifold N Y] [CompactSpace Y] [ConnectedSpace Y] (A : KahlerBackground N Y)
    (D : C11ChartData N Y) (B : ℝ), ∃ C : ℝ, ∀ f : Y → ℝ, IsCOneOne (N := N) f → C11Bound D f B →
      (∀ x, rooftopEnvelope A.form.val (fun y => ((f y : ℝ) : EReal)) x =
        ((envelopeReal A.form f x : ℝ) : EReal)) ∧
      IsCOneOne (N := N) (envelopeReal A.form f) ∧ C11Bound D (envelopeReal A.form f) C

/-- `TosattiChuZhouStatement` (no connectedness assumption) implies the connected version. -/
theorem tosattiChuZhouConnected_of_tosattiChuZhou (h : TosattiChuZhouStatement.{u}) :
    TosattiChuZhouConnectedStatement.{u} := by
  intro N Y _ _ _ _ _ A D B
  exact h N Y A D B

section Assembly

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

omit [IsComplexManifold N Y] in
/-- `C11Bound` is monotone in the bound. -/
theorem c11Bound_mono {D : C11ChartData N Y} {f : Y → ℝ} {B B' : ℝ} (h : C11Bound D f B)
    (hBB : B ≤ B') : C11Bound D f B' :=
  ⟨fun x => (h.1 x).trans hBB, fun i => ⟨fun z hz => ((h.2 i).1 z hz).trans hBB,
    fun z hz z' hz' => ((h.2 i).2 z hz z' hz').trans
      (mul_le_mul_of_nonneg_right hBB (norm_nonneg _))⟩⟩

/-- **Gradient from Hessian and values on a ball**: if `g` is `C²` on `B(z, δ)` with `‖D²g‖ ≤ M` and
`|g| ≤ C₀` there, then `‖Dg(z)‖ ≤ 2(2C₀ + M(δ/2)²)/(δ/2)`. -/
theorem norm_fderiv_le_of_hessian_ball {n : ℕ} {g : ComplexModel n → ℝ} {z : ComplexModel n}
    {δ M C₀ : ℝ} (hδ : 0 < δ) (hM0 : 0 ≤ M) (hC₀ : 0 ≤ C₀) (hg : ContDiffOn ℝ 2 g (ball z δ))
    (hM : ∀ y ∈ ball z δ, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M) (hC : ∀ y ∈ ball z δ, |g y| ≤ C₀) :
    ‖fderiv ℝ g z‖ ≤ 2 * (2 * C₀ + M * (δ / 2) ^ 2) / (δ / 2) := by
  have h2 : 2 * (δ / 2) = δ := by ring
  refine TosC11b.norm_fderiv_le_of_taylor (half_pos hδ) hM0 hC₀ (by rw [h2]; exact hC)
    (fun y hy => ?_)
  rw [h2] at hy
  exact abs_sub_fderiv_le_of_norm_fderiv_fderiv_le_on isOpen_ball hg (convex_ball z δ)
    subset_rfl hM (mem_ball_self hδ) hy

/-- **`thm:Tos_C11` from the penalized real-Hessian estimate** (FPT, proof of
`thm:kahler-real-c11-envelope` for one obstacle).  On a compact connected complex manifold with a
Kähler background `A` and chart data `D`, if `PenalizedHessianEstimate A D δ` holds for some `δ > 0`
with the closed `δ`-thickenings of the pieces inside the chart targets, then for every `B` there is `C`
such that for every `f ∈ C^{1,1}(Y)` with `‖f‖_{C^{1,1}, D} ≤ B` the envelope `P_A(f)` is real-valued,
belongs to `C^{1,1}(Y)` and satisfies `‖P_A(f)‖_{C^{1,1}, D} ≤ C`. -/
theorem tosattiChuZhou_of_penalizedHessianEstimate [CompactSpace Y] [ConnectedSpace Y]
    (A : KahlerBackground N Y) (D : C11ChartData N Y) {δ : ℝ} (hδ : 0 < δ)
    (hδU : ∀ i, cthickening δ (D.piece i) ⊆ (D.chart i).val.target)
    (H : PenalizedHessianEstimate A D δ) (B : ℝ) :
    ∃ C : ℝ, ∀ f : Y → ℝ, IsCOneOne (N := N) f → C11Bound D f B →
      (∀ x, rooftopEnvelope A.form.val (fun y => ((f y : ℝ) : EReal)) x =
        ((envelopeReal A.form f x : ℝ) : EReal)) ∧
      IsCOneOne (N := N) (envelopeReal A.form f) ∧ C11Bound D (envelopeReal A.form f) C := by
  classical
  have hB'0 : 0 ≤ max B 0 := le_max_right _ _
  obtain ⟨κ, hκ0, hsmooth⟩ := exists_smoothing A D
  -- the bound `BH` for the smoothed obstacles
  set BH : ℝ := max B 0 + κ * max B 0 with hBH
  have hBH0 : 0 ≤ BH := by positivity
  have hB'BH : max B 0 ≤ BH := le_add_of_nonneg_right (by positivity)
  have hκBH : κ * max B 0 ≤ BH := le_add_of_nonneg_left hB'0
  obtain ⟨β₀, CH, hCH⟩ := H BH
  -- the value bound for the solutions and the constant of the limit
  set C₀ : ℝ := BH + N * Real.log (1 + BH) with hC₀
  have hlog : 0 ≤ N * Real.log (1 + BH) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hC₀0 : 0 ≤ C₀ := by positivity
  set M : ℝ := max CH 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  obtain ⟨C, hC⟩ := TosC11b.exists_c11Bound_of_tendsto D hδ hδU C₀ M hC₀0 hM0
  refine ⟨C, fun f hf hfB => ?_⟩
  have hfB' : C11Bound D f (max B 0) := c11Bound_mono hfB (le_max_left _ _)
  have hf1 : ∀ e' : ComplexChart N Y, ContDiffOn ℝ 1 (fun z => f (e'.val.symm z)) e'.val.target :=
    fun e' => (hf e').1
  -- the smoothed obstacles `F k`, `1/(k+1)`-close to `f`
  choose F hF hFf hFB hFD hFddc using fun k : ℕ =>
    hsmooth f (max B 0) hB'0 hf1 hfB' (1 / ((k : ℝ) + 1)) (by positivity)
  have hFB' : ∀ k y, |F k y| ≤ BH := fun k y => (hFB k y).trans hB'BH
  have hFD' : ∀ k i, ∀ z ∈ D.piece i,
      ‖fderiv ℝ (fun z => F k ((D.chart i).val.symm z)) z‖ ≤ BH ∧
      ‖fderiv ℝ (fderiv ℝ (fun z => F k ((D.chart i).val.symm z))) z‖ ≤ BH := fun k i z hz =>
    ⟨((hFD k i z hz).1).trans hκBH, ((hFD k i z hz).2).trans hκBH⟩
  have hFddc' : ∀ k (e : ComplexChart N Y) (z : ComplexModel N), z ∈ e.val.target →
      ∀ v : ComplexModel N, (ddcClosedForm (F k) (hF k)).val.coeff e z ![v, Complex.I • v] ≤
        BH * A.form.val.coeff e z ![v, Complex.I • v] := fun k e z hz v =>
    (hFddc k e z hz v).trans (mul_le_mul_of_nonneg_right hκBH
      (coefficientSemipositive_of_isKahler A.isKahler hz v))
  -- the parameters `β k = k + max β₀ 1` and the solutions `U k`
  set c₀ : ℝ := max β₀ 1 with hc₀
  set β : ℕ → ℝ := fun k => (k : ℝ) + c₀ with hβdef
  have hβ1 : ∀ k, 1 ≤ β k := fun k => by
    have := le_max_right β₀ 1
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [hβdef]; linarith
  have hββ₀ : ∀ k, β₀ ≤ β k := fun k => by
    have := le_max_left β₀ 1
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    simp only [hβdef]; linarith
  have hβpos : ∀ k, 0 < β k := fun k => by linarith [hβ1 k]
  have U : ∀ k, BetaSolution A (β k) (F k) := fun k =>
    Classical.choice (exists_betaSolution A (hβpos k) (hF k))
  -- the envelope of `f` is real and the `U k` converge to it
  set η : ℕ → ℝ := fun k => N * Real.log (1 + BH) / β k + (2 * BH + N * Real.log (β k)) / β k +
    1 / ((k : ℝ) + 1) with hηdef
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h1 := tendsto_const_div_natCast_add (N * Real.log (1 + BH) + 2 * BH) c₀
    have h2 := (tendsto_log_div_natCast_add c₀).const_mul (N : ℝ)
    have h3 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h := (h1.add h2).add h3
    simp only [mul_zero, add_zero] at h
    refine h.congr fun k => ?_
    simp only [hηdef, hβdef]
    have hb : (k : ℝ) + c₀ ≠ 0 := (hβpos k).ne'
    field_simp
    ring
  have hreal : ∀ k x, rooftopEnvelope A.form.val (fun y => ((F k y : ℝ) : EReal)) x =
        ((envelopeReal A.form (F k) x : ℝ) : EReal) ∧
      |(U k).u x - envelopeReal A.form (F k) x| ≤
        N * Real.log (1 + BH) / β k + (2 * BH + N * Real.log (β k)) / β k := by
    intro k x
    obtain ⟨h1, h2⟩ := envelope_bounds A (hβ1 k) (hF k) hBH0 (hFddc' k) (hFB' k) (U k) x
    have hne_bot : rooftopEnvelope A.form.val (fun y => ((F k y : ℝ) : EReal)) x ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1
    have hne_top : rooftopEnvelope A.form.val (fun y => ((F k y : ℝ) : EReal)) x ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hfin := (EReal.coe_toReal hne_top hne_bot).symm
    refine ⟨hfin, ?_⟩
    rw [hfin] at h1 h2
    have h1' := EReal.coe_le_coe_iff.mp h1
    have h2' := EReal.coe_le_coe_iff.mp h2
    have p1 : 0 ≤ N * Real.log (1 + BH) / β k := div_nonneg hlog (hβpos k).le
    have p2 : 0 ≤ (2 * BH + N * Real.log (β k)) / β k := by
      have : 0 ≤ Real.log (β k) := Real.log_nonneg (hβ1 k)
      have := hβpos k
      positivity
    change |(U k).u x - (rooftopEnvelope A.form.val (fun y => ((F k y : ℝ) : EReal)) x).toReal|
      ≤ _
    rw [abs_le]
    constructor <;> linarith
  have hsand : ∀ k, (∀ x, rooftopEnvelope A.form.val (fun y => ((f y : ℝ) : EReal)) x =
        ((envelopeReal A.form f x : ℝ) : EReal)) ∧
      ∀ x, |envelopeReal A.form f x - envelopeReal A.form (F k) x| ≤ 1 / ((k : ℝ) + 1) := fun k =>
    DNTReg.envelope_sandwich A.form (F := F k) (G := f) (fun y => hFf k y) (fun x => (hreal k x).1)
  have hclose : ∀ k x, |(U k).u x - envelopeReal A.form f x| ≤ η k := by
    intro k x
    have h1 := (hreal k x).2
    have h2 := (hsand k).2 x
    calc |(U k).u x - envelopeReal A.form f x|
        ≤ |(U k).u x - envelopeReal A.form (F k) x| +
          |envelopeReal A.form f x - envelopeReal A.form (F k) x| := by
          rw [abs_sub_comm (envelopeReal A.form f x)]
          exact abs_sub_le _ _ _
      _ ≤ η k := by simp only [hηdef]; linarith
  have hconv : ∀ y, Tendsto (fun k => (U k).u y) atTop (𝓝 (envelopeReal A.form f y)) := by
    intro y
    have hlo : Tendsto (fun k => envelopeReal A.form f y - η k) atTop
        (𝓝 (envelopeReal A.form f y)) := by simpa using tendsto_const_nhds.sub hηlim
    have hhi : Tendsto (fun k => envelopeReal A.form f y + η k) atTop
        (𝓝 (envelopeReal A.form f y)) := by simpa using tendsto_const_nhds.add hηlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun k => ?_) (fun k => ?_)
    · linarith [(abs_le.mp (hclose k y)).1]
    · linarith [(abs_le.mp (hclose k y)).2]
  -- uniform bounds for the `U k`
  have hUval : ∀ k y, |(U k).u y| ≤ C₀ := fun k y =>
    TosC11b.abs_betaSolution_le (hβ1 k) (hF k) hBH0 (hFddc' k) (hFB' k) (U k) y
  have hUhess : ∀ k i, ∀ z ∈ cthickening δ (D.piece i),
      ‖fderiv ℝ (fderiv ℝ (fun z => (U k).u ((D.chart i).val.symm z))) z‖ ≤ M := fun k i z hz =>
    (hCH (β k) (hββ₀ k) (F k) (hF k) (hFB' k) (hFD' k) (hFddc' k) (U k) i z hz).trans
      (le_max_left _ _)
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hUsmooth : ∀ k (e : ComplexChart N Y),
      ContDiffOn ℝ 2 (fun z => (U k).u (e.val.symm z)) e.val.target := fun k e =>
    ((U k).smooth e).of_le h2
  -- gradient bounds on the pieces, from the Hessian bounds on the `δ`-balls
  set G : ℝ := 2 * (2 * C₀ + M * (δ / 2) ^ 2) / (δ / 2) with hG
  have hUgrad : ∀ k i, ∀ z ∈ D.piece i,
      ‖fderiv ℝ (fun z => (U k).u ((D.chart i).val.symm z)) z‖ ≤ G := by
    intro k i z hz
    have hball : ball z δ ⊆ cthickening δ (D.piece i) :=
      (ball_subset_thickening hz δ).trans (thickening_subset_cthickening δ _)
    exact norm_fderiv_le_of_hessian_ball hδ hM0 hC₀0
      ((hUsmooth k (D.chart i)).mono (hball.trans (hδU i)))
      (fun y hy => hUhess k i y (hball hy)) (fun y _ => hUval k _)
  refine ⟨(hsand 0).1, ?_, hC (fun k => (U k).u) (envelopeReal A.form f)
    (fun k i => hUsmooth k (D.chart i)) hconv hUval hUhess⟩
  -- `C^{1,1}`: Hessian bounds in every chart, by transfer from the charts of `D`
  refine TosC11b.isCOneOne_of_tendsto hUsmooth hconv hUval fun e K hK hKt => ?_
  obtain ⟨C', -, hC'⟩ := exists_hessian_transfer D e hK hKt
  set M' : ℝ := max C₀ (max G M) with hM'
  refine ⟨C' * M', fun k z hz => hC' (U k).u M' (hUsmooth k)
    (fun y => (hUval k y).trans (le_max_left _ _)) (fun i w hw => ⟨?_, ?_⟩) z hz⟩
  · exact (hUgrad k i w hw).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hUhess k i w (self_subset_cthickening _ hw)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end Assembly

/-- **`thm:Tos_C11` (connected `X`) from FPT `lem:penalized-real-hessian`**: the penalized real-Hessian
estimate implies the statement of `thm:Tos_C11` for every compact connected Kähler manifold. -/
theorem tosattiChuZhouConnected_of_penalizedHessianEstimate
    (H : PenalizedHessianEstimateStatement.{u}) : TosattiChuZhouConnectedStatement.{u} := by
  intro N Y _ _ _ _ _ A D B
  obtain ⟨δ, hδ, hδU⟩ := TosC11b.C11ChartData.exists_cthickening_subset D
  exact tosattiChuZhou_of_penalizedHessianEstimate A D hδ hδU (H N Y A D δ hδ hδU) B

end SGPT.Envelopes.TosC11c
