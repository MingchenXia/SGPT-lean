import SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanCollarGluing
import SGPT.Foundations.Analysis.Pending.ShiftedBergmanBranchFixedCoefficient

set_option autoImplicit false

/-!
# Analytic type through overlapping finite shifted Bergman collars

A later inner core need not avoid an earlier one.  At a point already carrying
a logarithmic presentation, a later collar step is locally either the maximum
with the new Bergman branch inside its source, or the old global candidate
outside that source.  The former is stable under concatenating generator
families with a common rational coefficient; the latter is a collar germ
equality.  This file isolates that finite overlap induction.  The only local
input retained in its final theorem is an explicit common-coefficient
presentation for each shifted branch; a subsequent local Bergman bridge may
supply it with coefficient `1 / m`.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanOverlapAnalyticType

open FirstPass
open FirstPass.QuasiEquisingularApproximation
open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open QuasiEquisingularCollarGluing
open FiniteBergmanCollarGluing
open FiniteShiftedBergmanCollarGluing
open ShiftedBergmanBranch
open ShiftedBergmanBranchFixedCoefficient

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Transport a fixed-coefficient logarithmic presentation through an equality
of germs without changing either its generators or its coefficient. -/
theorem LogarithmicTypeAt.of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v w : E → EReal} {x : E} {c : ℝ} {N : ℕ}
    {f : Fin N → E → ℂ}
    (hv : LogarithmicTypeAt v c f x) (hwv : w =ᶠ[𝓝 x] v) :
    LogarithmicTypeAt w c f x := by
  obtain ⟨hc, hf, b, hb, heq⟩ := hv
  exact ⟨hc, hf, b, hb, hwv.trans heq⟩

/-- One finite shifted collar step preserves a fixed rational logarithmic
coefficient at a chart germ, provided the local branch has that coefficient
where the chart point lies in its source.  No separation of cores is used. -/
theorem finiteShiftedBergmanGlued_logarithmicTypeAt_succ
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    {k : ℕ} (hk : k < A.count) {e : ComplexChart n M}
    {z : ComplexModel n} (hz : z ∈ e.val.target) {c : ℚ}
    (hbranch : ∀ (i : Fin A.count) {e : ComplexChart n M}
      {z : ComplexModel n}, z ∈ e.val.target → e.val.symm z ∈ (A.patch i).patch.source →
        ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
          LogarithmicTypeAt
            (chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e)
            (c : ℝ) f z)
    (hprev : ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt (chartFunction (finiteShiftedBergmanGlued A offset g k) e)
        (c : ℝ) f z) :
    ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt (chartFunction (finiteShiftedBergmanGlued A offset g (k + 1)) e)
        (c : ℝ) f z := by
  let i : Fin A.count := ⟨k, hk⟩
  rw [finiteShiftedBergmanGlued_succ A offset g hk]
  by_cases hzsource : e.val.symm z ∈ (A.patch i).patch.source
  · obtain ⟨N, f, hprevtype⟩ := hprev
    obtain ⟨L, q, hbranchtype⟩ := hbranch i hz hzsource
    refine ⟨L + N, Fin.append q f, ?_⟩
    have hmax : LogarithmicTypeAt
        (fun y => max
          (chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e y)
          (chartFunction (finiteShiftedBergmanGlued A offset g k) e y))
        (c : ℝ) (Fin.append q f) z :=
      LogarithmicTypeAt.max_of_generators hbranchtype hprevtype
    apply LogarithmicTypeAt.of_eventuallyEq hmax
    change (gluedMax ((A.patch i).patch.source : Set M)
      (shiftedBergmanBranch (A.patch i).patch (offset i))
      (finiteShiftedBergmanGlued A offset g k) ∘ e.val.symm) =ᶠ[𝓝 z]
        ((fun y => max
          (chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e y)
          (chartFunction (finiteShiftedBergmanGlued A offset g k) e y)))
    exact (gluedMax_eventually_eq_max (A.patch i).patch.source.isOpen hzsource).comp_tendsto
      (e.val.continuousAt_symm hz)
  · obtain ⟨N, f, hprevtype⟩ := hprev
    refine ⟨N, f, ?_⟩
    apply LogarithmicTypeAt.of_eventuallyEq hprevtype
    change (gluedMax ((A.patch i).patch.source : Set M)
      (shiftedBergmanBranch (A.patch i).patch (offset i))
      (finiteShiftedBergmanGlued A offset g k) ∘ e.val.symm) =ᶠ[𝓝 z]
        (finiteShiftedBergmanGlued A offset g k ∘ e.val.symm)
    exact (gluedMax_eventually_eq_global (H.closure_inner_subset i) (H.collar i) hzsource).comp_tendsto
      (e.val.continuousAt_symm hz)

/-- A shifted core produces a fixed-coefficient presentation at its gluing
stage whenever its own shifted branch has one. -/
theorem finiteShiftedBergmanGlued_logarithmicTypeAt_core
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count) {e : ComplexChart n M}
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i) {c : ℚ}
    (hbranch : ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt
        (chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e)
        (c : ℝ) f z) :
    ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt
        (chartFunction (finiteShiftedBergmanGlued A offset g (i.val + 1)) e)
        (c : ℝ) f z := by
  obtain ⟨N, f, hbranchtype⟩ := hbranch
  refine ⟨N, f, ?_⟩
  apply LogarithmicTypeAt.of_eventuallyEq hbranchtype
  rw [finiteShiftedBergmanGlued_succ A offset g i.isLt]
  change (gluedMax ((A.patch i).patch.source : Set M)
    (shiftedBergmanBranch (A.patch i).patch (offset i))
    (finiteShiftedBergmanGlued A offset g i.val) ∘ e.val.symm) =ᶠ[𝓝 z]
      (shiftedBergmanBranch (A.patch i).patch (offset i) ∘ e.val.symm)
  have hcore : gluedMax ((A.patch i).patch.source : Set M)
      (shiftedBergmanBranch (A.patch i).patch (offset i))
      (finiteShiftedBergmanGlued A offset g i.val) =ᶠ[𝓝 (e.val.symm z)]
      shiftedBergmanBranch (A.patch i).patch (offset i) := by
    filter_upwards [H.inner_open i |>.mem_nhds hzcore] with x hx
    rw [gluedMax_eq_max (H.closure_inner_subset i (subset_closure hx))]
    exact max_eq_left (H.core i x hx)
  exact hcore.comp_tendsto (e.val.continuousAt_symm hz)

/-- Once a shifted core has supplied one fixed-coefficient presentation, every
later finite collar step retains it by either a local maximum or a collar germ
equality. -/
theorem finiteShiftedBergmanGlued_logarithmicTypeAt_core_final
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (i : Fin A.count) {e : ComplexChart n M}
    {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hzcore : e.val.symm z ∈ H.inner i) {c : ℚ}
    (hbranch : ∀ (j : Fin A.count) {e : ComplexChart n M}
      {z : ComplexModel n}, z ∈ e.val.target → e.val.symm z ∈ (A.patch j).patch.source →
        ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
          LogarithmicTypeAt
            (chartFunction (shiftedBergmanBranch (A.patch j).patch (offset j)) e)
            (c : ℝ) f z) :
    ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt
        (chartFunction (finiteShiftedBergmanGlued A offset g A.count) e)
        (c : ℝ) f z := by
  have hstart := finiteShiftedBergmanGlued_logarithmicTypeAt_core A offset g H i hz hzcore
    (hbranch i hz (H.closure_inner_subset i (subset_closure hzcore)))
  have hprop : ∀ k : ℕ, i.val + 1 ≤ k → k ≤ A.count →
      ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
        LogarithmicTypeAt (chartFunction (finiteShiftedBergmanGlued A offset g k) e)
          (c : ℝ) f z := by
    intro k hik hk
    induction k, hik using Nat.le_induction with
    | base => exact hstart
    | succ k hik ih =>
        exact finiteShiftedBergmanGlued_logarithmicTypeAt_succ A offset g H
          (Nat.lt_of_succ_le hk) hz hbranch (ih (Nat.le_of_succ_le hk))
  exact hprop A.count (Nat.succ_le_of_lt i.isLt) le_rfl

/-- With a common rational branch coefficient, an explicit cover by finite
shifted collar cores gives analytic singularity type in every actual complex
chart.  In particular, unlike the earlier persistence theorem, no
later-core-separation hypothesis occurs. -/
theorem finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType_of_commonCoefficient
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g) {c : ℚ}
    (hbranch : ∀ (i : Fin A.count) {e : ComplexChart n M}
      {z : ComplexModel n}, z ∈ e.val.target → e.val.symm z ∈ (A.patch i).patch.source →
        ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
          LogarithmicTypeAt
            (chartFunction (shiftedBergmanBranch (A.patch i).patch (offset i)) e)
            (c : ℝ) f z)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    HasManifoldAnalyticSingularityType (n := n)
      (finiteShiftedBergmanGlued A offset g A.count) := by
  intro e z hz
  obtain ⟨i, hzcore⟩ := hcover (e.val.symm z)
  obtain ⟨N, f, htype⟩ :=
    finiteShiftedBergmanGlued_logarithmicTypeAt_core_final A offset g H i hz hzcore hbranch
  exact ⟨c, N, f, htype⟩

/-- Every shifted Bergman branch has the common rational coefficient
`1 / m`. Therefore a finite core cover gives analytic singularity type for the
final collar candidate without any later-core-separation condition. -/
theorem finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType_of_coreCover
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    HasManifoldAnalyticSingularityType (n := n)
      (finiteShiftedBergmanGlued A offset g A.count) := by
  apply finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType_of_commonCoefficient
    A offset g H (c := (m : ℚ)⁻¹)
  · intro i e z hz hzsource
    exact ⟨(A.patch i).patch.N,
      fun l y => (A.patch i).patch.generator l
        (chartTransition e (A.patch i).patch.chart y),
      shiftedBergmanBranch_logarithmicTypeAt (A.patch i).patch (offset i) hm e hz hzsource⟩
  · exact hcover

/-- Under finite shifted collar data whose inner cores cover the manifold, the
final candidate is one effective theta-PSH term with analytic singularity
type. Neither later-core separation nor any sequence-level Demailly property
is used here. -/
theorem finiteShiftedBergmanGlued_effectiveTerm_of_coreCover
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (A : FiniteUniformLocalBergmanAtlas θ u m) (offset : Fin A.count → ℝ)
    (g : M → EReal) (H : FiniteShiftedBergmanCollarData A offset g)
    (hm : 0 < m) (hg : IsThetaPshPotential θ g)
    (hcover : ∀ x : M, ∃ i : Fin A.count, x ∈ H.inner i) :
    IsThetaPshPotential θ (finiteShiftedBergmanGlued A offset g A.count) ∧
      HasManifoldAnalyticSingularityType (n := n)
        (finiteShiftedBergmanGlued A offset g A.count) := by
  refine ⟨finiteShiftedBergmanGlued_isThetaPshPotential A offset g H hm hg A.count le_rfl,
    finiteShiftedBergmanGlued_hasManifoldAnalyticSingularityType_of_coreCover
      A offset g H hm hcover⟩

end

end SGPT.Foundations.Analysis.Pending.FiniteShiftedBergmanOverlapAnalyticType
