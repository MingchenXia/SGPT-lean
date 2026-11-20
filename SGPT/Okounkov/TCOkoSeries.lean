import SGPT.Okounkov.AlgebraicDXBody
import SGPT.LineBundle.SectionFiltration

/-!
# Okounkov bodies of graded linear series

Source: `rmk:Okounkov:L2335` (chapter *The theory of Okounkov bodies*, section *Okounkov test
curves*): *"`Δ_{Y•}(θ, Γ_τ)` is the Okounkov body of a graded linear series `⊕_k 𝓕^{kτ}_k` …
our theory of partial Okounkov bodies recovers the Okounkov bodies of the filtered linear
series in the sense of [BC11]."*  Lane TC-OKO, blueprint `claude-tc-oko`.

A *graded linear series* of `L` [LM09, §1.3] is a family of subspaces
`W_k ⊆ H⁰(X, L^k)` with `W_k · W_{k'} ⊆ W_{k+k'}`.  Its Okounkov body ([LM09, Def. 1.8],
[BC11, §1]) is the Okounkov body (the book's `def:Okokk`, `SGPT.AlmostSemigroup.Okounkov.body`)
of its valuative semigroup `Γ(W) = {(ν(s), k) : s ∈ W_k ∖ 0}`, `ν = ν_{Y•}` the flag valuation
of a smooth flag (the setting of `def:Okobd`, `lineBundleOkounkovBody`, which is the case
`W_k = H⁰(X, L^k)`).  The *filtered linear series* of a filtration `𝓕` of `R(X, L)`
(`def:testcurve:L1134`) at level `τ` is `V^τ_k = 𝓕^{kτ}_k` ([BC11, §1.3]).

## Main definitions

* `GradedLinearSeries f a`: graded linear series of `L`; `filtrationSeries 𝓕 τ`: `⊕_k 𝓕^{kτ}_k`.
* `seriesSemigroup`, `seriesBody`: the valuative semigroup `Γ(W)` and the Okounkov body `Δ(W)`.

## Main results

* `seriesBody_subset_generalPartialBody`: if every `s ∈ W_k` lies in `H⁰(X, L^k ⊗ 𝓘(kφ))`, then
  `Δ(W) ⊆ Δ_{Y•}(θ, φ)` (the partial Okounkov body of `θ_φ`, `def:generalPOB`).
* `finrank_le_integerLatticeCount`: `dim W_k ≤ #(k Δ(W) ∩ ℤⁿ)` (one-dimensional leaves of `ν`).
* `liminf_le_seriesBody`: `liminf_k n! dim W_k / kⁿ ≤ n! vol Δ(W)` for `Δ(W)` compact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.TCOko

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.LineBundle SGPT.AlmostSemigroup
open scoped Topology ENNReal Pointwise

/-! ### Graded linear series -/

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) {L : X.Modules} (a : LineBundleAtlas L)

/-- **A graded linear series** of `L` [LM09, §1.3]: subspaces `W_k ⊆ H⁰(X, L^k)` with
`W_k · W_{k'} ⊆ W_{k+k'}` (products of sections, `SectionSpace.mul`). -/
structure GradedLinearSeries where
  /-- The degree-`k` piece `W_k ⊆ H⁰(X, L^k)`. -/
  piece : ∀ k : ℕ, Submodule ℂ (SectionSpace f L k)
  /-- `W_k · W_{k'} ⊆ W_{k+k'}`. -/
  mul_mem : ∀ (k k' : ℕ) (s : SectionSpace f L k) (t : SectionSpace f L k'),
    s ∈ piece k → t ∈ piece k' → SectionSpace.mul f a k k' s t ∈ piece (k + k')

variable {f a}

/-- **The filtered linear series** `V^τ_• = ⊕_k 𝓕^{kτ}_k` of a filtration `𝓕` of `R(X, L)` at
level `τ ∈ ℝ` ([BC11, §1.3]; the graded linear series of `rmk:Okounkov:L2335`). -/
def filtrationSeries (F : SectionFiltration f a) (τ : ℝ) : GradedLinearSeries f a where
  piece k := F.piece ((k : ℝ) * τ) k
  mul_mem k k' s t hs ht := by
    have h := F.mul_mem _ _ k k' s t hs ht
    have heq : (k : ℝ) * τ + (k' : ℝ) * τ = ((k + k' : ℕ) : ℝ) * τ := by push_cast; ring
    rwa [heq] at h

@[simp] theorem filtrationSeries_piece (F : SectionFiltration f a) (τ : ℝ) (k : ℕ) :
    (filtrationSeries F τ).piece k = F.piece ((k : ℝ) * τ) k := rfl

/-! ### The valuative semigroup and the Okounkov body -/

variable (f) (n : ℕ) [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance tcOkoSeriesTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcOkoSeriesCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable [IsIntegral X] (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **The valuative semigroup** `Γ(W) = {(ν(s), k) : k ∈ ℕ, s ∈ W_k ∖ 0}` of a graded linear
series (an additive semigroup: `ν(st) = ν(s) + ν(t)` and `st ≠ 0` on the integral `X`). -/
def seriesSemigroup (W : GradedLinearSeries f a) : AddSubsemigroup ((Fin n → ℤ) × ℤ) := by
  letI := E.isSeparated
  letI := E.quasiCompact
  let ω := schemeProjectiveTNKahlerBackground f n E
  let p := (schemeProjectiveOriginalFlagPoint f n E ω Y hY).val
  refine
    { carrier := {z | ∃ (k : ℕ) (s : SectionSpace f L k) (hs : s ≠ 0), s ∈ W.piece k ∧
        z = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ))}
      add_mem' := ?_ }
  rintro z w ⟨k, s, hs, hsW, rfl⟩ ⟨k', t, ht, htW, rfl⟩
  have hu : atlasPowerGlobalMul a k k' s t ≠ 0 :=
    schemePointPowerGlobalMul_ne_zero f n p a k k' s t hs ht
  have hv := schemeOriginalFlagSectionVector_mul f n E ω Y hY a k k' s t hs ht
  change schemeFubiniStudySectionVector f n E Y hY a (k + k') (atlasPowerGlobalMul a k k' s t) hu =
    schemeFubiniStudySectionVector f n E Y hY a k s hs +
      schemeFubiniStudySectionVector f n E Y hY a k' t ht at hv
  refine ⟨k + k', atlasPowerGlobalMul a k k' s t, hu, W.mul_mem k k' s t hsW htW, ?_⟩
  rw [hv]
  ext i <;> simp

/-- **The Okounkov body of a graded linear series** `Δ_{Y•}(W) = Δ(Γ(W))` ([LM09, Def. 1.8],
[BC11, §1.2]): the height-one slice of the closed convex cone generated by `Γ(W)`
(the book's `def:Okokk`). -/
def seriesBody (W : GradedLinearSeries f a) : Set (Fin n → ℝ) :=
  SGPT.AlmostSemigroup.Okounkov.body (seriesSemigroup f n E Y hY W)

variable {f n E Y hY}

theorem mem_seriesSemigroup {W : GradedLinearSeries f a} {z : (Fin n → ℤ) × ℤ} :
    z ∈ seriesSemigroup f n E Y hY W ↔
      ∃ (k : ℕ) (s : SectionSpace f L k) (hs : s ≠ 0), s ∈ W.piece k ∧
        z = ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)) :=
  Iff.rfl

/-- `Δ(W)` is closed. -/
theorem isClosed_seriesBody (W : GradedLinearSeries f a) :
    IsClosed (seriesBody f n E Y hY W) := by
  have hc := SGPT.AlmostSemigroup.Okounkov.isClosed_closedCone (seriesSemigroup f n E Y hY W)
  exact hc.preimage (continuous_id.prodMk continuous_const)

/-- `Δ(W)` is convex. -/
theorem convex_seriesBody (W : GradedLinearSeries f a) : Convex ℝ (seriesBody f n E Y hY W) :=
  SGPT.AlmostSemigroup.Okounkov.convex_body _

/-- Normalized points of `Γ(W)` lie in `Δ(W)`: `k⁻¹ ν(s) ∈ Δ(W)` for `0 ≠ s ∈ W_k`, `k > 0`. -/
theorem normalized_mem_seriesBody {W : GradedLinearSeries f a} {k : ℕ} (hk : 0 < k)
    {s : SectionSpace f L k} (hs : s ≠ 0) (hsW : s ∈ W.piece k) :
    (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)) ∈
      seriesBody f n E Y hY W := by
  have hz : ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)) ∈
      seriesSemigroup f n E Y hY W := ⟨k, s, hs, hsW, rfl⟩
  have h := SGPT.AlmostSemigroup.Okounkov.normalizedPoint_mem_heightOne
    (SGPT.AlmostSemigroup.Okounkov.closedCone (seriesSemigroup f n E Y hY W) :
      ConvexCone ℝ ((Fin n → ℝ) × ℝ))
    (z := ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)))
    (SGPT.AlmostSemigroup.Okounkov.mem_closedCone_of_mem _ hz)
    (show (0 : ℤ) < (k : ℤ) by exact_mod_cast hk)
  have heq : (k : ℝ)⁻¹ • (fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℝ)) =
      SGPT.AlmostSemigroup.Okounkov.normalizedPoint
        ((fun i => (schemeFubiniStudySectionVector f n E Y hY a k s hs i : ℤ)), (k : ℤ)) := by
    funext i
    simp [SGPT.AlmostSemigroup.Okounkov.normalizedPoint, Counting.integerCast]
  rw [heq]
  exact h

/-! ### Counting: `dim W_k ≤ #(k Δ(W) ∩ ℤⁿ)` -/

/-- **Valuative points count dimensions, against the body**: for `k > 0` and `Δ(W)` compact,
`dim W_k ≤ #(k Δ(W) ∩ ℤⁿ)` (the `dim W_k` distinct values `ν(s)`, `[LM09, Lemma 1.3]`, are
lattice points of `k Δ(W)`). -/
theorem finrank_le_integerLatticeCount (W : GradedLinearSeries f a)
    (hc : IsCompact (seriesBody f n E Y hY W)) {k : ℕ} (hk : 0 < k) :
    Module.finrank ℂ (W.piece k) ≤
      Counting.integerLatticeCount (seriesBody f n E Y hY W) k := by
  rw [← SGPT.IGood.DXMain.card_sectionValues_eq_finrank f n E Y hY a k (W.piece k)]
  have hfin := Counting.finite_integerPoints_dilate hc k
  have := hfin.to_subtype
  let g : SGPT.IGood.DXMain.sectionValues f n E Y hY a k (W.piece k) →
      Counting.integerPoints ((k : ℝ) • seriesBody f n E Y hY W) := fun v =>
    ⟨fun i => (v.val i : ℤ), by
      obtain ⟨s, hs, hsW, hsv⟩ := v.property
      have hz : ((fun i => (v.val i : ℤ)), (k : ℤ)) ∈ seriesSemigroup f n E Y hY W :=
        ⟨k, s, hs, hsW, by rw [hsv]⟩
      have hmem := SGPT.AlmostSemigroup.Okounkov.mem_closedCone_of_mem _ hz
      exact (Counting.mem_slice_iff_integerPoints_heightOne
        (SGPT.AlmostSemigroup.Okounkov.closedCone (seriesSemigroup f n E Y hY W) :
          ConvexCone ℝ ((Fin n → ℝ) × ℝ)) k hk _).mp hmem⟩
  have hg : Function.Injective g := by
    intro v w hvw
    apply Subtype.ext
    funext i
    have h := congrFun (congrArg Subtype.val hvw) i
    change ((v.val i : ℕ) : ℤ) = (w.val i : ℤ) at h
    exact_mod_cast h
  exact Nat.card_le_card_of_injective g hg

/-- **Asymptotic upper bound**: for `Δ(W)` compact,
`liminf_k n! dim W_k / kⁿ ≤ n! vol Δ(W)` (lattice point count of the compact convex `Δ(W)`). -/
theorem liminf_le_seriesBody (W : GradedLinearSeries f a)
    (hc : IsCompact (seriesBody f n E Y hY W)) :
    liminf (fun k : ℕ => ((n.factorial : ℝ≥0∞) * (Module.finrank ℂ (W.piece k) : ℝ≥0∞)) /
      (k : ℝ≥0∞) ^ n) atTop ≤ (n.factorial : ℝ≥0∞) * volume (seriesBody f n E Y hY W) := by
  set K := seriesBody f n E Y hY W with hK
  have hlim := Counting.tendsto_integer_lattice_count hc (convex_seriesBody (Y := Y) (hY := hY) W)
  have hlim' : Tendsto (fun k : ℕ => (n.factorial : ℝ≥0∞) *
      ENNReal.ofReal ((k : ℝ)⁻¹ ^ n * (Counting.integerLatticeCount K k : ℝ))) atTop
      (𝓝 ((n.factorial : ℝ≥0∞) * ENNReal.ofReal (volume.real K))) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hlim) (Or.inr (ENNReal.natCast_ne_top _))
  have hvol : ENNReal.ofReal (volume.real K) = volume K :=
    ENNReal.ofReal_toReal hc.measure_lt_top.ne
  rw [hvol] at hlim'
  rw [← hlim'.liminf_eq]
  refine liminf_le_liminf ((eventually_gt_atTop 0).mono fun k hk => ?_)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcount := finrank_le_integerLatticeCount W hc hk
  have heq : ENNReal.ofReal ((k : ℝ)⁻¹ ^ n * (Counting.integerLatticeCount K k : ℝ)) =
      (Counting.integerLatticeCount K k : ℝ≥0∞) / (k : ℝ≥0∞) ^ n := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos hkR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      ← ENNReal.inv_pow, mul_comm, div_eq_mul_inv]
  rw [heq, mul_div_assoc]
  gcongr

end SGPT.Okounkov.TCOko
