import SGPT.Envelopes.DinewMeasureGlobal
import SGPT.Envelopes.RelativeCYDinew
import SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion

/-!
# Convex combinations against a common measure

Xia, *Foundations of pluripotential theory* (FPT), `cor:nonpluripolar-common-measure-convex`: if
`⟨Tⁿ⟩ ≥ f ν` and `⟨Sⁿ⟩ ≥ g ν`, then for `0 ≤ t ≤ 1`
`⟨(tT + (1-t)S)ⁿ⟩ ≥ (t f^{1/n} + (1-t) g^{1/n})ⁿ ν`.

* `diagonalPotentialMeasure_convexComb_ge` proves this for `T = θ₁ + ddᶜu`, `S = θ₂ + ddᶜv`
  (`tT + (1-t)S = (tθ₁ + (1-t)θ₂) + ddᶜ(tu + (1-t)v)`), conditional on the bounded coordinate
  inequality `BoundedMultifactorCommonMeasure n` (FPT `thm:bounded-multifactor-common-measure`).
  FPT's proof: the multilinear expansion of the non-pluripolar product of the convex combination
  (TN `globalMixedMeasure_diagonal_sumPot`), the mixed lower bound of every term
  (`globalMixedMeasure_ge_withDensity_prod`, FPT `prop:nonpluripolar-multifactor-common-measure`),
  and the binomial formula for the densities (`Finset.sum_pow'`). The endpoints `t = 0, 1` are the
  hypotheses.
* `globalMixedMeasure_ge_mixed`, `globalMixedMeasure_ge_mixed_pow`: FPT
  `cor:nonpluripolar-common-measure-mixed`, `⟨Tᵏ ∧ Sⁿ⁻ᵏ⟩ ≥ f^{k/n} g^{(n-k)/n} ν` (and the form for
  an arbitrary assignment of `T`, `S` to the slots), conditional on the same input.
* `commonMeasureConvexLowerBound_of_boundedMultifactor`: hence S61's statement
  `SGPT.Envelopes.RelativeCY.CommonMeasureConvexLowerBound n M` (the case `θ₁ = θ₂`) follows from
  `BoundedMultifactorCommonMeasure n`, on every compact complex manifold with its Borel
  σ-algebra.
* `commonMeasureConvexLowerBound_one`: in dimension `1` the bounded input holds, so
  `CommonMeasureConvexLowerBound 1 M` is unconditional.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

universe u

namespace SGPT.Envelopes.DinewMeasure

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.GlobalMultilinearExpansion
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Diagonal non-pluripolar measures depend only on the form and the potential. -/
theorem diagonalPotentialMeasure_congr' {θ θ' : ClosedRealOneOneForm n M} {u u' : M → EReal}
    (hθ : θ = θ') (hu : u = u') (h : IsThetaPshPotential θ.val u)
    (h' : IsThetaPshPotential θ'.val u') :
    diagonalPotentialMeasure θ u h = diagonalPotentialMeasure θ' u' h' := by
  subst hθ hu
  rfl

/-- The binomial formula for the densities:
`(a f^{1/n} + b g^{1/n})ⁿ = ∑_σ (∏ⱼ c(σⱼ)) ∏ⱼ h(σⱼ)^{1/n}` over all `σ : Fin n → Bool`. -/
theorem convex_density_expand (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (F G : ℝ≥0∞) :
    (ENNReal.ofReal a * F ^ ((n : ℝ)⁻¹) + ENNReal.ofReal b * G ^ ((n : ℝ)⁻¹)) ^ n =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
        ENNReal.ofReal (∏ j, cond (σ j) a b) * ∏ j, (cond (σ j) F G) ^ ((n : ℝ)⁻¹) := by
  have h2 : ENNReal.ofReal a * F ^ ((n : ℝ)⁻¹) + ENNReal.ofReal b * G ^ ((n : ℝ)⁻¹) =
      ∑ c : Bool, ENNReal.ofReal (cond c a b) * (cond c F G) ^ ((n : ℝ)⁻¹) := by
    rw [Fintype.sum_bool]
    rfl
  rw [h2, Finset.sum_pow']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg fun j _ => by
    cases σ j
    · exact hb
    · exact ha]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- The slot `b` of a two-current tuple is `θ₁`-psh or `θ₂`-psh. -/
theorem thetaPlurisubharmonic_cond {θ₁ θ₂ : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : ThetaPlurisubharmonic θ₁.val u) (hv : ThetaPlurisubharmonic θ₂.val v) (b : Bool) :
    ThetaPlurisubharmonic (cond b θ₁ θ₂).val (cond b u v) := by
  cases b
  · exact hv
  · exact hu

/-- **Mixed products of two currents against a common measure** (Xia, *Foundations of
pluripotential theory*, `cor:nonpluripolar-common-measure-mixed`, for an arbitrary assignment
`σ` of the two currents to the slots; conditional on `BoundedMultifactorCommonMeasure n`): if
`⟨(θ₁ + ddᶜu)ⁿ⟩ ≥ f ν` and `⟨(θ₂ + ddᶜv)ⁿ⟩ ≥ g ν`, the mixed product with slot `j` carrying
`θ₁ + ddᶜu` when `σ j` and `θ₂ + ddᶜv` otherwise is at least `∏ⱼ hⱼ^{1/n} ν`, `hⱼ = f` or `g`. -/
theorem globalMixedMeasure_ge_mixed (hB : BoundedMultifactorCommonMeasure n) (hn : 0 < n)
    {θ₁ θ₂ : ClosedRealOneOneForm n M} {u v : M → EReal} (hu : ThetaPlurisubharmonic θ₁.val u)
    (hv : ThetaPlurisubharmonic θ₂.val v) (ν : Measure M) [IsFiniteMeasure ν] {f g : M → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfu : ν.withDensity f ≤ globalMixedMeasure (fun _ => θ₁) (fun _ => u) (fun _ => hu))
    (hgv : ν.withDensity g ≤ globalMixedMeasure (fun _ => θ₂) (fun _ => v) (fun _ => hv))
    (σ : Fin n → Bool) :
    ν.withDensity (fun x => ∏ j, (cond (σ j) (f x) (g x)) ^ ((n : ℝ)⁻¹)) ≤
      globalMixedMeasure (fun j => cond (σ j) θ₁ θ₂) (fun j => cond (σ j) u v)
        (fun j => thetaPlurisubharmonic_cond hu hv (σ j)) := by
  have hslot : ∀ b : Bool, ν.withDensity (fun x => cond b (f x) (g x)) ≤
      globalMixedMeasure (fun _ => cond b θ₁ θ₂) (fun _ => cond b u v)
        (fun _ => thetaPlurisubharmonic_cond hu hv b) := fun b => by
    cases b
    · exact hgv
    · exact hfu
  have hm : ∀ b : Bool, Measurable (fun x => cond b (f x) (g x)) := fun b => by
    cases b
    · exact hg
    · exact hf
  exact globalMixedMeasure_ge_withDensity_prod hB hn (fun j => cond (σ j) θ₁ θ₂)
    (fun j => cond (σ j) u v) (fun j => thetaPlurisubharmonic_cond hu hv (σ j)) ν
    (fun j x => cond (σ j) (f x) (g x)) (fun j => hm (σ j)) (fun j => hslot (σ j))

/-- **FPT `cor:nonpluripolar-common-measure-mixed`** (conditional on
`BoundedMultifactorCommonMeasure n`): with the first `k` slots carrying `T = θ₁ + ddᶜu` and the
other `n - k` slots `S = θ₂ + ddᶜv`, `⟨Tᵏ ∧ Sⁿ⁻ᵏ⟩ ≥ f^{k/n} g^{(n-k)/n} ν` (`0 ≤ k ≤ n`; the
endpoint cases are the hypotheses). -/
theorem globalMixedMeasure_ge_mixed_pow (hB : BoundedMultifactorCommonMeasure n) (hn : 0 < n)
    {θ₁ θ₂ : ClosedRealOneOneForm n M} {u v : M → EReal} (hu : ThetaPlurisubharmonic θ₁.val u)
    (hv : ThetaPlurisubharmonic θ₂.val v) (ν : Measure M) [IsFiniteMeasure ν] {f g : M → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfu : ν.withDensity f ≤ globalMixedMeasure (fun _ => θ₁) (fun _ => u) (fun _ => hu))
    (hgv : ν.withDensity g ≤ globalMixedMeasure (fun _ => θ₂) (fun _ => v) (fun _ => hv))
    (k : ℕ) (hk : k ≤ n) :
    ν.withDensity (fun x => f x ^ ((k : ℝ) / n) * g x ^ (((n - k : ℕ) : ℝ) / n)) ≤
      globalMixedMeasure (fun j : Fin n => cond (decide ((j : ℕ) < k)) θ₁ θ₂)
        (fun j => cond (decide ((j : ℕ) < k)) u v)
        (fun j => thetaPlurisubharmonic_cond hu hv (decide ((j : ℕ) < k))) := by
  have h := globalMixedMeasure_ge_mixed hB hn hu hv ν hf hg hfu hgv
    (fun j : Fin n => decide ((j : ℕ) < k))
  have hd : (fun x => ∏ j : Fin n, (cond (decide ((j : ℕ) < k)) (f x) (g x)) ^ ((n : ℝ)⁻¹)) =
      fun x => f x ^ ((k : ℝ) / n) * g x ^ (((n - k : ℕ) : ℝ) / n) := by
    funext x
    rw [Fin.prod_univ_eq_prod_range
      (fun m => (cond (decide (m < k)) (f x) (g x)) ^ ((n : ℝ)⁻¹)) n]
    simp only [Bool.cond_decide, apply_ite (fun y : ℝ≥0∞ => y ^ ((n : ℝ)⁻¹))]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.range n).filter (fun m => m < k) = Finset.range k := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    have h2 : (Finset.range n).filter (fun m => ¬ m < k) = Finset.Ico k n := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [h1, h2, Finset.card_range, Nat.card_Ico, ← ENNReal.rpow_mul_natCast,
      ← ENNReal.rpow_mul_natCast, inv_mul_eq_div, inv_mul_eq_div]
  rwa [hd] at h

/-- **Convex combinations against a common measure** (Xia, *Foundations of pluripotential
theory*, `cor:nonpluripolar-common-measure-convex`, conditional on
`BoundedMultifactorCommonMeasure n`): for `θ₁`-psh `u`, `θ₂`-psh `v`, a finite measure `ν` and
measurable `f, g ≥ 0` with `⟨(θ₁ + ddᶜu)ⁿ⟩ ≥ f ν`, `⟨(θ₂ + ddᶜv)ⁿ⟩ ≥ g ν`, and `0 ≤ t ≤ 1`,
`⟨((tθ₁ + (1-t)θ₂) + ddᶜ(tu + (1-t)v))ⁿ⟩ ≥ (t f^{1/n} + (1-t) g^{1/n})ⁿ ν`. -/
theorem diagonalPotentialMeasure_convexComb_ge (hB : BoundedMultifactorCommonMeasure n)
    (hn : 0 < n) (θ₁ θ₂ : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential θ₁.val u) (hv : IsThetaPshPotential θ₂.val v) (ν : Measure M)
    [IsFiniteMeasure ν] (f g : M → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfu : ν.withDensity f ≤ diagonalPotentialMeasure θ₁ u hu)
    (hgv : ν.withDensity g ≤ diagonalPotentialMeasure θ₂ v hv) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hw : IsThetaPshPotential (t • θ₁ + (1 - t) • θ₂).val (convexComb t u v)) :
    ν.withDensity (fun x => (ENNReal.ofReal t * f x ^ ((n : ℝ)⁻¹) +
        ENNReal.ofReal (1 - t) * g x ^ ((n : ℝ)⁻¹)) ^ n) ≤
      diagonalPotentialMeasure (t • θ₁ + (1 - t) • θ₂) (convexComb t u v) hw := by
  classical
  have hn0 : n ≠ 0 := hn.ne'
  rcases ht0.eq_or_lt with rfl | ht0'
  · -- `t = 0`: the hypothesis on `v`
    have hθ : (0 : ℝ) • θ₁ + ((1 : ℝ) - 0) • θ₂ = θ₂ := by simp
    have hc : convexComb 0 u v = v := by funext x; simp [convexComb]
    rw [diagonalPotentialMeasure_congr' hθ hc hw hv]
    have hd : (fun x => (ENNReal.ofReal 0 * f x ^ ((n : ℝ)⁻¹) +
        ENNReal.ofReal (1 - 0) * g x ^ ((n : ℝ)⁻¹)) ^ n) = g := by
      funext x
      simp [ENNReal.rpow_inv_natCast_pow hn0]
    rw [hd]
    exact hgv
  rcases ht1.eq_or_lt with rfl | ht1'
  · -- `t = 1`: the hypothesis on `u`
    have hθ : (1 : ℝ) • θ₁ + ((1 : ℝ) - 1) • θ₂ = θ₁ := by simp
    have hc : convexComb 1 u v = u := by funext x; simp [convexComb]
    rw [diagonalPotentialMeasure_congr' hθ hc hw hu]
    have hd : (fun x => (ENNReal.ofReal 1 * f x ^ ((n : ℝ)⁻¹) +
        ENNReal.ofReal (1 - 1) * g x ^ ((n : ℝ)⁻¹)) ^ n) = f := by
      funext x
      simp [ENNReal.rpow_inv_natCast_pow hn0]
    rw [hd]
    exact hfu
  -- `0 < t < 1`: multilinear expansion
  set α : Bool → ClosedRealOneOneForm n M := fun c => cond c θ₁ θ₂ with hαdef
  set F : Bool → M → EReal := fun c => cond c u v with hFdef
  set wt : Bool → ℝ := fun c => cond c t (1 - t) with hwtdef
  set H : Bool → M → ℝ≥0∞ := fun c x => cond c (f x) (g x) with hHdef
  have hwt : ∀ c, 0 < wt c := fun c => by
    cases c
    · exact sub_pos.mpr ht1'
    · exact ht0'
  have hF : ∀ c, IsThetaPshPotential (α c).val (F c) := fun c => by
    cases c
    · exact hv
    · exact hu
  have hHm : ∀ c, Measurable (H c) := fun c => by
    cases c
    · exact hg
    · exact hf
  have hH : ∀ c, ν.withDensity (H c) ≤
      globalMixedMeasure (fun _ => α c) (fun _ => F c) (fun _ => (hF c).1) := fun c => by
    cases c
    · exact hgv
    · exact hfu
  have hform : sumForm Finset.univ wt α = t • θ₁ + (1 - t) • θ₂ := by
    simp only [sumForm, Fintype.sum_bool]
    rfl
  have hpot : sumPot Finset.univ wt F = convexComb t u v := by
    funext x
    simp only [sumPot, Fintype.sum_bool]
    rfl
  have hexp := globalMixedMeasure_diagonal_sumPot Finset.univ_nonempty hwt (fun c => (hF c).1)
    (fun c => ⟨(hF c).1.quasiPlurisubharmonic, (hF c).2⟩)
  have hmeas : diagonalPotentialMeasure (t • θ₁ + (1 - t) • θ₂) (convexComb t u v) hw =
      ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
        ENNReal.ofReal (∏ j, wt (σ j)) • globalMixedMeasure (fun j => α (σ j))
          (fun j => F (σ j)) (fun j => (hF (σ j)).1) := by
    rw [← hexp]
    exact SGPT.Foundations.Analysis.Pending.GlobalDiagonalScaling.globalMixedMeasure_congr
      (funext fun _ => hform.symm) (funext fun _ => hpot.symm) _ _
  -- the mixed lower bound of every term
  have hterm : ∀ σ : Fin n → Bool, ν.withDensity (fun x => ∏ j, H (σ j) x ^ ((n : ℝ)⁻¹)) ≤
      globalMixedMeasure (fun j => α (σ j)) (fun j => F (σ j)) (fun j => (hF (σ j)).1) :=
    fun σ => globalMixedMeasure_ge_withDensity_prod hB hn (fun j => α (σ j)) (fun j => F (σ j))
      (fun j => (hF (σ j)).1) ν (fun j => H (σ j)) (fun j => hHm (σ j)) (fun j => hH (σ j))
  -- assemble
  rw [hmeas]
  refine Measure.le_iff.mpr fun s hs => ?_
  have hD : (fun x => (ENNReal.ofReal t * f x ^ ((n : ℝ)⁻¹) +
      ENNReal.ofReal (1 - t) * g x ^ ((n : ℝ)⁻¹)) ^ n) =
      fun x => ∑ σ ∈ Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset Bool)),
        ENNReal.ofReal (∏ j, wt (σ j)) * ∏ j, H (σ j) x ^ ((n : ℝ)⁻¹) :=
    funext fun x => convex_density_expand t (1 - t) ht0 (sub_nonneg.mpr ht1) (f x) (g x)
  have hPm : ∀ σ : Fin n → Bool, Measurable (fun x => ∏ j, H (σ j) x ^ ((n : ℝ)⁻¹)) :=
    fun σ => Finset.measurable_prod _ fun j _ => (hHm (σ j)).pow_const _
  rw [hD, withDensity_apply _ hs, lintegral_finsetSum _ fun σ _ => (hPm σ).const_mul _,
    Measure.finsetSum_apply]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [lintegral_const_mul _ (hPm σ), Measure.smul_apply, smul_eq_mul, ← withDensity_apply _ hs]
  exact mul_le_mul_right (hterm σ s) _

/-- **S61's `CommonMeasureConvexLowerBound` from the bounded coordinate inequality**: Dinew's
lower bound for convex combinations of two potentials of one class against a common finite
measure (FPT `cor:nonpluripolar-common-measure-convex` with `T = θ_u`, `S = θ_v`) holds on every
compact complex manifold with its Borel σ-algebra, given FPT
`thm:bounded-multifactor-common-measure` (`BoundedMultifactorCommonMeasure k`). -/
theorem commonMeasureConvexLowerBound_of_boundedMultifactor {k : ℕ} (M : Type u)
    [TopologicalSpace M] [ChartedSpace (ComplexModel k) M] [IsComplexManifold k M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    (hB : BoundedMultifactorCommonMeasure k) :
    SGPT.Envelopes.RelativeCY.CommonMeasureConvexLowerBound k M := by
  intro hk θ u v hu hv ν _ f g hf hg hfu hgv t ht0 ht1 hw
  have hθ : t • θ + (1 - t) • θ = θ := by rw [← add_smul, add_sub_cancel, one_smul]
  have hw' : IsThetaPshPotential (t • θ + (1 - t) • θ).val (convexComb t u v) := by
    rw [hθ]; exact hw
  have h := diagonalPotentialMeasure_convexComb_ge hB hk θ θ u v hu hv ν f g hf hg hfu hgv t ht0
    ht1 hw'
  rwa [diagonalPotentialMeasure_congr' hθ rfl hw' hw] at h

/-- **`CommonMeasureConvexLowerBound` in dimension `1`** (unconditional). -/
theorem commonMeasureConvexLowerBound_one (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel 1) M] [IsComplexManifold 1 M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] : SGPT.Envelopes.RelativeCY.CommonMeasureConvexLowerBound 1 M :=
  commonMeasureConvexLowerBound_of_boundedMultifactor M boundedMultifactorCommonMeasure_one

end SGPT.Envelopes.DinewMeasure
