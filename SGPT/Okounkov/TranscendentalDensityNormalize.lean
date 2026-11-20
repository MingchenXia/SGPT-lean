import SGPT.Okounkov.TranscendentalDensityLocal
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.ChartGeneratorLift

/-!
# Clearing the denominators of an analytic singularity type

Source: blueprint node `tok:density`, first step of the proof ("by compactness and
`tok:analytic-algebra` there is an integer `N` with `φ = (1/N) log ∑ᵢ |g_{x,i}|² + O(1)` near every
`x`; … we may replace `ξ` by `Nξ` and assume `N = 1`").

A potential `φ` with analytic singularities (TN's `HasManifoldAnalyticSingularityType`: in every
holomorphic chart, near every point, `φ = c log ∑ |fᵢ|² + O(1)` with `c ∈ ℚ_{>0}`) on a compact
complex manifold admits one positive integer `N` such that `Nφ = log ∑ |gᵢ|² + O(1)` near every
point, with holomorphic `gᵢ` on the manifold (`exists_nat_unitLogPresentedAt`). Near each point
the presentation in the preferred chart is pulled back to the manifold
(`SGPT.Foundations.Analysis.Pending.ChartGeneratorLift`); compactness gives finitely many
coefficients `c_x`, `N` is the product of their denominators, and `N c_x log ∑ |f|²` is the
logarithm of the `N c_x`-fold products of the `fᵢ` (`generatorLog_tensorPowerFamily`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalDensity

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
open SGPT.Foundations.Analysis.Pending.ChartGeneratorLift

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Finite products of holomorphic functions on an open set of `ℂⁿ` are holomorphic. -/
theorem differentiableOn_tensorPowerFamily {N r : ℕ} {f : Fin N → ComplexModel n → ℂ}
    {W : Set (ComplexModel n)} (hf : ∀ i, DifferentiableOn ℂ (f i) W)
    (s : Fin (Fintype.card (Fin r → Fin N))) :
    DifferentiableOn ℂ (tensorPowerFamily f r s) W := by
  have h : DifferentiableOn ℂ
      (∏ i : Fin r, f ((Fintype.equivFin (Fin r → Fin N)).symm s i)) W :=
    Finset.prod_induction _ (fun F => DifferentiableOn ℂ F W) (fun _ _ ha hb => ha.mul hb)
      (differentiableOn_const 1) (fun i _ => hf _)
  refine h.congr fun z _ => ?_
  simp [tensorPowerFamily, Finset.prod_apply]

omit [IsComplexManifold n X] in
/-- The local presentation of `φ` near `x`, in the preferred chart, on an open coordinate set. -/
theorem exists_local_chart_presentation {φ : X → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := n) φ) (x : X) :
    ∃ c : ℚ, 0 < c ∧ ∃ (W : Set (ComplexModel n)) (r : ℕ) (f : Fin r → ComplexModel n → ℂ)
      (b : ComplexModel n → ℝ) (C : ℝ), IsOpen W ∧
      (complexChartAt (n := n) x).val x ∈ W ∧ W ⊆ (complexChartAt (n := n) x).val.target ∧
      (∀ i, DifferentiableOn ℂ (f i) W) ∧ (∀ z ∈ W, |b z| ≤ C) ∧
      ∀ z ∈ W, chartFunction φ (complexChartAt (n := n) x) z =
        ((c : ℝ) : EReal) * generatorLog f z + (b z : EReal) := by
  set e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨c, r, f, hc, ⟨V, hV, hxV, hfV⟩, b, ⟨C, -, hbC⟩, heq⟩ :=
    hφ e (e.val x) (e.val.map_source hx)
  have hS : {z | chartFunction φ e z = ((c : ℝ) : EReal) * generatorLog f z + (b z : EReal) ∧
      |b z| ≤ C} ∩ V ∩ e.val.target ∈ 𝓝 (e.val x) :=
    inter_mem (inter_mem (heq.and hbC) (hV.mem_nhds hxV))
      (e.val.open_target.mem_nhds (e.val.map_source hx))
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hS
  refine ⟨c, by exact_mod_cast hc, W, r, f, b, C, hW, hxW, fun z hz => (hWsub hz).2,
    fun i => (hfV i).mono fun z hz => (hWsub hz).1.2, fun z hz => (hWsub hz).1.1.2,
    fun z hz => (hWsub hz).1.1.1⟩

/-- A positive rational times a suitable positive integer is a positive integer. -/
theorem exists_nat_eq_mul_of_den_dvd {c : ℚ} (hc : 0 < c) {N : ℕ} (hN : c.den ∣ N) :
    ∃ p : ℕ, ((p : ℕ) : ℝ) = (N : ℝ) * (c : ℝ) := by
  obtain ⟨q, rfl⟩ := hN
  refine ⟨q * c.num.toNat, ?_⟩
  have hnum : ((c.num.toNat : ℕ) : ℚ) = c.num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hc.le)
  have hq : ((q * c.num.toNat : ℕ) : ℚ) = ((c.den * q : ℕ) : ℚ) * c := by
    push_cast
    rw [hnum, ← Rat.mul_den_eq_num]
    ring
  have := congrArg (fun t : ℚ => (t : ℝ)) hq
  push_cast at this ⊢
  exact this

/-- **Clearing denominators** (`tok:density`, first step): on a compact complex manifold, a
potential with analytic singularities has a positive integer multiple `Nφ` which is
`log ∑ |gᵢ|² + O(1)` near every point, with holomorphic `gᵢ`. -/
theorem exists_nat_unitLogPresentedAt [CompactSpace X] {φ : X → EReal}
    (hφ : HasManifoldAnalyticSingularityType (n := n) φ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, UnitLogPresentedAt (n := n) (fun y => ((N : ℝ) : EReal) * φ y) x := by
  classical
  choose c hc W r f b C hW hxW hWt hfW hbC heq using exists_local_chart_presentation hφ
  let U : X → Set X := fun x => domain (complexChartAt (n := n) x) (W x)
  have hU : ∀ x, IsOpen (U x) := fun x => isOpen_domain _ (hW x)
  have hxU : ∀ x, x ∈ U x := fun x => ⟨mem_complexChartAt_source x, hxW x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨∏ x ∈ s, (c x).den, Finset.prod_pos fun x _ => (c x).den_pos, fun y => ?_⟩
  set N := ∏ x ∈ s, (c x).den with hN
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
  obtain ⟨hxs, hyx⟩ := mem_iUnion.mp hx
  obtain ⟨p, hp⟩ := exists_nat_eq_mul_of_den_dvd (hc x)
    (Finset.dvd_prod_of_mem (fun x => (c x).den) hxs)
  set e := complexChartAt (n := n) x
  refine ⟨U x, hU x, hyx, Fintype.card (Fin p → Fin (r x)),
    generator e (tensorPowerFamily (f x) p),
    generator_mdifferentiableOn e (W x) _ (differentiableOn_tensorPowerFamily (hfW x)),
    fun y' => (N : ℝ) * b x (e.val y'), (N : ℝ) * C x, fun y' hy' => ?_, fun y' hy' => ?_⟩
  · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left (hbC x _ hy'.2) (Nat.cast_nonneg N)
  · have hchart : φ y' = chartFunction φ e (e.val y') := by
      change φ y' = φ (e.val.symm (e.val y'))
      rw [e.val.left_inv hy'.1]
    rw [← hN] at hp
    dsimp only
    rw [hchart, heq x _ hy'.2, generatorLog_apply, generatorLog_tensorPowerFamily, hp,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (Nat.cast_nonneg N))
        (EReal.coe_ne_top _), ← mul_assoc, ← EReal.coe_mul, ← EReal.coe_mul]

end SGPT.Okounkov.TranscendentalDensity
