import SGPT.Foundations.Analysis.Pending.MeteredDivisorGlobalIdeal
import SGPT.Foundations.Analysis.Pending.DivisorMetric

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.Pending
open MeteredDivisorGlobalIdeal MeteredDivisorSingleGenerator

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Original local functions, their genuine logarithms and finite continuous
remainders assemble an actual effective Cartier divisor. The ideal is
constructed from principal holomorphic germs and is then read in EVERY
original presentation; no divisor or valuation is supplied by the caller. -/
theorem exists_effectiveDivisor_of_log_presentation (u : M → EReal)
    (hdata : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ (G : M → ℂ) (r : M → ℝ),
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
        NowhereIdenticallyZeroOn G U ∧
        (∀ y ∈ U, ContinuousAt r y) ∧
        ∀ y ∈ U, u y = singleLog G y + (r y : EReal)) :
    ∃ D : EffectiveDivisor n M,
      HasAnalyticSingularitiesOfType u 1 D.ideal ∧
      ∀ (V : Set M) (_ : IsOpen V) (G : M → ℂ) (r : M → ℝ),
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G V →
        NowhereIdenticallyZeroOn G V →
        (∀ y ∈ V, ContinuousAt r y) →
        (∀ y ∈ V, u y = singleLog G y + (r y : EReal)) →
        ∀ y ∈ V, ∀ f, D.ideal.mem y f ↔ IsInSpanAt (n := n) (· = G) y f := by
  classical
  choose U hU hxU G r hG hne hr hu using hdata
  let I : GermIdeal n M := ⟨fun x f => IsInSpanAt (n := n) (· = G x) x f⟩
  have hread (V : Set M) (hV : IsOpen V) (H : M → ℂ) (s : M → ℝ)
      (hH : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H V)
      (hHne : NowhereIdenticallyZeroOn H V)
      (hs : ∀ y ∈ V, ContinuousAt s y)
      (hueq : ∀ y ∈ V, u y = singleLog H y + (s y : EReal)) :
      ∀ y ∈ V, ∀ f, I.mem y f ↔ IsInSpanAt (n := n) (· = H) y f := by
    intro y hy f
    change IsInSpanAt (n := n) (· = G y) y f ↔ _
    have hopen := (hU y).inter hV
    have hpoint : y ∈ U y ∩ V := ⟨hxU y, hy⟩
    apply isInSpanAt_iff_of_sameSingularityTypeAt hopen
      ((hG y).mono inter_subset_left) (hH.mono inter_subset_right)
      (NowhereIdenticallyZeroOn.mono (hne y) inter_subset_left)
      (NowhereIdenticallyZeroOn.mono hHne inter_subset_right) hpoint
    refine sameSingularityTypeAt_of_weight_eq (c := 1) zero_lt_one
      (hopen.mem_nhds hpoint) ?_ (hr y y (hxU y)) (hs y hy)
    intro z hz
    simpa only [EReal.coe_one, one_mul] using (hu y z hz.1).symm.trans (hueq z hz.2)
  have hI : I.IsInvertible := by
    intro x
    exact ⟨U x, hU x, hxU x, G x, hG x, hne x,
      hread (U x) (hU x) (G x) (r x) (hG x) (hne x) (hr x) (hu x)⟩
  let D : EffectiveDivisor n M := ⟨I, hI⟩
  refine ⟨D, ?_, hread⟩
  refine ⟨zero_lt_one, ?_, ?_⟩
  · exact DivisorMetric.isCoherent_of_isInvertible hI
  · intro x
    obtain ⟨C, _, hC⟩ := boundedRealGermAt_of_continuousAt (hr x x (hxU x))
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hC
    refine ⟨U x ∩ V, (hU x).inter hV, ⟨hxU x, hxV⟩, 1, fun _ => G x,
      fun _ => (hG x).mono inter_subset_left, ?_, r x, C,
      fun y hy => hVsub hy.2, ?_⟩
    · intro y hy f
      change I.mem y f ↔ _
      rw [hread (U x) (hU x) (G x) (r x) (hG x) (hne x) (hr x) (hu x) y hy.1 f]
      exact isInSpanAt_congr_pred (by intro t; simp) y f
    · intro y hy
      simpa only [Rat.cast_one, EReal.coe_one, one_mul, singleLog] using hu x y hy.1

end SGPT.Okounkov
