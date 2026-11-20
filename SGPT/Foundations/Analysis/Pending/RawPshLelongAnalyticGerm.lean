import SGPT.Foundations.Analysis.Pending.RawLelongBergmanJetEquations
import SGPT.Foundations.Analysis.Pending.CommonDomainHolomorphicZeroSet
import SGPT.Foundations.Analysis.Pending.LelongChartReaderInvariance
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option autoImplicit false

/-! # Genuine raw Siu superlevel analytic germs

The full common-domain family of original Bergman jets is finitely presented
on one internally produced neighborhood. No analytic-superlevel or finite
Lelong certificate is assumed. The local raw quasi-PSH consequence retains
the original smooth correction and all pole cases.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RawPshLelongAnalyticGerm

open FirstPass FirstPass.NonKahlerLocus BergmanGenerators AnalyticGermDecomposition
  LelongNumberComparison LelongChartReaderInvariance

noncomputable section

private def jetEvaluation {n j : ℕ} (v : Fin j → ComplexModel n) :
    (ComplexModel n [×j]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => F v
      map_add' := fun F G => by simp
      map_smul' := fun a F => by simp }
    (∏ i, ‖v i‖) (fun F => by
      dsimp
      simpa only [mul_comm] using F.le_opNorm v)

/-- Every original raw PSH superlevel is an actual finite-equation analytic
germ, with all its weighted jet equations on one common original domain. -/
theorem isAnalyticGerm_superlevel {n : ℕ} (P : ComplexModel n → EReal)
    {R : ℝ} (hR : 0 < R) (hP : PlurisubharmonicOn P (ball 0 (4 * R))) (q : ℝ) :
    IsAnalyticGerm {x : ComplexModel n | ENNReal.ofReal q ≤ lelongNumber (n := n) P x} := by
  classical
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  cases n with
  | zero =>
    have htop (x : ComplexModel 0) : lelongNumber (n := 0) P x = ⊤ :=
      LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot
        (by rw [LelongNumberChartTransport.nhdsWithin_ne_eq_bot_of_dim_eq_zero rfl]
            exact Filter.eventually_bot)
    have hset : {x : ComplexModel 0 | ENNReal.ofReal q ≤ lelongNumber (n := 0) P x} =
        univ := by
      ext x
      simp only [htop, le_top, ofPred_true]
    rw [hset]
    exact isAnalyticGerm_univ
  | succ m =>
    let e := (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).toBasis
    let I := (Σ j : ℕ, Fin j → Fin (m + 1)) × ℕ × ℕ × (ComplexModel (m + 1) → ℂ)
    let eligible : I → Prop := fun s => 1 ≤ s.2.1 ∧
      2 * ((s.2.2.1 : ℝ) + ((m + 1 : ℕ) : ℝ)) / (s.2.1 : ℝ) ≤ q ∧
      s.2.2.2 ∈ bergmanUnitBall 0 R (fun y => multiplierWeight (s.2.1 : ℝ) (P y)) ∧
      s.1.1 < s.2.2.1
    let g : I → ComplexModel (m + 1) → ℂ := fun s x =>
      if eligible s then iteratedFDeriv ℂ s.1.1 s.2.2.2 x (fun i => e (s.1.2 i)) else 0
    have hg (s : I) : DifferentiableOn ℂ (g s) (ball 0 (2 * R)) := by
      by_cases hs : eligible s
      · have hf : DifferentiableOn ℂ s.2.2.2 (ball 0 (2 * R)) := hs.2.2.1.1
        have ha : AnalyticOnNhd ℂ s.2.2.2 (ball 0 (2 * R)) :=
          HolomorphicAnalytic.analyticOnNhd_of_differentiableOn isOpen_ball hf
        let E := jetEvaluation (fun i => e (s.1.2 i))
        have hjet := E.comp_analyticOnNhd (ha.iteratedFDeriv s.1.1)
        intro x hx
        have hdiff : DifferentiableWithinAt ℂ (fun x => E (iteratedFDeriv ℂ s.1.1 s.2.2.2 x))
            (ball 0 (2 * R)) x := (hjet x hx).differentiableAt.differentiableWithinAt
        change DifferentiableWithinAt ℂ (fun x => iteratedFDeriv ℂ s.1.1 s.2.2.2 x
          (fun i => e (s.1.2 i))) (ball 0 (2 * R)) x at hdiff
        simpa only [g, if_pos hs] using hdiff
      · simpa only [g, if_neg hs] using
          (differentiableOn_const (s := ball (0 : ComplexModel (m + 1)) (2 * R)) (0 : ℂ))
    have heq (x : ComplexModel (m + 1)) (hx : x ∈ ball 0 (2 * R)) :
        (ENNReal.ofReal q ≤ lelongNumber (n := m + 1) P x) ↔ ∀ s, g s x = 0 := by
      rw [RawLelongBergmanJetEquations.superlevel_iff m R hR P hP x hx q]
      constructor
      · intro h s
        by_cases hs : eligible s
        · dsimp only [g]
          rw [if_pos hs, h s.2.1 hs.1 s.2.2.1 hs.2.1 s.2.2.2 hs.2.2.1 s.1.1 hs.2.2.2]
          rfl
        · simp only [g, if_neg hs]
      · intro h k hk K hK f hf j hj
        apply ContinuousMultilinearMap.toMultilinearMap_injective
        apply Module.Basis.ext_multilinear (fun _ : Fin j => e)
        intro v
        change iteratedFDeriv ℂ j f x (fun i => e (v i)) = 0
        let s : I := (⟨j, v⟩, k, K, f)
        have hs : eligible s := ⟨hk, hK, hf, hj⟩
        have hz := h s
        simpa only [g, if_pos hs, s] using hz
    have hcommon : ∀ s, DifferentiableOn ℂ (g s) (ball 0 (4 * (R / 2))) := by
      have hradius : 4 * (R / 2) = 2 * R := by ring
      rw [hradius]
      exact hg
    obtain ⟨N, G, hG, hzero⟩ :=
      CommonDomainHolomorphicZeroSet.isAnalyticGerm_zero_set g (by positivity) hcommon
    refine ⟨N, G, hG, ?_⟩
    filter_upwards [hzero, ball_mem_nhds (0 : ComplexModel (m + 1))
      (by positivity : 0 < 2 * R)] with x hz hx
    exact (heq x hx).trans hz

/-- A raw quasi-PSH germ has genuine analytic Lelong superlevels, including
identically minus-infinite germs, with no nondegeneracy or finite reader input. -/
theorem isAnalyticGerm_superlevel_of_quasiPlurisubharmonicAt {n : ℕ}
    {u : ComplexModel n → EReal} (hu : QuasiPlurisubharmonicAt u 0) (q : ℝ) :
    IsAnalyticGerm {x : ComplexModel n | ENNReal.ofReal q ≤ lelongNumber (n := n) u x} := by
  obtain ⟨P, h, ⟨W, hW, h0W, hP⟩, hsmooth, heq⟩ := hu
  have hnear : ∀ᶠ x in 𝓝 (0 : ComplexModel n),
      (x ∈ W ∧ u x = P x + (h x : EReal)) ∧ ContDiffAt ℝ ∞ h x :=
    ((show ∀ᶠ x in 𝓝 (0 : ComplexModel n), x ∈ W from
      hW.mem_nhds h0W).and heq).and hsmooth
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hPball : PlurisubharmonicOn P (ball 0 (4 * (r / 8))) :=
    (hP.plurisubharmonicOn hW).mono fun x hx =>
      (hball (ball_subset_ball (by linarith) hx)).1.1
  have hν (x : ComplexModel n) (hx : x ∈ ball 0 r) :
      lelongNumber (n := n) u x = lelongNumber (n := n) P x := by
    have hloc : u =ᶠ[𝓝 x] fun y => P y + (h y : EReal) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ ball 0 r from
        isOpen_ball.mem_nhds hx).mono fun y hy => (hball hy).1.2
    rw [lelongNumber_congr hloc,
      lelongNumber_add_continuous_eq (hball hx).2.continuousAt]
  obtain ⟨N, g, hg, hset⟩ := isAnalyticGerm_superlevel P (by positivity) hPball q
  refine ⟨N, g, hg, ?_⟩
  filter_upwards [hset, ball_mem_nhds (0 : ComplexModel n) hr] with x hx hxball
  simpa only [mem_ofPred_eq, hν x hxball] using hx

end

end SGPT.Foundations.Analysis.Pending.RawPshLelongAnalyticGerm
