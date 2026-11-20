import SGPT.Foundations.Analysis.Pending.ActualFiniteGeneratorLelongNormalization
import SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import Mathlib.LinearAlgebra.Multilinear.Basis

set_option autoImplicit false

/-! # Actual analytic superlevel germs of a finite logarithmic family

The least original point jet and the literal squared-logarithm coefficient
produce the finite jet locus internally, including the identically zero
family. Translation and fixed multilinear coordinates give genuine finite
holomorphic equations. This is not a global Siu decomposition.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongJetLocus

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

private def jetEvaluation {n k : ℕ} (v : Fin k → ComplexModel n) :
    (ComplexModel n [×k]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => F v
      map_add' := fun F G => by simp
      map_smul' := fun a F => by simp }
    (∏ i, ‖v i‖) (fun F => by
      dsimp
      simpa only [mul_comm] using F.le_opNorm v)

private theorem translated_jet {n k : ℕ} (f : ComplexModel n → ℂ)
    (x : ComplexModel n) :
    iteratedFDeriv ℂ k (fun z => f (z + x)) 0 = iteratedFDeriv ℂ k f x := by
  simpa only [vadd_set_univ, iteratedFDerivWithin_univ, zero_add] using
    (iteratedFDerivWithin_comp_add_right (𝕜 := ℂ) (s := univ) (f := f) k x 0)

private theorem translated_reader {n : ℕ} (u : ComplexModel n → EReal)
    (x : ComplexModel n) :
    lelongNumber (n := n) (fun z => u (z + x)) 0 = lelongNumber (n := n) u x := by
  let Φ : LocalHolomorphicEquivAt (n := n) x := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z - x
    invFun := fun z => z + x
    toFun_holomorphic := (differentiable_id.sub_const x).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const x).differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => sub_add_cancel z x
    right_inv := fun z _ => add_sub_cancel_right z x }
  simpa only [Φ, sub_self] using
    (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ (mem_univ x)
      (u := u))

private theorem center_superlevel_iff {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) z)
    {c : ℝ} (hc : 0 < c) {b : ComplexModel (m + 1) → ℝ}
    (hb : BoundedRealGermAt b 0) (K : ℕ) :
    (ENNReal.ofReal (2 * c * (K : ℝ)) ≤
      lelongNumber (n := m + 1) (fun z => (c : EReal) * generatorLog f z + (b z : EReal)) 0) ↔
      ∀ i k, k < K → iteratedFDeriv ℂ k (f i) 0 = 0 := by
  classical
  by_cases hne : ∃ i, ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0
  · obtain ⟨a, hlow, ⟨i, hi⟩, hν⟩ :=
      ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization f hf hne
    rw [hν c hc b hb, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    constructor
    · intro h j k hk
      have hKa : K ≤ a := by
        by_contra hnot
        have hlt : (a : ℝ) < (K : ℝ) := by exact_mod_cast Nat.lt_of_not_ge hnot
        nlinarith
      exact hlow j k (hk.trans_le hKa)
    · intro h
      have hKa : K ≤ a := by
        by_contra hnot
        exact hi (h i a (Nat.lt_of_not_ge hnot))
      have hcast : (K : ℝ) ≤ (a : ℝ) := by exact_mod_cast hKa
      exact mul_le_mul_of_nonneg_left hcast (by positivity)
  · have hzero : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), f i z = 0 := by
      simpa only [not_exists, not_not] using hne
    have hbot : ∀ᶠ z in 𝓝[≠] (0 : ComplexModel (m + 1)),
        (c : EReal) * generatorLog f z + (b z : EReal) = ⊥ := by
      have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)), ∀ i, f i z = 0 :=
        eventually_all.mpr hzero
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds hall] with z hz
      rw [(generatorLog_eq_bot_iff f z).mpr hz, EReal.coe_mul_bot_of_pos hc,
        EReal.bot_add]
    rw [LelongNumberChartTransport.lelongNumber_eq_top_of_eventually_bot hbot]
    simp only [le_top, true_iff]
    intro i k _
    have hgerm : f i =ᶠ[𝓝 (0 : ComplexModel (m + 1))] fun _ => 0 := hzero i
    have hjet := (hgerm.iteratedFDeriv ℂ k).eq_of_nhds
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using hjet

/-- All low jets are genuine finite holomorphic equations for the actual
logarithmic superlevel, with the literal neighborhood equivalence produced
from the original family and the merely bounded remainder. -/
theorem isAnalyticGerm_lelong_superlevel {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) x)
    {c : ℝ} (hc : 0 < c) {b : ComplexModel (m + 1) → ℝ}
    (hb : BoundedRealGermAt b 0) (K : ℕ) :
    AnalyticGermDecomposition.IsAnalyticGerm
      {x : ComplexModel (m + 1) | ENNReal.ofReal (2 * c * (K : ℝ)) ≤
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x} ∧
    ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)),
      (ENNReal.ofReal (2 * c * (K : ℝ)) ≤
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x) ↔
        ∀ i k, k < K → iteratedFDeriv ℂ k (f i) x = 0 := by
  classical
  obtain ⟨B, hB, hbound⟩ := hb
  obtain ⟨U, hprops, hU, h0⟩ :=
    eventually_nhds_iff.mp ((eventually_all.mpr hf).and hbound)
  have hU0 : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), x ∈ U := hU.mem_nhds h0
  have hhol (i : Fin N) : AnalyticOnNhd ℂ (f i) U :=
    HolomorphicAnalytic.analyticOnNhd_of_differentiableOn hU
      (fun x hx => (hprops x hx).1 i |>.differentiableWithinAt)
  have hcriterion : ∀ x ∈ U,
      (ENNReal.ofReal (2 * c * (K : ℝ)) ≤
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x) ↔
        ∀ i k, k < K → iteratedFDeriv ℂ k (f i) x = 0 := by
    intro x hx
    have hfx : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
        DifferentiableAt ℂ (fun z => f i (z + x)) z := by
      intro i
      have hcont : Tendsto (fun z : ComplexModel (m + 1) => z + x) (𝓝 0) (𝓝 x) := by
        have h : ContinuousAt (fun z : ComplexModel (m + 1) => z + x) 0 :=
          continuousAt_id.add continuousAt_const
        simpa only [zero_add] using h.tendsto
      filter_upwards [hcont.eventually (hU.mem_nhds hx)] with z hz
      exact ((hprops (z + x) hz).1 i).comp z (differentiableAt_id.add_const x)
    have hUx : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
    have hbx : BoundedRealGermAt b ((0 : ComplexModel (m + 1)) + x) := by
      simpa only [zero_add] using
        (show BoundedRealGermAt b x from ⟨B, hB, hUx.mono fun y hy => (hprops y hy).2⟩)
    have hbt : BoundedRealGermAt (fun z => b (z + x)) 0 := by
      exact hbx.comp_continuousAt (F := fun z : ComplexModel (m + 1) => z + x) (y := 0)
        (show ContinuousAt (fun z : ComplexModel (m + 1) => z + x) 0 from
          continuousAt_id.add continuousAt_const)
    have h := center_superlevel_iff (fun i z => f i (z + x)) hfx hc hbt K
    have heq : generatorLog (fun i z => f i (z + x)) =
        fun z => generatorLog f (z + x) := rfl
    rw [heq] at h
    have hreader := translated_reader
      (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) x
    rw [hreader] at h
    simpa only [translated_jet] using h
  have hcriterion0 := hU0.mono fun x hx => hcriterion x hx
  refine ⟨?_, hcriterion0⟩
  let e := (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).toBasis
  let I := Fin N × (Σ k : Fin K, Fin k.val → Fin (m + 1))
  let g : I → ComplexModel (m + 1) → ℂ := fun s x =>
    iteratedFDeriv ℂ s.2.1.val (f s.1) x (fun j => e (s.2.2 j))
  apply AnalyticGermDecomposition.isAnalyticGerm_of_finite g
  · intro s
    filter_upwards [hU0] with x hx
    let E := jetEvaluation (fun j => e (s.2.2 j))
    have ha := E.comp_analyticOnNhd ((hhol s.1).iteratedFDeriv s.2.1.val)
    exact (ha x hx).differentiableAt
  · filter_upwards [hU0] with x hx
    change (_ ≤ _) ↔ ∀ s, g s x = 0
    rw [hcriterion x hx]
    constructor
    · intro h s
      dsimp only [g]
      rw [h s.1 s.2.1.val s.2.1.isLt]
      rfl
    · intro h i k hk
      apply ContinuousMultilinearMap.toMultilinearMap_injective
      apply Module.Basis.ext_multilinear (fun _ : Fin k => e)
      intro v
      change iteratedFDeriv ℂ k (f i) x (fun j => e (v j)) = 0
      exact h (i, ⟨⟨k, hk⟩, v⟩)

end

end SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongJetLocus
