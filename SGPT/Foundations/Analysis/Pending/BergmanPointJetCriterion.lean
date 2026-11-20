import SGPT.Foundations.Analysis.Pending.BergmanInteriorUniformGenerators
import SGPT.Foundations.Analysis.Pending.ActualAnalyticLelongJetLocus
import SGPT.Foundations.Analysis.Pending.QuantitativeRegularizationBergmanGeneratorComparison
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling

set_option autoImplicit false

/-!
# All original weighted functions give the point jets of the same kernel

The literal reader has logarithmic coefficient one for `log ‖z‖`, hence the
squared family logarithm has coefficient two. The point-jet equivalences below
are in positive complex dimension; no finite-reader hypothesis is imposed.

The finite family for a kernel is produced internally at each original interior
point. All tests remain members of the same original weighted unit ball.
Reference: Demailly, *Analytic Methods*, Corollary 14.3, fixed-domain jet equations.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.BergmanPointJetCriterion

open FirstPass FirstPass.NonKahlerLocus BergmanGenerators BergmanSupWeight
  QuantitativeRegularizationBergmanGeneratorComparison
  QuantitativeRegularizationBergmanUnitBallDomination

noncomputable section

/-- Integer thresholds of the literal finite-family reader are exactly the original
low point jets, with a merely bounded real remainder. -/
theorem family_point_jet_iff {m N : ℕ} (f : Fin N → ComplexModel (m + 1) → ℂ)
    (p : ComplexModel (m + 1))
    (hf : ∀ i, ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ (f i) y)
    {c : ℝ} (hc : 0 < c) {b : ComplexModel (m + 1) → ℝ}
    (hb : BoundedRealGermAt b p) (K : ℕ) :
    (ENNReal.ofReal (2 * c * (K : ℝ)) ≤ lelongNumber (n := m + 1)
      (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) p) ↔
      ∀ i j, j < K → iteratedFDeriv ℂ j (f i) p = 0 := by
  let Φ : LocalHolomorphicEquivAt (n := m + 1) p := {
    source := univ
    target := univ
    isOpen_source := isOpen_univ
    isOpen_target := isOpen_univ
    center_mem_source := mem_univ _
    toFun := fun z => z - p
    invFun := fun z => z + p
    toFun_holomorphic := (differentiable_id.sub_const p).differentiableOn
    invFun_holomorphic := (differentiable_id.add_const p).differentiableOn
    mapsTo_toFun := mapsTo_univ _ _
    mapsTo_invFun := mapsTo_univ _ _
    left_inv := fun z _ => sub_add_cancel z p
    right_inv := fun z _ => add_sub_cancel_right z p }
  have hft : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel (m + 1)),
      DifferentiableAt ℂ (fun z => f i (z + p)) z :=
    fun i => eventually_differentiableAt_translate (hf i)
  have hb0 : BoundedRealGermAt b ((0 : ComplexModel (m + 1)) + p) := by
    simpa only [zero_add] using hb
  have hbt : BoundedRealGermAt (fun z => b (z + p)) 0 :=
    hb0.comp_continuousAt (F := fun z : ComplexModel (m + 1) => z + p) (y := 0)
      (continuousAt_id.add continuousAt_const)
  have h := (ActualAnalyticLelongJetLocus.isAnalyticGerm_lelong_superlevel
    (fun i z => f i (z + p)) hft hc hbt K).2.self_of_nhds
  have hreader : lelongNumber (n := m + 1)
      (fun z => (c : EReal) * generatorLog (fun i z => f i (z + p)) z +
        (b (z + p) : EReal)) 0 =
      lelongNumber (n := m + 1)
        (fun y => (c : EReal) * generatorLog f y + (b y : EReal)) p := by
    have hgencomp : generatorLog (fun i z => f i (z + p)) =
        fun z => generatorLog f (z + p) := rfl
    rw [hgencomp]
    simpa only [Φ, sub_self] using
      (LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq Φ (mem_univ p)
        (u := fun y => (c : EReal) * generatorLog f y + (b y : EReal)))
  rw [hreader] at h
  have hjet (i : Fin N) (j : ℕ) :
      iteratedFDeriv ℂ j (fun z => f i (z + p)) 0 = iteratedFDeriv ℂ j (f i) p := by
    simpa only [vadd_set_univ, iteratedFDerivWithin_univ, zero_add] using
      (iteratedFDerivWithin_comp_add_right (𝕜 := ℂ) (s := univ) (f := f i) j p 0)
  simpa only [hjet] using h

/-- At every original interior point, the scaled kernel threshold is equivalent to
vanishing of all low jets of every member of the same original weighted unit ball. -/
theorem kernel_point_jet_iff {m : ℕ}
    [MeasurableSpace (ComplexModel (m + 1))] [BorelSpace (ComplexModel (m + 1))]
    {z p : ComplexModel (m + 1)} {R : ℝ} {w : ComplexModel (m + 1) → ℝ≥0∞}
    (hR : 0 < R) (hw : AEMeasurable w (volume.restrict (ball z (2 * R))))
    {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y)
    (hp : p ∈ ball z (2 * R)) {c : ℝ} (hc : 0 < c) (K : ℕ) :
    (ENNReal.ofReal (2 * c * (K : ℝ)) ≤ lelongNumber (n := m + 1)
      (fun y => (c : EReal) * bergmanLog (ball z (2 * R)) w y) p) ↔
      ∀ f ∈ bergmanUnitBall z R w, ∀ j, j < K → iteratedFDeriv ℂ j f p = 0 := by
  classical
  have hzero : BoundedRealGermAt (fun _ : ComplexModel (m + 1) => (0 : ℝ)) p :=
    boundedRealGermAt_of_continuousAt continuousAt_const
  have hhol {N : ℕ} (g : Fin N → ComplexModel (m + 1) → ℂ)
      (hg : ∀ i, g i ∈ bergmanUnitBall z R w) :
      ∀ i, ∀ᶠ y in 𝓝 p, DifferentiableAt ℂ (g i) y := by
    intro i
    filter_upwards [isOpen_ball.mem_nhds hp] with y hy
    exact (hg i).1.differentiableAt (isOpen_ball.mem_nhds hy)
  constructor
  · intro hν f hf j hj
    let F : Fin 1 → ComplexModel (m + 1) → ℂ := fun _ => f
    have hF : ∀ i, F i ∈ bergmanUnitBall z R w := fun _ => hf
    have hlo : ∀ y, generatorLog F y ≤ bergmanLog (ball z (2 * R)) w y +
        (Real.log ((1 : ℝ) + 1) : EReal) :=
      by simpa only [Nat.cast_one] using
        (generatorLog_le_bergmanLog_add_of_mem_bergmanBall hF)
    have hle : lelongNumber (n := m + 1) (bergmanLog (ball z (2 * R)) w) p ≤
        lelongNumber (n := m + 1) (generatorLog F) p := by
      have h := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := m + 1) (x := p)
        (Filter.Eventually.of_forall hlo)
      rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
        (boundedRealGermAt_of_continuousAt
          (continuousAt_const : ContinuousAt
            (fun _ : ComplexModel (m + 1) => Real.log ((1 : ℝ) + 1)) p))] at h
      exact h
    have hscaled : lelongNumber (n := m + 1)
        (fun y => (c : EReal) * bergmanLog (ball z (2 * R)) w y) p ≤
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog F y) p := by
      rw [ActualLelongPositiveScaling.lelongNumber_smul_eq hc,
        ActualLelongPositiveScaling.lelongNumber_smul_eq hc]
      gcongr
    have hcrit := family_point_jet_iff F p (hhol F hF) hc hzero K
    simp only [EReal.coe_zero, add_zero] at hcrit
    exact hcrit.mp (hν.trans hscaled) (0 : Fin 1) j hj
  · intro hjets
    obtain ⟨N, g, r, A, hr, hg, hdom⟩ :=
      BergmanInteriorUniformGenerators.exists_uniform_generators_at hR hw hδ hlow hp
    let C : ℝ := max A 0 + 1
    have hC : 0 < C := by dsimp only [C]; linarith [le_max_right A 0]
    have hAC : A ≤ C := by dsimp only [C]; linarith [le_max_left A 0]
    have hgball : ∀ i, g i ∈ bergmanBall (ball z (2 * R)) w := hg
    have hdom' : ∀ f ∈ bergmanBall (ball z (2 * R)) w,
        ∀ y ∈ ball p r, ‖f y‖ ^ 2 ≤ C * generatorNormSq g y := by
      intro f hf y hy
      exact (hdom f hf y hy).trans
        (mul_le_mul_of_nonneg_right hAC (generatorNormSq_nonneg g y))
    have hup : ∀ y ∈ ball p r, bergmanLog (ball z (2 * R)) w y ≤
        generatorLog g y + (Real.log C : EReal) :=
      fun y hy => bergmanLog_le_generatorLog_add_of_domination hC hdom' hy
    have hlo : ∀ y ∈ ball p r, generatorLog g y ≤
        bergmanLog (ball z (2 * R)) w y + (Real.log ((N : ℝ) + 1) : EReal) :=
      fun y _ => generatorLog_le_bergmanLog_add_of_mem_bergmanBall hgball y
    have hb : ∀ᶠ y in 𝓝 p, y ∈ ball p r := ball_mem_nhds p hr
    have huv : ∀ᶠ y in 𝓝[≠] p, bergmanLog (ball z (2 * R)) w y ≤
        generatorLog g y + (Real.log C : EReal) :=
      (hb.mono fun y hy => hup y hy).filter_mono nhdsWithin_le_nhds
    have hvu : ∀ᶠ y in 𝓝[≠] p, generatorLog g y ≤
        bergmanLog (ball z (2 * R)) w y + (Real.log ((N : ℝ) + 1) : EReal) :=
      (hb.mono fun y hy => hlo y hy).filter_mono nhdsWithin_le_nhds
    have ha := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := m + 1) huv
    have hb' := KahlerCurrentMax.lelongNumber_le_of_eventually_le (n := m + 1) hvu
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt
        (continuousAt_const : ContinuousAt (fun _ : ComplexModel (m + 1) => Real.log C) p))]
      at ha
    rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq
      (boundedRealGermAt_of_continuousAt
        (continuousAt_const : ContinuousAt
          (fun _ : ComplexModel (m + 1) => Real.log ((N : ℝ) + 1)) p))] at hb'
    have hread := le_antisymm hb' ha
    have hscaled : lelongNumber (n := m + 1)
        (fun y => (c : EReal) * bergmanLog (ball z (2 * R)) w y) p =
        lelongNumber (n := m + 1) (fun y => (c : EReal) * generatorLog g y) p := by
      rw [ActualLelongPositiveScaling.lelongNumber_smul_eq hc,
        ActualLelongPositiveScaling.lelongNumber_smul_eq hc, hread]
    rw [hscaled]
    have hcrit := family_point_jet_iff g p (hhol g hg) hc hzero K
    simp only [EReal.coe_zero, add_zero] at hcrit
    exact hcrit.mpr fun i j hj => hjets (g i) (hg i) j hj

end

end SGPT.Foundations.Analysis.Pending.BergmanPointJetCriterion
