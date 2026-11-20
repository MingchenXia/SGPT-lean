import SGPT.Foundations.Analysis.Pending.BergmanKernelSmooth
import Mathlib.Analysis.SpecialFunctions.Exp
import SGPT.Bergman.SourceBergmanNorms
import SGPT.Bergman.SourceTensorDictionary
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import Mathlib.Analysis.Real.Sqrt

-- PORT-SOURCE bergman-bernstein-markov/LocalExponentialHolomorphicBound.lean; mathematical source retained.

/-! Genuine native local upper estimates for the original BM comparison.
The complete source-facing route precedes Lean in bernstein-markov.tex.
All radii and constants precede EVERY degree and EVERY holomorphic function.
No BM bound, trace limit, finite basis or analytic extension is an input.
The literal all-degree tensor/H0 bridge is supplied by the single final tensor mother. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.BernsteinMarkov

open Set Filter MeasureTheory Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

variable {n : ℕ}

/-- Continuity itself manufactures the SAME closed-ball lower bound and
outer/inner oscillation. None of these output conditions is supplied. -/
theorem exists_local_oscillation_data {U : Set (ComplexModel n)} (hU : IsOpen U)
    {y : ComplexModel n} (hy : y ∈ U) {α g γ : ComplexModel n → ℝ}
    (hα : ContinuousAt α y) (hg : ContinuousAt g y) (hγ : ContinuousAt γ y)
    (hgpos : 0 < g y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r c D : ℝ, 0 < r ∧ 0 < c ∧ 0 < D ∧ closedBall y r ⊆ U ∧
      (∀ x ∈ closedBall y r, c ≤ g x ∧ γ x ≤ D) ∧
      ∀ x ∈ closedBall y r, ∀ z ∈ ball y (r / 2), α x ≤ α z + ε := by
  let c : ℝ := g y / 2
  let D : ℝ := max (γ y) 0 + 1
  have hc : 0 < c := half_pos hgpos
  have hD : 0 < D := by dsimp only [D]; have h := le_max_right (γ y) 0; linarith
  have hcgy : c < g y := half_lt_self hgpos
  have hγD : γ y < D := by dsimp only [D]; have h := le_max_left (γ y) 0; linarith
  have hαnear := (Metric.tendsto_nhds.mp hα) (ε / 2) (half_pos hε)
  have hgnear := hg.eventually (Ioi_mem_nhds hcgy)
  have hγnear := hγ.eventually (Iio_mem_nhds hγD)
  let A : Set (ComplexModel n) := {x | x ∈ U ∧ |α x - α y| < ε / 2 ∧ c < g x ∧ γ x < D}
  have hA : A ∈ 𝓝 y := by
    filter_upwards [hU.mem_nhds hy, hαnear, hgnear, hγnear] with x hxU hxα hxg hxγ
    exact ⟨hxU, by simpa only [Real.dist_eq] using hxα, hxg, hxγ⟩
  obtain ⟨s, hs, hsA⟩ := Metric.mem_nhds_iff.mp hA
  let r : ℝ := s / 2
  have hr : 0 < r := half_pos hs
  have hclosed : closedBall y r ⊆ A :=
    (closedBall_subset_ball (half_lt_self hs)).trans hsA
  refine ⟨r, c, D, hr, hc, hD, fun x hx => (hclosed hx).1,
    fun x hx => ⟨(hclosed hx).2.2.1.le, (hclosed hx).2.2.2.le⟩, ?_⟩
  intro x hx z hz
  have hxα := (hclosed hx).2.1
  have hzclosed : z ∈ closedBall y r :=
    ball_subset_closedBall ((ball_subset_ball (half_le_self hr.le)) hz)
  have hzα := (hclosed hzclosed).2.1
  have hxU := (abs_lt.mp hxα).2
  have hzL := (abs_lt.mp hzα).1
  linarith

/-- The TRUE native holomorphic submean theorem gives a uniform exponential
point bound from natural local geometric data, at ALL nonnegative real
degrees and for ALL genuine holomorphic functions on the original domain. -/
theorem exists_point_bound_of_local_data {U : Set (ComplexModel n)} (hU : IsOpen U)
    {y : ComplexModel n} {α g γ : ComplexModel n → ℝ} {ε r c D : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hD : 0 < D) (hsub : closedBall y r ⊆ U)
    (hlocal : ∀ x ∈ closedBall y r, c ≤ g x ∧ γ x ≤ D)
    (hosc : ∀ x ∈ closedBall y r, ∀ z ∈ ball y (r / 2), α x ≤ α z + ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → ∀ F : ComplexModel n → ℂ,
      DifferentiableOn ℂ F U → ∀ z ∈ ball y (r / 2),
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(q * α z)) * γ z) ≤
        ENNReal.ofReal (C * Real.exp (ε * q)) *
          ∫⁻ x in U, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(q * α x)) * g x) := by
  let V : ℝ := (volume (ball (0 : ComplexModel n) (r / 2))).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos volume (0 : ComplexModel n) (half_pos hr)).ne' measure_ball_lt_top.ne
  have hVcoe : ENNReal.ofReal V = volume (ball (0 : ComplexModel n) (r / 2)) :=
    ENNReal.ofReal_toReal measure_ball_lt_top.ne
  let C : ℝ := D / (c * V)
  have hC : 0 < C := div_pos hD (mul_pos hc hV)
  have hCv : C * (c * V) = D := div_mul_cancel₀ D (mul_ne_zero hc.ne' hV.ne')
  refine ⟨C, hC, fun q hq F hF z hz => ?_⟩
  let δ : ℝ := c * Real.exp (-(q * (α z + ε)))
  let w : ComplexModel n → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-(q * α x)) * g x)
  have hδ : 0 < δ := mul_pos hc (Real.exp_pos _)
  have hlow : ∀ x ∈ closedBall y r, ENNReal.ofReal δ ≤ w x := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-(q * (α z + ε))) ≤ Real.exp (-(q * α x)) :=
      Real.exp_le_exp.mpr (by nlinarith [hosc x hx z hz])
    calc
      δ ≤ c * Real.exp (-(q * α x)) := mul_le_mul_of_nonneg_left he hc.le
      _ ≤ g x * Real.exp (-(q * α x)) :=
        mul_le_mul_of_nonneg_right (hlocal x hx).1 (Real.exp_pos _).le
      _ = Real.exp (-(q * α x)) * g x := mul_comm _ _
  have hm := BergmanKernelSmooth.ofReal_mul_normSq_le hU hF hr hsub hlow hz
  have hI : (∫⁻ x in U, ENNReal.ofReal (‖F x‖ ^ 2) * w x) =
      ∫⁻ x in U, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(q * α x)) * g x) := by
    apply lintegral_congr
    intro x
    dsimp only [w]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  rw [hI] at hm
  have hzclosed : z ∈ closedBall y r :=
    ball_subset_closedBall ((ball_subset_ball (half_le_self hr.le)) hz)
  have hγD := (hlocal z hzclosed).2
  have hecancel : Real.exp (ε * q) * Real.exp (-(q * (α z + ε))) =
      Real.exp (-(q * α z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hcancel : (C * Real.exp (ε * q)) * (δ * V * ‖F z‖ ^ 2) =
      ‖F z‖ ^ 2 * Real.exp (-(q * α z)) * D := by
    calc
      _ = (C * (c * V)) *
          (Real.exp (ε * q) * Real.exp (-(q * (α z + ε)))) * ‖F z‖ ^ 2 := by
        dsimp only [δ]
        ring
      _ = _ := by rw [hCv, hecancel]; ring
  have hscale : 0 ≤ C * Real.exp (ε * q) := (mul_pos hC (Real.exp_pos _)).le
  have hcalc : ENNReal.ofReal (C * Real.exp (ε * q)) *
      (ENNReal.ofReal δ * volume (ball (0 : ComplexModel n) (r / 2)) *
        ENNReal.ofReal (‖F z‖ ^ 2)) =
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(q * α z)) * D) := by
    rw [← hVcoe, ← ENNReal.ofReal_mul hδ.le,
      ← ENNReal.ofReal_mul (mul_nonneg hδ.le hV.le), ← ENNReal.ofReal_mul hscale, hcancel]
  calc
    ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(q * α z)) * γ z) ≤
        ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(q * α z)) * D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hγD
        (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
    _ = ENNReal.ofReal (C * Real.exp (ε * q)) *
        (ENNReal.ofReal δ * volume (ball (0 : ComplexModel n) (r / 2)) *
          ENNReal.ofReal (‖F z‖ ^ 2)) := hcalc.symm
    _ ≤ _ := mul_le_mul' le_rfl hm

/-- The actual missing local BM analytic producer: continuity and genuine
holomorphicity ONLY; one radius and constant precede ALL degrees/functions.
No desired pointwise/L2 comparison, finite integral or extension is input. -/
theorem exists_local_exponential_point_bound {U : Set (ComplexModel n)} (hU : IsOpen U)
    {y : ComplexModel n} (hy : y ∈ U) {α g γ : ComplexModel n → ℝ}
    (hα : ContinuousAt α y) (hg : ContinuousAt g y) (hγ : ContinuousAt γ y)
    (hgpos : 0 < g y) {ε : ℝ} (hε : 0 < ε) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ closedBall y r ⊆ U ∧
      ∀ q : ℝ, 0 ≤ q → ∀ F : ComplexModel n → ℂ, DifferentiableOn ℂ F U →
        ∀ z ∈ ball y (r / 2),
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(q * α z)) * γ z) ≤
            ENNReal.ofReal (C * Real.exp (ε * q)) *
              ∫⁻ x in U, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-(q * α x)) * g x) := by
  obtain ⟨r, c, D, hr, hc, hD, hsub, hlocal, hosc⟩ :=
    exists_local_oscillation_data hU hy hα hg hγ hgpos hε
  obtain ⟨C, hC, hbound⟩ := exists_point_bound_of_local_data hU hr hc hD hsub hlocal hosc
  exact ⟨r, C, hr, hC, hsub, hbound⟩

#print axioms exists_local_oscillation_data
#print axioms exists_point_bound_of_local_data
#print axioms exists_local_exponential_point_bound
end SGPT.Bergman.BernsteinMarkov

-- PORT-SOURCE bergman-bernstein-markov/ProbabilityNormComparison.lean; mathematical source retained.

/-! Original eq:Nkinfcomp, for the actual extended norms and their exact
pole-deleted supremum. No finite-norm or Bernstein--Markov premise. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.BernsteinMarkov
open MeasureTheory Set
open scoped ENNReal

/-- On a probability space, a half-power L2 norm is bounded by the supremum
of half-power densities over any set of full measure, including infinite values. -/
theorem integral_half_rpow_le_poleDeletedSup {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (D : A → ℝ≥0∞) (P : A → Prop)
    (hP : ∀ᵐ x ∂μ, P x) :
    (∫⁻ x, D x ∂μ) ^ (1 / 2 : ℝ) ≤ ⨆ x, ⨆ (_ : P x), D x ^ (1 / 2 : ℝ) := by
  let S : ℝ≥0∞ := ⨆ x, ⨆ (_ : P x), D x ^ (1 / 2 : ℝ)
  have hD : ∀ᵐ x ∂μ, D x ≤ S ^ (2 : ℝ) := by
    filter_upwards [hP] with x hx
    have h : D x ^ (1 / 2 : ℝ) ≤ S := le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have hh := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
      ENNReal.rpow_one] using hh
  have hI : (∫⁻ x, D x ∂μ) ≤ S ^ (2 : ℝ) := by
    calc
      _ ≤ ∫⁻ _, S ^ (2 : ℝ) ∂μ := lintegral_mono_ae hD
      _ = _ := by simp
  have hh := ENNReal.rpow_le_rpow hI (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one] using hh

open Bundle
open scoped Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

omit [IsComplexManifold n X] [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- The WHOLE original probability norm comparison, using the SAME native
holomorphic sections, measure, extended weight, and exact pole-deleted supremum. -/
theorem weightedL2Norm_le_weightedSupNorm {K : Set X} [MeasurableSpace K]
    (k : ℕ) (v : K → EReal) (μ : Measure K) [IsProbabilityMeasure μ]
    (hpoles : μ {x | v x = ⊥} = 0) (s : HolomorphicSections (n := n) V) :
    weightedL2Norm V k v μ s ≤ weightedSupNorm V k v s := by
  apply integral_half_rpow_le_poleDeletedSup
  apply ae_iff.mpr
  simpa only [not_not] using hpoles

#print axioms integral_half_rpow_le_poleDeletedSup
#print axioms weightedL2Norm_le_weightedSupNorm
end SGPT.Bergman.BernsteinMarkov

-- PORT-SOURCE bergman-bernstein-markov/VolumeSectionDensityBound.lean; mathematical source retained.

/-! Actual SAME-metric tensor sections against an actual smooth positive
volume. All constants precede ALL degrees and ALL native holomorphic sections.
The final SourceTensorDictionary mother is imported once; no copied mother bodies. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.BernsteinMarkov
open Bundle Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M]

/-- The actual original real-weight squared density on ALL of X. -/
def realWeightedSectionDensity (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (s : twistedSections L T k) (x : M) : ℝ :=
  ‖s x‖ ^ 2 * Real.exp (-((k : ℝ) * v x))

omit [MeasurableSpace M] [BorelSpace M] in
theorem realWeightedSectionDensity_continuous (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (s : twistedSections L T k) :
    Continuous (realWeightedSectionDensity L T v k s) :=
  ((sectionNormMap (twistedPower L T k).Fiber s).continuous.pow 2).mul
    (Real.continuous_exp.comp (continuous_const.mul v.continuous).neg)

/-- Exact scalar exponential algebra, with the true positive frame factor. -/
theorem exp_weight_frame_factor (a b : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.exp (-((k : ℝ) * (b - Real.log a))) =
      a ^ k * Real.exp (-((k : ℝ) * b)) := by
  have he : -((k : ℝ) * (b - Real.log a)) = (k : ℝ) * Real.log a + -((k : ℝ) * b) := by ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_log ha]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Exact all-degree weighted readback in original atlas frames, rather than
a supplied density/BM comparison. -/
theorem realWeightedSectionDensity_frame (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (e : AtlasFrame L) (f : AtlasFrame T)
    (k : ℕ) (s : twistedSections L T k) {x : M}
    (hx : x ∈ e.val.baseSet) (hy : x ∈ f.val.baseSet) :
    realWeightedSectionDensity L T v k s x =
      ‖((twistedPowerAtlasFrame e f k).val ⟨x, s x⟩).2‖ ^ 2 *
        Real.exp (-((k : ℝ) * (v x - Real.log (‖e.val.symm x 1‖ ^ 2)))) *
          ‖f.val.symm x 1‖ ^ 2 := by
  let := e.property
  have ha : 0 < ‖e.val.symm x 1‖ ^ 2 :=
    sq_pos_of_pos (frameNorm_pos L.Fiber e.val hx)
  rw [realWeightedSectionDensity, twistedSection_norm_sq_frame e f k s hx hy,
    exp_weight_frame_factor _ _ ha k]
  ring

/-- The genuine local geometric producer. Smooth positivity supplies the
actual chart density and transport. The same open neighborhood and C are
chosen BEFORE EVERY original tensor degree and EVERY full H0 section. -/
theorem exists_local_section_density_bound (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∀ s : twistedSections L T k, ∀ y ∈ W,
        ENNReal.ofReal (realWeightedSectionDensity L T v k s y) ≤
          ENNReal.ofReal (C * Real.exp (ε * k)) *
            ∫⁻ z, ENNReal.ofReal (realWeightedSectionDensity L T v k s z) ∂μ := by
  let c := complexChartAt (n := n) x
  let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x, inferInstance⟩
  let f : AtlasFrame T := ⟨trivializationAt ℂ T.Fiber x, inferInstance⟩
  let := e.property
  let := f.property
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ L.Fiber x
  have hf : x ∈ f.val.baseSet := mem_baseSet_trivializationAt ℂ T.Fiber x
  let y₀ := c.val x
  have hy₀ : y₀ ∈ c.val.target := c.val.map_source hx
  have hinv : c.val.symm y₀ = x := c.val.left_inv hx
  let D := c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ f.val.baseSet)
  have hD : IsOpen D := c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter f.val.open_baseSet)
  have hyD : y₀ ∈ D := ⟨hy₀, by
    change c.val.symm y₀ ∈ e.val.baseSet ∩ f.val.baseSet
    rw [hinv]
    exact ⟨he, hf⟩⟩
  obtain ⟨R₀, hR₀, hR₀D⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hyD)
  let R := R₀ / 2
  have hR : 0 < R := half_pos hR₀
  have hRD : closedBall y₀ R ⊆ D :=
    (closedBall_subset_ball (half_lt_self hR₀)).trans hR₀D
  obtain ⟨ρ, hρsmooth, hρpos, hmap⟩ := hμ c
  let a : ComplexModel n → ℝ := fun z => ‖e.val.symm (c.val.symm z) 1‖ ^ 2
  let γ : ComplexModel n → ℝ := fun z => ‖f.val.symm (c.val.symm z) 1‖ ^ 2
  let α : ComplexModel n → ℝ := fun z => v (c.val.symm z) - Real.log (a z)
  let g : ComplexModel n → ℝ := fun z => γ z * ρ z
  have hccont : ContinuousAt c.val.symm y₀ :=
    c.val.continuousOn_symm.continuousAt (c.val.open_target.mem_nhds hy₀)
  have he₀ : c.val.symm y₀ ∈ e.val.baseSet := by rw [hinv]; exact he
  have hf₀ : c.val.symm y₀ ∈ f.val.baseSet := by rw [hinv]; exact hf
  have hacont : ContinuousAt a y₀ :=
    (((frameNorm_continuousOn L.Fiber e.val).continuousAt
      (e.val.open_baseSet.mem_nhds he₀)).comp hccont).pow 2
  have hγcont : ContinuousAt γ y₀ :=
    (((frameNorm_continuousOn T.Fiber f.val).continuousAt
      (f.val.open_baseSet.mem_nhds hf₀)).comp hccont).pow 2
  have hapos : 0 < a y₀ := sq_pos_of_pos (frameNorm_pos L.Fiber e.val he₀)
  have hγpos : 0 < γ y₀ := sq_pos_of_pos (frameNorm_pos T.Fiber f.val hf₀)
  have hαcont : ContinuousAt α y₀ :=
    (v.continuous.continuousAt.comp hccont).sub (hacont.log hapos.ne')
  have hgcont : ContinuousAt g y₀ := hγcont.mul
    (hρsmooth.continuousOn.continuousAt (c.val.open_target.mem_nhds hy₀))
  have hgpos : 0 < g y₀ := mul_pos hγpos (hρpos _ hy₀)
  obtain ⟨r, C, hr, hC, hrsub, hbound⟩ := exists_local_exponential_point_bound
    isOpen_ball (mem_ball_self hR) hαcont hgcont hγcont hgpos hε
  let W := c.val.source ∩ c.val ⁻¹' ball y₀ (r / 2)
  have hW : IsOpen W := c.val.continuousOn.isOpen_inter_preimage c.val.open_source isOpen_ball
  have hxW : x ∈ W := ⟨hx, mem_ball_self (half_pos hr)⟩
  refine ⟨W, hW, hxW, C, hC, fun k s y hy => ?_⟩
  let t := twistedPowerAtlasFrame e f k
  let := t.property
  let F := sectionCoefficient (twistedPower L T k).Fiber t.val s ∘ c.val.symm
  have hF : DifferentiableOn ℂ F (ball y₀ R) := by
    apply (sectionCoefficient_chart_differentiable (twistedPower L T k).Fiber t.val x s).mono
    intro z hz
    have hzD := hRD (ball_subset_closedBall hz)
    exact ⟨hzD.1, twistedPowerAtlasFrame_mem e f hzD.2.1 hzD.2.2 k⟩
  have hpoint := hbound (k : ℝ) (Nat.cast_nonneg _) F hF (c.val y) hy.2
  have hyD : c.val y ∈ D := hRD (ball_subset_closedBall
    (hrsub (ball_subset_closedBall ((ball_subset_ball (half_le_self hr.le)) hy.2))))
  have hye : y ∈ e.val.baseSet := by
    have h := hyD.2.1
    change c.val.symm (c.val y) ∈ _ at h
    rwa [c.val.left_inv hy.1] at h
  have hyf : y ∈ f.val.baseSet := by
    have h := hyD.2.2
    change c.val.symm (c.val y) ∈ _ at h
    rwa [c.val.left_inv hy.1] at h
  have hread : ‖F (c.val y)‖ ^ 2 * Real.exp (-((k : ℝ) * α (c.val y))) * γ (c.val y) =
      realWeightedSectionDensity L T v k s y := by
    dsimp only [F, Function.comp_apply, α, a, γ, sectionCoefficient]
    rw [c.val.left_inv hy.1]
    exact (realWeightedSectionDensity_frame L T v e f k s hye hyf).symm
  rw [hread] at hpoint
  have hI : (∫⁻ z in ball y₀ R,
      ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-((k : ℝ) * α z)) * g z)) ≤
      ∫⁻ z, ENNReal.ofReal (realWeightedSectionDensity L T v k s z) ∂μ := by
    calc
      _ ≤ ∫⁻ z in closedBall y₀ R,
          ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-((k : ℝ) * α z)) * g z) :=
        lintegral_mono_set ball_subset_closedBall
      _ = ∫⁻ z in closedBall y₀ R, ENNReal.ofReal (ρ z) *
          ENNReal.ofReal (realWeightedSectionDensity L T v k s (c.val.symm z)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem isClosed_closedBall.measurableSet] with z hz
        have hzD := hRD hz
        rw [realWeightedSectionDensity_frame L T v e f k s hzD.2.1 hzD.2.2]
        dsimp only [g, F, Function.comp_apply, α, a, γ, sectionCoefficient]
        rw [← ENNReal.ofReal_mul (hρpos _ hzD.1).le]
        congr 1
        ring
      _ = ∫⁻ z in c.val.source ∩ c.val ⁻¹' closedBall y₀ R,
          ENNReal.ofReal (realWeightedSectionDensity L T v k s z) ∂μ := by
        exact (setLIntegral_source_inter_preimage c hρsmooth.continuousOn hmap
          (isCompact_closedBall _ _) (fun z hz => (hRD hz).1)
          (ENNReal.continuous_ofReal.comp
            (realWeightedSectionDensity_continuous L T v k s)).measurable).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  exact hpoint.trans (mul_le_mul' le_rfl hI)

#print axioms realWeightedSectionDensity_continuous
#print axioms exp_weight_frame_factor
#print axioms realWeightedSectionDensity_frame
#print axioms exists_local_section_density_bound
end SGPT.Bergman.BernsteinMarkov

-- PORT-SOURCE bergman-bernstein-markov/GlobalVolumeBernsteinMarkov.lean; mathematical source retained.

/-! The original BM assertion for K=X, actual original tensor sections and
actual smooth positive probability volumes. The constant is chosen before
ALL degrees and ALL sections. No BM/trace/point-estimate certificate is input. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.BernsteinMarkov
open Bundle Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.QuantizationDraft

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Compactness applied to the actual geometric local estimates, with one
finite constant preceding every degree and every full original H0 section. -/
theorem exists_global_section_density_bound (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, ∀ s : twistedSections L T k, ∀ x : M,
      ENNReal.ofReal (realWeightedSectionDensity L T v k s x) ≤
        ENNReal.ofReal (A * Real.exp (ε * k)) *
          ∫⁻ y, ENNReal.ofReal (realWeightedSectionDensity L T v k s y) ∂μ := by
  classical
  have hlocal := fun x => exists_local_section_density_bound L T v μ hμ x hε
  choose W hW hxW C hC hb using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  let A : ℝ := 1 + ∑ x ∈ t, C x
  have hsum : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  have hA : 0 < A := by dsimp only [A]; linarith
  refine ⟨A, hA, fun k s x => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hCA : C y ≤ A := by
    have hle := Finset.single_le_sum (fun z (_ : z ∈ t) => (hC z).le) hyt
    dsimp only [A]
    linarith
  exact (hb y k s x hxy).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le)) le_rfl)

/-- The source K=X weight is read on the SAME actual subtype, with no poles. -/
def univRealWeight (v : C(M, ℝ)) : ↥(Set.univ : Set M) → EReal :=
  fun x => (v x.val : EReal)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Exact source-density/global-real-density dictionary at the original point. -/
theorem weightedSectionDensity_univ (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (s : twistedSections L T k) (x : ↥(Set.univ : Set M)) :
    weightedSectionDensity (twistedPower L T k).Fiber k (univRealWeight v) s x =
      ENNReal.ofReal (realWeightedSectionDensity L T v k s x.val) := by
  rw [weightedSectionDensity, univRealWeight, multiplierWeight_coe,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  rfl

omit [CompactSpace M] [BorelSpace M] in
/-- The lower integral is on the SAME original K subtype, comapped from the
actual smooth volume; the equality is actual chart-free measure transport. -/
theorem weightedL2Norm_univ (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (μ : Measure M) (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
      (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s =
      (∫⁻ x, ENNReal.ofReal (realWeightedSectionDensity L T v k s x) ∂μ) ^ (1 / 2 : ℝ) := by
  unfold weightedL2Norm
  simp_rw [weightedSectionDensity_univ]
  have hi := lintegral_subtype_comap (μ := μ) MeasurableSet.univ
    (fun x => ENNReal.ofReal (realWeightedSectionDensity L T v k s x))
  simpa only [Measure.restrict_univ] using congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) hi

omit [BorelSpace M] in
/-- Genuine finite norms, manufactured from continuity and compactness on the
actual manifold, with only the original finite measure hypothesis. -/
theorem weightedL2Norm_univ_ne_top (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (k : ℕ) (μ : Measure M) [IsFiniteMeasure μ]
    (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
      (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s ≠ ⊤ := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (realWeightedSectionDensity_continuous L T v k s).continuousOn
  have hbound : (∫⁻ x, ENNReal.ofReal (realWeightedSectionDensity L T v k s x) ∂μ) ≤
      ENNReal.ofReal B * μ Set.univ := by
    calc
      _ ≤ ∫⁻ _, ENNReal.ofReal B ∂μ := lintegral_mono (fun x =>
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB x (mem_univ x))))
      _ = _ := lintegral_const _
  rw [weightedL2Norm_univ]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hbound)

/-- Exact positive square-root exponential readback, also at zero degree. -/
theorem half_rpow_exponential (A ε : ℝ) (hA : 0 ≤ A) (k : ℕ) :
    ENNReal.ofReal (A * Real.exp ((2 * ε) * k)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt A * Real.exp (ε * k)) := by
  have hsq : (Real.sqrt A * Real.exp (ε * k)) ^ 2 = A * Real.exp ((2 * ε) * k) := by
    rw [mul_pow, Real.sq_sqrt hA, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [← hsq, ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le),
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

/-- WHOLE original smooth-volume Bernstein--Markov estimate, retaining the
exact original section norms, the SAME h^k tensor h_T metric, and ONE C before
ALL degrees and ALL sections. It even includes degree zero and continuous v. -/
theorem smoothPositiveVolume_bernsteinMarkov (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) (hμ : IsSmoothPositiveVolume (n := n) μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
            (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s := by
  obtain ⟨A, hA, hb⟩ := exists_global_section_density_bound L T v μ hμ
    (show 0 < 2 * ε from mul_pos (by norm_num) hε)
  refine ⟨Real.sqrt A, Real.sqrt_pos_of_pos hA, fun k s => ?_⟩
  unfold weightedSupNorm
  apply iSup_le
  intro x
  apply iSup_le
  intro _
  rw [weightedSectionDensity_univ, weightedL2Norm_univ]
  have hh := ENNReal.rpow_le_rpow (hb k s x.val) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), half_rpow_exponential A ε hA.le k] at hh
  exact hh

/-- Original probability-measure BM definition on K=X, as an output property
of the actual original norms, without a section family, basis or certificates. -/
def IsVolumeBernsteinMarkov (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 0 < k → ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s ≤
        ENNReal.ofReal (C * Real.exp (ε * k)) *
          weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
            (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s

/-- Full source-facing consumer: original probability smooth volume is BM,
both actual norms are finite, and the original reverse probability comparison
holds for EVERY original degree and EVERY original full H0 section. -/
theorem whole_volume_bernstein_markov (L T : HermitianHolomorphicLineBundle n M)
    (v : C(M, ℝ)) (μ : Measure M) [IsProbabilityMeasure μ]
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    IsVolumeBernsteinMarkov L T v μ ∧ ∀ k : ℕ, ∀ s : twistedSections L T k,
      weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s ≠ ⊤ ∧
      weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
        (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s ≠ ⊤ ∧
      weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight v)
        (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) s ≤
      weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s := by
  have hp : IsVolumeBernsteinMarkov L T v μ := by
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨C, hC, hb⟩ := smoothPositiveVolume_bernsteinMarkov L T v μ hμ hε
    exact ⟨C, hC, fun k _ s => hb k s⟩
  refine ⟨hp, fun k s => ?_⟩
  have hfin := weightedL2Norm_univ_ne_top L T v k μ s
  obtain ⟨C, _, hb⟩ := smoothPositiveVolume_bernsteinMarkov L T v μ hμ (by norm_num : (0 : ℝ) < 1)
  have hsup : weightedSupNorm (twistedPower L T k).Fiber k (univRealWeight v) s ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) (hb k s)
  let : IsProbabilityMeasure (μ.comap (Subtype.val : ↥(Set.univ : Set M) → M)) :=
    (MeasurableEmbedding.subtype_coe MeasurableSet.univ).isProbabilityMeasure_comap
      (ae_of_all _ (fun x => ⟨⟨x, mem_univ x⟩, rfl⟩))
  refine ⟨hsup, hfin, weightedL2Norm_le_weightedSupNorm (twistedPower L T k).Fiber
    k (univRealWeight v) _ ?_ s⟩
  simp only [univRealWeight, EReal.coe_ne_bot, Set.ofPred_false, measure_empty]

#print axioms exists_global_section_density_bound
#print axioms weightedSectionDensity_univ
#print axioms weightedL2Norm_univ
#print axioms weightedL2Norm_univ_ne_top
#print axioms half_rpow_exponential
#print axioms smoothPositiveVolume_bernsteinMarkov
#print axioms whole_volume_bernstein_markov
end SGPT.Bergman.BernsteinMarkov
