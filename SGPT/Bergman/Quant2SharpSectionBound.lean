import SGPT.Bergman.Quant2SharpSubmean
import SGPT.Bergman.SourceSmoothWeightedBergmanBound
import SGPT.Bergman.Quant2SharpLocalCalculus
import SGPT.Bergman.SourceSmoothWeightedPolynomialBound
import SGPT.Bergman.SourcePartialBergmanDensity

/-!
# Quant2SharpSectionBound

Pointwise bounds of weighted holomorphic sections by rescaled local Gaussian integrals (local holomorphic Morse inequality).

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalSectionIntegral.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
/-- The SAME original chart density is chosen before every degree, section,
spectral map and radius. Actual original global weighted-L² admissibility,
the true rescaling Jacobian and exact chart pushforward internally give the
unit local integral. No local energy/measure equality is supplied as a premise.
The ordinary image-in-chart condition is discharged by the original Taylor
rescaling domain producer in the final Berman consumer. -/
theorem sourceSharp_original_chart_rescaled_unit_integral
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ))
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) (c : ComplexChart n X) :
    ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ c.val.target ∧
      (∀ z ∈ c.val.target, 0 < ρ z) ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      ∀ (k : ℕ) (_hk : 0 < k) (s : twistedSections L T k),
      weightedL2Norm (twistedPower L T k).Fiber k
        (wholeWeightedSubset (n := n) v).erealWeight
        (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) s ≤ 1 →
      ∀ (a : ComplexModel n) (S : ComplexModel n →ₗ[ℂ] ComplexModel n),
      Complex.normSq (LinearMap.det S) = 1 → ∀ R : ℝ,
      (fun z => a + sourceRescaleRadius k • S z) ''
        ((fun w : Fin n → ℂ => toLp 2 w) '' closedBall 0 R) ⊆ c.val.target →
      (∫⁻ w in closedBall (0 : Fin n → ℂ) R,
        ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          (ENNReal.ofReal (ρ (a + sourceRescaleRadius k • S (toLp 2 w))) *
          ENNReal.ofReal (realWeightedSectionDensity L T v k s
            (c.val.symm (a + sourceRescaleRadius k • S (toLp 2 w)))))) ≤ 1 := by
  obtain ⟨ρ,hρsmooth,hρpos,hmap⟩ := hμ c
  refine ⟨ρ,hρsmooth,hρpos,hmap,fun k hk s hs a S hS R hdom => ?_⟩
  let T0 := fun w : Fin n → ℂ => toLp 2 w
  let A0 := fun z : ComplexModel n => a + sourceRescaleRadius k • S z
  let K := A0 '' (T0 '' closedBall (0 : Fin n → ℂ) R)
  have hT0 : Continuous T0 := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.continuous
  have hA0 : Continuous A0 := continuous_const.add (S.continuous_of_finiteDimensional.const_smul (sourceRescaleRadius k))
  have hK : IsCompact K := ((isCompact_closedBall (0 : Fin n → ℂ) R).image hT0).image hA0
  let F0 := fun x : X => ENNReal.ofReal (realWeightedSectionDensity L T v k s x)
  have hF0 : Measurable F0 := (ENNReal.continuous_ofReal.comp
    (realWeightedSectionDensity_continuous L T v k s)).measurable
  have hTransport := setLIntegral_source_inter_preimage c hρsmooth.continuousOn hmap hK hdom hF0
  have hLocal : (∫⁻ z in K, ENNReal.ofReal (ρ z) * F0 (c.val.symm z)) ≤ 1 := by
    calc
      _ = ∫⁻ x in c.val.source ∩ c.val ⁻¹' K, F0 x ∂μ := hTransport.symm
      _ ≤ ∫⁻ x, F0 x ∂μ := setLIntegral_le_lintegral _ _
      _ ≤ 1 := integral_realWeightedSectionDensity_le_one_of_admissible L T v μ k s hs
  have hImage := sourceSharp_rescaled_polydisc_lintegral hk a S hS R
    (fun z => ENNReal.ofReal (ρ z) * F0 (c.val.symm z))
  rw [← hImage]
  exact hLocal
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpSubmeanLIntegral.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Real Metric Set MeasureTheory
open scoped ENNReal
/-- Nonnegative-integral form of the actual finite-polydisc submean, for
composition with the original section's global weighted unit integral.
Integrability is manufactured from original holomorphy, for every signed
spectrum; no energy certificate is supplied. -/
theorem sourceSharp_weighted_polydisc_submean_lintegral {n : ℕ} {R : ℝ} (hR : 0 < R)
    {F : (Fin n → ℂ) → ℂ} (hF : DiffContOnCl ℂ F (ball 0 R)) (d : Fin n → ℝ) :
    ENNReal.ofReal (‖F 0‖ ^ 2) *
      ENNReal.ofReal (∫ z in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d z) ≤
      ∫⁻ z in ball (0 : Fin n → ℂ) R,
        ENNReal.ofReal (‖F z‖ ^ 2 * sourceDiagonalGaussian d z) := by
  have hi := sourceSharp_polydisc_weighted_integrable hR hF d
  rw [sourceSharp_pi_disk_measure hR] at hi
  have hpos : ∀ z : Fin n → ℂ, 0 ≤ ‖F z‖ ^ 2 * sourceDiagonalGaussian d z := by
    intro z
    exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hpos),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (sourceSharp_weighted_polydisc_submean hR hF d)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpCompactRescaling.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp Set MeasureTheory Metric Filter
open scoped Topology ContDiff
/-- A fixed actual spectral image of the closed coordinate polydisc has an
internally produced bound BEFORE all degrees and all original sections. -/
theorem sourceSharp_spectral_polydisc_bound {n : ℕ}
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ closedBall (0 : Fin n → ℂ) R,
      S (toLp 2 w) ∈ closedBall (0 : EuclideanSpace ℂ (Fin n)) B := by
  have hT : Continuous (fun w : Fin n → ℂ => toLp 2 w) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.continuous
  have hS := S.continuous_of_finiteDimensional.comp hT
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Fin n → ℂ) R).exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  simpa only [mem_closedBall, dist_zero_right, Function.comp_apply] using (hC w hw).trans (le_max_left _ _)

/-- The accepted original small-Taylor producer transports to the actual
spectral coordinate polydisc, retaining uniformity and the SAME original
open domain. No rescaled-domain or exponent approximation output is assumed. -/
theorem sourceSharp_rescaled_exponent_polydisc {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℂ (Fin n) → ℝ} (hp : ContDiffOn ℝ 2 p U)
    {q : EuclideanSpace ℂ (Fin n) → ℝ} {a : EuclideanSpace ℂ (Fin n)}
    (ha : a ∈ U) (hq : ContinuousAt q a)
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (R : ℝ) :
    TendstoUniformlyOn
      (fun (k : ℕ) (w : Fin n → ℂ) => sourceRescaledPhysicalExponent p q a k (S (toLp 2 w)))
      (fun w => hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (S (toLp 2 w)))
      atTop (closedBall 0 R) ∧
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ closedBall (0 : Fin n → ℂ) R,
      a + sourceRescaleRadius k • S (toLp 2 w) ∈ U := by
  obtain ⟨B,hB,hbound⟩ := sourceSharp_spectral_polydisc_bound S R
  obtain ⟨hu,hd⟩ := sourceActual_rescaled_exponent_uniform hU hp ha hq hB
  refine ⟨(hu.comp (fun w : Fin n → ℂ => S (toLp 2 w))).mono hbound, ?_⟩
  filter_upwards [hd] with k hk w hw
  exact hk _ (hbound w hw)

/-- Original chart density continuity at the SAME center gives a
section-independent uniform rescaled density limit on every fixed compact
spectral set. This is later applied to the actual density produced by hμ. -/
theorem sourceSharp_rescaled_density_compact {n : ℕ}
    {ρ : EuclideanSpace ℂ (Fin n) → ℝ} {a : EuclideanSpace ℂ (Fin n)}
    (hρ : ContinuousAt ρ a) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K) :
    TendstoUniformlyOn (fun k z => ρ (a + sourceRescaleRadius k • z))
      (fun _ => ρ a) atTop K := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hρδ⟩ := Metric.continuousAt_iff.mp hρ ε hε
  have ht : Tendsto (fun k => sourceRescaleRadius k * B) atTop (𝓝 0) := by
    simpa only [zero_mul] using sourceRescaleRadius_tendsto.mul_const B
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with k hk z hz
  have hb : ‖z‖ ≤ B := (hC z hz).trans (le_max_left _ _)
  have hdist : dist (a + sourceRescaleRadius k • z) a < δ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sourceRescaleRadius_nonneg k)]
    exact (mul_le_mul_of_nonneg_left hb (sourceRescaleRadius_nonneg k)).trans_lt hk
  simpa only [dist_comm] using hρδ hdist
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpSpectralWeightLower.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp Set MeasureTheory Metric Filter
open scoped Topology ContDiff BigOperators
/-- The original fixed smooth weights and actual continuous chart density
manufacture the uniform Gaussian lower comparison BEFORE any section is
selected. The spectral equality is the exact existing Hessian readback,
not a sharp estimate. No global strict positivity or eigenvalue sign enters. -/
theorem sourceSharp_rescaled_spectral_weight_lower {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {p : EuclideanSpace ℂ (Fin n) → ℝ} (hp : ContDiffOn ℝ 2 p U)
    {q ρ : EuclideanSpace ℂ (Fin n) → ℝ} {a : EuclideanSpace ℂ (Fin n)}
    (ha : a ∈ U) (hq : ContinuousAt q a) (hρ : ContinuousAt ρ a)
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (d : Fin n → ℝ)
    (hQ : ∀ z : EuclideanSpace ℂ (Fin n),
      hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (S z) = -∑ j, d j * ‖z j‖ ^ 2)
    (R ε : ℝ) (hε : 0 < ε) (hερ : ε < ρ a) :
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ closedBall (0 : Fin n → ℂ) R,
      (ρ a - ε) * Real.exp (-ε) * sourceDiagonalGaussian d w ≤
        ρ (a + sourceRescaleRadius k • S (toLp 2 w)) *
          Real.exp (sourceRescaledPhysicalExponent p q a k (S (toLp 2 w))) := by
  obtain ⟨hu,_⟩ := sourceSharp_rescaled_exponent_polydisc hU hp ha hq S R
  obtain ⟨B,hB,hbound⟩ := sourceSharp_spectral_polydisc_bound S R
  have hρu := sourceSharp_rescaled_density_compact hρ (closedBall 0 B) (isCompact_closedBall _ _)
  have hρp := (hρu.comp (fun w : Fin n → ℂ => S (toLp 2 w))).mono hbound
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε,
    Metric.tendstoUniformlyOn_iff.mp hρp ε hε] with k hkE hkρ w hw
  have hELower : hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (S (toLp 2 w)) - ε ≤
      sourceRescaledPhysicalExponent p q a k (S (toLp 2 w)) := by
    have h := hkE w hw
    rw [Real.dist_eq] at h
    have hb := abs_lt.mp h
    linarith
  have hρLower : ρ a - ε ≤ ρ (a + sourceRescaleRadius k • S (toLp 2 w)) := by
    have h := hkρ w hw
    dsimp only [Function.comp_apply] at h
    rw [Real.dist_eq] at h
    have hb := abs_lt.mp h
    linarith
  have heq : Real.exp (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ p) a) (S (toLp 2 w)) - ε) =
      Real.exp (-ε) * sourceDiagonalGaussian d w := by
    rw [sub_eq_add_neg, Real.exp_add, hQ]
    simp only [sourceDiagonalGaussian]
    ring
  have hExp : Real.exp (-ε) * sourceDiagonalGaussian d w ≤
      Real.exp (sourceRescaledPhysicalExponent p q a k (S (toLp 2 w))) := by
    rw [← heq]
    exact Real.exp_le_exp.mpr hELower
  have hpos : 0 ≤ ρ (a + sourceRescaleRadius k • S (toLp 2 w)) :=
    (sub_pos.mpr hερ).le.trans hρLower
  calc
    _ = (ρ a - ε) * (Real.exp (-ε) * sourceDiagonalGaussian d w) := by ring
    _ ≤ _ := mul_le_mul hρLower hExp (by unfold sourceDiagonalGaussian; positivity) hpos
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpRescaledHolomorphic.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Complex Module WithLp Set Metric
/-- The actual affine complex rescaling preserves original holomorphy on
the finite polydisc, with closed continuity internally manufactured. The
ordinary range condition is produced by original Taylor-domain rescaling. -/
theorem sourceSharp_rescaled_holomorphic_on_polydisc {n k : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {G : EuclideanSpace ℂ (Fin n) → ℂ}
    (hG : DifferentiableOn ℂ G U) (a : EuclideanSpace ℂ (Fin n))
    (S : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (R : ℝ)
    (hImage : MapsTo (fun w : Fin n → ℂ => a + sourceRescaleRadius k • S (toLp 2 w))
      (closedBall 0 R) U) :
    DiffContOnCl ℂ (fun w : Fin n → ℂ => G (a + sourceRescaleRadius k • S (toLp 2 w)))
      (ball 0 R) := by
  have hd0 : Differentiable ℂ (fun w : Fin n → ℂ => S (toLp 2 w)) :=
    S.toContinuousLinearMap.differentiable.comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiable
  have hd : Differentiable ℂ (fun w : Fin n → ℂ => a + sourceRescaleRadius k • S (toLp 2 w)) := by
    have he : (fun w : Fin n → ℂ => a + (sourceRescaleRadius k : ℂ) • S (toLp 2 w)) =
        (fun w : Fin n → ℂ => a + sourceRescaleRadius k • S (toLp 2 w)) := by
      funext w
      rw [Complex.coe_smul]
    rw [← he]
    exact (hd0.const_smul (sourceRescaleRadius k : ℂ)).const_add a
  apply DiffContOnCl.mk_ball
  · exact hG.comp hd.differentiableOn (fun w hw => hImage (ball_subset_closedBall hw))
  · exact hG.continuousOn.comp hd.continuous.continuousOn hImage
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/NEW-SHARP/REVISION-02/sources/SourcePhysicalQuadraticNormalForm.lean`.
section
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.SharpLocalUpper

open Bundle Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.BernsteinMarkov
open SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- The original physical metric and original smooth obstacle, in the SAME
actual atlas frame and actual chart. -/
def sourcePhysicalChartWeight (L : HermitianHolomorphicLineBundle n X)
    (v : C(X, ℝ)) (c : ComplexChart n X) (e : AtlasFrame L) (z : ComplexModel n) : ℝ :=
  Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2) - v (c.val.symm z)

def sourcePhysicalTwistChartWeight (T : HermitianHolomorphicLineBundle n X)
    (c : ComplexChart n X) (f : AtlasFrame T) (z : ComplexModel n) : ℝ :=
  Real.log (‖f.val.symm (c.val.symm z) 1‖ ^ 2)

def sourcePhysicalChartDomain (L T : HermitianHolomorphicLineBundle n X)
    (c : ComplexChart n X) (e : AtlasFrame L) (f : AtlasFrame T) : Set (ComplexModel n) :=
  c.val.target ∩ c.val.symm ⁻¹' (e.val.baseSet ∩ f.val.baseSet)

def sourcePhysicalChartCoefficient (L T : HermitianHolomorphicLineBundle n X)
    (c : ComplexChart n X) (e : AtlasFrame L) (f : AtlasFrame T)
    (k : ℕ) (s : twistedSections L T k) : ComplexModel n → ℂ :=
  sectionCoefficient (twistedPower L T k).Fiber (twistedPowerAtlasFrame e f k).val s ∘ c.val.symm

/-- Genuine original smooth metrics supply the actual fixed-ball quadratic
limit for the exact original physical chart weights, in every dimension. -/
theorem sourcePhysicalChartWeights_rescaled_uniform
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (c : ComplexChart n X) (e : AtlasFrame L) (f : AtlasFrame T)
    {a : ComplexModel n} (ha : a ∈ sourcePhysicalChartDomain L T c e f)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (sourceRescaledPhysicalExponent (sourcePhysicalChartWeight L v c e)
        (sourcePhysicalTwistChartWeight T c f) a)
      (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a))
      atTop (closedBall 0 R) ∧
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ closedBall (0 : ComplexModel n) R,
      a + sourceRescaleRadius k • z ∈ sourcePhysicalChartDomain L T c e f := by
  let D := sourcePhysicalChartDomain L T c e f
  have hD : IsOpen D :=
    c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter f.val.open_baseSet)
  have hpL : ContDiffOn ℝ 2 (fun z => Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)) D :=
    (frame_logNormSq_contDiffOn L hL c e).mono (fun z hz => ⟨hz.1, hz.2.1⟩)
  have hpv : ContDiffOn ℝ 2 (fun z => v (c.val.symm z)) D :=
    ((hv c).of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).mono
      (fun z hz => hz.1)
  have hp : ContDiffOn ℝ 2 (sourcePhysicalChartWeight L v c e) D := hpL.sub hpv
  have hq : ContDiffOn ℝ 2 (sourcePhysicalTwistChartWeight T c f) D :=
    (frame_logNormSq_contDiffOn T hT c f).mono (fun z hz => ⟨hz.1, hz.2.2⟩)
  exact sourceActual_rescaled_exponent_uniform hD hp ha
    (hq.continuousOn.continuousAt (hD.mem_nhds ha)) hR

/-- Every original full H0 section supplies its holomorphic quadratic gauge;
no coordinate coefficient or holomorphy flag is supplied by a caller. -/
theorem sourcePhysicalChartGauge_holomorphic
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ))
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T) (k : ℕ) (s : twistedSections L T k) :
    let c := complexChartAt (n := n) x
    DifferentiableOn ℂ
      (sourceQuadraticGauge (sourcePhysicalChartWeight L v c e)
        (sourcePhysicalTwistChartWeight T c f) (c.val x) k
        (sourcePhysicalChartCoefficient L T c e f k s))
      (sourcePhysicalChartDomain L T c e f) := by
  intro c
  apply sourceQuadraticGauge_differentiableOn
  let t := twistedPowerAtlasFrame e f k
  let := t.property
  exact (sectionCoefficient_chart_differentiable (twistedPower L T k).Fiber t.val x s).mono
    (fun z hz => ⟨hz.1, twistedPowerAtlasFrame_mem e f hz.2.1 hz.2.2 k⟩)

/-- Exact density identity for the SAME original section at every actual
point of the frame/chart domain, including k=0 and section zeros. -/
theorem sourcePhysicalChartGauge_density
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ))
    (c : ComplexChart n X) (e : AtlasFrame L) (f : AtlasFrame T)
    (a : ComplexModel n) (k : ℕ) (s : twistedSections L T k)
    {z : ComplexModel n} (hz : z ∈ sourcePhysicalChartDomain L T c e f) :
    realWeightedSectionDensity L T v k s (c.val.symm z) =
      ‖sourceQuadraticGauge (sourcePhysicalChartWeight L v c e)
        (sourcePhysicalTwistChartWeight T c f) a k
        (sourcePhysicalChartCoefficient L T c e f k s) z‖ ^ 2 *
      Real.exp ((k : ℝ) *
        (hermitianHessianQuadratic (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a)
            (z - a) + sourceActualTaylorResidual (sourcePhysicalChartWeight L v c e) a z) +
        sourcePhysicalTwistChartWeight T c f z - sourcePhysicalTwistChartWeight T c f a) := by
  rw [weightedTwistedSection_norm_sq_exp_frame L T v e f k s hz.2.1 hz.2.2]
  exact sourceQuadraticGauge_physicalDensity (sourcePhysicalChartWeight L v c e)
    (sourcePhysicalTwistChartWeight T c f) a k (sourcePhysicalChartCoefficient L T c e f k s) z

/-- Center readback is the original physical density at the original point. -/
theorem sourcePhysicalChartGauge_center
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ))
    (c : ComplexChart n X) (e : AtlasFrame L) (f : AtlasFrame T)
    {x : X} (hx : x ∈ c.val.source) (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet)
    (k : ℕ) (s : twistedSections L T k) :
    ‖sourceQuadraticGauge (sourcePhysicalChartWeight L v c e)
      (sourcePhysicalTwistChartWeight T c f) (c.val x) k
      (sourcePhysicalChartCoefficient L T c e f k s) (c.val x)‖ ^ 2 =
      realWeightedSectionDensity L T v k s x := by
  rw [sourceQuadraticGauge_center, weightedTwistedSection_norm_sq_exp_frame L T v e f k s he hf]
  simp only [sourcePhysicalChartCoefficient, Function.comp_apply, sourcePhysicalChartWeight,
    sourcePhysicalTwistChartWeight]
  rw [c.val.left_inv hx]
  rfl

end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalSectionBound.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
/-- Actual original unit sections obey the fixed-radius sharp Berman bound.
The SAME chart density is produced before all spectral choices and sections;
all rescaled-domain, holomorphy, integrability and local unit-mass inputs are
manufactured. The exact Hessian diagonalization is supplied by the existing
spectral producer, with no sign hypothesis on its eigenvalues. -/
theorem sourceSharp_original_section_fixed_radius_bound
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
    ∀ (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (d : Fin n → ℝ),
      Complex.normSq (LinearMap.det S) = 1 →
      (∀ z : ComplexModel n,
        hermitianHessianQuadratic
          (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a) (S z) =
          -∑ j, d j * ‖z j‖ ^ 2) →
      ∀ (R ε : ℝ), 0 < R → 0 < ε → ε < ρ a →
      ∀ᶠ k : ℕ in atTop, ∀ s : twistedSections L T k,
        weightedL2Norm (twistedPower L T k).Fiber k
          (wholeWeightedSubset (n := n) v).erealWeight
          (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) s ≤ 1 →
        ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          ENNReal.ofReal ((ρ a - ε) * Real.exp (-ε)) *
          ENNReal.ofReal (realWeightedSectionDensity L T v k s x) *
          ENNReal.ofReal (∫ w in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d w) ≤ 1 := by
  intro c a
  have hx : x ∈ c.val.source := mem_complexChartAt_source x
  have ha : a ∈ sourcePhysicalChartDomain L T c e f :=
    ⟨c.val.map_source hx, by simpa only [a, Set.mem_preimage, Set.mem_inter_iff, c.val.left_inv hx] using And.intro he hf⟩
  let U := sourcePhysicalChartDomain L T c e f
  let p := sourcePhysicalChartWeight L v c e
  let q := sourcePhysicalTwistChartWeight T c f
  have hU : IsOpen U := c.val.isOpen_inter_preimage_symm (e.val.open_baseSet.inter f.val.open_baseSet)
  have hpL : ContDiffOn ℝ 2 (fun z => Real.log (‖e.val.symm (c.val.symm z) 1‖ ^ 2)) U :=
    (frame_logNormSq_contDiffOn L hL c e).mono (fun z hz => ⟨hz.1,hz.2.1⟩)
  have hpv : ContDiffOn ℝ 2 (fun z => v (c.val.symm z)) U :=
    ((hv c).of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)).mono
      (fun z hz => hz.1)
  have hp : ContDiffOn ℝ 2 p U := hpL.sub hpv
  have hq : ContinuousAt q a :=
    ((frame_logNormSq_contDiffOn T hT c f).mono (fun z hz => ⟨hz.1,hz.2.2⟩)).continuousOn.continuousAt
      (hU.mem_nhds ha)
  obtain ⟨ρ,hρsm,hρpos,hmap,hunit⟩ := sourceSharp_original_chart_rescaled_unit_integral L T v μ hμ c
  have hρ : ContinuousAt ρ a := hρsm.continuousOn.continuousAt (c.val.open_target.mem_nhds ha.1)
  refine ⟨ρ,hρsm,hmap,hρpos a ha.1,fun S d hS hQ R ε hR hε hερ => ?_⟩
  obtain ⟨_,hdom⟩ := sourceSharp_rescaled_exponent_polydisc hU hp ha hq S R
  have hwgt := sourceSharp_rescaled_spectral_weight_lower hU hp ha hq hρ S d hQ R ε hε hερ
  filter_upwards [hdom, hwgt, eventually_gt_atTop 0] with k hkD hkW hk s hs
  let F : (Fin n → ℂ) → ℂ := fun w =>
    sourceQuadraticGauge p q a k (sourcePhysicalChartCoefficient L T c e f k s)
      (a + sourceRescaleRadius k • S (toLp 2 w))
  have hF : DiffContOnCl ℂ F (ball 0 R) := sourceSharp_rescaled_holomorphic_on_polydisc
    (sourcePhysicalChartGauge_holomorphic L T v x e f k s) a S R hkD
  have hcenter : ‖F 0‖ ^ 2 = realWeightedSectionDensity L T v k s x := by
    simpa only [F, p, q, a, WithLp.toLp_zero, map_zero, smul_zero, add_zero] using
      sourcePhysicalChartGauge_center L T v c e f hx he hf k s
  let C := (ρ a - ε) * Real.exp (-ε)
  have hC : 0 ≤ C := mul_nonneg (sub_pos.mpr hερ).le (Real.exp_pos _).le
  have hcomp : ∀ w ∈ closedBall (0 : Fin n → ℂ) R,
      C * (‖F w‖ ^ 2 * sourceDiagonalGaussian d w) ≤
        ρ (a + sourceRescaleRadius k • S (toLp 2 w)) *
        realWeightedSectionDensity L T v k s
          (c.val.symm (a + sourceRescaleRadius k • S (toLp 2 w))) := by
    intro w hw
    have hid := sourcePhysicalChartGauge_density L T v c e f a k s (hkD w hw)
    change realWeightedSectionDensity L T v k s _ =
      ‖F w‖ ^ 2 * Real.exp (sourceRescaledPhysicalExponent p q a k (S (toLp 2 w))) at hid
    calc
      _ = ‖F w‖ ^ 2 * (C * sourceDiagonalGaussian d w) := by ring
      _ ≤ ‖F w‖ ^ 2 * (ρ (a + sourceRescaleRadius k • S (toLp 2 w)) *
          Real.exp (sourceRescaledPhysicalExponent p q a k (S (toLp 2 w)))) :=
        mul_le_mul_of_nonneg_left (hkW w hw) (sq_nonneg _)
      _ = _ := by rw [hid]; ring
  have hu := hunit k hk s hs a S hS R (by
    rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    exact (hkD w hw).1)
  have hsub := sourceSharp_weighted_polydisc_submean_lintegral hR hF d
  rw [hcenter] at hsub
  let J := ENNReal.ofReal (((k : ℝ) ^ n)⁻¹)
  calc
    _ ≤ J * ENNReal.ofReal C *
        (∫⁻ w in ball (0 : Fin n → ℂ) R,
          ENNReal.ofReal (‖F w‖ ^ 2 * sourceDiagonalGaussian d w)) := by
      simpa only [J, C, mul_assoc] using mul_le_mul_right hsub (J * ENNReal.ofReal C)
    _ = ∫⁻ w in ball (0 : Fin n → ℂ) R,
        J * ENNReal.ofReal (C * (‖F w‖ ^ 2 * sourceDiagonalGaussian d w)) := by
      simp only [ENNReal.ofReal_mul hC]
      rw [lintegral_const_mul' J _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [mul_assoc]
    _ ≤ ∫⁻ w in ball (0 : Fin n → ℂ) R,
        J * (ENNReal.ofReal (ρ (a + sourceRescaleRadius k • S (toLp 2 w))) *
          ENNReal.ofReal (realWeightedSectionDensity L T v k s
            (c.val.symm (a + sourceRescaleRadius k • S (toLp 2 w))))) := by
      apply setLIntegral_mono' measurableSet_ball
      intro w hw
      apply mul_le_mul_right
      rw [← ENNReal.ofReal_mul (hρpos _ (hkD w (ball_subset_closedBall hw)).1).le]
      exact ENNReal.ofReal_le_ofReal (hcomp w (ball_subset_closedBall hw))
    _ ≤ _ := (lintegral_mono_set ball_subset_closedBall).trans hu
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalBergmanBound.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter Metric MeasureTheory WithLp
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal BigOperators
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X]
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.MultiplierSectionsDraft
/-- The sharp fixed-radius bound on the literal original Gamma supremum,
without a maximizing section or any singularity-type restriction. -/
theorem sourceSharp_original_Bergman_fixed_radius_bound
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (x : X) (e : AtlasFrame L) (f : AtlasFrame T)
    (he : x ∈ e.val.baseSet) (hf : x ∈ f.val.baseSet) (φ : X → EReal) :
    let c := complexChartAt (n := n) x
    let a := c.val x
    ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ c.val.target ∧
      Measure.map c.val (μ.restrict c.val.source) =
        (volume.restrict c.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)) ∧
      0 < ρ a ∧
    ∀ (S : ComplexModel n →ₗ[ℂ] ComplexModel n) (d : Fin n → ℝ),
      Complex.normSq (LinearMap.det S) = 1 →
      (∀ z : ComplexModel n,
        hermitianHessianQuadratic
          (fderiv ℝ (fderiv ℝ (sourcePhysicalChartWeight L v c e)) a) (S z) =
          -∑ j, d j * ‖z j‖ ^ 2) →
      ∀ (R ε : ℝ), 0 < R → 0 < ε → ε < ρ a →
      ∀ᶠ k : ℕ in atTop,
        ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
          ENNReal.ofReal ((ρ a - ε) * Real.exp (-ε)) *
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
            ⟨x, Set.mem_univ x⟩ *
          ENNReal.ofReal (∫ w in ball (0 : Fin n → ℂ) R, sourceDiagonalGaussian d w) ≤ 1 := by
  intro c a
  obtain ⟨ρ,hρsm,hmap,hρ,hbound⟩ := sourceSharp_original_section_fixed_radius_bound L T hL hT v hv μ hμ x e f he hf
  refine ⟨ρ,hρsm,hmap,hρ,fun S d hS hQ R ε hR hε hερ => ?_⟩
  filter_upwards [hbound S d hS hQ R ε hR hε hερ] with k hk
  simp only [sourcePartialBergmanDensity, ENNReal.mul_iSup, ENNReal.iSup_mul]
  refine iSup₂_le fun s hs => ?_
  change ENNReal.ofReal (((k : ℝ) ^ n)⁻¹) *
    ENNReal.ofReal ((ρ a - ε) * Real.exp (-ε)) *
    weightedSectionDensity (twistedPower L T k).Fiber k (univRealWeight v)
      (literalTwistedMultiplierSectionEquiv L T k φ s).val ⟨x,Set.mem_univ x⟩ * _ ≤ 1
  rw [weightedSectionDensity_univ]
  exact hk (literalTwistedMultiplierSectionEquiv L T k φ s).val hs
end SGPT.Bergman.SharpLocalUpper
end
end
