import SGPT.Trace.TwistedL2SingularUniform
import SGPT.Trace.TwistedL2SingularLimit
import SGPT.Trace.TwistedL2SingularMeanValue

/-!
# Local frame coefficients and original section `L²` norms

A compact chart ball contained in the base of a genuine line-bundle frame has
positive lower bounds for the frame norm and the actual smooth-volume density.
The Euclidean square integral of a holomorphic section's coefficient is thus
bounded by a constant times the original fiber-norm integral over the inverse
image of that same chart ball. The constant precedes every section.

-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- Transport an actual section `L²` bound to its coefficient in the same
chart and frame. The constant is independent of the open domain and section. -/
theorem exists_frame_coefficient_l2_bound
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    (c : ComplexChart n X) (e : AtlasFrame L)
    (z : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (hchart : closedBall z R ⊆ chartFrameDomain L c e) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (V : Set X), IsOpen V →
      c.val.symm '' closedBall z R ⊆ V →
      ∀ S : (x : X) → L.Fiber x,
        SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S V →
        (∫⁻ w in ball z R, ENNReal.ofReal (‖chartCoeff L c e S w‖ ^ 2)) ≤
          C * ∫⁻ x in c.val.symm '' closedBall z R, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ := by
  classical
  let := e.property
  set K : Set (ComplexModel n) := closedBall z R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKt : K ⊆ c.val.target := fun w hw => (hchart hw).1
  have hKe : ∀ w ∈ K, c.val.symm w ∈ e.val.baseSet := fun w hw => (hchart hw).2
  have hKne : K.Nonempty := ⟨z, mem_closedBall_self hR.le⟩
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ c
  obtain ⟨z₁, hz₁K, hρmin⟩ := hK.exists_isMinOn hKne (hρs.continuousOn.mono hKt)
  have hρm : 0 < ρ z₁ := hρpos z₁ (hKt hz₁K)
  have hframe : ContinuousOn (fun w => ‖e.val.symm (c.val.symm w) 1‖) K :=
    (SGPT.Bergman.CompactHolomorphicSectionsDraft.frameNorm_continuousOn L.Fiber e.val).comp
      (c.val.continuousOn_symm.mono hKt) hKe
  obtain ⟨z₂, hz₂K, hφmin⟩ := hK.exists_isMinOn hKne hframe
  set m : ℝ := ‖e.val.symm (c.val.symm z₂) 1‖
  have hm : 0 < m := frameNorm_pos L e.val (hKe z₂ hz₂K)
  set C₀ : ℝ := 1 / (m ^ 2 * ρ z₁)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨ENNReal.ofReal C₀, ENNReal.ofReal_lt_top, ?_⟩
  intro V hVo hKV S hS
  set H : X → ℝ≥0∞ := V.indicator (fun x => ENNReal.ofReal (‖S x‖ ^ 2))
  have hHm : Measurable H := by
    rw [show H = V.indicator (fun x => ENNReal.ofReal (‖S x‖ ^ 2)) from rfl,
      ← Set.piecewise_eq_indicator]
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hVo.measurableSet
    exact ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_norm_of_holomorphic L hS).pow 2)
  have hpt : ∀ w ∈ K, ENNReal.ofReal (‖chartCoeff L c e S w‖ ^ 2) ≤
      ENNReal.ofReal C₀ * (ENNReal.ofReal (ρ w) * H (c.val.symm w)) := by
    intro w hw
    have hwV : c.val.symm w ∈ V := hKV ⟨w, hw, rfl⟩
    have hnorm := norm_eq_coord_mul L e.val (hKe w hw) (S (c.val.symm w))
    have hρw : ρ z₁ ≤ ρ w := hρmin hw
    have hmw : m ≤ ‖e.val.symm (c.val.symm w) 1‖ := hφmin hw
    rw [show H (c.val.symm w) = ENNReal.ofReal (‖S (c.val.symm w)‖ ^ 2) by simp [H, hwV],
      hnorm, ← ENNReal.ofReal_mul (hρpos w (hKt hw)).le, ← ENNReal.ofReal_mul hC₀]
    refine ENNReal.ofReal_le_ofReal ?_
    change ‖chartCoeff L c e S w‖ ^ 2 ≤ C₀ *
      (ρ w * (‖chartCoeff L c e S w‖ * ‖e.val.symm (c.val.symm w) 1‖) ^ 2)
    have hprod : m ^ 2 * ρ z₁ ≤ ρ w * ‖e.val.symm (c.val.symm w) 1‖ ^ 2 := by
      have : m ^ 2 ≤ ‖e.val.symm (c.val.symm w) 1‖ ^ 2 := by nlinarith
      nlinarith
    rw [show C₀ = 1 / (m ^ 2 * ρ z₁) from rfl, mul_pow]
    have hpos : 0 < m ^ 2 * ρ z₁ := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
    nlinarith [sq_nonneg ‖chartCoeff L c e S w‖]
  have hsource : c.val.source ∩ c.val ⁻¹' K ⊆ c.val.symm '' K := by
    rintro x ⟨hx, hxK⟩
    exact ⟨c.val x, hxK, c.val.left_inv hx⟩
  calc ∫⁻ w in ball z R, ENNReal.ofReal (‖chartCoeff L c e S w‖ ^ 2)
      ≤ ∫⁻ w in K, ENNReal.ofReal (‖chartCoeff L c e S w‖ ^ 2) :=
        lintegral_mono_set ball_subset_closedBall
    _ ≤ ∫⁻ w in K, ENNReal.ofReal C₀ * (ENNReal.ofReal (ρ w) * H (c.val.symm w)) :=
        setLIntegral_mono' hK.isClosed.measurableSet hpt
    _ = ENNReal.ofReal C₀ * ∫⁻ w in K, ENNReal.ofReal (ρ w) * H (c.val.symm w) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal C₀ * ∫⁻ x in c.val.source ∩ c.val ⁻¹' K, H x ∂μ := by
        rw [setLIntegral_source_inter_preimage c hρs.continuousOn hmap hK hKt hHm]
    _ ≤ ENNReal.ofReal C₀ * ∫⁻ x in c.val.symm '' K, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc ∫⁻ x in c.val.source ∩ c.val ⁻¹' K, H x ∂μ
            ≤ ∫⁻ x in c.val.symm '' K, H x ∂μ := lintegral_mono_set hsource
          _ = ∫⁻ x in c.val.symm '' K, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ := by
              have hK' : IsCompact (c.val.symm '' K) := hK.image_of_continuousOn
                (c.val.continuousOn_symm.mono hKt)
              refine setLIntegral_congr_fun hK'.isClosed.measurableSet fun x hx => ?_
              simp [H, hKV hx]

end SGPT.Trace.TwistedL2
