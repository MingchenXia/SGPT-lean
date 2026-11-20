import SGPT.Trace.BertiniFamilyPhysicalDensity

/-! True physical energy read in the actual matched-volume family charts. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

theorem familyPhysical_normSq_measurable :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      Measurable (fun q => ENNReal.ofReal (‖S q‖ ^ 2)) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro S hS
  have hn : Continuous (fun q => ‖S q‖) := continuousOn_univ.mp
    (ContinuousFiberNorm.continuous.comp_continuousOn hS.continuousOn)
  exact (ENNReal.continuous_ofReal.comp (hn.pow 2)).measurable

def familyPhysicalCoordinateDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ComplexChart (d + 1) (familyIncidence p i a v U) →
      (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ≥0∞) → ComplexModel (d + 1) → ℝ≥0∞ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun e S w z => if hz : z ∈ e.val.target then
    ENNReal.ofReal (‖familyPhysicalCoordinateEquiv p i a v U hsm L e
      (e.val.symm z) (e.val.map_target hz) (S (e.val.symm z))‖ ^ 2) * w (e.val.symm z) else 0

theorem familyPhysical_energy_in_chart :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U))
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      (∫⁻ q in e.val.source, ENNReal.ofReal (‖S q‖ ^ 2) * w q ∂familyMatchedVolume p i a v U hsm) =
        ∫⁻ z in e.val.target, familyPhysicalCoordinateDensity p i a v U hsm L e S w z ∂volume := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e S hS w hw
  let F : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (‖S q‖ ^ 2) * w q
  let μ := familyMatchedVolume p i a v U hsm
  let ρ := familyMatchedCoordinateDensity p i a v U hsm e
  have hF : Measurable F := (familyPhysical_normSq_measurable p i a v U hsm L S hS).mul hw
  have he : AEMeasurable e.val (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hinv : AEMeasurable e.val.symm (volume.restrict e.val.target) :=
    e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet
  have hFi := hF.comp_aemeasurable hinv
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict e.val.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (familyMatchedCoordinateDensity_smooth p i a v U hsm e).continuousOn).aemeasurable
        e.val.open_target.measurableSet
  have hFi' : AEMeasurable (fun z => F (e.val.symm z)) (Measure.map e.val (μ.restrict e.val.source)) := by
    rw [familyMatchedVolume_chart p i a v U hsm e]
    exact hFi.mono_ac (withDensity_absolutelyContinuous _ _)
  calc
    (∫⁻ q in e.val.source, F q ∂μ) = ∫⁻ q in e.val.source, F (e.val.symm (e.val q)) ∂μ := by
      apply setLIntegral_congr_fun e.val.open_source.measurableSet
      intro q hq
      dsimp only
      rw [e.val.left_inv hq]
    _ = ∫⁻ z, F (e.val.symm z) ∂Measure.map e.val (μ.restrict e.val.source) :=
      (lintegral_map' hFi' he).symm
    _ = ∫⁻ z in e.val.target, ENNReal.ofReal (ρ z) * F (e.val.symm z) ∂volume := by
      rw [familyMatchedVolume_chart p i a v U hsm e]
      exact lintegral_withDensity_eq_lintegral_mul₀ hρ hFi
    _ = ∫⁻ z in e.val.target, familyPhysicalCoordinateDensity p i a v U hsm L e S w z ∂volume := by
      apply setLIntegral_congr_fun e.val.open_target.measurableSet
      intro z hz
      dsimp only [F]
      unfold familyPhysicalCoordinateDensity
      rw [dif_pos hz, ← mul_assoc, ← ENNReal.ofReal_mul
        (familyMatchedCoordinateDensity_pos p i a v U hsm e z hz).le]
      congr 1
      apply congrArg ENNReal.ofReal
      have h := familyPhysicalCoordinate_norm_density p i a v U hsm L e
        (e.val.symm z) (e.val.map_target hz) (S (e.val.symm z))
      unfold familyMatchedCoordinateDensity
      rw [dif_pos hz, mul_comm]
      exact h

end SGPT.Trace.BertiniFamilyCanonical
