import SGPT.Trace.BertiniFamilyTubeKernelLimit
import Mathlib.MeasureTheory.Measure.Prod

/-! Actual raw-weight normal Borel density and genuine original physical Tonelli integral. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.OTMargin
open SGPT.Trace.BertiniNativeNormalKernel

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (affinePoint i (a - t.val 0 • v)))
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)

omit [MeasurableSpace X] [BorelSpace X] in
theorem familyNormalPhysicalDensity_real_zero_weight :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q)
      (w : familyIncidence p i a v U → ℝ≥0∞) (z : ComplexModel (d + 1)) (_hz : z ∈ F.flat.target),
      familyNormalPhysicalDensity p i a v U hsm L F S w z =
        ENNReal.ofReal (familyNormalRealDensity p i a v U hsm L F S (fun _ => 0) z) * w (finv F z) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S w z hz
  have h := familyNormalRealDensity_ofReal p i a v U hsm L F S (fun _ => 0) z hz
  rw [familyNormalPhysicalDensity_eq_value p i a v U hsm L F S _ z hz] at h
  simp only [neg_zero,Real.exp_zero,ENNReal.ofReal_one,mul_one] at h
  rw [familyNormalPhysicalDensity_eq_value p i a v U hsm L F S w z hz,h]

def familyNormalBorelDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)}, FlatData (d + 1) d (familyIncidence p i a v U) W →
      (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ≥0∞) → ComplexModel (d + 1) → ℝ≥0∞ := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  exact fun _ F S w z => if z ∈ F.flat.target then familyNormalPhysicalDensity p i a v U hsm L F S w z else 0

theorem familyNormalBorelDensity_measurable :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      Measurable (familyNormalBorelDensity p i a v U hsm L F S w) := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS w hw
  have hD : ContinuousOn (familyNormalRealDensity p i a v U hsm L F S (fun _ => 0)) F.flat.target :=
    familyNormalRealDensity_continuousOn p i a v U hsm L F S hS (fun _ => 0) continuous_const
  have hI : Continuous (fun z : F.flat.target => finv F z.val) := (continuousOn_finv F).domRestrict
  have hsub : Measurable (fun z : F.flat.target => familyNormalPhysicalDensity p i a v U hsm L F S w z.val) := by
    have heq : (fun z : F.flat.target => familyNormalPhysicalDensity p i a v U hsm L F S w z.val) =
        fun z => ENNReal.ofReal (familyNormalRealDensity p i a v U hsm L F S (fun _ => 0) z.val) * w (finv F z.val) := by
      funext z
      exact familyNormalPhysicalDensity_real_zero_weight p i a v U hsm L F S w z.val z.property
    rw [heq]
    exact (ENNReal.continuous_ofReal.comp hD.domRestrict).measurable.mul (hw.comp hI.measurable)
  unfold familyNormalBorelDensity
  exact Measurable.dite hsub measurable_const F.flat.open_target.measurableSet

theorem familyPhysical_integral_normal_fubini :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      (∫⁻ q in F.ambSource, ENNReal.ofReal (‖S q‖ ^ 2) * w q ∂familyMatchedVolume p i a v U hsm) =
        ∫⁻ τ : ℂ, ∫⁻ u : ComplexModel d,
          familyNormalBorelDensity p i a v U hsm L F S w (normalProductEquiv d (u,τ)) ∂volume ∂volume := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS w hw
  let D := familyNormalBorelDensity p i a v U hsm L F S w
  have hD : Measurable D := familyNormalBorelDensity_measurable p i a v U hsm L F S hS w hw
  have hsupp : Function.support D ⊆ F.flat.target := by
    intro z hz
    by_contra hzt
    exact hz (if_neg hzt)
  have heq : (∫⁻ z in F.flat.target, familyNormalPhysicalDensity p i a v U hsm L F S w z ∂volume) =
      ∫⁻ z : ComplexModel (d + 1), D z ∂volume := by
    calc
      _ = ∫⁻ z in F.flat.target, D z ∂volume := by
        apply setLIntegral_congr_fun F.flat.open_target.measurableSet
        intro z hz
        exact (if_pos hz).symm
      _ = _ := setLIntegral_eq_of_support_subset hsupp
  have hprod : Measurable (fun q : ComplexModel d × ℂ => D (normalProductEquiv d q)) :=
    hD.comp (normalProductEquiv d).continuous.measurable
  calc
    _ = ∫⁻ z : ComplexModel (d + 1), D z ∂volume :=
      (familyPhysical_energy_in_flatData p i a v U hsm L F S hS w hw).trans heq
    _ = ∫⁻ q : ComplexModel d × ℂ, D (normalProductEquiv d q) ∂(volume.prod volume) :=
      ((measurePreserving_normalProductEquiv d).lintegral_comp hD).symm
    _ = _ := lintegral_prod_symm' _ hprod

theorem familyNormalMarginal_measurable :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      Measurable (fun τ : ℂ => ∫⁻ u : ComplexModel d,
        familyNormalBorelDensity p i a v U hsm L F S w (normalProductEquiv d (u,τ)) ∂volume) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS w hw
  have hprod : Measurable (fun q : ComplexModel d × ℂ => familyNormalBorelDensity p i a v U hsm L F S w (normalProductEquiv d q)) :=
    (familyNormalBorelDensity_measurable p i a v U hsm L F S hS w hw).comp (normalProductEquiv d).continuous.measurable
  exact hprod.lintegral_prod_left'

end SGPT.Trace.BertiniFamilyCanonical
