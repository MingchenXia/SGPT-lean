import SGPT.Toric.TropicalPolarIntegral
import SGPT.Convex.FiniteAlexandrovContinuity
import SGPT.Convex.SmoothFiniteApproximation
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory TopologicalSpace SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorContinuity
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
open scoped Topology ContDiff Distributions ENNReal RealInnerProductSpace CompactlySupported

variable {n : ℕ}

local notation "D" => tropicalSmoothDomain n

/-- Original smooth coordinate pullbacks give continuity of the same tropical map. -/
theorem continuousOn_tropicalization : ContinuousOn (@tropicalization n) D := by
  have hc : ContinuousOn (fun z : ComplexModel n => fun i => tropicalization z i) D := by
    apply continuousOn_pi.mpr
    intro i
    exact (contDiffOn_tropicalSmoothProfile
      (show ContDiff ℝ ∞ (fun a : EuclideanSpace ℝ (Fin n) => a i) by fun_prop)).continuousOn
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using
    (PiLp.continuous_toLp 2 _).comp_continuousOn hc

/-- Finite convexity supplies actual continuous locally bounded PSH on the original torus. -/
theorem isLocallyBoundedPshOn_tropicalConvexProfile
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f) :
    IsLocallyBoundedPshOn D (fun z => f (tropicalization z)) :=
  LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_tropicalPullback_of_convexOn hc)
    ((continuousOn_univ.mp (hc.continuousOn isOpen_univ)).comp_continuousOn
      continuousOn_tropicalization)

/-- Genuine normalized convex smoothing and actual composition manufacture the complex limit. -/
theorem tendstoLocallyUniformlyOn_tropicalConvexProfile_smoothApprox
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f) :
    TendstoLocallyUniformlyOn
      (fun j => fun z : ComplexModel n => finiteConvexSmoothApprox volume f j (tropicalization z))
      (fun z => f (tropicalization z)) atTop D := by
  have hr : TendstoLocallyUniformlyOn (finiteConvexSmoothApprox volume f) f atTop univ := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
    intro K _ hK
    exact tendstoUniformlyOn_finiteConvexSmoothApprox volume hc hK
  simpa only [Function.comp_def] using
    hr.comp tropicalization (fun _ _ => mem_univ _) continuousOn_tropicalization

/-- The independently constructed original canonical real-tuple BT measure. -/
def tropicalCanonicalBTMeasure {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hc : ConvexOn ℝ univ f) : Measure (ComplexModel n) :=
  canonicalMixedBedfordTaylorMeasure D (fun _ : Fin n => fun z => f (tropicalization z))
    (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)

/-- Actual general BT continuity, canonical trace and diagonal smooth readbacks. -/
theorem tendsto_integral_tropicalCanonicalBT_smoothApprox
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {g : ComplexModel n → ℝ} (hg : Continuous g) (hK : HasCompactSupport g)
    (hD : tsupport g ⊆ D) :
    Tendsto (fun j => ∫ z, g z ∂smoothMeasure D
      (fun z => finiteConvexSmoothApprox volume f j (tropicalization z))
      (isSmoothPshOn_tropicalSmoothProfile
        (contDiff_finiteConvexSmoothApprox volume hc j)
        (convexOn_finiteConvexSmoothApprox volume hc j))) atTop
      (𝓝 (∫ z, g z ∂tropicalCanonicalBTMeasure hc)) := by
  let v : ℕ → Fin n → ComplexModel n → ℝ := fun j _ z =>
    finiteConvexSmoothApprox volume f j (tropicalization z)
  let v0 : Fin n → ComplexModel n → ℝ := fun _ z => f (tropicalization z)
  let T := oneCurrentOf (U := D) (Nat.zero_add n)
  have hv (j : ℕ) (i : Fin n) : IsLocallyBoundedPshOn D (v j i) :=
    isLocallyBoundedPshOn_of_isSmoothPshOn (isSmoothPshOn_tropicalSmoothProfile
      (contDiff_finiteConvexSmoothApprox volume hc j)
      (convexOn_finiteConvexSmoothApprox volume hc j))
  have hP (j : ℕ) : IsPositive (btProduct n 0 (v j) T) :=
    (isPositive_btProduct n 0 (v j) T (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) (hv j)).1
  have hP0 : IsPositive (btProduct n 0 v0 T) :=
    (isPositive_btProduct n 0 v0 T (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _)
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)).1
  have hw := weakTendsto_btProduct n 0 v v0 (fun _ => T) T
    (fun _ => isPositive_oneCurrentOf _) (fun _ => isClosedAny_oneCurrentOf _)
    (by intro _ _; exact tendsto_const_nhds) hv
    (fun _ => (continuousOn_univ.mp (hc.continuousOn isOpen_univ)).comp_continuousOn
      continuousOn_tropicalization)
    (fun _ => tendstoLocallyUniformlyOn_tropicalConvexProfile_smoothApprox hc)
  have hl := tendsto_integral_traceMeasure_of_weakTendsto hP hP0 hw hg hK hD
  change Tendsto (fun j => ∫ z, g z ∂recursiveMixedTraceMeasure D (v j) (hv j)) atTop
    (𝓝 (∫ z, g z ∂recursiveMixedTraceMeasure D v0
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc))) at hl
  have es (j : ℕ) : recursiveMixedTraceMeasure D (v j) (hv j) =
      smoothMeasure D (fun z => finiteConvexSmoothApprox volume f j (tropicalization z))
        (isSmoothPshOn_tropicalSmoothProfile (contDiff_finiteConvexSmoothApprox volume hc j)
          (convexOn_finiteConvexSmoothApprox volume hc j)) := by
    exact (recursiveMixedTraceMeasure_eq_smoothMixedMeasure
      (fun _ => contDiffOn_tropicalSmoothProfile (contDiff_finiteConvexSmoothApprox volume hc j))
      (fun _ => plurisubharmonicOn_tropicalPullback_of_convexOn
        (convexOn_finiteConvexSmoothApprox volume hc j))).trans
      (smoothMixedMeasure_diagonal _ _ _ _)
  have et : tropicalCanonicalBTMeasure hc = recursiveMixedTraceMeasure D v0
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc) :=
    canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc)
  simp_rw [es, ← et] at hl
  exact hl

private theorem tropicalBT_smoothMeasure_ae_torus
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : ConvexOn ℝ univ f) :
    ∀ᵐ z ∂smoothMeasure D (fun z => f (tropicalization z))
      (isSmoothPshOn_tropicalSmoothProfile hf hc), z ∈ complexTorus n := by
  apply ae_iff.mpr
  change smoothMeasure D (fun z => f (tropicalization z))
    (isSmoothPshOn_tropicalSmoothProfile hf hc) (complexTorus n)ᶜ = 0
  rw [smoothMeasure, withDensity_apply _ (isOpen_complexTorus n).measurableSet.compl]
  have hz : (volume.restrict (D : Set (ComplexModel n))) (complexTorus n)ᶜ = 0 := by
    rw [Measure.restrict_apply (isOpen_complexTorus n).measurableSet.compl]
    simp only [tropicalSmoothDomain, Opens.coe_mk, compl_inter_self, measure_empty]
  exact setLIntegral_measure_zero _ _ hz

/-- Both actual limits test the same original signed compact function. -/
theorem integral_tropicalCanonicalBT_source_test
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Continuous φ)
    (hK : HasCompactSupport φ) :
    (∫ z, φ (tropicalization z) ∂tropicalCanonicalBTMeasure hc) =
      ∫ a, φ a ∂alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (f a : EReal)) := by
  obtain ⟨η, hη, hηK, hηD, hread⟩ := exists_tropical_compact_test_pullback hφ hK
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hs (j : ℕ) :
      (∫ z, η z ∂smoothMeasure D
        (fun z => finiteConvexSmoothApprox volume f j (tropicalization z))
        (isSmoothPshOn_tropicalSmoothProfile (contDiff_finiteConvexSmoothApprox volume hc j)
          (convexOn_finiteConvexSmoothApprox volume hc j))) =
      ∫ a, φ a ∂alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (finiteConvexSmoothApprox volume f j a : EReal)) := by
    rw [← tropicalization_smoothMeasure_eq_alexandrov
      (contDiff_finiteConvexSmoothApprox volume hc j)
      (convexOn_finiteConvexSmoothApprox volume hc j),
      integral_map hT.aemeasurable hφ.aestronglyMeasurable]
    exact integral_congr_ae ((tropicalBT_smoothMeasure_ae_torus
      (contDiff_finiteConvexSmoothApprox volume hc j)
      (convexOn_finiteConvexSmoothApprox volume hc j)).mono (fun z hz => hread z hz))
  have hb := tendsto_integral_tropicalCanonicalBT_smoothApprox hc hη hηK hηD
  have hr := tendsto_integral_alexandrovMeasure_of_finite_convex_compact_convergence
    (ν := volume) (innerₗ (EuclideanSpace ℝ (Fin n))) hc
    (convexOn_finiteConvexSmoothApprox volume hc)
    (fun _ hcomp => tendstoUniformlyOn_finiteConvexSmoothApprox volume hc hcomp)
    (⟨⟨φ, hφ⟩, hK⟩ : C_c(EuclideanSpace ℝ (Fin n), ℝ))
  simp_rw [hs] at hb
  have hm : ∀ᵐ z ∂tropicalCanonicalBTMeasure hc, z ∈ complexTorus n :=
    ae_iff.mpr (canonicalMixedBedfordTaylorMeasure_compl _ _ _)
  exact (integral_congr_ae (hm.mono (fun z hz => (hread z hz).symm))).trans
    (tendsto_nhds_unique hb hr)

/-- Genuine compact lifts manufacture local finiteness before regular-measure uniqueness. -/
theorem tropicalization_canonicalBTMeasure_eq_alexandrov
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hc : ConvexOn ℝ univ f) :
    Measure.map tropicalization (tropicalCanonicalBTMeasure hc) =
      alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (f a : EReal)) := by
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  have hm : ∀ᵐ z ∂tropicalCanonicalBTMeasure hc, z ∈ complexTorus n :=
    ae_iff.mpr (canonicalMixedBedfordTaylorMeasure_compl _ _ _)
  let : IsFiniteMeasureOnCompacts (Measure.map tropicalization
      (tropicalCanonicalBTMeasure hc)) := ⟨by
    intro K hK
    obtain ⟨_, L, hL, hLD, hcover⟩ := exists_compact_tropical_torus_lift hK
    rw [Measure.map_apply hT hK.measurableSet]
    apply lt_of_le_of_lt (measure_mono_ae (hm.mono (fun z hz hpre => hcover z hz hpre)))
    exact canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
      (fun _ => isLocallyBoundedPshOn_tropicalConvexProfile hc) hL hLD⟩
  let : IsLocallyFiniteMeasure
      (alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin n))) volume
        (fun a => (f a : EReal))) := isLocallyFiniteMeasure_alexandrovMeasure_coe _ hc
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hmap : (∫ a, φ a ∂Measure.map tropicalization (tropicalCanonicalBTMeasure hc)) =
      ∫ z, φ (tropicalization z) ∂tropicalCanonicalBTMeasure hc :=
    integral_map hT.aemeasurable φ.continuous.aestronglyMeasurable
  exact hmap.trans (integral_tropicalCanonicalBT_source_test hc
    φ.continuous φ.hasCompactSupport)

end SGPT.Toric
