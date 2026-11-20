import SGPT.Toric.GlobalTropicalChartMass
import SGPT.Convex.BoundedLegendreVariation
import SGPT.Foundations.Analysis.Pending.ActualSingularChartMassLiminf

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ENNReal RealInnerProductSpace
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {θ : ClosedRealOneOneForm n M} {u φ v : M → EReal}
  {ρ : ComplexModel n → ℝ}
  {fu fφ fv : EuclideanSpace ℝ (Fin n) → ℝ}
local notation "D" => tropicalSmoothDomain n
local notation "B" => innerₗ (EuclideanSpace ℝ (Fin n))

/-- Every actual nonnegative tropical weight transports through the genuine
whole native NP measure and actual canonical BT/Alexandrov maps. -/
theorem globalMixedMeasure_lintegral_eq_tropical
    (hv : IsThetaPshPotential θ.val v) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ) (hcv : ConvexOn ℝ univ fv)
    (heqv : EqOn (fun z => chartFunction v e z + (ρ z : EReal))
      (fun z => (fv (tropicalization z) : EReal)) D)
    {w : M → EReal} (hw : IsGlobalQuasiPshPotential (n := n) w)
    (hpole : ((tropicalPotentialPatch e hρ hcv heqv).source : Set M)ᶜ ⊆ {x | w x = ⊥})
    (a : M → ℝ≥0∞) {q : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hq : Measurable q)
    (heq : ∀ z ∈ D, a (e.val.symm z) = q (tropicalization z)) :
    (∫⁻ p, a p ∂GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ)
      (fun _ => v) (fun _ => hv.1)) =
      ∫⁻ x, q x ∂alexandrovMeasure B volume (fun x => (fv x : EReal)) := by
  let P := tropicalPotentialPatch e hρ hcv heqv
  let ν := tropicalCanonicalBTMeasure hcv
  have hs : ν (P.domain : Set (ComplexModel n))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hwhole : GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ)
      (fun _ => v) (fun _ => hv.1) = P.pushMeasure ν :=
    globalMixedMeasure_eq_tropical_chart_pushMeasure hv e hρ hcv heqv hw hpole
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  calc
    _ = ∫⁻ z, a (e.val.symm z) ∂ν := by
      rw [hwhole]
      exact ActualSingularChartMassLiminf.lintegral_pushMeasure P hs a
    _ = ∫⁻ z, q (tropicalization z) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_iff.mpr hs] with z hz
      exact heq z hz
    _ = ∫⁻ x, q x ∂Measure.map tropicalization ν := (lintegral_map hq hT).symm
    _ = _ := by rw [tropicalization_canonicalBTMeasure_eq_alexandrov hcv]

private theorem recover_finite_corrected (a : EReal) (F r : ℝ)
    (h : a + (r : EReal) = (F : EReal)) : a = ((F - r : ℝ) : EReal) := by
  have he := congrArg (fun z : EReal => z + ((-r : ℝ) : EReal)) h
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero, ← EReal.coe_add] at he
  simpa only [sub_eq_add_neg] using he

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Original finite corrected values recover both actual source values before
real conversion, so their literal cross-input chart gap cancels the correction. -/
theorem tropical_chart_original_gap (_hu : IsThetaPshPotential θ.val u)
    (_hφ : IsThetaPshPotential θ.val φ) (e : ComplexChart n M)
    (hequ : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (fu (tropicalization z) : EReal)) D)
    (heqφ : EqOn (fun z => chartFunction φ e z + (ρ z : EReal))
      (fun z => (fφ (tropicalization z) : EReal)) D)
    {z : ComplexModel n} (hz : z ∈ D) :
    u (e.val.symm z) - φ (e.val.symm z) =
      ((fu (tropicalization z) - fφ (tropicalization z) : ℝ) : EReal) := by
  have hu := hequ hz
  have hφ := heqφ hz
  change u (e.val.symm z) + (ρ z : EReal) = (fu (tropicalization z) : EReal) at hu
  change φ (e.val.symm z) + (ρ z : EReal) = (fφ (tropicalization z) : EReal) at hφ
  rw [recover_finite_corrected _ _ _ hu, recover_finite_corrected _ _ _ hφ, ← EReal.coe_sub]
  congr 1
  ring

/-- Actual independent native weight/reference and measure potentials have
exact integrability transport through their genuine original chart geometry. -/
theorem globalMixedMeasure_integrable_gap_iff_tropical
    (hu : IsThetaPshPotential θ.val u) (hφ : IsThetaPshPotential θ.val φ)
    (hv : IsThetaPshPotential θ.val v) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ)
    (hcu : ConvexOn ℝ univ fu) (hcφ : ConvexOn ℝ univ fφ) (hcv : ConvexOn ℝ univ fv)
    (hequ : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (fu (tropicalization z) : EReal)) D)
    (heqφ : EqOn (fun z => chartFunction φ e z + (ρ z : EReal))
      (fun z => (fφ (tropicalization z) : EReal)) D)
    (heqv : EqOn (fun z => chartFunction v e z + (ρ z : EReal))
      (fun z => (fv (tropicalization z) : EReal)) D)
    {w : M → EReal} (hw : IsGlobalQuasiPshPotential (n := n) w)
    (hpole : ((tropicalPotentialPatch e hρ hcv heqv).source : Set M)ᶜ ⊆ {x | w x = ⊥}) :
    Integrable (fun p => (u p - φ p).toReal)
      (GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1)) ↔
      Integrable (fun x => fu x - fφ x) (alexandrovMeasure B volume (fun x => (fv x : EReal))) := by
  let a : M → ℝ := fun p => (u p - φ p).toReal
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fu x - fφ x
  have ha : Measurable a :=
    (hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable.sub
      hφ.1.quasiPlurisubharmonic.upperSemicontinuous.measurable).ereal_toReal
  have hq : Continuous q :=
    (continuousOn_univ.mp (hcu.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (hcφ.continuousOn isOpen_univ))
  have hnorm : (∫⁻ p, ENNReal.ofReal ‖a p‖ ∂GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1)) =
      ∫⁻ x, ENNReal.ofReal ‖q x‖ ∂alexandrovMeasure B volume (fun x => (fv x : EReal)) := by
    apply globalMixedMeasure_lintegral_eq_tropical hv e hρ hcv heqv hw hpole _
      (ENNReal.measurable_ofReal.comp hq.norm.measurable)
    intro z hz
    dsimp only [a, q, Function.comp_def]
    rw [tropical_chart_original_gap hu hφ e hequ heqφ hz, EReal.toReal_coe]
  change Integrable a _ ↔ Integrable q _
  constructor
  · intro h
    refine ⟨hq.aestronglyMeasurable, (hasFiniteIntegral_iff_norm q).mpr ?_⟩
    rw [← hnorm]
    exact (hasFiniteIntegral_iff_norm a).mp h.2
  · intro h
    refine ⟨ha.aestronglyMeasurable, (hasFiniteIntegral_iff_norm a).mpr ?_⟩
    rw [hnorm]
    exact (hasFiniteIntegral_iff_norm q).mp h.2

/-- Genuine arbitrary-rank original native cross-input signed integration,
retaining the actual NP singular measure parts and genuine original values. -/
theorem globalMixedMeasure_integral_gap_eq_tropical
    (hu : IsThetaPshPotential θ.val u) (hφ : IsThetaPshPotential θ.val φ)
    (hv : IsThetaPshPotential θ.val v) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ)
    (hcu : ConvexOn ℝ univ fu) (hcφ : ConvexOn ℝ univ fφ) (hcv : ConvexOn ℝ univ fv)
    (hequ : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (fu (tropicalization z) : EReal)) D)
    (heqφ : EqOn (fun z => chartFunction φ e z + (ρ z : EReal))
      (fun z => (fφ (tropicalization z) : EReal)) D)
    (heqv : EqOn (fun z => chartFunction v e z + (ρ z : EReal))
      (fun z => (fv (tropicalization z) : EReal)) D)
    {w : M → EReal} (hw : IsGlobalQuasiPshPotential (n := n) w)
    (hpole : ((tropicalPotentialPatch e hρ hcv heqv).source : Set M)ᶜ ⊆ {x | w x = ⊥})
    (hint : Integrable (fun p => (u p - φ p).toReal)
      (GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1))) :
    (∫ p, (u p - φ p).toReal ∂GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1)) =
      ∫ x, (fu x - fφ x) ∂alexandrovMeasure B volume (fun x => (fv x : EReal)) := by
  let P := tropicalPotentialPatch e hρ hcv heqv
  let ν := tropicalCanonicalBTMeasure hcv
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fu x - fφ x
  have hs : ν (P.domain : Set (ComplexModel n))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hwhole : GlobalNonPluripolar.globalMixedMeasure (fun _ : Fin n => θ)
      (fun _ => v) (fun _ => hv.1) = P.pushMeasure ν :=
    globalMixedMeasure_eq_tropical_chart_pushMeasure hv e hρ hcv heqv hw hpole
  have hq : Integrable q (Measure.map tropicalization ν) := by
    rw [tropicalization_canonicalBTMeasure_eq_alexandrov hcv]
    exact (globalMixedMeasure_integrable_gap_iff_tropical hu hφ hv e hρ hcu hcφ hcv
      hequ heqφ heqv hw hpole).mp hint
  obtain ⟨hT, _⟩ := exists_compact_tropical_torus_lift (n := n) isCompact_empty
  calc
    _ = ∫ z, (u (e.val.symm z) - φ (e.val.symm z)).toReal ∂ν := by
      rw [hwhole]
      exact P.integral_pushMeasure hs _
    _ = ∫ z, q (tropicalization z) ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_iff.mpr hs] with z hz
      rw [tropical_chart_original_gap hu hφ e hequ heqφ hz, EReal.toReal_coe]
    _ = ∫ x, q x ∂Measure.map tropicalization ν :=
      (integral_map hT.aemeasurable hq.aestronglyMeasurable).symm
    _ = _ := by rw [tropicalization_canonicalBTMeasure_eq_alexandrov hcv]

/-- Original bounded growth and genuine support growth internally manufacture
both real and native signed integrability before consuming actual transport. -/
theorem globalMixedMeasure_integral_gap_eq_tropical_of_boundedGrowth
    (hu : IsThetaPshPotential θ.val u) (hφ : IsThetaPshPotential θ.val φ)
    (hv : IsThetaPshPotential θ.val v) (e : ComplexChart n M)
    (hρ : IsSmoothLocalPotential θ.val e D ρ)
    (hcu : ConvexOn ℝ univ fu) (hcφ : ConvexOn ℝ univ fφ) (hcv : ConvexOn ℝ univ fv)
    (hequ : EqOn (fun z => chartFunction u e z + (ρ z : EReal))
      (fun z => (fu (tropicalization z) : EReal)) D)
    (heqφ : EqOn (fun z => chartFunction φ e z + (ρ z : EReal))
      (fun z => (fφ (tropicalization z) : EReal)) D)
    (heqv : EqOn (fun z => chartFunction v e z + (ρ z : EReal))
      (fun z => (fv (tropicalization z) : EReal)) D)
    {w : M → EReal} (hw : IsGlobalQuasiPshPotential (n := n) w)
    (hpole : ((tropicalPotentialPatch e hρ hcv heqv).source : Set M)ᶜ ⊆ {x | w x = ⊥})
    {P : Set (EuclideanSpace ℝ (Fin n))} (hP : IsCompact P) (hconv : Convex ℝ P)
    (hfu : (fun x => (fu x : EReal)) ∈ BoundedGrowthClass B P)
    (hfφ : (fun x => (fφ x : EReal)) ∈ BoundedGrowthClass B P)
    (hfv : (fun x => (fv x : EReal)) ∈ GrowthClass B P) :
    (∫ p, (u p - φ p).toReal ∂GlobalNonPluripolar.globalMixedMeasure
      (fun _ : Fin n => θ) (fun _ => v) (fun _ => hv.1)) =
      ∫ x, (fu x - fφ x) ∂alexandrovMeasure B volume (fun x => (fv x : EReal)) := by
  have hν := isFiniteMeasure_tropicalCanonicalBTMeasure_of_mem_growthClass hcv hP hconv hfv
  have hfinite : IsFiniteMeasure (alexandrovMeasure B volume (fun x => (fv x : EReal))) := by
    rw [← tropicalization_canonicalBTMeasure_eq_alexandrov hcv]
    infer_instance
  obtain ⟨C, hC⟩ := boundedGrowthPair_exists_abs_sub_le
    (f := ⟨fφ, hcφ⟩) (g := ⟨fu, hcu⟩) hfφ hfu
  have hq : Continuous (fun x => fu x - fφ x) :=
    (continuousOn_univ.mp (hcu.continuousOn isOpen_univ)).sub
      (continuousOn_univ.mp (hcφ.continuousOn isOpen_univ))
  have hiq : Integrable (fun x => fu x - fφ x)
      (alexandrovMeasure B volume (fun x => (fv x : EReal))) :=
    Integrable.of_bound hq.aestronglyMeasurable C
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))
  have hin := (globalMixedMeasure_integrable_gap_iff_tropical hu hφ hv e hρ hcu hcφ hcv
    hequ heqφ heqv hw hpole).mpr hiq
  exact globalMixedMeasure_integral_gap_eq_tropical hu hφ hv e hρ hcu hcφ hcv
    hequ heqφ heqv hw hpole hin
end SGPT.Toric
