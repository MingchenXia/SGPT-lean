import SGPT.Trace.BertiniFamilyPhysicalChartIntegral
import SGPT.Trace.BertiniExactNormalCoordinates

/-! Actual source-subset and genuine flattening-coordinate physical energy. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical

open Bundle Set Filter TensorProduct MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Trace.Bertini SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniPencilNormal SGPT.Trace.OTMargin

private theorem actualChartImage_measurable {n : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : ComplexChart n Y) (A : Set Y) (hA : MeasurableSet A) (hs : A ⊆ e.val.source) :
    MeasurableSet (e.val '' A) := by
  let g : e.val.target → Y := fun z => e.val.symm z.val
  have hg : Continuous g := e.val.continuousOn_symm.domRestrict
  have hm := e.val.open_target.measurableSet.subtype_image (hA.preimage hg.measurable)
  have hset : e.val '' A = (Subtype.val : e.val.target → ComplexModel n) '' (g ⁻¹' A) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨e.val x, e.val.map_source (hs hx)⟩, ?_, rfl⟩
      change e.val.symm (e.val x) ∈ A
      rw [e.val.left_inv (hs hx)]
      exact hx
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.val.symm z.val, hz, e.val.right_inv z.property⟩
  rw [hset]
  exact hm

variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞)
  (i : Fin (N + 1)) (a v : ComplexModel N) (U : TopologicalSpace.Opens (ComplexModel 1))
  (hsm : ∀ t : U, IsSmoothHypersurfaceMember (d + 1) p (pencilParameter i a v t.val))
  (L : HermitianHolomorphicLineBundle (d + 1) X)

theorem familyPhysical_energy_in_chart_set :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (e : ComplexChart (d + 1) (familyIncidence p i a v U))
      (A : Set (familyIncidence p i a v U)) (_hA : MeasurableSet A) (_hs : A ⊆ e.val.source)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      (∫⁻ q in A, ENNReal.ofReal (‖S q‖ ^ 2) * w q ∂familyMatchedVolume p i a v U hsm) =
        ∫⁻ z in e.val '' A, familyPhysicalCoordinateDensity p i a v U hsm L e S w z ∂volume := by
  classical
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro e A hA hs S hS w hw
  let μ := familyMatchedVolume p i a v U hsm
  let K := e.val '' A
  let ρ := familyMatchedCoordinateDensity p i a v U hsm e
  let G : familyIncidence p i a v U → ℝ≥0∞ := fun q => ENNReal.ofReal (‖S q‖ ^ 2) * w q
  have hK : MeasurableSet K := actualChartImage_measurable e A hA hs
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨q, hq, rfl⟩
    exact e.val.map_source (hs hq)
  have hAK : e.val.source ∩ e.val ⁻¹' K = A := by
    ext q
    constructor
    · rintro ⟨hqs, x, hxA, heq⟩
      have hqx : q = x := e.val.injOn hqs (hs hxA) heq.symm
      rwa [hqx]
    · intro hqA
      exact ⟨hs hqA, q, hqA, rfl⟩
  have he : AEMeasurable e.val (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hr : (μ.restrict e.val.source).restrict (e.val ⁻¹' K) = μ.restrict A := by
    rw [Measure.restrict_restrict' e.val.open_source.measurableSet, inter_comm, hAK]
  have hmap : Measure.map e.val (μ.restrict A) =
      (volume.restrict K).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    have h := Measure.restrict_map_of_aemeasurable he hK
    rw [hr, familyMatchedVolume_chart p i a v U hsm e, restrict_withDensity hK,
      Measure.restrict_restrict hK, inter_eq_left.mpr hKt] at h
    exact h.symm
  have heA : AEMeasurable e.val (μ.restrict A) :=
    (e.val.continuousOn.mono hs).aemeasurable hA
  have hinv : AEMeasurable e.val.symm (volume.restrict K) :=
    (e.val.continuousOn_symm.mono hKt).aemeasurable hK
  have hG : Measurable G := (familyPhysical_normSq_measurable p i a v U hsm L S hS).mul hw
  have hGi := hG.comp_aemeasurable hinv
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict K) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((familyMatchedCoordinateDensity_smooth p i a v U hsm e).continuousOn.mono hKt)).aemeasurable hK
  have hGi' : AEMeasurable (fun z => G (e.val.symm z)) (Measure.map e.val (μ.restrict A)) := by
    rw [hmap]
    exact hGi.mono_ac (withDensity_absolutelyContinuous _ _)
  calc
    (∫⁻ q in A, G q ∂μ) = ∫⁻ q in A, G (e.val.symm (e.val q)) ∂μ := by
      apply setLIntegral_congr_fun hA
      intro q hq
      dsimp only
      rw [e.val.left_inv (hs hq)]
    _ = ∫⁻ z, G (e.val.symm z) ∂Measure.map e.val (μ.restrict A) := (lintegral_map' hGi' heA).symm
    _ = ∫⁻ z in K, ENNReal.ofReal (ρ z) * G (e.val.symm z) ∂volume := by
      rw [hmap]
      exact lintegral_withDensity_eq_lintegral_mul₀ hρ hGi
    _ = ∫⁻ z in K, familyPhysicalCoordinateDensity p i a v U hsm L e S w z ∂volume := by
      apply setLIntegral_congr_fun hK
      intro z hz
      have hzt := hKt hz
      dsimp only [G]
      unfold familyPhysicalCoordinateDensity
      rw [dif_pos hzt, ← mul_assoc, ← ENNReal.ofReal_mul
        (familyMatchedCoordinateDensity_pos p i a v U hsm e z hzt).le]
      congr 1
      apply congrArg ENNReal.ofReal
      have h := familyPhysicalCoordinate_norm_density p i a v U hsm L e
        (e.val.symm z) (e.val.map_target hzt) (S (e.val.symm z))
      unfold familyMatchedCoordinateDensity
      rw [dif_pos hzt, mul_comm]
      exact h

def familyNormalPhysicalDensity :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)}, FlatData (d + 1) d (familyIncidence p i a v U) W →
      (∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q) →
      (familyIncidence p i a v U → ℝ≥0∞) → ComplexModel (d + 1) → ℝ≥0∞ := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S w z
  exact ENNReal.ofReal |(fderiv ℝ F.flat.symm z).det| *
    familyPhysicalCoordinateDensity p i a v U hsm L F.amb S w (F.flat.symm z)

theorem familyPhysical_energy_in_flatData :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ {W : Set (familyIncidence p i a v U)} (F : FlatData (d + 1) d (familyIncidence p i a v U) W)
      (S : ∀ q, (familyNativePhysicalModel p i a v U hsm L).Fiber q),
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := d + 1)
        (familyNativePhysicalModel p i a v U hsm L).Fiber S univ →
      ∀ (w : familyIncidence p i a v U → ℝ≥0∞), Measurable w →
      (∫⁻ q in F.ambSource, ENNReal.ofReal (‖S q‖ ^ 2) * w q ∂familyMatchedVolume p i a v U hsm) =
        ∫⁻ z in F.flat.target, familyNormalPhysicalDensity p i a v U hsm L F S w z ∂volume := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro W F S hS w hw
  have h := familyPhysical_energy_in_chart_set p i a v U hsm L F.amb F.ambSource
    F.isOpen_ambSource.measurableSet (fun _ hx => hx.1) S hS w hw
  have himage : F.amb.val '' F.ambSource = F.flat.source := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq.2
    · intro hy
      refine ⟨F.amb.val.symm y, ⟨F.amb.val.map_target (F.flat_source_subset hy), ?_⟩,
        F.amb.val.right_inv (F.flat_source_subset hy)⟩
      change F.amb.val (F.amb.val.symm y) ∈ F.flat.source
      rwa [F.amb.val.right_inv (F.flat_source_subset hy)]
  rw [himage] at h
  apply h.trans
  have hderiv : ∀ z ∈ F.flat.target, HasFDerivWithinAt F.flat.symm (fderiv ℝ F.flat.symm z) F.flat.target z := by
    intro z hz
    exact (((F.differentiableOn_flat_symm.differentiableAt (F.flat.open_target.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt).hasFDerivWithinAt
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume F.flat.open_target.measurableSet
    hderiv F.flat.symm.injOn (familyPhysicalCoordinateDensity p i a v U hsm L F.amb S w)
  have hrev : F.flat.symm '' F.flat.target = F.flat.source := F.flat.symm.image_source_eq_target
  rw [hrev] at hc
  exact hc

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem exists_actual_parameter_normal_flatData :
    letI := familyChartedSpace p i a v U p.contMDiff hsm
    letI := isComplexManifold_family p i a v U p.contMDiff hsm
    ∀ (q : familyIncidence p i a v U), scalarParameter p i a v U q = 0 →
      ∃ F : FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0},
        q ∈ F.ambSource ∧ fcoord F q = 0 ∧
        (∀ y ∈ F.ambSource, fcoord F y (Fin.last d) = scalarParameter p i a v U y) ∧
        ∀ z ∈ F.flat.target, scalarParameter p i a v U (finv F z) = z (Fin.last d) := by
  let := familyChartedSpace p i a v U p.contMDiff hsm
  let := isComplexManifold_family p i a v U p.contMDiff hsm
  intro q hq
  obtain ⟨_hn, F, hsrc, hzero, hnormal⟩ := SGPT.Trace.BertiniExactNormalCoordinates.exists_exact_normal_flatData
    (contMDiff_scalarParameter p i a v U p.contMDiff hsm)
    (surjective_mfderiv_scalarParameter p i a v U p.contMDiff hsm q) hq
  change FlatData (d + 1) d (familyIncidence p i a v U) {y | scalarParameter p i a v U y = 0} at F
  refine ⟨F, hsrc, hzero, ?_, ?_⟩
  · intro y hy
    exact hnormal y hy
  · intro z hz
    exact SGPT.Trace.BertiniExactNormalCoordinates.exact_normal_inverse hnormal hz

end SGPT.Trace.BertiniFamilyCanonical
