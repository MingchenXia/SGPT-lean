import SGPT.Toric.ScalarPuncturedBedfordTaylor
import SGPT.Toric.ProjectiveToricNewtonGeometry
import SGPT.Toric.ProjectiveLogLogPuncturedPatch
import SGPT.Toric.ProjectiveToricModelEnvelope

set_option autoImplicit false
noncomputable section

namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere MongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedMongeAmpere
open scoped Topology ContDiff

local notation "P1" => Projectivization ℂ (Fin 2 → ℂ)

/-- The literal scalar descent is defined from the original function alone. -/
def projectiveToricScalarProfile (u : P1 → EReal) (x : ℝ) : ℝ :=
  (projectiveToricCorrectedDescent u (WithLp.toLp 2 (fun _ : Fin 1 => x))).toReal

theorem projectiveToricScalarProfile_convex {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    ConvexOn ℝ univ (projectiveToricScalarProfile u) := by
  obtain ⟨f, hf, heq⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  let e : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => WithLp.toLp 2 (fun _ => x)
  have hH (x : ℝ) : projectiveToricScalarProfile u x = f (e x) := by
    simp only [projectiveToricScalarProfile, heq, EReal.toReal_coe, e]
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have he : a • e x + b • e y = e (a * x + b * y) := by
    ext i
    simp [e, PiLp.add_apply, PiLp.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, hH, hH, hH, ← he]
  exact hf.2 (mem_univ _) (mem_univ _) ha hb hab

theorem projectiveToricScalarProfile_corrected {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) {z : ComplexModel 1} (hz : z ∈ complexTorus 1) :
    u ((projectiveModelChart false).symm z) + (projectiveFSPotential z : EReal) =
      (projectiveToricScalarProfile u (Real.log (‖z 0‖ ^ 2)) : EReal) := by
  obtain ⟨f, _hf, heq⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  have ht : tropicalization z =
      WithLp.toLp 2 (fun _ : Fin 1 => Real.log (‖z 0‖ ^ 2)) := by
    ext i
    have hi0 : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    exact tropicalization_apply_eq_log_norm_sq z 0
  calc
    _ = projectiveToricCorrectedDescent u (tropicalization z) :=
      (projectiveToricCorrectedDescent_tropicalPullback hi hz).symm
    _ = (f (tropicalization z) : EReal) := congrFun heq _
    _ = _ := by
      rw [ht]
      simp only [projectiveToricScalarProfile, heq, EReal.toReal_coe]

/-- The same original native diagonal constructor, with no radial definition. -/
def projectiveToricNonPluripolarMeasure {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) : Measure P1 :=
  DiagonalMass.diagonalPotentialMeasure projectiveNativeFSBackground.form u
    (isThetaPshPotential_projectiveNativeFS_of_source hu)

theorem isFiniteMeasure_projectiveToricNonPluripolarMeasure {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    IsFiniteMeasure (projectiveToricNonPluripolarMeasure hu) :=
  DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    projectiveNativeFSBackground projectiveNativeFSBackground.form
    (isThetaPshPotential_projectiveNativeFS_of_source hu)

/-- Genuine OTHER original section poles make both boundary points null for every u. -/
theorem projectiveToricNonPluripolarMeasure_boundary {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    projectiveToricNonPluripolarMeasure hu projectiveToricBoundary = 0 := by
  let μ := projectiveToricNonPluripolarMeasure hu
  have hpole {v : P1 → EReal}
      (hv : projectiveLineAtlas.IsThetaPSH projectiveFSForm v) :
      μ {p | v p = ⊥} = 0 := by
    simpa only [μ, projectiveToricNonPluripolarMeasure,
      DiagonalMass.diagonalPotentialMeasure] using
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (θ := fun _ : Fin 1 => projectiveNativeFSBackground.form)
        (u := fun _ => u)
        (fun _ => (isThetaPshPotential_projectiveNativeFS_of_source hu).1)
        (isThetaPshPotential_projectiveNativeFS_of_source hv)
  have h0 : μ {projectiveOrigin} = 0 := by
    apply measure_mono_null _ (hpole isThetaPSH_projectiveLogSingularity)
    intro p hp
    have he := mem_singleton_iff.mp hp
    subst p
    exact projectiveLogSingularity_origin
  have hinfty : μ {projectiveInfinity} = 0 := by
    apply measure_mono_null _ (hpole isThetaPSH_projectiveOppositeLogSingularity)
    intro p hp
    have he := mem_singleton_iff.mp hp
    subst p
    exact projectiveOppositeLogSingularity_infinity
  have hB : projectiveToricBoundary = {projectiveOrigin} ∪ {projectiveInfinity} := by
    ext p
    simp [projectiveToricBoundary, or_comm]
  change μ projectiveToricBoundary = 0
  rw [hB]
  apply le_antisymm _ zero_le
  calc
    _ ≤ μ {projectiveOrigin} + μ {projectiveInfinity} := measure_union_le _ _
    _ = 0 := by rw [h0, hinfty, add_zero]

/-- Actual preferred-FS patch for the same arbitrary original source function. -/
def projectiveToricPuncturedPatch {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    Patch (fun _ : Fin 1 => projectiveNativeFSBackground.form) (fun _ => u) where
  chart := projectiveNativeChart false
  domain := scalarPuncturedBTDomain
  domain_le_target := by
    intro z _
    change z ∈ (projectiveModelChart false).target
    simp [projectiveModelChart, projectiveQuotientScalarChart_target]
  potential := fun _ => projectiveFSPotential
  localPotential := fun _ => ⟨scalarPuncturedBTDomain.isOpen, by
    intro z _
    change z ∈ (projectiveModelChart false).target
    simp [projectiveModelChart, projectiveQuotientScalarChart_target],
    contDiff_projectiveFSPotential.contDiffOn, fun _ _ => rfl⟩
  plurisubharmonic := by
    intro _
    change PlurisubharmonicOn
      (fun z => u ((projectiveModelChart false).symm z) +
        (projectiveFSPotential z : EReal)) scalarPuncturedBTDomain
    have hp := hu.preferred_chart_corrected false
      contDiff_projectiveFSPotential.contDiffOn (fun _ _ => rfl)
    change PlurisubharmonicOn
      (fun z : ComplexModel 1 => u ((projectiveModelChart false).symm z) +
        (projectiveFSPotential z : EReal)) (projectiveModelChart false).target at hp
    exact hp.mono (by
      intro z _
      simp [projectiveModelChart, projectiveQuotientScalarChart_target])

theorem projectiveToricPuncturedPatch_source {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u) :
    ((projectiveToricPuncturedPatch hu).source : Set P1) = projectiveToricBoundaryᶜ := by
  change (projectiveLogLogPuncturedPatch.source : Set P1) = projectiveToricBoundaryᶜ
  exact projectiveLogLogPuncturedPatch_source

/-- Actual original NP truncation agrees with the generic genuine scalar BT construction. -/
theorem projectiveToricNonPluripolarMeasure_restrict_punctured {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    (projectiveToricNonPluripolarMeasure hu).restrict projectiveToricBoundaryᶜ =
      (projectiveToricPuncturedPatch hu).pushMeasure
        (scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)) := by
  rw [← projectiveToricPuncturedPatch_source hu]
  change (GlobalNonPluripolar.globalMixedMeasure
    (fun _ : Fin 1 => projectiveNativeFSBackground.form) (fun _ => u)
    (fun _ => (isThetaPshPotential_projectiveNativeFS_of_source hu).1)).restrict _ = _
  rw [GlobalNonPluripolar.globalMixedMeasure_restrict_patch]
  unfold GlobalNonPluripolar.patchMeasure
  apply congrArg (projectiveToricPuncturedPatch hu).pushMeasure
  exact MixedNonPluripolar.mixedTruncationLimitMeasure_eq_canonical_of_eqOn
    (fun _ => isLocallyBoundedPshOn_scalarPuncturedProfile
      (projectiveToricScalarProfile_convex hu hi))
    (projectiveToricPuncturedPatch hu).plurisubharmonic
    (fun _ z hz => by
      change u ((projectiveModelChart false).symm z) + (projectiveFSPotential z : EReal) = _
      simpa only [scalarPuncturedProfile, tropicalization_apply_eq_log_norm_sq]
        using projectiveToricScalarProfile_corrected hu hi hz)

/-- The global equality uses genuine boundary nullity and the common full BT producer. -/
theorem projectiveToricNonPluripolarMeasure_eq_push_scalarRadial {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNonPluripolarMeasure hu =
      (projectiveToricPuncturedPatch hu).pushMeasure
        (Measure.map projectiveModelEquiv
          (scalarAlexandrovRadialMeasure (projectiveToricScalarProfile u))) := by
  have ha : ∀ᵐ p ∂projectiveToricNonPluripolarMeasure hu,
      p ∈ projectiveToricBoundaryᶜ := by
    apply ae_iff.mpr
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using
      projectiveToricNonPluripolarMeasure_boundary hu
  calc
    _ = (projectiveToricNonPluripolarMeasure hu).restrict projectiveToricBoundaryᶜ :=
      (Measure.restrict_eq_self_of_ae_mem ha).symm
    _ = (projectiveToricPuncturedPatch hu).pushMeasure
        (scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)) :=
      projectiveToricNonPluripolarMeasure_restrict_punctured hu hi
    _ = _ := congrArg (projectiveToricPuncturedPatch hu).pushMeasure
      (scalarCanonicalBT_eq_map_radial (projectiveToricScalarProfile_convex hu hi))

private def projectiveNPScalarCoordinate : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

private theorem projectiveNPScalarCoordinate_apply (x : ℝ) (i : Fin 1) :
    projectiveNPScalarCoordinate x i = x := by
  exact OrthonormalBasis.singleton_repr x i

private theorem projectiveNPScalarCoordinate_inverse (x : EuclideanSpace ℝ (Fin 1)) :
    projectiveNPScalarCoordinate (x 0) = x := by
  ext i
  rw [projectiveNPScalarCoordinate_apply, Fin.eq_zero i]

private theorem projectiveNPScalarCoordinate_volume_image (S : Set ℝ) :
    volume (projectiveNPScalarCoordinate '' S) = volume S := by
  change volume (projectiveNPScalarCoordinate.toHomeomorph '' S) = volume S
  rw [← projectiveNPScalarCoordinate.toHomeomorph.preimage_symm]
  exact projectiveNPScalarCoordinate.symm.measurePreserving.measure_preimage_emb
    projectiveNPScalarCoordinate.symm.toHomeomorph.measurableEmbedding S

private theorem projectiveNPInner_coordinate (x m : EuclideanSpace ℝ (Fin 1)) :
    innerₗ (EuclideanSpace ℝ (Fin 1)) x m = x 0 * m 0 := by
  simp [innerₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

private theorem projectiveNPDescent_scalar {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (x : EuclideanSpace ℝ (Fin 1)) :
    projectiveToricCorrectedDescent u x = (projectiveToricScalarProfile u (x 0) : EReal) := by
  obtain ⟨f, _hf, heq⟩ := exists_real_convex_projectiveToricCorrectedDescent hu hi
  have hx : WithLp.toLp 2 (fun _ : Fin 1 => x 0) = x := by
    ext i
    rw [Fin.eq_zero i]
  simp only [projectiveToricScalarProfile, hx, heq, EReal.toReal_coe]

private theorem projectiveNPRawSubgradient_coordinate {h : ℝ → ℝ}
    (x m : EuclideanSpace ℝ (Fin 1)) :
    m ∈ rawSubdifferential (innerₗ (EuclideanSpace ℝ (Fin 1)))
      (fun y => (h (y 0) : EReal)) x ↔
    m 0 ∈ rawSubdifferential scalarPairing (fun y => (h y : EReal)) (x 0) := by
  change (∀ y, (h (x 0) : EReal) +
      (innerₗ (EuclideanSpace ℝ (Fin 1)) (y - x) m : EReal) ≤ (h (y 0) : EReal)) ↔ _
  simp only [projectiveNPInner_coordinate, PiLp.sub_apply]
  constructor
  · intro hm y
    simpa only [projectiveNPScalarCoordinate_apply, scalarPairing, LinearMap.mul_apply']
      using hm (projectiveNPScalarCoordinate y)
  · intro hm y
    simpa only [scalarPairing, LinearMap.mul_apply'] using hm (y 0)

private theorem projectiveNPRawImage_coordinate {h : ℝ → ℝ}
    (A : Set (EuclideanSpace ℝ (Fin 1))) :
    rawSubgradientImageOn (innerₗ (EuclideanSpace ℝ (Fin 1)))
      (fun y => (h (y 0) : EReal)) A =
    projectiveNPScalarCoordinate '' rawSubgradientImageOn scalarPairing
      (fun y => (h y : EReal)) (projectiveNPScalarCoordinate ⁻¹' A) := by
  ext m
  constructor
  · intro hm
    obtain ⟨x, hx⟩ := mem_iUnion.mp hm
    obtain ⟨hxA, hxm⟩ := mem_iUnion.mp hx
    refine ⟨m 0, mem_iUnion.mpr ⟨x 0, mem_iUnion.mpr ⟨?_, ?_⟩⟩,
      projectiveNPScalarCoordinate_inverse m⟩
    · change projectiveNPScalarCoordinate (x 0) ∈ A
      rwa [projectiveNPScalarCoordinate_inverse]
    · exact (projectiveNPRawSubgradient_coordinate x m).mp hxm
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := mem_iUnion.mp ht
    obtain ⟨hxA, hxt⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨projectiveNPScalarCoordinate x, mem_iUnion.mpr ⟨hxA, ?_⟩⟩
    apply (projectiveNPRawSubgradient_coordinate _ _).mpr
    simpa only [projectiveNPScalarCoordinate_apply] using hxt

/-- Genuine coordinate covariance of the original Borel raw-image measure, for every finite h. -/
private theorem projectiveNPScalarAlexandrov_coordinate {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) :
    Measure.map projectiveNPScalarCoordinate
      (alexandrovMeasure scalarPairing volume (fun x => (h x : EReal))) =
    alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin 1))) volume
      (fun x => (h (x 0) : EReal)) := by
  have hf : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin 1) => h (x 0)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      hc.2 (mem_univ (x 0)) (mem_univ (y 0)) ha hb hab
  ext A hA
  rw [Measure.map_apply projectiveNPScalarCoordinate.continuous.measurable hA,
    alexandrovMeasure_apply_coe scalarPairing hc
      (hA.preimage projectiveNPScalarCoordinate.continuous.measurable),
    alexandrovMeasure_apply_coe (innerₗ (EuclideanSpace ℝ (Fin 1))) hf hA,
    projectiveNPRawImage_coordinate, projectiveNPScalarCoordinate_volume_image]
  simp

private theorem projectiveNPMeasurable_tropicalization :
    Measurable (tropicalization : ComplexModel 1 → EuclideanSpace ℝ (Fin 1)) := by
  unfold tropicalization
  apply (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul
    (Real.measurable_log.comp (PiLp.continuous_apply 2 _ i).measurable.norm)

/-- The printed tropical formula has the original Euclidean Alexandrov measure on its RHS. -/
theorem projectiveToricCanonicalBT_tropicalPushforward {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    Measure.map tropicalization
      (scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)) =
    alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin 1))) volume
      (projectiveToricCorrectedDescent u) := by
  let H := projectiveToricScalarProfile u
  let μ := alexandrovMeasure scalarPairing volume (fun x => (H x : EReal))
  let : IsLocallyFiniteMeasure μ :=
    isLocallyFiniteMeasure_alexandrovMeasure_coe scalarPairing
      (projectiveToricScalarProfile_convex hu hi)
  have hm := projectiveNPMeasurable_tropicalization
  have he : (tropicalization ∘ projectiveModelEquiv) ∘ logLogRadialPoint =
      projectiveNPScalarCoordinate ∘ Prod.fst := by
    funext p
    ext i
    rw [Fin.eq_zero i]
    simp only [Function.comp_apply, tropicalization_apply_eq_log_norm_sq,
      projectiveModelEquiv_apply_zero, projectiveNPScalarCoordinate_apply,
      norm_logLogRadialPoint]
    rw [← Real.exp_nat_mul]
    have he2 : ((2 : ℕ) : ℝ) * (p.1 / 2) = p.1 := by norm_num; ring
    rw [he2, Real.log_exp]
  have hmap : Measure.map tropicalization
      (scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)) =
      Measure.map projectiveNPScalarCoordinate μ := by
    rw [scalarCanonicalBT_eq_map_radial, scalarAlexandrovRadialMeasure,
      Measure.map_map hm projectiveModelEquiv.continuous.measurable,
      Measure.map_map (hm.comp projectiveModelEquiv.continuous.measurable)
        continuous_logLogRadialPoint.measurable, he,
      ← Measure.map_map projectiveNPScalarCoordinate.continuous.measurable measurable_fst,
      Measure.map_fst_prod, logLogAngularMeasure_univ, one_smul]
  rw [hmap, projectiveNPScalarAlexandrov_coordinate (projectiveToricScalarProfile_convex hu hi)]
  congr 1
  funext x
  exact (projectiveNPDescent_scalar hu hi x).symm

/-- Literal all-cost Euclidean Legendre transform, with both infinities retained. -/
theorem projectiveToricLegendre_scalarProfile {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) (m : EuclideanSpace ℝ (Fin 1)) :
    projectiveToricLegendre u m = conjugate scalarPairing
      (fun x => (projectiveToricScalarProfile u x : EReal)) (m 0) := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin 1) => x 0) := by
    intro x
    exact ⟨projectiveNPScalarCoordinate x, projectiveNPScalarCoordinate_apply x 0⟩
  calc
    _ = ⨆ x : EuclideanSpace ℝ (Fin 1),
        ((x 0 * m 0 : ℝ) : EReal) - (projectiveToricScalarProfile u (x 0) : EReal) := by
      unfold projectiveToricLegendre conjugate
      congr 1
      funext x
      rw [projectiveNPInner_coordinate, projectiveNPDescent_scalar hu hi]
    _ = _ := by
      simpa only [conjugate, scalarPairing, LinearMap.mul_apply'] using
        hsurj.iSup_comp (fun x : ℝ =>
          ((x * m 0 : ℝ) : EReal) - (projectiveToricScalarProfile u x : EReal))

/-- True closure transport of the entire original finite Legendre domain. -/
theorem projectiveToricNewtonBody_scalarProfile {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNewtonBody u =
      (fun x : ℝ => WithLp.toLp 2 (fun _ : Fin 1 => x)) '' closure
        (effectiveDomain (conjugate scalarPairing
          (fun x => (projectiveToricScalarProfile u x : EReal)))) := by
  let C := effectiveDomain (conjugate scalarPairing
    (fun x => (projectiveToricScalarProfile u x : EReal)))
  have hd : effectiveDomain (projectiveToricLegendre u) =
      projectiveNPScalarCoordinate '' C := by
    ext m
    constructor
    · intro hm
      refine ⟨m 0, ?_, projectiveNPScalarCoordinate_inverse m⟩
      change conjugate scalarPairing
        (fun x => (projectiveToricScalarProfile u x : EReal)) (m 0) < ⊤
      rwa [← projectiveToricLegendre_scalarProfile hu hi]
    · rintro ⟨x, hx, rfl⟩
      change projectiveToricLegendre u (projectiveNPScalarCoordinate x) < ⊤
      rw [projectiveToricLegendre_scalarProfile hu hi,
        projectiveNPScalarCoordinate_apply]
      exact hx
  have he : (projectiveNPScalarCoordinate : ℝ → EuclideanSpace ℝ (Fin 1)) =
      fun x => WithLp.toLp 2 (fun _ : Fin 1 => x) := by
    funext x
    ext i
    exact projectiveNPScalarCoordinate_apply x i
  calc
    _ = closure (projectiveNPScalarCoordinate '' C) := by
      rw [projectiveToricNewtonBody, convexNewtonBody, hd]
    _ = projectiveNPScalarCoordinate '' closure C :=
      (projectiveNPScalarCoordinate.toHomeomorph.image_closure C).symm
    _ = _ := by rw [he]

/-- The actual original NP measure has the literal original Newton length. -/
theorem projectiveToricNonPluripolarMeasure_univ_eq_newtonLength {u : P1 → EReal}
    (hu : projectiveLineAtlas.IsThetaPSH projectiveFSForm u)
    (hi : ProjectiveCircleInvariant u) :
    projectiveToricNonPluripolarMeasure hu univ = volume (projectiveToricNewtonBody u) := by
  let ν := scalarCanonicalBTMeasure (projectiveToricScalarProfile_convex hu hi)
  have hν0 : ν (scalarPuncturedBTDomain : Set (ComplexModel 1))ᶜ = 0 :=
    canonicalMixedBedfordTaylorMeasure_compl _ _ _
  have hνr : ν.restrict scalarPuncturedBTDomain = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hν0)
  have hf := projectiveToricCorrectedDescent_mem_growthClass hu hi
  have hlsc := lowerSemicontinuous_of_isClosedConvex
    (isClosedConvex_of_mem_growthClass _ isCompact_projectiveMomentInterval
      nonempty_projectiveMomentInterval hf)
  calc
    _ = ν scalarPuncturedBTDomain := by
      rw [projectiveToricNonPluripolarMeasure_eq_push_scalarRadial hu hi,
        ← scalarCanonicalBT_eq_map_radial (projectiveToricScalarProfile_convex hu hi),
        (projectiveToricPuncturedPatch hu).pushMeasure_apply]
      simp only [preimage_univ, inter_univ]
      rfl
    _ = (ν.restrict scalarPuncturedBTDomain) univ := (Measure.restrict_apply_univ _).symm
    _ = ν univ := by rw [hνr]
    _ = (Measure.map tropicalization ν) univ := by
      rw [Measure.map_apply projectiveNPMeasurable_tropicalization MeasurableSet.univ,
        preimage_univ]
    _ = alexandrovMeasure (innerₗ (EuclideanSpace ℝ (Fin 1))) volume
        (projectiveToricCorrectedDescent u) univ := by
      rw [projectiveToricCanonicalBT_tropicalPushforward hu hi]
    _ = volume (projectiveToricNewtonBody u) := by
      rw [alexandrovMeasure_univ_eq_closure_rawSubgradientImage _ hf.1 hlsc,
        ← projectiveToricNewtonBody_eq_closure_rawSubgradientImage hu hi]
      simp

/-- Exact normalized reference mass on the original P1/FS quotient. -/
theorem projectiveToricNonPluripolarMeasure_zero_univ :
    projectiveToricNonPluripolarMeasure isThetaPSH_projectiveZero univ = 1 := by
  have hi : ProjectiveCircleInvariant (fun _ : P1 => (0 : EReal)) := fun _ _ _ => rfl
  rw [projectiveToricNonPluripolarMeasure_univ_eq_newtonLength isThetaPSH_projectiveZero hi,
    projectiveToricNewtonBody_zero]
  have hI : projectiveNPScalarCoordinate '' Icc (0 : ℝ) 1 = projectiveMomentInterval := by
    ext m
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [projectiveMomentInterval, mem_ofPred_eq, mem_Icc,
        projectiveNPScalarCoordinate_apply] using hx
    · intro hm
      exact ⟨m 0, hm, projectiveNPScalarCoordinate_inverse m⟩
  rw [← hI, projectiveNPScalarCoordinate_volume_image, Real.volume_Icc]
  norm_num

end SGPT.Toric
