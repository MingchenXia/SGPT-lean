import SGPT.Okounkov.OF12NormalProjectiveExistence
import SGPT.Okounkov.OF12ProjectiveFieldDimension
import SGPT.Okounkov.OF14IntrinsicModification
import SGPT.Unibranch.KS3KahlerResolution
import SGPT.Unibranch.CHPrimeRealization
import SGPT.Unibranch.OriginalProperBimeromorphicNative
import SGPT.Unibranch.HironakaG10MwRemmertTheorem
import SGPT.Unibranch.EmbeddedCommonResolutionGeneralAnalyticSubsets
import SGPT.Projective.OkoNov16OriginalRestrictedGoodInverse

/-! Algebraize a native projective terminal stage while retaining its actual finite modification. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SGPT.Okounkov.OF12

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Unibranch SGPT.Unibranch.SourceReducedComplexSpace
open SGPT.Unibranch.OriginalNativeModification SGPT.Unibranch.SmoothCentreModification
open SGPT.Projective SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.BDivisor.GM
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra SGPT.Toric.monomialProjectiveTopology

local instance stagePointTopology {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint g) := schemeAnalyticPointTopology g

local instance stagePointCharts {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] : ChartedSpace (ComplexModel n) (SchemeComplexPoint g) :=
  schemeAnalyticTNChartedSpace g n

local instance stagePointManifold {A : Scheme.{0}} (g : A ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n g] [IsSeparated g] [QuasiCompact g] :
    IsComplexManifold n (SchemeComplexPoint g) := schemeAnalyticTN_isComplexManifold g n

private def stageWholeModelIso {n : ℕ} {M N : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel n) N] [IsComplexManifold n N]
    (e : M ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ N) :
    wholeModel (n := n) M ≅ wholeModel (n := n) N where
  hom := nativeMorphism e.contMDiff
  inv := nativeMorphism e.symm.contMDiff
  hom_inv_id := by
    apply morphism_eq_of_pointwise_eq
    intro z
    exact Subtype.ext (e.symm_apply_apply z.val)
  inv_hom_id := by
    apply morphism_eq_of_pointwise_eq
    intro z
    exact Subtype.ext (e.apply_symm_apply z.val)

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  [IsSeparated f] [QuasiCompact f] [LocallyOfFiniteType f]

omit [IsIntegral X] in
private theorem exists_projectiveAmbientAnalyticMap (E : ClosedProjectiveEmbedding f) :
    ∃ J : UnibAn.analytification f ⟶
      wholeModel (n := E.ambientDimension) (ComplexProjectiveSpace E.ambientDimension),
      ∀ x : (UnibAn.analytification f).obj.left,
        (J.hom.left.base x).val = ambientPoint E (UnibAn.pointMap f x) := by
  let d := E.ambientDimension
  let g := polynomialProjStructureMap ℂ d
  let P := SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint.identityEmbedding d
  let : IsSeparated g := P.isSeparated
  let : QuasiCompact g := P.quasiCompact
  let : LocallyOfFiniteType g := P.locallyOfFiniteType
  let : SmoothOfRelativeDimension d g := inferInstanceAs
    (SmoothOfRelativeDimension d (polynomialProjStructureMap ℂ d))
  obtain ⟨I, hI⟩ := UnibAn.exists_smoothModel_analytification_iso g d
  let i : UnibAn.analytification f ⟶ UnibAn.analytification g :=
    UnibAn.analytificationMorphism E.map E.over_base
  let F : UnibAn.analytification f ⟶ wholeModel (n := d) (SchemeComplexPoint g) := i ≫ I.inv
  have hpoint (x : (UnibAn.analytification f).obj.left) :
      (F.hom.left.base x).val = schemeComplexPointMap f g E.map E.over_base (UnibAn.pointMap f x) := by
    change (I.inv.hom.left.base (i.hom.left.base x)).val = _
    exact (UnibAn.smoothIso_inv_point I hI _).trans
      (UnibAn.pointMap_analytificationMorphism E.map E.over_base _)
  have hread (z : SchemeComplexPoint g) :
      projectivePoint g P d z = originalProjectiveHomeomorph d z := by
    rw [← ambientPoint_eq_projectivePoint P d z]
    change originalProjectiveHomeomorph d (schemeComplexPointMap g g (𝟙 _) P.over_base z) = _
    apply congrArg (originalProjectiveHomeomorph d)
    exact Subtype.ext (Category.comp_id z.val)
  have hhol := SGPT.GAGA.SmoothFlags.contMDiff_of_isHolomorphicEmbedding
    (isHolomorphicEmbedding_projectivePoint g P d)
  refine ⟨F ≫ nativeMorphism hhol, fun x => ?_⟩
  change projectivePoint g P d (F.hom.left.base x).val = _
  rw [hread, hpoint]
  rfl

omit [IsIntegral X] in
private theorem stage_projection_to_projective_contMDiff
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] (E : ClosedProjectiveEmbedding f)
    (p : wholeModel (n := n) M ⟶ UnibAn.analytification f) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel E.ambientDimension) ∞
      (fun y : M => ambientPoint E (UnibAn.pointMap f (p.hom.left.base ⟨y, mem_univ y⟩))) := by
  obtain ⟨J, hJ⟩ := exists_projectiveAmbientAnalyticMap E
  convert OriginalProperBimeromorphicNative.nativePointMap_contMDiff (p ≫ J) using 1
  funext y
  exact (hJ _).symm

omit [IsIntegral X] in
/-- Chow's theorem recovers the literal algebraic trace of an intrinsic analytic
subset on the original projective analytification. -/
theorem exists_original_closed_trace_of_projectiveAnalyticSubset
    (E : ClosedProjectiveEmbedding f) {A : Set (UnibAn.analytification f).obj.left}
    (hA : (UnibAn.analytification f).IsAnalyticSubset A) :
    ∃ Z : Set X, IsClosed Z ∧ A = (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z := by
  obtain ⟨J, hJ⟩ := exists_projectiveAmbientAnalyticMap E
  let d := E.ambientDimension
  let T := ComplexProjectiveSpace d
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have hC : CompactSpace (UnibAn.analytification f).obj.left :=
    (UnibAn.pointHomeomorph f).symm.compactSpace
  have hT : T2Space (wholeModel (n := d) T).obj.left := by
    change T2Space (↥(univ : Set T))
    infer_instance
  have hp : IsProperMap J.hom.left.base :=
    @Continuous.isProperMap _ _ _ _ _ hC hT J.hom.left.base.hom.continuous
  have hJS := HironakaG10MwRemmertTheorem.isAnalyticSubset_image_of_isProperMap J hp hA
  have hC' : IsComplexAnalyticSubset (n := d)
      ((Subtype.val : ↥(univ : Set T) → T) '' (J.hom.left.base '' A)) :=
    isComplexAnalyticSubset_image_of_isAnalyticSubset_closedAnalytic hJS
  obtain ⟨Z, hZ, htrace⟩ := exists_closed_trace_of_ambient_analyticSubset E hC'
  refine ⟨Z, hZ, Set.ext fun x => ?_⟩
  change x ∈ A ↔ schemeComplexPointImage f (UnibAn.pointMap f x) ∈ Z
  rw [htrace, ← hJ x]
  constructor
  · intro hx
    exact ⟨J.hom.left.base x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, heq⟩
    rw [hJ w, hJ x] at heq
    have : w = x := UnibAn.pointMap_injective (ambientPoint_injective E heq)
    exact this ▸ hw

omit [IsIntegral X] in
private theorem stage_restrict_bijective
    {Y : Scheme.{0}} (ρ : Y ⟶ X) [Nonempty (SchemeComplexPoint (ρ ≫ f))]
    {A : SourceReducedComplexSpace} (p : A ⟶ UnibAn.analytification f)
    (e : SchemeComplexPoint (ρ ≫ f) ≃ A.obj.left)
    (he : ∀ y, UnibAn.pointMap f (p.hom.left.base (e y)) =
      schemeComplexPointMap (ρ ≫ f) f ρ rfl y)
    (U : X.Opens)
    (hU : IsIsoOver p ((schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' (U : Set X))) :
    Function.Bijective
      (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl) := by
  classical
  let P := schemeComplexPointMap (ρ ≫ f) f ρ rfl
  have hx := analytic_bijOn_of_isIsoOver hU
  have hsurj (x : SchemeComplexPoint f) (hxU : schemeComplexPointImage f x ∈ U) :
      ∃ y, P y = x := by
    obtain ⟨z, hz⟩ := UnibAn.pointMap_surjective x
    obtain ⟨w, _, hw⟩ := hx.surjOn (show
      schemeComplexPointImage f (UnibAn.pointMap f z) ∈ U by rwa [hz])
    refine ⟨e.symm w, ?_⟩
    change schemeComplexPointMap (ρ ≫ f) f ρ rfl (e.symm w) = x
    rw [← he (e.symm w), e.apply_symm_apply, hw, hz]
  let s : SchemeComplexPoint f → SchemeComplexPoint (ρ ≫ f) :=
    fun x => if h : schemeComplexPointImage f x ∈ U then (hsurj x h).choose else Classical.choice inferInstance
  have hr x (hxU : schemeComplexPointImage f x ∈ U) : P (s x) = x := by
    rw [show s x = (hsurj x hxU).choose by simp only [s, dif_pos hxU]]
    exact (hsurj x hxU).choose_spec
  have hl y (hyU : schemeComplexPointImage f (P y) ∈ U) : s (P y) = y := by
    apply e.injective
    apply hx.injOn
    · change schemeComplexPointImage f (UnibAn.pointMap f (p.hom.left.base (e (s (P y))))) ∈ U
      rw [he (s (P y))]
      change schemeComplexPointImage f (P (s (P y))) ∈ U
      rwa [hr (P y) hyU]
    · change schemeComplexPointImage f (UnibAn.pointMap f (p.hom.left.base (e y))) ∈ U
      rwa [he]
    · apply UnibAn.pointMap_injective
      rw [he (s (P y)), he y]
      exact hr (P y) hyU
  have hb := OkoNov16.original_restricted_complexPoint_bijective_of_good_inverse f ρ U s hr hl
  have h : (ρ ∣_ U) ≫ (U.ι ≫ f) = (ρ ⁻¹ᵁ U).ι ≫ (ρ ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have transport {g : (ρ ⁻¹ᵁ U).toScheme ⟶ Spec (.of ℂ)}
      (hg : (ρ ∣_ U) ≫ (U.ι ≫ f) = g)
      (hb' : Function.Bijective (schemeComplexPointMap g (U.ι ≫ f) (ρ ∣_ U) hg)) :
      Function.Bijective
        (schemeComplexPointMap ((ρ ∣_ U) ≫ (U.ι ≫ f)) (U.ι ≫ f) (ρ ∣_ U) rfl) := by
    subst g
    exact hb'
  exact transport h hb

/-- Algebraize the actual compact terminal stage. The literal good-open premise
is the comparison needed to read its analytic birationality on the original algebraic base. -/
theorem exists_intrinsic_resolution_of_projective_stage
    (E : ClosedProjectiveEmbedding f) (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {m d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsComplexManifold d M] [CompactSpace M]
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ))
    (Ψ : M → ComplexProjectiveSpace N) (hΨ : IsHolomorphicEmbedding (n := d) Ψ)
    (p : wholeModel (n := d) M ⟶ UnibAn.analytification f) (hp : IsModification p)
    (U : X.Opens) [Nonempty U]
    (hU : IsIsoOver p ((schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' (U : Set X))) :
    ∃ R : Resolution f m, IsModification R.π ∧ IsIso (R.ρ.stalkMap (genericPoint R.Y)) := by
  have hpb := CHPrimeRealization.isProperBimeromorphic_of_isModification hp
  let := connectedSpace_projective_analytification f E
  have hM := KS3KahlerResolution.connectedSpace_of_isProperBimeromorphic hpb
    (isUnibranch_analytification_of_normal f hX)
  let : ConnectedSpace M := (Homeomorph.Set.univ M).connectedSpace_iff.mp hM
  obtain ⟨j, hj⟩ := chow_image hΨ (isComplexAnalyticSubset_univ (n := d) (M := M))
  obtain ⟨μ, hμ, P, hP, hgen, hzero⟩ := hj j le_rfl
  rw [image_univ] at hgen hzero
  let := hμ
  obtain ⟨Y, g, hsm, EY, hY, e, _, _⟩ := OF14.exists_integral_algebraization_of_chow hΨ P hP hgen hzero
  let := hY
  let := hsm
  let := EY.isSeparated
  let := EY.quasiCompact
  let J := stageWholeModelIso e
  let q : smoothModel g d ⟶ UnibAn.analytification f := J.hom ≫ p
  have hq := HironakaG1NativeModificationIsoTransport.isModification_precomp_iso hp J
  have hmap := (stage_projection_to_projective_contMDiff E p).comp e.contMDiff
  obtain ⟨ρ, ⟨hρ, hpoint⟩, _⟩ := exists_unique_morphism_of_mdifferentiable g EY d f E
    (fun y => ambientPoint E (UnibAn.pointMap f (p.hom.left.base ⟨e y, mem_univ _⟩)))
    (hmap.mdifferentiable (by simp)) (fun _ => mem_range_self _)
  subst g
  have hread (y : SchemeComplexPoint (ρ ≫ f)) :
      UnibAn.pointMap f (q.hom.left.base ⟨y, mem_univ y⟩) =
        schemeComplexPointMap (ρ ≫ f) f ρ rfl y :=
    (ambientPoint_injective E (hpoint y)).symm
  let : Nonempty (SchemeComplexPoint (ρ ≫ f)) := Nonempty.map e.symm inferInstance
  let : IsProper (ρ ≫ f) := EY.isProper
  let : IsProper ρ := IsProper.of_comp ρ f
  have hbij := stage_restrict_bijective ρ q (Homeomorph.Set.univ _).symm.toEquiv hread U
    (hU.precomp_iso J)
  obtain ⟨hgeneric, Efield, hfield⟩ := birationalData_of_restrict_complexPoint_bijective f ρ U hbij
  let := schemeFunctionFieldAlgebra f
  have hstageDim := functionField_trdeg_of_stalkCompatible_smooth_model f ρ Efield hfield d
  have hdm : d = m + 1 := by
    exact_mod_cast hstageDim.symm.trans hdim
  subst d
  let R : Resolution f m :=
    { Y := Y
      fY := ρ ≫ f
      E := EY
      ρ := ρ
      comp_eq := rfl
      φ := Efield
      stalkCompatible := hfield
      π := q
      isProperBimeromorphic := CHPrimeRealization.isProperBimeromorphic_of_isModification hq
      point_eq := hread }
  exact ⟨R, hq, hgeneric⟩

/-- The projective terminal stage itself supplies the nonempty good algebraic open:
algebraize the exceptional analytic subset by the exact ambient trace theorem. -/
theorem exists_intrinsic_resolution_of_projective_stage_of_modification
    (E : ClosedProjectiveEmbedding f) (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {m d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsComplexManifold d M] [CompactSpace M]
    (hdim : letI := schemeFunctionFieldAlgebra f
      Algebra.trdeg ℂ X.functionField = (m + 1 : ℕ))
    (Ψ : M → ComplexProjectiveSpace N) (hΨ : IsHolomorphicEmbedding (n := d) Ψ)
    (p : wholeModel (n := d) M ⟶ UnibAn.analytification f) (hp : IsModification p) :
    ∃ R : Resolution f m, IsModification R.π ∧ IsIso (R.ρ.stalkMap (genericPoint R.Y)) := by
  have hpb := CHPrimeRealization.isProperBimeromorphic_of_isModification hp
  obtain ⟨_, A, ha, hthin, _, hiso⟩ := hpb
  obtain ⟨Z, hZ, htrace⟩ := exists_original_closed_trace_of_projectiveAnalyticSubset E ha
  let U : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  let := connectedSpace_projective_analytification f E
  have hproper : A ≠ univ := by
    intro h
    rw [h, interior_univ] at hthin
    exact Set.univ_nonempty.ne_empty hthin
  obtain ⟨x, hx⟩ := Set.nonempty_compl.mpr hproper
  let : Nonempty U := ⟨⟨schemeComplexPointImage f (UnibAn.pointMap f x), by
    change x ∉ (schemeComplexPointImage f ∘ UnibAn.pointMap f) ⁻¹' Z
    rwa [← htrace]⟩⟩
  apply exists_intrinsic_resolution_of_projective_stage E hX hdim Ψ hΨ p hp U
  rw [htrace, ← preimage_compl] at hiso
  exact hiso

end SGPT.Okounkov.OF12
