import SGPT.Unibranch.HironakaG1PrimaryNativeGraph

/-!
# Actual canonical-model submersion certificates for the SAME primary maps

The frozen native graph functions are retained. Explicit canonical block
linear identifications and the actual scaling chart prove chart-form
submersion; no caller local-product packet or Jacobian converse is used.
Blueprint FIRST: `hironaka-g1-primary-graph-submersions.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace SGPT.Unibranch.HironakaG1PrimaryGraphSubmersions

open SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaG1PrimaryNativeGraph

open scoped ProductComplexManifold

noncomputable section

/-- Explicit WHOLE source-model identification, keeping all four actual blocks. -/
def sourceBlocks (r a b : ℕ) : ComplexModel ((r+a)+(r+b)) ≃L[ℂ]
    HironakaG1RelativeBoundaryProjections.Ambient r a b :=
  (ProductComplexManifold.prodModelEquiv (r+a) (r+b)).symm |>.trans
    (((ProductComplexManifold.prodModelEquiv r a).symm).prodCongr
      (ProductComplexManifold.prodModelEquiv r b).symm) |>.trans
    ((((EuclideanSpace.equiv (Fin r) ℂ).prodCongr (EuclideanSpace.equiv (Fin a) ℂ))).prodCongr
      ((EuclideanSpace.equiv (Fin r) ℂ).prodCongr (EuclideanSpace.equiv (Fin b) ℂ))) |>.trans
    (ContinuousLinearEquiv.prodProdProdComm ℂ _ _ _ _)

/-- Actual target-model identification, with active/other target coordinates. -/
def targetBlocks (r b : ℕ) : ComplexModel (r+b) ≃L[ℂ]
    (HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block b) :=
  (ProductComplexManifold.prodModelEquiv r b).symm |>.trans
    ((EuclideanSpace.equiv (Fin r) ℂ).prodCongr (EuclideanSpace.equiv (Fin b) ℂ))

private def rightArrange (r a b : ℕ) : HironakaG1RelativeBoundaryProjections.Ambient r a b ≃L[ℂ]
    ((HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block b) ×
      (HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block a)) where
  toFun p := ((p.1.1,p.2.2),(p.1.2,p.2.1))
  invFun p := ((p.1.1,p.2.1),(p.2.2,p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def sourceTargetEquiv (r a b : ℕ) : ComplexModel ((r+a)+(r+b)) ≃L[ℂ]
    (ComplexModel (r+b) × (HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block a)) :=
  ((sourceBlocks r a b).trans (rightArrange r a b)).trans
    ((targetBlocks r b).symm.prodCongr (ContinuousLinearEquiv.refl ℂ _))

private theorem sourceTargetEquiv_fst (r a b : ℕ) (z : ComplexModel ((r+a)+(r+b))) :
    (sourceTargetEquiv r a b z).1 = (targetBlocks r b).symm ((rightArrange r a b (sourceBlocks r a b z)).1) := rfl

/-- The REAL earlier scaling chart transported through the explicit whole model map. -/
def canonicalScalingChart (r a b : ℕ) :
    OpenPartialHomeomorph (ComplexModel ((r+a)+(r+b))) (ComplexModel ((r+a)+(r+b))) :=
  ((sourceBlocks r a b).toHomeomorph.toOpenPartialHomeomorph.trans
    (HironakaG1RelativeBoundaryProjections.scalingChart r a b)).trans
      (sourceBlocks r a b).symm.toHomeomorph.toOpenPartialHomeomorph

theorem canonicalScalingChart_source (r a b : ℕ) :
    (canonicalScalingChart r a b).source =
      sourceBlocks r a b ⁻¹' HironakaG1RelativeBoundaryProjections.unitLocus r a b := by
  ext z
  simp [canonicalScalingChart, HironakaG1RelativeBoundaryProjections.scalingChart, mfld_simps]

theorem canonicalScalingChart_target (r a b : ℕ) :
    (canonicalScalingChart r a b).target =
      sourceBlocks r a b ⁻¹' HironakaG1RelativeBoundaryProjections.unitLocus r a b := by
  ext z
  simp [canonicalScalingChart, HironakaG1RelativeBoundaryProjections.scalingChart, mfld_simps]

theorem canonicalScalingChart_mem_maximalAtlas (r a b : ℕ) :
    canonicalScalingChart r a b ∈ IsManifold.maximalAtlas
      𝓘(ℂ,ComplexModel ((r+a)+(r+b))) ∞ (ComplexModel ((r+a)+(r+b))) := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have h : ContDiff ℂ ∞ (fun z : ComplexModel ((r+a)+(r+b)) =>
        (sourceBlocks r a b).symm
          (HironakaG1RelativeBoundaryProjections.unitScaling r a b (sourceBlocks r a b z))) :=
      (sourceBlocks r a b).symm.contDiff.comp
        ((HironakaG1RelativeBoundaryProjections.contDiff_unitScaling r a b).comp (sourceBlocks r a b).contDiff)
    exact h.contDiffOn.contMDiffOn
  · have h : ContDiffOn ℂ ∞ (fun z : ComplexModel ((r+a)+(r+b)) =>
        HironakaG1RelativeBoundaryProjections.unitUnscaling r a b (sourceBlocks r a b z))
          (canonicalScalingChart r a b).target :=
      (HironakaG1RelativeBoundaryProjections.contDiffOn_unitUnscaling r a b).comp
        (sourceBlocks r a b).contDiff.contDiffOn (fun z hz =>
          Set.ext_iff.mp (canonicalScalingChart_target r a b) z |>.mp hz)
    exact ((sourceBlocks r a b).symm.contDiff.comp_contDiffOn h).contMDiffOn

/-- The SAME second coordinate formula in genuine canonical model coordinates. -/
def rawSecond (r a b : ℕ) (z : ComplexModel ((r+a)+(r+b))) : ComplexModel (r+b) :=
  (targetBlocks r b).symm
    (HironakaG1RelativeBoundaryProjections.rightProjection r a b (sourceBlocks r a b z))

private theorem rawSecond_chart_inverse (r a b : ℕ) (z : ComplexModel ((r+a)+(r+b)))
    (hz : z ∈ (canonicalScalingChart r a b).target) :
    rawSecond r a b ((canonicalScalingChart r a b).symm z) =
      (targetBlocks r b).symm ((rightArrange r a b (sourceBlocks r a b z)).1) := by
  have hzU : sourceBlocks r a b z ∈ HironakaG1RelativeBoundaryProjections.unitLocus r a b :=
    (Set.ext_iff.mp (canonicalScalingChart_target r a b) z).mp hz
  change (targetBlocks r b).symm
    (HironakaG1RelativeBoundaryProjections.rightProjection r a b
      (sourceBlocks r a b ((sourceBlocks r a b).symm
        (HironakaG1RelativeBoundaryProjections.unitUnscaling r a b (sourceBlocks r a b z))))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact congrArg (targetBlocks r b).symm
    (congrArg (fun p : HironakaG1RelativeBoundaryProjections.Ambient r a b => (p.1.1,p.2.2))
      (HironakaG1RelativeBoundaryProjections.unitScaling_unitUnscaling r a b (sourceBlocks r a b z) hzU))

theorem rawSecond_isSubmersionAt (r a b : ℕ) (p : ComplexModel ((r+a)+(r+b)))
    (hp : sourceBlocks r a b p ∈ HironakaG1RelativeBoundaryProjections.unitLocus r a b) :
    Manifold.IsSubmersionAtOfComplement
      (HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block a)
      𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞ (rawSecond r a b) p := by
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (sourceTargetEquiv r a b) (canonicalScalingChart r a b)
    (OpenPartialHomeomorph.refl (ComplexModel (r+b)))
  · exact (Set.ext_iff.mp (canonicalScalingChart_source r a b) p).mpr hp
  · exact mem_univ _
  · exact canonicalScalingChart_mem_maximalAtlas r a b
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn <;> exact contMDiffOn_id
  · intro _ _
    exact mem_univ _
  · intro z hz
    have hz' : z ∈ (canonicalScalingChart r a b).target := by
      simpa [OpenPartialHomeomorph.extend] using hz
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.id_def, sourceTargetEquiv_fst]
    exact rawSecond_chart_inverse r a b z hz'


private theorem sourceBlocks_join (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) :
    sourceBlocks r a b (ProductComplexManifold.prodModelEquiv (r+a) (r+b) (x,z)) =
      ((fun i : Fin r => x (i.castAdd a), fun i : Fin r => z (i.castAdd b)),
        (fun j : Fin a => x (j.natAdd r), fun j : Fin b => z (j.natAdd r))) := by
  simp only [sourceBlocks, ContinuousLinearEquiv.trans_apply]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

private theorem targetBlocks_assembled (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) :
    targetBlocks r b (assembled r a b x z) =
      (fun i : Fin r => z (i.castAdd b) * x (i.castAdd a), fun j : Fin b => z (j.natAdd r)) := by
  apply Prod.ext
  · funext i
    change assembled r a b x z (i.castAdd b) = _
    exact assembled_active r a b x z i
  · funext j
    change assembled r a b x z (j.natAdd r) = _
    exact assembled_other r a b x z j

private theorem rawSecond_join (r a b : ℕ) (x : ComplexModel (r+a)) (z : ComplexModel (r+b)) :
    rawSecond r a b (ProductComplexManifold.prodModelEquiv (r+a) (r+b) (x,z)) = assembled r a b x z := by
  apply (targetBlocks r b).injective
  rw [rawSecond, ContinuousLinearEquiv.apply_symm_apply, sourceBlocks_join, targetBlocks_assembled]
  rfl

private theorem chartAt_open_apply {n : ℕ} (P : Opens (ComplexModel n)) (x y : P) :
    chartAt (ComplexModel n) x y = y.val := rfl

private theorem chartAt_open_mem {n : ℕ} (P : Opens (ComplexModel n)) (x y : P) :
    y ∈ (chartAt (ComplexModel n) x).source := by
  exact ⟨trivial,trivial⟩

private theorem chartAt_productOpen_apply {n m : ℕ} (P : Opens (ComplexModel n))
    (O : Opens (P × ComplexModel m)) (x y : O) :
    chartAt (ComplexModel (n+m)) x y = ProductComplexManifold.prodModelEquiv n m (y.val.1.val,y.val.2) := rfl

private theorem maximalAtlas_trans_self {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ∞ M]
    (e : OpenPartialHomeomorph M E) (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,E) ∞ M)
    (s : OpenPartialHomeomorph E E) (hs : s ∈ IsManifold.maximalAtlas 𝓘(ℂ,E) ∞ E) :
    e.trans s ∈ IsManifold.maximalAtlas 𝓘(ℂ,E) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (s ∘ e) (e.source ∩ e ⁻¹' s.source)
    exact (contMDiffOn_of_mem_maximalAtlas hs).comp
      ((contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ,E) 𝓘(ℂ,E) ∞ (e.symm ∘ s.symm) (s.target ∩ s.symm ⁻¹' e.target)
    exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hs).mono inter_subset_left) (fun _ hz => hz.2)


variable {r a b : ℕ}
  (P : Opens (ComplexModel (r+a))) (V : Opens (ComplexModel (r+b))) (C : Set P) (D : Set V)
  (F : actualSubspaceLocallyRingedSpace (n := r+a) C ⟶ actualSubspaceLocallyRingedSpace (n := r+b) D)
  (hF : F ≫ HironakaReducedComplexAnalyticSpaces.subspacePointMap (n := r+b) D =
    HironakaReducedComplexAnalyticSpaces.subspacePointMap (n := r+a) C) (c : C)
  (hI : ∀ i : Fin r, Ideal.map (F.stalkMap c).hom (coordinateImageIdeal V D (F.base c) (i.castAdd b)) =
    coordinateImageIdeal P C c (i.castAdd a))

local notation "A0" => primaryOpen P V C D F hF c hI
local notation "Q0" => commonOpen P V C D F hF c hI

private theorem secondAmbient_chart (p y : Q0) :
    (secondAmbient P V C D F hF c hI y).val =
      rawSecond r a b (chartAt (ComplexModel ((r+a)+(r+b))) p y) := by
  rw [chartAt_productOpen_apply A0 Q0 p y, rawSecond_join]
  rfl

/-- A certificate for the EXACT frozen first ambient function in its actual
canonical source model and genuine original source-reader target. -/
theorem firstAmbient_isSubmersion : Manifold.IsSubmersionOfComplement (ComplexModel (r+b))
    𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+a)) ∞ (firstAmbient P V C D F hF c hI) := by
  intro p
  let e := chartAt (ComplexModel ((r+a)+(r+b))) p
  let f := chartAt (ComplexModel (r+a)) (firstAmbient P V C D F hF c hI p)
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts
    (ProductComplexManifold.prodModelEquiv (r+a) (r+b)).symm e f
    (mem_chart_source _ p) (mem_chart_source _ (firstAmbient P V C D F hF c hI p))
    (IsManifold.chart_mem_maximalAtlas _) (IsManifold.chart_mem_maximalAtlas _)
  · intro z _hz
    exact chartAt_open_mem A0 (firstAmbient P V C D F hF c hI p) (firstAmbient P V C D F hF c hI z)
  · intro z hz
    have hz' : z ∈ e.target := by simpa only [mfld_simps] using hz
    have hInv : ProductComplexManifold.prodModelEquiv (r+a) (r+b)
        ((e.symm z).val.1.val,(e.symm z).val.2) = z :=
      (chartAt_productOpen_apply A0 Q0 p (e.symm z)).symm.trans (e.right_inv hz')
    have he := congrArg (fun w : ComplexModel ((r+a)+(r+b)) =>
      ((ProductComplexManifold.prodModelEquiv (r+a) (r+b)).symm w).1) hInv
    simp only [ContinuousLinearEquiv.symm_apply_apply] at he
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, Function.id_def]
    exact (chartAt_open_apply A0 (firstAmbient P V C D F hF c hI p)
      (firstAmbient P V C D F hF c hI (e.symm z))).trans he

/-- A certificate for the EXACT frozen second ambient function: actual
canonical-model charts retain every whole original projection coordinate. -/
theorem secondAmbient_isSubmersion : Manifold.IsSubmersionOfComplement
    (HironakaG1RelativeBoundaryProjections.Block r × HironakaG1RelativeBoundaryProjections.Block a)
    𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ComplexModel (r+b)) ∞ (secondAmbient P V C D F hF c hI) := by
  intro p
  let e := chartAt (ComplexModel ((r+a)+(r+b))) p
  let f := chartAt (ComplexModel (r+b)) (secondAmbient P V C D F hF c hI p)
  let s := canonicalScalingChart r a b
  let d := e.trans s
  have hpU : sourceBlocks r a b (e p) ∈ HironakaG1RelativeBoundaryProjections.unitLocus r a b := by
    change sourceBlocks r a b (chartAt (ComplexModel ((r+a)+(r+b))) p p) ∈ _
    rw [chartAt_productOpen_apply A0 Q0 p p, sourceBlocks_join]
    exact p.property.1
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts (sourceTargetEquiv r a b) d f
  · exact ⟨mem_chart_source _ p,(Set.ext_iff.mp (canonicalScalingChart_source r a b) (e p)).mpr hpU⟩
  · exact mem_chart_source _ (secondAmbient P V C D F hF c hI p)
  · exact maximalAtlas_trans_self e (IsManifold.chart_mem_maximalAtlas _) s (canonicalScalingChart_mem_maximalAtlas r a b)
  · exact IsManifold.chart_mem_maximalAtlas _
  · intro z _hz
    exact chartAt_open_mem V (secondAmbient P V C D F hF c hI p) (secondAmbient P V C D F hF c hI z)
  · intro z hz
    have hz' : z ∈ d.target := by simpa only [mfld_simps] using hz
    have hzS : z ∈ (canonicalScalingChart r a b).target := hz'.1
    have hInv : e (e.symm (s.symm z)) = s.symm z := e.right_inv hz'.2
    have hNative : f (secondAmbient P V C D F hF c hI (d.symm z)) = rawSecond r a b (s.symm z) :=
      (chartAt_open_apply V (secondAmbient P V C D F hF c hI p) (secondAmbient P V C D F hF c hI (d.symm z))).trans
        ((secondAmbient_chart P V C D F hF c hI p (d.symm z)).trans (congrArg (rawSecond r a b) hInv))
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, Function.id_def]
    exact hNative.trans ((rawSecond_chart_inverse r a b z hzS).trans (sourceTargetEquiv_fst r a b z).symm)


private def wholeSection (n : ℕ) {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (f : M → ℂ) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f) :
    actualComplexSection (n := n) (⊤ : Opens M) :=
  ⟨fun z => f z.val,hf.comp contMDiff_subtype_val⟩

private theorem wholeSection_germ_isUnit_iff (n : ℕ) {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (f : M → ℂ) (hf : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ f) (x : M) :
    IsUnit ((actualComplexStructureSheaf (n := n) M).presheaf.germ ⊤ x (by trivial) (wholeSection n f hf)) ↔ f x ≠ 0 := by
  refine (isUnit_map_iff (actualStalkChartEquiv (n := n) x) _).symm.trans ?_
  have he := actualStalkChartEquiv_germ (n := n) (⊤ : Opens M) x (by trivial)
    (wholeSection n f hf)
  refine (Iff.of_eq (congrArg IsUnit he)).trans ?_
  rw [HolGerm.isUnit_iff_eval_ne_zero]
  change sectionExtension ⊤ (wholeSection n f hf)
    ((chartAt (ComplexModel n) x).symm (0 + chartAt (ComplexModel n) x x)) ≠ 0 ↔ f x ≠ 0
  rw [zero_add,(chartAt (ComplexModel n) x).left_inv (mem_chart_source _ x),
    sectionExtension_apply ⊤ (wholeSection n f hf) x (by trivial)]
  rfl

private def leftCoordinate (i : Fin r) (z : Q0) : ℂ :=
  (firstAmbient P V C D F hF c hI z).val (i.castAdd a)

private def rightCoordinate (i : Fin r) (z : Q0) : ℂ :=
  (secondAmbient P V C D F hF c hI z).val (i.castAdd b)

private def ratioCoordinate (i : Fin r) (z : Q0) : ℂ := z.val.2 (i.castAdd b)

private theorem leftCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (leftCoordinate P V C D F hF c hI i) :=
  (EuclideanSpace.proj (i.castAdd a)).contMDiff.comp
    (contMDiff_subtype_val.comp (firstAmbient_holomorphic P V C D F hF c hI))

private theorem rightCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (rightCoordinate P V C D F hF c hI i) :=
  (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
    (contMDiff_subtype_val.comp (secondAmbient_holomorphic P V C D F hF c hI))

private theorem ratioCoordinate_holomorphic (i : Fin r) :
    ContMDiff 𝓘(ℂ,ComplexModel ((r+a)+(r+b))) 𝓘(ℂ,ℂ) ∞ (ratioCoordinate P V C D F hF c hI i) :=
  (EuclideanSpace.proj (i.castAdd b)).contMDiff.comp
    (ProductComplexManifold.contMDiff_snd.comp contMDiff_subtype_val)

/-- The exact original source-coordinate stalk element in the REAL common ambient. -/
def leftBoundaryGerm (x : Q0) (i : Fin r) : actualComplexStructureStalk (n := (r+a)+(r+b)) x :=
  (actualComplexStructureSheaf (n := (r+a)+(r+b)) Q0).presheaf.germ ⊤ x (by trivial)
    (wholeSection _ (leftCoordinate P V C D F hF c hI i) (leftCoordinate_holomorphic P V C D F hF c hI i))

/-- The exact target coordinate pulled through the SAME actual second ambient map. -/
def rightBoundaryGerm (x : Q0) (i : Fin r) : actualComplexStructureStalk (n := (r+a)+(r+b)) x :=
  (actualComplexStructureSheaf (n := (r+a)+(r+b)) Q0).presheaf.germ ⊤ x (by trivial)
    (wholeSection _ (rightCoordinate P V C D F hF c hI i) (rightCoordinate_holomorphic P V C D F hF c hI i))

/-- The REAL ratio-coordinate unit, in the actual ambient structure-sheaf stalk. -/
def ratioBoundaryGerm (x : Q0) (i : Fin r) : actualComplexStructureStalk (n := (r+a)+(r+b)) x :=
  (actualComplexStructureSheaf (n := (r+a)+(r+b)) Q0).presheaf.germ ⊤ x (by trivial)
    (wholeSection _ (ratioCoordinate P V C D F hF c hI i) (ratioCoordinate_holomorphic P V C D F hF c hI i))

theorem ratioBoundaryGerm_isUnit (x : Q0) (i : Fin r) : IsUnit (ratioBoundaryGerm P V C D F hF c hI x i) :=
  (wholeSection_germ_isUnit_iff _ _ _ x).mpr (x.property.1 i)

theorem rightBoundaryGerm_eq_mul (x : Q0) (i : Fin r) :
    rightBoundaryGerm P V C D F hF c hI x i =
      ratioBoundaryGerm P V C D F hF c hI x i * leftBoundaryGerm P V C D F hF c hI x i := by
  let s := wholeSection _ (rightCoordinate P V C D F hF c hI i) (rightCoordinate_holomorphic P V C D F hF c hI i)
  let t := wholeSection _ (ratioCoordinate P V C D F hF c hI i) (ratioCoordinate_holomorphic P V C D F hF c hI i)
  let u := wholeSection _ (leftCoordinate P V C D F hF c hI i) (leftCoordinate_holomorphic P V C D F hF c hI i)
  have he : s = t * u := by
    apply ContMDiffMap.ext
    intro z
    exact assembled_active r a b z.val.val.1.val z.val.val.2 i
  exact (congrArg (fun s => (actualComplexStructureSheaf (n := (r+a)+(r+b)) Q0).presheaf.germ ⊤ x (by trivial) s) he).trans
    (map_mul _ _ _)

/-- EVERY original selector slot is retained, with generator ONE at absent slots. -/
def leftSlotGerm {ι : Type*} (slot : ι → Option (Fin r)) (x : Q0) (i : ι) :
    actualComplexStructureStalk (n := (r+a)+(r+b)) x :=
  match slot i with
  | none => 1
  | some j => leftBoundaryGerm P V C D F hF c hI x j

def rightSlotGerm {ι : Type*} (slot : ι → Option (Fin r)) (x : Q0) (i : ι) :
    actualComplexStructureStalk (n := (r+a)+(r+b)) x :=
  match slot i with
  | none => 1
  | some j => rightBoundaryGerm P V C D F hF c hI x j

/-- ENTIRE ambient ideals for ALL original slots; no support radical is substituted. -/
theorem slotIdeal_eq {ι : Type*} (slot : ι → Option (Fin r)) (x : Q0) (i : ι) :
    Ideal.span {rightSlotGerm P V C D F hF c hI slot x i} =
      Ideal.span {leftSlotGerm P V C D F hF c hI slot x i} := by
  cases hslot : slot i with
  | none => simp only [leftSlotGerm,rightSlotGerm,hslot]
  | some j =>
    simp only [leftSlotGerm,rightSlotGerm,hslot]
    rw [rightBoundaryGerm_eq_mul, ← Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_eq_top.mpr (ratioBoundaryGerm_isUnit P V C D F hF c hI x j), Ideal.top_mul]

/-- The ACTUAL graph quotient preserves the ENTIRE full-slot ideal images,
even when they are zero or have zero-divisor generators. -/
theorem graph_slotIdeal_image_eq {ι : Type*} (slot : ι → Option (Fin r))
    (x : graphTrace P V C D F hF c hI) (i : ι) :
    Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)).stalkMap x).hom
        (Ideal.span {rightSlotGerm P V C D F hF c hI slot x.val i}) =
      Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)).stalkMap x).hom
        (Ideal.span {leftSlotGerm P V C D F hF c hI slot x.val i}) :=
  congrArg (Ideal.map ((actualSubspaceInclusion (n := (r+a)+(r+b)) (graphTrace P V C D F hF c hI)).stalkMap x).hom)
    (slotIdeal_eq P V C D F hF c hI slot x.val i)

end
end SGPT.Unibranch.HironakaG1PrimaryGraphSubmersions
