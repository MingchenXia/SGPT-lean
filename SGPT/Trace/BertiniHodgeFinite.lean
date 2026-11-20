import SGPT.Trace.BertiniHodgePositive
import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence

/-! Actual intrinsic canonical physical Hodge finite mass and FULL original
native multiplier H0. Raw extended weights and pole components retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Toric.F1IntersectionDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

section General
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} n X)

def nativePreferredPhysicalFrame (x : X) : AtlasFrame (tensor (nativeCanonicalBundle (n := n) (X := X)) L) :=
  tensorAtlasFrame (nativeCanonicalFrame (n := n) x) ⟨trivializationAt ℂ L.Fiber x,inferInstance⟩

private theorem actualHodgeFiniteOfLocal
    (S : ∀ x, (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber x) (w : X → ℝ≥0∞)
    (hloc : ∀ x : X, ∃ W : TopologicalSpace.Opens X, x ∈ W ∧
      ∃ c : ComplexChart n X, (W : Set X) ⊆ c.val.source ∧
        (∫⁻ z in c.val '' (W : Set X), nativeCanonicalPhysicalCoordinateDensity L S w c z) < ⊤) :
    nativePhysicalHodgeEnergy L S w < ⊤ := by
  classical
  choose W hxW c hsub hfin using hloc
  have hcover : (univ : Set X) ⊆ ⋃ x, (W x : Set X) :=
    fun x _ => mem_iUnion.mpr ⟨x,hxW x⟩
  obtain ⟨A,hA⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) hcover
  let a : Fin A.card → X := fun k => (A.equivFin.symm k).val
  let V : Fin A.card → Set X := fun k => W (a k)
  have hV : ∀ k, MeasurableSet (V k) := fun k => (W (a k)).isOpen.measurableSet
  have hVcover : ⋃ k, V k = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨y,hyA,hxy⟩ := mem_iUnion₂.mp (hA (mem_univ x))
    refine mem_iUnion.mpr ⟨A.equivFin ⟨y,hyA⟩,?_⟩
    simpa only [V,a,Equiv.symm_apply_apply] using hxy
  let P : NativeCanonicalChartPartition n X := {
    size := A.card
    chart := fun k => c (a k)
    piece := disjointed V
    measurable_piece := fun k => disjointedRec (fun {t j} ht => ht.diff (hV j)) (hV k)
    piece_subset := fun k => (disjointed_subset V k).trans (hsub (a k))
    disjoint_piece := disjoint_disjointed V
    cover := by rw [iUnion_disjointed,hVcover] }
  rw [nativePhysicalHodgeEnergy_eq_partition L S w P]
  change (∑ k : Fin A.card, ∫⁻ z in (c (a k)).val '' disjointed V k,
    nativeCanonicalPhysicalCoordinateDensity L S w (c (a k)) z) < ⊤
  apply ENNReal.sum_lt_top.mpr
  intro k _
  exact (lintegral_mono_set (image_mono (disjointed_subset V k))).trans_lt (hfin (a k))

theorem nativePhysicalHodgeEnergy_finite_iff_multiplierGerms
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber)
    (φ : X → EReal) (hφm : Measurable φ) :
    nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) < ⊤ ↔
      ∀ x : X, (multiplierIdeal (n := n) 1 φ).mem x
        (sectionCoefficient (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber
          (nativePreferredPhysicalFrame L x).val S) := by
  classical
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  constructor
  · intro hfinite x
    let c := complexChartAt (n := n) x
    let z₀ := c.val x
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x,inferInstance⟩
    let q := nativePreferredPhysicalFrame L x
    let := e.property
    let := q.property
    have hx : x ∈ c.val.source := mem_complexChartAt_source _
    have hz₀ : z₀ ∈ c.val.target := c.val.map_source hx
    have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    have hq : x ∈ q.val.baseSet := ⟨hx,he⟩
    have hinv : c.val.symm z₀ = x := c.val.left_inv hx
    let D := c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet
    have hD : IsOpen D := c.val.isOpen_inter_preimage_symm e.val.open_baseSet
    have hzD : z₀ ∈ D := ⟨hz₀,by
      change c.val.symm z₀ ∈ e.val.baseSet
      rwa [hinv]⟩
    obtain ⟨R,hR,hRD⟩ := Metric.isOpen_iff.mp hD z₀ hzD
    let r := R / 2
    have hr : 0 < r := half_pos hR
    have hKR : closedBall z₀ r ⊆ ball z₀ R := closedBall_subset_ball (half_lt_self hR)
    have hKD : closedBall z₀ r ⊆ D := hKR.trans hRD
    have hKt : closedBall z₀ r ⊆ c.val.target := fun z hz => (hKD hz).1
    have hKe : ∀ z ∈ closedBall z₀ r, c.val.symm z ∈ e.val.baseSet := fun z hz => (hKD hz).2
    let W := c.val.source ∩ c.val ⁻¹' ball z₀ R
    have hW : IsOpen W := c.val.isOpen_inter_preimage isOpen_ball
    have himage : c.val '' W = ball z₀ R := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy.2
      · intro hz
        have hzt := (hRD hz).1
        refine ⟨c.val.symm z,⟨c.val.map_target hzt,?_⟩,c.val.right_inv hzt⟩
        change c.val (c.val.symm z) ∈ ball z₀ R
        rwa [c.val.right_inv hzt]
    have hlocal := (nativePhysicalHodgeEnergy_ge_chartSubset L S
      (fun y => multiplierWeight 1 (φ y)) c W hW.measurableSet inter_subset_left).trans_lt hfinite
    rw [himage] at hlocal
    have hKmass := (lintegral_mono_set hKR).trans_lt hlocal
    have hcoef := (nativePhysicalPreferredCompact_finite_iff L S φ x e
      (isCompact_closedBall z₀ r) hKt hKe).mp hKmass
    let F := sectionCoefficient B.Fiber q.val S ∘ c.val.symm
    change (∫⁻ z in closedBall z₀ r, multiplierDensity (chartFunction φ c) 1 F z) < ⊤ at hcoef
    have hBt : ball z₀ r ⊆ c.val.target := ball_subset_closedBall.trans hKt
    have hBe : ∀ z ∈ ball z₀ r, c.val.symm z ∈ q.val.baseSet :=
      fun z hz => ⟨c.val.map_target (hBt hz),hKe z (ball_subset_closedBall hz)⟩
    have hF : DifferentiableOn ℂ F (ball z₀ r) :=
      (sectionCoefficient_chart_differentiable B.Fiber q.val x S).mono (fun z hz => ⟨hBt hz,hBe z hz⟩)
    have hφa : AEMeasurable (chartFunction φ c) (volume.restrict (ball z₀ r)) :=
      hφm.comp_aemeasurable ((c.val.continuousOn_symm.mono hBt).aemeasurable isOpen_ball.measurableSet)
    have hweight : AEMeasurable (fun z => multiplierWeight 1 (chartFunction φ c z))
        (volume.restrict (ball z₀ r)) :=
      (measurable_originalMultiplierWeight measurable_id 1).comp_aemeasurable hφa
    refine ⟨originalSectionCoefficient_holomorphicAt (n := n) B.Fiber q S hq,
      one_pos,ball z₀ r,isOpen_ball,mem_ball_self hr,hF,?_,?_⟩
    · exact ((hF.continuousOn.aemeasurable isOpen_ball.measurableSet).norm.pow_const 2).ennreal_ofReal.mul hweight
    · exact (lintegral_mono_set ball_subset_closedBall).trans_lt hcoef
  · intro hpoint
    apply actualHodgeFiniteOfLocal L S (fun x => multiplierWeight 1 (φ x))
    intro x
    let c := complexChartAt (n := n) x
    let z₀ := c.val x
    let e : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x,inferInstance⟩
    let q := nativePreferredPhysicalFrame L x
    have hx : x ∈ c.val.source := mem_complexChartAt_source _
    have hz₀ : z₀ ∈ c.val.target := c.val.map_source hx
    have he : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    have hinv : c.val.symm z₀ = x := c.val.left_inv hx
    obtain ⟨_hhol,_hc,O,hO,hzO,_hF,_hweight,hfinO⟩ := hpoint x
    let D := O ∩ (c.val.target ∩ c.val.symm ⁻¹' e.val.baseSet)
    have hD : IsOpen D := hO.inter (c.val.isOpen_inter_preimage_symm e.val.open_baseSet)
    have hzD : z₀ ∈ D := ⟨hzO,hz₀,by
      change c.val.symm z₀ ∈ e.val.baseSet
      rwa [hinv]⟩
    obtain ⟨R,hR,hRD⟩ := Metric.isOpen_iff.mp hD z₀ hzD
    let r := R / 2
    have hr : 0 < r := half_pos hR
    have hKD : closedBall z₀ r ⊆ D := (closedBall_subset_ball (half_lt_self hR)).trans hRD
    have hKt : closedBall z₀ r ⊆ c.val.target := fun z hz => (hKD hz).2.1
    have hKe : ∀ z ∈ closedBall z₀ r, c.val.symm z ∈ e.val.baseSet := fun z hz => (hKD hz).2.2
    have hcoef := (lintegral_mono_set (show closedBall z₀ r ⊆ O from fun z hz => (hKD hz).1)).trans_lt hfinO
    have hKmass := (nativePhysicalPreferredCompact_finite_iff L S φ x e
      (isCompact_closedBall z₀ r) hKt hKe).mpr hcoef
    let W := c.val.source ∩ c.val ⁻¹' ball z₀ r
    have hW : IsOpen W := c.val.isOpen_inter_preimage isOpen_ball
    have hxW : x ∈ W := ⟨hx,mem_ball_self hr⟩
    have himage : c.val '' W = ball z₀ r := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy.2
      · intro hz
        have hzt := hKt (ball_subset_closedBall hz)
        refine ⟨c.val.symm z,⟨c.val.map_target hzt,?_⟩,c.val.right_inv hzt⟩
        change c.val (c.val.symm z) ∈ ball z₀ r
        rwa [c.val.right_inv hzt]
    refine ⟨⟨W,hW⟩,hxW,c,inter_subset_left,?_⟩
    change (∫⁻ z in c.val '' W, nativeCanonicalPhysicalCoordinateDensity L S
      (fun y => multiplierWeight 1 (φ y)) c z) < ⊤
    rw [himage]
    exact (lintegral_mono_set ball_subset_closedBall).trans_lt hKmass

theorem nativePhysicalHodgeEnergy_finite_iff_originalIdeal
    (hn : 0 < n) {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ)
    (S : HolomorphicSections (n := n) (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber) :
    S ∈ fullHolomorphicIdealSections (n := n)
      (tensor (nativeCanonicalBundle (n := n) (X := X)) L).Fiber
      (sourceDegreeMultiplierIdeal (n := n) 1 φ) ↔
      nativePhysicalHodgeEnergy L S (fun x => multiplierWeight 1 (φ x)) < ⊤ := by
  classical
  let B := tensor (nativeCanonicalBundle (n := n) (X := X)) L
  let I := sourceDegreeMultiplierIdeal (n := n) 1 φ
  have hIeq : I = multiplierIdeal (n := n) 1 φ := by
    simpa only [I,Nat.cast_one] using (sourceDegreeMultiplierIdeal_pos (n := n) 1 one_pos φ)
  have hI : I.IsCoherent := by
    rw [hIeq]
    exact SGPT.Foundations.Analysis.Pending.GlobalQuasiPshMultiplierCoherence.isCoherent_multiplierIdeal_of_manifoldQuasiPlurisubharmonic
      hn hφ one_pos
  rw [nativePhysicalHodgeEnergy_finite_iff_multiplierGerms L S φ hφ.upperSemicontinuous.measurable]
  constructor
  · intro hS x
    let q := nativePreferredPhysicalFrame L x
    have hq : x ∈ q.val.baseSet := ⟨mem_complexChartAt_source _,mem_baseSet_trivializationAt ℂ _ _⟩
    change globalSectionSheafEquiv (n := n) B.Fiber S ∈ idealOpenSectionSubmodule (n := n) B.Fiber I ⊤ at hS
    have h := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI q S hq).mp
      (hS q ⟨x,mem_univ x⟩ hq)
    rw [hIeq] at h
    exact h
  · intro hpoint
    change globalSectionSheafEquiv (n := n) B.Fiber S ∈ idealOpenSectionSubmodule (n := n) B.Fiber I ⊤
    intro e x hxe
    let q := nativePreferredPhysicalFrame L x.val
    have hq : x.val ∈ q.val.baseSet := ⟨mem_complexChartAt_source _,mem_baseSet_trivializationAt ℂ _ _⟩
    apply (localFrameCoefficientGerm_mem_iff (n := n) B.Fiber I ⊤ e q
      (globalSectionSheafEquiv (n := n) B.Fiber S) x hxe hq).mpr
    apply (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) B.Fiber I hI q S hq).mpr
    rw [hIeq]
    exact hpoint x.val
end General


theorem nativeBertiniMemberHodgeEnergy_finite_iff_originalIdeal {d N : ℕ}
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (d + 1)) Y]
    [IsComplexManifold (d + 1) Y] [CompactSpace Y]
    (hd : 0 < d)
    (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
    (i : Fin (N + 1)) (ζ : ComplexModel N)
    (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ))
    (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) Y) {φ : Y → EReal}
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    letI := nativeBertiniMemberChartedSpace p i ζ hsm
    letI := nativeBertiniMemberComplex p i ζ hsm
    letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
    ∀ S : HolomorphicSections (n := d) (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
      (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber,
      S ∈ fullHolomorphicIdealSections (n := d)
        (tensor (nativeCanonicalBundle (n := d) (X := member p (affinePoint i ζ)))
          (nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm))).Fiber
        (sourceDegreeMultiplierIdeal (n := d) 1 (fun y => φ y.val)) ↔
      nativeBertiniMemberHodgeEnergy p i ζ hsm L φ S < ⊤ := by
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  intro S
  exact nativePhysicalHodgeEnergy_finite_iff_originalIdeal _ hd
    (SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback.manifoldQuasiPlurisubharmonic_comp
      (nativeBertiniMemberInclusionMap p i ζ hsm).contMDiff hφ) S

end SGPT.Trace.Bertini
