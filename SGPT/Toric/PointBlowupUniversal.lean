import SGPT.Toric.PointBlowupGeometry
import SGPT.Foundations.Analysis.Pending.BlowupExistence
import SGPT.Foundations.Analysis.Pending.PointSupportedIdealPrincipalization
import SGPT.Foundations.Analysis.Pending.BlowupSourceBiholomorphism
import Lean.Elab.Command

section PointBlowupCanonicalFragment001
/- BEGIN NativeProjectivePointBlowupDraft; original source SHA256 ee3adfe59c6edbd5383732512acfb29c5cb3885be13c0e69bfbc418899a681cb -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

/-- The actual three standard projective coordinate points. -/
def nativeProjectiveBasisPoint (i : Fin 3) : SGPT.Projective.ComplexProjectiveSpace 2 :=
  SGPT.Projective.ComplexProjectiveSpace.mk (Pi.single i (1 : ℂ))
    (by intro h; have hi := congrFun h i; simp at hi)

/-- At a coordinate point the native preferred projective chart is forced,
rather than supplied as an atlas-identification assumption. -/
theorem projective_chartIndex_basisPoint (i : Fin 3) :
    SGPT.Projective.ComplexProjectiveSpace.chartIndex (nativeProjectiveBasisPoint i) = i := by
  have h := SGPT.Projective.ComplexProjectiveSpace.mem_affineChart_chartIndex (nativeProjectiveBasisPoint i)
  change SGPT.Projective.ComplexProjectiveSpace.mk (Pi.single i (1 : ℂ)) _ ∈ _ at h
  have hc : (Pi.single i (1 : ℂ) : Fin 3 → ℂ)
      (SGPT.Projective.ComplexProjectiveSpace.chartIndex (nativeProjectiveBasisPoint i)) ≠ 0 :=
    (SGPT.Projective.ComplexProjectiveSpace.mk_mem_affineChart_source_iff _
      (v := Pi.single i (1 : ℂ)) (by intro hz; have hi := congrFun hz i; simp at hi)).mp h
  by_contra hn
  simp [hn] at hc

theorem nativeProjectiveBasisPoint_zero : nativeProjectiveBasisPoint 0 = blowdownOrigin := by
  unfold nativeProjectiveBasisPoint blowdownOrigin
  congr 1
  funext j
  fin_cases j <;> simp

theorem projective_chartAt_origin :
    chartAt (ComplexModel 2) blowdownOrigin = SGPT.Projective.ComplexProjectiveSpace.affineChart 0 := by
  change SGPT.Projective.ComplexProjectiveSpace.affineChart
    (SGPT.Projective.ComplexProjectiveSpace.chartIndex blowdownOrigin) = _
  rw [← nativeProjectiveBasisPoint_zero, projective_chartIndex_basisPoint]

theorem projective_origin_chart_zero :
    SGPT.Projective.ComplexProjectiveSpace.affineChart 0 blowdownOrigin = 0 := by
  unfold blowdownOrigin
  rw [SGPT.Projective.ComplexProjectiveSpace.affineChart_mk 0 _ one_ne_zero]
  ext i
  fin_cases i <;> simp [SGPT.Projective.ComplexProjectiveSpace.affineRatio_apply]

/-- Existing ordinary native singleton geometry, reused without adding a
resolution/common-modification/Kähler theorem. -/
instance nativeProjectivePointCentre : Fact (IsClosedSubmanifold 2 ({blowdownOrigin} :
    Set (SGPT.Projective.ComplexProjectiveSpace 2))) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence blowdownOrigin).1⟩

/-- The actual singleton has empty interior; a genuine punctured projective
line curve approaches it through noncentral points. -/
theorem projective_origin_interior_empty :
    interior ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) = ∅ := by
  let f : ℂ → SGPT.Projective.ComplexProjectiveSpace 2 :=
    fun t => originalBlowdown blowup_edgeSmooth (blowupOriginalChartPoint blowup_edgeSmooth 0 ![t, 0])
  have hf : Continuous f := (contMDiff_originalBlowdown blowup_edgeSmooth).continuous.comp
    ((continuous_blowupOriginalChartPoint blowup_edgeSmooth 0).comp (by
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop))
  have hf0 : f 0 = blowdownOrigin := by
    change originalBlowdown blowup_edgeSmooth
      (blowupOriginalChartPoint blowup_edgeSmooth 0 ![0, 0]) = blowdownOrigin
    rw [originalBlowdown_chart, projective_mk_eq_blowdownOrigin_iff]
    simp [blowdownChartVector]
  have hs : f '' ({(0 : ℂ)}ᶜ) ⊆ ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))ᶜ := by
    rintro p ⟨t, ht, rfl⟩ hbad
    have hbad' : originalBlowdown blowup_edgeSmooth
        (blowupOriginalChartPoint blowup_edgeSmooth 0 ![t, 0]) = blowdownOrigin := hbad
    rw [originalBlowdown_chart, projective_mk_eq_blowdownOrigin_iff] at hbad'
    exact ht hbad'.1
  have hclosure := mem_closure_image hf.continuousAt (dense_compl_singleton (0 : ℂ) 0)
  rw [hf0] at hclosure
  have hnot : blowdownOrigin ∉ interior ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) := by
    have h := closure_mono hs hclosure
    rwa [closure_compl] at h
  apply Subset.antisymm
  · intro p hp
    have heq : p = blowdownOrigin := Set.mem_singleton_iff.mp
      (show p ∈ ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) from interior_subset hp)
    exact (hnot (heq ▸ hp)).elim
  · exact empty_subset _

/-- The already constructed native intrinsic point blowup, on the literal
projective base and literal book origin, with its unchanged native topology. -/
abbrev NativeProjectivePointBlowup :=
  BlowupConstruction.BlowupSpace 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))

def nativeProjectivePointBlowupProjection : NativeProjectivePointBlowup →
    SGPT.Projective.ComplexProjectiveSpace 2 := BlowupConstruction.blowupProj 2 _

/-- The existing genuine native point-ideal universal property applies to
this literal base and centre, internally supplying the entire native UP. -/
theorem nativeProjectivePointBlowup_isBlowupAlong :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
      nativeProjectivePointBlowupProjection :=
  BlowupConstruction.isBlowupAlong_blowupProj projective_origin_interior_empty

/-- The actual identity flattening in the FORCED native chart at the
literal projective origin, with whole affine source and target. -/
def projectiveOriginFlattening : LocalHolomorphicEquivAt (n := 2)
    (chartAt (ComplexModel 2) blowdownOrigin blowdownOrigin) where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := id
  invFun := id
  toFun_holomorphic := differentiableOn_id
  invFun_holomorphic := differentiableOn_id
  mapsTo_toFun := mapsTo_univ _ _
  mapsTo_invFun := mapsTo_univ _ _
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

theorem projectiveOriginFlattening_source :
    projectiveOriginFlattening.source ⊆ (chartAt (ComplexModel 2) blowdownOrigin).target := by
  change univ ⊆ (chartAt (ComplexModel 2) blowdownOrigin).target
  rw [projective_chartAt_origin]
  simp

/-- The point centre is the actual zero-coordinate plane in its actual
forced native chart, with no supplied flattening or geometric certificate. -/
theorem projectiveOriginFlattening_centre
    {q : SGPT.Projective.ComplexProjectiveSpace 2}
    (hq : q ∈ (chartAt (ComplexModel 2) blowdownOrigin).source)
    (_ : chartAt (ComplexModel 2) blowdownOrigin q ∈ projectiveOriginFlattening.source) :
    (q ∈ ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) ↔
      projectiveOriginFlattening.toFun (chartAt (ComplexModel 2) blowdownOrigin q) ∈
        complexCoordinatePlane 2 0) := by
  change q = blowdownOrigin ↔ ∀ i : Fin 2, 0 ≤ i.val →
    chartAt (ComplexModel 2) blowdownOrigin q i = 0
  rw [projective_chartAt_origin] at hq ⊢
  constructor
  · intro h
    subst q
    rw [projective_origin_chart_zero]
    intro i _
    rfl
  · intro h
    apply (SGPT.Projective.ComplexProjectiveSpace.affineChart 0).injOn hq
      ((SGPT.Projective.ComplexProjectiveSpace.mk_mem_affineChart_source_iff 0 _).mpr one_ne_zero)
    change SGPT.Projective.ComplexProjectiveSpace.affineChart 0 q =
      SGPT.Projective.ComplexProjectiveSpace.affineChart 0 blowdownOrigin
    rw [projective_origin_chart_zero]
    ext i
    exact h i (Nat.zero_le _)

/-- The two actual normal-index charts in the EXISTING native blowup, with
all standard pullback ideal/universal-property infrastructure unchanged. -/
def nativeProjectivePointNormalData (j : Fin 2) : BlowupConstruction.FlatChart 2
    ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) where
  y₀ := blowdownOrigin
  k := 0
  Φ := projectiveOriginFlattening
  hsrc := projectiveOriginFlattening_source
  hflat := projectiveOriginFlattening_centre
  j := j
  hj := Nat.zero_le _

def nativeProjectivePointNormalChart (j : Fin 2) :
    OpenPartialHomeomorph NativeProjectivePointBlowup (ComplexModel 2) :=
  (nativeProjectivePointNormalData j).homeo

theorem nativeProjectivePointNormalChart_target (j : Fin 2) :
    (nativeProjectivePointNormalChart j).target = univ := by
  change (nativeProjectivePointNormalData j).target = univ
  simp [BlowupConstruction.FlatChart.target, nativeProjectivePointNormalData, projectiveOriginFlattening]

/-- Actual native chart projection, before any comparison with the toric
manifold; all boundary points are retained in the whole affine chart. -/
theorem nativeProjectivePointNormalChart_projection (j : Fin 2) (w : ComplexModel 2) :
    nativeProjectivePointBlowupProjection ((nativeProjectivePointNormalChart j).symm w) =
      SGPT.Projective.ComplexProjectiveSpace.affinePoint 0 (BlowupMonomialCharts.monomial 0 j w) := by
  have hw : w ∈ (nativeProjectivePointNormalData j).target := by
    change w ∈ (nativeProjectivePointNormalChart j).target
    rw [nativeProjectivePointNormalChart_target]
    exact mem_univ _
  change BlowupConstruction.blowupProj 2 _ ((nativeProjectivePointNormalData j).invFun w) = _
  rw [(nativeProjectivePointNormalData j).blowupProj_invFun hw]
  change (chartAt (ComplexModel 2) blowdownOrigin).symm (BlowupMonomialCharts.monomial 0 j w) = _
  rw [projective_chartAt_origin, SGPT.Projective.ComplexProjectiveSpace.affineChart_symm_apply]

end SGPT.Toric.BlowdownDraft

end
/- END NativeProjectivePointBlowupDraft -/
end PointBlowupCanonicalFragment001

section PointBlowupCanonicalFragment002
/- BEGIN NativeProjectivePointFourChartsDraft; original source SHA256 0ebbe153c3d58a8ce5695c9fa54b23e4fd31dae9027bd6951d7c9800b4234e1f -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

theorem projective_chartAt_basisPoint (i : Fin 3) :
    chartAt (ComplexModel 2) (nativeProjectiveBasisPoint i) =
      SGPT.Projective.ComplexProjectiveSpace.affineChart i := by
  change SGPT.Projective.ComplexProjectiveSpace.affineChart
    (SGPT.Projective.ComplexProjectiveSpace.chartIndex (nativeProjectiveBasisPoint i)) = _
  rw [projective_chartIndex_basisPoint]

theorem projective_origin_not_mem_nonzero_chart (i : Fin 2) :
    blowdownOrigin ∉ (SGPT.Projective.ComplexProjectiveSpace.affineChart i.succ).source := by
  intro h
  change SGPT.Projective.ComplexProjectiveSpace.mk (![1, 0, 0] : Fin 3 → ℂ) _ ∈ _ at h
  have hc : (![1, 0, 0] : Fin 3 → ℂ) i.succ ≠ 0 :=
    (SGPT.Projective.ComplexProjectiveSpace.mk_mem_affineChart_source_iff _ _).mp h
  fin_cases i <;> simp at hc

/-- The two EXISTING native off-centre charts, rooted at the actual other
two projective coordinate points. -/
def nativeProjectivePointOffData (i : Fin 2) : BlowupConstruction.OffChart 2
    ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) where
  x₀ := nativeProjectiveBasisPoint i.succ
  hx₀ := by
    intro h
    have heq : nativeProjectiveBasisPoint i.succ = blowdownOrigin := Set.mem_singleton_iff.mp h
    have hi := congrArg SGPT.Projective.ComplexProjectiveSpace.chartIndex heq
    rw [projective_chartIndex_basisPoint, ← nativeProjectiveBasisPoint_zero,
      projective_chartIndex_basisPoint] at hi
    have hval := congrArg Fin.val hi
    simp at hval

def nativeProjectivePointOffChart (i : Fin 2) :
    OpenPartialHomeomorph NativeProjectivePointBlowup (ComplexModel 2) :=
  BlowupConstruction.atlasHomeo (nativeProjectivePointOffData i).toPartialEquiv
    (Or.inr ⟨nativeProjectivePointOffData i, rfl⟩)

theorem nativeProjectivePointOffChart_target (i : Fin 2) :
    (nativeProjectivePointOffChart i).target = univ := by
  change (nativeProjectivePointOffData i).toPartialEquiv.target = univ
  rw [BlowupConstruction.OffChart.target_eq]
  have he : (nativeProjectivePointOffData i).e =
      SGPT.Projective.ComplexProjectiveSpace.affineChart i.succ := projective_chartAt_basisPoint i.succ
  rw [he]
  apply Set.eq_univ_of_forall
  intro z
  refine ⟨by simp, ?_⟩
  intro h
  have heq : (SGPT.Projective.ComplexProjectiveSpace.affineChart i.succ).symm z = blowdownOrigin :=
    Set.mem_singleton_iff.mp h
  have hz := (SGPT.Projective.ComplexProjectiveSpace.affineChart i.succ).map_target (by simp : z ∈ _)
  rw [heq] at hz
  exact projective_origin_not_mem_nonzero_chart i hz

theorem nativeProjectivePointOffChart_projection (i : Fin 2) (w : ComplexModel 2) :
    nativeProjectivePointBlowupProjection ((nativeProjectivePointOffChart i).symm w) =
      SGPT.Projective.ComplexProjectiveSpace.affinePoint i.succ w := by
  have hw : w ∈ (nativeProjectivePointOffData i).toPartialEquiv.target := by
    change w ∈ (nativeProjectivePointOffChart i).target
    rw [nativeProjectivePointOffChart_target]
    exact mem_univ _
  have hn : (nativeProjectivePointOffData i).e.symm w ∉
      ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2)) := hw.2
  change nativeProjectivePointBlowupProjection ((nativeProjectivePointOffData i).toPartialEquiv.symm w) = _
  rw [(nativeProjectivePointOffData i).symm_apply_of_not_mem hn]
  change (nativeProjectivePointOffData i).e.symm w = _
  rw [show (nativeProjectivePointOffData i).e =
    SGPT.Projective.ComplexProjectiveSpace.affineChart i.succ from projective_chartAt_basisPoint i.succ,
      SGPT.Projective.ComplexProjectiveSpace.affineChart_symm_apply]

/-- The native point blowup has the same four whole affine chart types as
the original toric model, before the actual comparison is constructed. -/
def nativeProjectivePointChart : Fin 4 →
    OpenPartialHomeomorph NativeProjectivePointBlowup (ComplexModel 2) :=
  ![nativeProjectivePointNormalChart 0, nativeProjectivePointOffChart 0,
    nativeProjectivePointOffChart 1, nativeProjectivePointNormalChart 1]

theorem nativeProjectivePointChart_target (k : Fin 4) :
    (nativeProjectivePointChart k).target = univ := by
  fin_cases k
  · exact nativeProjectivePointNormalChart_target 0
  · exact nativeProjectivePointOffChart_target 0
  · exact nativeProjectivePointOffChart_target 1
  · exact nativeProjectivePointNormalChart_target 1

/-- The native chart at X1≠0 uses (s,t); the actual original source order is
(t,s). The single interchange is DERIVED explicitly, and all other orders
are identical to the original primitive source basis order. -/
def nativeProjectivePointChartInput (k : Fin 4) (z : ComplexModel 2) : ComplexModel 2 :=
  ![z, modelPoint ![z 1, z 0], z, z] k

def nativeProjectivePointChartPoint (k : Fin 4) (z : Fin 2 → ℂ) : NativeProjectivePointBlowup :=
  (nativeProjectivePointChart k).symm (nativeProjectivePointChartInput k (modelPoint z))

theorem nativeProjectivePointChartPoint_projection (k : Fin 4) (z : Fin 2 → ℂ) :
    nativeProjectivePointBlowupProjection (nativeProjectivePointChartPoint k z) =
      SGPT.Projective.ComplexProjectiveSpace.mk (blowdownChartVector k z)
        (blowdownChartVector_ne_zero k z) := by
  fin_cases k
  · change nativeProjectivePointBlowupProjection ((nativeProjectivePointNormalChart 0).symm (modelPoint z)) = _
    rw [nativeProjectivePointNormalChart_projection]
    unfold SGPT.Projective.ComplexProjectiveSpace.affinePoint
    congr 1
    funext i
    fin_cases i <;> simp [SGPT.Projective.ComplexProjectiveSpace.affineLift,
      BlowupMonomialCharts.monomial_apply, blowdownChartVector]
    change z 1 * z 0 = z 0 * z 1
    ring
  · change nativeProjectivePointBlowupProjection ((nativeProjectivePointOffChart 0).symm (modelPoint ![z 1, z 0])) = _
    rw [nativeProjectivePointOffChart_projection]
    unfold SGPT.Projective.ComplexProjectiveSpace.affinePoint
    congr 1
    funext i
    fin_cases i <;> simp [SGPT.Projective.ComplexProjectiveSpace.affineLift,
      blowdownChartVector] <;> rfl
  · change nativeProjectivePointBlowupProjection ((nativeProjectivePointOffChart 1).symm (modelPoint z)) = _
    rw [nativeProjectivePointOffChart_projection]
    unfold SGPT.Projective.ComplexProjectiveSpace.affinePoint
    congr 1
    funext i
    fin_cases i <;> simp [SGPT.Projective.ComplexProjectiveSpace.affineLift,
      blowdownChartVector] <;> rfl
  · change nativeProjectivePointBlowupProjection ((nativeProjectivePointNormalChart 1).symm (modelPoint z)) = _
    rw [nativeProjectivePointNormalChart_projection]
    unfold SGPT.Projective.ComplexProjectiveSpace.affinePoint
    congr 1
    funext i
    fin_cases i <;> simp [SGPT.Projective.ComplexProjectiveSpace.affineLift,
      BlowupMonomialCharts.monomial_apply, blowdownChartVector]
    rfl

/-- The two prescribed actual point-normal native charts cover EVERY point
over the actual original projective affine0 open, including every direction
at the centre. No preferred native flattening is substituted. -/
theorem exists_mem_prescribed_nativePointNormalChart (p : NativeProjectivePointBlowup)
    (hp : p.base ∈ (SGPT.Projective.ComplexProjectiveSpace.affineChart 0).source) :
    ∃ j, p ∈ (nativeProjectivePointNormalChart j).source := by
  have hdom : p.base ∈ BlowupFlatCoordinates.flatDomain projectiveOriginFlattening := by
    exact ⟨by rwa [projective_chartAt_origin], mem_univ _⟩
  have hex : ∃ j : Fin 2, BlowupConstruction.extVal
      (BlowupFlatCoordinates.flatCoord projectiveOriginFlattening j) p ≠ 0 := by
    by_cases hC : p.base ∈ ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
    · have hnot := BlowupConstruction.BlowupSpace.dirVec_not_mem hC
      rw [BlowupSpaceTangent.mem_tangentSpace_iff projectiveOriginFlattening_source
        projectiveOriginFlattening_centre hdom hC] at hnot
      push Not at hnot
      obtain ⟨j, _, hj⟩ := hnot
      refine ⟨j, ?_⟩
      rw [BlowupConstruction.extVal_of_mem hC]
      exact hj
    · by_contra h
      push Not at h
      have hplane : projectiveOriginFlattening.toFun
          (chartAt (ComplexModel 2) blowdownOrigin p.base) ∈ complexCoordinatePlane 2 0 := by
        intro j _
        have hj := h j
        rw [BlowupConstruction.extVal_of_not_mem hC] at hj
        exact hj
      exact hC ((projectiveOriginFlattening_centre hdom.1 hdom.2).mpr hplane)
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hdom, hj⟩

/-- The four explicitly manufactured native point-blowup charts cover the
ENTIRE native UP object, including all projective boundary points. -/
theorem nativeProjectivePointChart_cover (p : NativeProjectivePointBlowup) :
    ∃ k, p ∈ (nativeProjectivePointChart k).source := by
  obtain ⟨i, hi⟩ := SGPT.Projective.ComplexProjectiveSpace.exists_mem_affineChart_source p.base
  fin_cases i
  · obtain ⟨j, hj⟩ := exists_mem_prescribed_nativePointNormalChart p hi
    fin_cases j
    · exact ⟨0, hj⟩
    · exact ⟨3, hj⟩
  · refine ⟨1, ?_⟩
    change p.base ∈ (chartAt (ComplexModel 2) (nativeProjectiveBasisPoint 1)).source ∧ p.base ∉ {blowdownOrigin}
    refine ⟨by rwa [projective_chartAt_basisPoint], ?_⟩
    intro h
    have heq : p.base = blowdownOrigin := Set.mem_singleton_iff.mp h
    rw [heq] at hi
    exact projective_origin_not_mem_nonzero_chart 0 hi
  · refine ⟨2, ?_⟩
    change p.base ∈ (chartAt (ComplexModel 2) (nativeProjectiveBasisPoint 2)).source ∧ p.base ∉ {blowdownOrigin}
    refine ⟨by rwa [projective_chartAt_basisPoint], ?_⟩
    intro h
    have heq : p.base = blowdownOrigin := Set.mem_singleton_iff.mp h
    rw [heq] at hi
    exact projective_origin_not_mem_nonzero_chart 1 hi

end SGPT.Toric.BlowdownDraft

end
/- END NativeProjectivePointFourChartsDraft -/
end PointBlowupCanonicalFragment002

section PointBlowupCanonicalFragment003
/- BEGIN OriginalNativeBlowupLocalMapsDraft; original source SHA256 ff89a36da8e37a62a7cdcbb5dd285cb3a7fc4933359f1adcfec2998f918e6a4e -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

/-- Actual native chart membership, with the existing native blowup atlas. -/
theorem nativeProjectivePointChart_mem_atlas (k : Fin 4) :
    nativeProjectivePointChart k ∈ atlas (ComplexModel 2) NativeProjectivePointBlowup := by
  fin_cases k
  · exact BlowupConstruction.atlasHomeo_mem_atlas (nativeProjectivePointNormalData 0).toPartialEquiv
      (Or.inl ⟨nativeProjectivePointNormalData 0, rfl⟩)
  · exact BlowupConstruction.atlasHomeo_mem_atlas (nativeProjectivePointOffData 0).toPartialEquiv
      (Or.inr ⟨nativeProjectivePointOffData 0, rfl⟩)
  · exact BlowupConstruction.atlasHomeo_mem_atlas (nativeProjectivePointOffData 1).toPartialEquiv
      (Or.inr ⟨nativeProjectivePointOffData 1, rfl⟩)
  · exact BlowupConstruction.atlasHomeo_mem_atlas (nativeProjectivePointNormalData 1).toPartialEquiv
      (Or.inl ⟨nativeProjectivePointNormalData 1, rfl⟩)

theorem nativeProjectivePointChartInput_involutive (k : Fin 4) (z : ComplexModel 2) :
    nativeProjectivePointChartInput k (nativeProjectivePointChartInput k z) = z := by
  fin_cases k
  · rfl
  · ext i
    fin_cases i <;> rfl
  · rfl
  · rfl

theorem contDiff_nativeProjectivePointChartInput (k : Fin 4) :
    ContDiff ℂ ∞ (nativeProjectivePointChartInput k) := by
  fin_cases k
  · exact contDiff_id
  · apply (contDiff_piLp 2).mpr
    intro j
    fin_cases j
    · exact (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).contDiff
  · exact contDiff_id
  · exact contDiff_id

/-- The actual native inverse charts are globally holomorphic on their
proved WHOLE affine targets, including all exceptional directions. -/
theorem contMDiff_nativeProjectivePointChart_symm (k : Fin 4) :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (nativeProjectivePointChart k).symm := by
  intro z
  exact (contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
      (M := NativeProjectivePointBlowup) (nativeProjectivePointChart_mem_atlas k))).contMDiffAt
        (by rw [nativeProjectivePointChart_target]; exact Filter.univ_mem)

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Derived source basis order, expressed as an actual linear permutation
of the unchanged native complex model. -/
def originalOrderedModelCoordinates (k : Fin 4) (z : ComplexModel 2) : ComplexModel 2 :=
  modelPoint (fun j => z ((blowupOriginalPermutation hs k).symm j))

theorem contDiff_originalOrderedModelCoordinates (k : Fin 4) :
    ContDiff ℂ ∞ (originalOrderedModelCoordinates hs k) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (EuclideanSpace.proj (𝕜 := ℂ) ((blowupOriginalPermutation hs k).symm j)).contDiff

theorem originalOrderedModelCoordinates_native (k : Fin 4) (z : Fin 2 → ℂ) :
    originalOrderedModelCoordinates hs k (blowupOriginalCoordinates hs k z) = modelPoint z := by
  ext j
  simp [originalOrderedModelCoordinates, blowupOriginalCoordinates, modelPoint_apply]

/-- Genuine local map from an ACTUAL original chart into the EXISTING native
intrinsic point-blowup object, using the matching actual affine charts. -/
def originalToNativeBlowupLocal (k : Fin 4) (p : PolytopeToricVariety blowupGenerator hs) :
    NativeProjectivePointBlowup :=
  (nativeProjectivePointChart k).symm (nativeProjectivePointChartInput k
    (originalOrderedModelCoordinates hs k
      (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) p)))

theorem originalToNativeBlowupLocal_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    originalToNativeBlowupLocal hs k (blowupOriginalChartPoint hs k z) =
      nativeProjectivePointChartPoint k z := by
  unfold originalToNativeBlowupLocal nativeProjectivePointChartPoint
  rw [blowupOriginalChartPoint_coordinate, originalOrderedModelCoordinates_native]

/-- Holomorphy on the ENTIRE actual original vertex open, not only its torus. -/
theorem contMDiffOn_originalToNativeBlowupLocal (k : Fin 4) :
    ContMDiffOn 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞
      (originalToNativeBlowupLocal hs k)
      (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source := by
  intro p hp
  let cs : OpenPartialHomeomorph (PolytopeToricVariety blowupGenerator hs) (ComplexModel 2) :=
    originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)
  have hcs : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ cs p :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := PolytopeToricVariety blowupGenerator hs)
        (show cs ∈ atlas (ComplexModel 2) (PolytopeToricVariety blowupGenerator hs) from ⟨blowupVertex k, rfl⟩)) hp
  exact ((contMDiff_nativeProjectivePointChart_symm k).contMDiffAt.comp p
    ((contDiff_nativeProjectivePointChartInput k).contMDiff.contMDiffAt.comp p
      ((contDiff_originalOrderedModelCoordinates hs k).contMDiff.contMDiffAt.comp p hcs))).contMDiffWithinAt

/-- Actual local comparison commutes with the literal projective base on
all source boundary strata, proved from the two independent chart formulas. -/
theorem originalToNativeBlowupLocal_projection (k : Fin 4)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source) :
    nativeProjectivePointBlowupProjection (originalToNativeBlowupLocal hs k p) = originalBlowdown hs p := by
  obtain ⟨z, rfl⟩ := exists_blowupOriginalChartPoint_of_mem hs k p hp
  rw [originalToNativeBlowupLocal_chart, nativeProjectivePointChartPoint_projection, originalBlowdown_chart]

/-- Every genuine original torus point maps off the literal centre. -/
theorem originalBlowdown_torus_ne_origin (a : Fin 2 → ℂˣ) :
    originalBlowdown hs (polytopeToricEmbedding blowupGenerator hs a) ≠ blowdownOrigin := by
  have h := congrArg (simplexProjectiveHomeomorph targetSimplexSmooth)
    (originalBlowdownToSimplex_torus hs a)
  simp only [originalBlowdownToSimplex, Function.comp_apply, Homeomorph.apply_symm_apply,
    simplexProjectiveHomeomorph_embedding] at h
  intro hbad
  have hz := (projective_mk_eq_blowdownOrigin_iff _ _).mp (h.symm.trans hbad)
  exact Units.ne_zero (a 0) (show (a 0 : ℂ) = 0 from hz.1)

end SGPT.Toric.BlowdownDraft

end
/- END OriginalNativeBlowupLocalMapsDraft -/
end PointBlowupCanonicalFragment003

section PointBlowupCanonicalFragment004
/- BEGIN OriginalNativeBlowupGlobalMapDraft; original source SHA256 ad9c6616085e58555a8490377f4329efe58e60a8a9627ed29931eae1056d1f7c -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem exists_originalBlowupVertexSource (p : PolytopeToricVariety blowupGenerator hs) :
    ∃ k, p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source := by
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  exact ⟨k, blowupOriginalChartPoint_mem hs k z⟩

/-- Internal finite-cover choice, with no incoming geometric or overlap
certificate and no continuity asserted for the raw choice. -/
def originalBlowupVertexSourceIndex (p : PolytopeToricVariety blowupGenerator hs) : Fin 4 :=
  (exists_originalBlowupVertexSource hs p).choose

theorem originalBlowupVertexSourceIndex_mem (p : PolytopeToricVariety blowupGenerator hs) :
    p ∈ (originalPolytopeNativeModelChart blowupGenerator hs
      (blowupVertex (originalBlowupVertexSourceIndex hs p))).source :=
  (exists_originalBlowupVertexSource hs p).choose_spec

/-- The ACTUAL original map to the EXISTING native intrinsic blowup object,
manufactured from the two independently proved geometric chart systems. -/
def originalToNativePointBlowup (p : PolytopeToricVariety blowupGenerator hs) :
    NativeProjectivePointBlowup :=
  originalToNativeBlowupLocal hs (originalBlowupVertexSourceIndex hs p) p

/-- Agreement on the genuine dense original torus and native singleton
fibres off the centre proves compatibility on EVERY actual overlap,
including all original exceptional and projective boundary points. -/
theorem originalToNativePointBlowup_eq_local (k : Fin 4)
    {p : PolytopeToricVariety blowupGenerator hs}
    (hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source) :
    originalToNativePointBlowup hs p = originalToNativeBlowupLocal hs k p := by
  let w := originalBlowupVertexSourceIndex hs p
  have hw : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex w)).source :=
    originalBlowupVertexSourceIndex_mem hs p
  let U := (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex w)).source ∩
    (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source
  have hU : IsOpen U :=
    (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex w)).open_source.inter
      (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).open_source
  have hf : ContinuousOn (originalToNativeBlowupLocal hs w) U :=
    (contMDiffOn_originalToNativeBlowupLocal hs w).continuousOn.mono inter_subset_left
  have hg : ContinuousOn (originalToNativeBlowupLocal hs k) U :=
    (contMDiffOn_originalToNativeBlowupLocal hs k).continuousOn.mono inter_subset_right
  have heq := toricCartier_eqOn_of_denseTorus U hU _ _ hf hg (by
    intro a ha
    apply BlowupConstruction.eq_of_base_eq_of_not_mem
    · change nativeProjectivePointBlowupProjection (originalToNativeBlowupLocal hs w
        (polytopeToricEmbedding blowupGenerator hs a)) =
          nativeProjectivePointBlowupProjection (originalToNativeBlowupLocal hs k
            (polytopeToricEmbedding blowupGenerator hs a))
      rw [originalToNativeBlowupLocal_projection hs w ha.1,
        originalToNativeBlowupLocal_projection hs k ha.2]
    · change nativeProjectivePointBlowupProjection (originalToNativeBlowupLocal hs w
        (polytopeToricEmbedding blowupGenerator hs a)) ∉ {blowdownOrigin}
      rw [originalToNativeBlowupLocal_projection hs w ha.1]
      exact fun hz => originalBlowdown_torus_ne_origin hs a hz)
  exact heq ⟨hw, hp⟩

/-- The genuine original-to-intrinsic comparison is holomorphic on the
ENTIRE same original compact manifold, proved by its exact local formulas. -/
theorem contMDiff_originalToNativePointBlowup :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalToNativePointBlowup hs) := by
  intro p
  let k := originalBlowupVertexSourceIndex hs p
  have hp : p ∈ (originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).source :=
    originalBlowupVertexSourceIndex_mem hs p
  apply ((contMDiffOn_originalToNativeBlowupLocal hs k).contMDiffAt
    ((originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).open_source.mem_nhds hp)).congr_of_eventuallyEq
  filter_upwards [(originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)).open_source.mem_nhds hp] with q hq
  exact originalToNativePointBlowup_eq_local hs k hq

/-- The comparison is literally OVER the unchanged projective base. -/
theorem originalToNativePointBlowup_projection (p : PolytopeToricVariety blowupGenerator hs) :
    nativeProjectivePointBlowupProjection (originalToNativePointBlowup hs p) = originalBlowdown hs p :=
  originalToNativeBlowupLocal_projection hs (originalBlowupVertexSourceIndex hs p)
    (originalBlowupVertexSourceIndex_mem hs p)

/-- Actual global readback in every entire original affine chart. -/
theorem originalToNativePointBlowup_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    originalToNativePointBlowup hs (blowupOriginalChartPoint hs k z) =
      nativeProjectivePointChartPoint k z := by
  rw [originalToNativePointBlowup_eq_local hs k (blowupOriginalChartPoint_mem hs k z),
    originalToNativeBlowupLocal_chart]

end SGPT.Toric.BlowdownDraft

end
/- END OriginalNativeBlowupGlobalMapDraft -/
end PointBlowupCanonicalFragment004

section PointBlowupCanonicalFragment005
/- BEGIN NativeOriginalBlowupInverseLocalDraft; original source SHA256 a17dcc4eeae678396a458a3717c1d0051299d73825368ba72083968bfc3737df -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

theorem nativeProjectivePointChartPoint_mem (k : Fin 4) (z : Fin 2 → ℂ) :
    nativeProjectivePointChartPoint k z ∈ (nativeProjectivePointChart k).source := by
  apply (nativeProjectivePointChart k).map_target
  rw [nativeProjectivePointChart_target]
  exact mem_univ _

/-- Every point of a specified genuine native chart is produced by that
SAME native whole-affine parametrization in the actual original order. -/
theorem exists_nativeProjectivePointChartPoint_of_mem (k : Fin 4)
    (q : NativeProjectivePointBlowup) (hq : q ∈ (nativeProjectivePointChart k).source) :
    ∃ z, nativeProjectivePointChartPoint k z = q := by
  let w := nativeProjectivePointChartInput k (nativeProjectivePointChart k q)
  refine ⟨fun j => w j, ?_⟩
  have hw : modelPoint (fun j => w j) = w := by ext j; rfl
  unfold nativeProjectivePointChartPoint
  rw [hw]
  change (nativeProjectivePointChart k).symm
    (nativeProjectivePointChartInput k (nativeProjectivePointChartInput k (nativeProjectivePointChart k q))) = q
  rw [nativeProjectivePointChartInput_involutive]
  exact (nativeProjectivePointChart k).left_inv hq

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- Actual inverse source basis permutation, as a complex linear polynomial. -/
def originalNativeModelCoordinates (k : Fin 4) (z : ComplexModel 2) : ComplexModel 2 :=
  modelPoint (fun j => z (blowupOriginalPermutation hs k j))

theorem contDiff_originalNativeModelCoordinates (k : Fin 4) :
    ContDiff ℂ ∞ (originalNativeModelCoordinates hs k) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (EuclideanSpace.proj (𝕜 := ℂ) (blowupOriginalPermutation hs k j)).contDiff

def originalOrderedChartParam (k : Fin 4) (z : ComplexModel 2) :
    PolytopeToricVariety blowupGenerator hs := blowupOriginalChartPoint hs k (fun j => z j)

/-- Entire holomorphic parametrization in the actual original source
chart, using its internally derived primitive coordinate order. -/
theorem contMDiff_originalOrderedChartParam (k : Fin 4) :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalOrderedChartParam hs k) := by
  let cs : OpenPartialHomeomorph (PolytopeToricVariety blowupGenerator hs) (ComplexModel 2) :=
    originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k)
  have hinv : ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ cs.symm := by
    intro z
    exact (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := PolytopeToricVariety blowupGenerator hs)
        (show originalPolytopeNativeModelChart blowupGenerator hs (blowupVertex k) ∈
          atlas (ComplexModel 2) (PolytopeToricVariety blowupGenerator hs) from ⟨blowupVertex k, rfl⟩))).contMDiffAt
            (by rw [originalPolytopeNativeModelChart_target]; exact Filter.univ_mem)
  exact hinv.comp (contDiff_originalNativeModelCoordinates hs k).contMDiff

/-- Genuine local inverse from each ACTUAL intrinsic point-blowup chart to
the SAME original toric manifold. -/
def nativeToOriginalBlowupLocal (k : Fin 4) (q : NativeProjectivePointBlowup) :
    PolytopeToricVariety blowupGenerator hs :=
  originalOrderedChartParam hs k (nativeProjectivePointChartInput k (nativeProjectivePointChart k q))

theorem nativeToOriginalBlowupLocal_chart (k : Fin 4) (z : Fin 2 → ℂ) :
    nativeToOriginalBlowupLocal hs k (nativeProjectivePointChartPoint k z) =
      blowupOriginalChartPoint hs k z := by
  have ht : nativeProjectivePointChartInput k (modelPoint z) ∈ (nativeProjectivePointChart k).target := by
    rw [nativeProjectivePointChart_target]
    exact mem_univ _
  unfold nativeToOriginalBlowupLocal nativeProjectivePointChartPoint
  rw [(nativeProjectivePointChart k).right_inv ht, nativeProjectivePointChartInput_involutive]
  rfl

/-- The local inverse is holomorphic on the ENTIRE native chart source,
including every native exceptional direction and projective boundary. -/
theorem contMDiffOn_nativeToOriginalBlowupLocal (k : Fin 4) :
    ContMDiffOn 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (nativeToOriginalBlowupLocal hs k)
      (nativeProjectivePointChart k).source := by
  intro q hq
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (nativeProjectivePointChart k) q :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℂ, ComplexModel 2)) (n := ∞)
        (M := NativeProjectivePointBlowup) (nativeProjectivePointChart_mem_atlas k)) hq
  exact ((contMDiff_originalOrderedChartParam hs k).contMDiffAt.comp q
    ((contDiff_nativeProjectivePointChartInput k).contMDiff.contMDiffAt.comp q hc)).contMDiffWithinAt

/-- The actual inverse local map is also literally OVER the unchanged
projective base. -/
theorem nativeToOriginalBlowupLocal_projection (k : Fin 4)
    {q : NativeProjectivePointBlowup} (hq : q ∈ (nativeProjectivePointChart k).source) :
    originalBlowdown hs (nativeToOriginalBlowupLocal hs k q) = nativeProjectivePointBlowupProjection q := by
  obtain ⟨z, rfl⟩ := exists_nativeProjectivePointChartPoint_of_mem k q hq
  rw [nativeToOriginalBlowupLocal_chart, originalBlowdown_chart, nativeProjectivePointChartPoint_projection]

end SGPT.Toric.BlowdownDraft

end
/- END NativeOriginalBlowupInverseLocalDraft -/
end PointBlowupCanonicalFragment005

section PointBlowupCanonicalFragment006
/- BEGIN NativeBlowupDenseOffCentreDraft; original source SHA256 beada0cf6e82e6a5124500978b308b0ea43d711b02b8c69aae2194734aa3a8a5 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

def projectiveBaseDirectionVector (p : SGPT.Projective.ComplexProjectiveSpace 2) : Fin 2 → ℂ :=
  ![p.rep 1, p.rep 2]

theorem projectiveBaseDirectionVector_ne_zero (p : SGPT.Projective.ComplexProjectiveSpace 2)
    (hp : p ≠ blowdownOrigin) : projectiveBaseDirectionVector p ≠ 0 := by
  intro h
  have h1 : p.rep 1 = 0 := congrFun h 0
  have h2 : p.rep 2 = 0 := congrFun h 1
  have heq := (projective_mk_eq_blowdownOrigin_iff p.rep p.rep_ne_zero).mpr ⟨h1, h2⟩
  rw [SGPT.Projective.ComplexProjectiveSpace.mk_rep] at heq
  exact hp heq

/-- At every actual noncentral projective point the literal incidence
equation uniquely fixes the entire actual projective direction. -/
theorem projectiveDirection_eq_of_incidence
    (p : SGPT.Projective.ComplexProjectiveSpace 2) (hp : p ≠ blowdownOrigin)
    (u : SGPT.Projective.ComplexProjectiveSpace 1)
    (hinc : p.rep 1 * u.rep 1 = p.rep 2 * u.rep 0) :
    u = SGPT.Projective.ComplexProjectiveSpace.mk (projectiveBaseDirectionVector p)
      (projectiveBaseDirectionVector_ne_zero p hp) := by
  conv_lhs => rw [← SGPT.Projective.ComplexProjectiveSpace.mk_rep u]
  apply (SGPT.Projective.ComplexProjectiveSpace.mk_eq_mk_iff _ _).mpr
  by_cases h1 : p.rep 1 = 0
  · have h2 : p.rep 2 ≠ 0 := by
      intro h2
      apply projectiveBaseDirectionVector_ne_zero p hp
      funext i
      fin_cases i <;> simp [projectiveBaseDirectionVector, h1, h2]
    have hu0 : u.rep 0 = 0 :=
      (mul_eq_zero.mp (by simpa [h1] using hinc.symm)).resolve_left h2
    refine ⟨u.rep 1 / p.rep 2, ?_⟩
    funext i
    fin_cases i
    · change (u.rep 1 / p.rep 2) * p.rep 1 = u.rep 0
      simp [h1, hu0]
    · change (u.rep 1 / p.rep 2) * p.rep 2 = u.rep 1
      exact div_mul_cancel₀ _ h2
  · refine ⟨u.rep 0 / p.rep 1, ?_⟩
    funext i
    fin_cases i
    · change (u.rep 0 / p.rep 1) * p.rep 1 = u.rep 0
      exact div_mul_cancel₀ _ h1
    · change (u.rep 0 / p.rep 1) * p.rep 2 = u.rep 1
      field_simp
      linear_combination -hinc

/-- The actual original blowdown is genuinely injective outside the literal
centre, derived from the independently proved incidence identification. -/
theorem originalBlowdown_injective_off_origin
    (hs : latticePolytopeEdgeSmooth blowupGenerator)
    {p q : PolytopeToricVariety blowupGenerator hs}
    (hπ : originalBlowdown hs p = originalBlowdown hs q)
    (hp : originalBlowdown hs p ≠ blowdownOrigin) : p = q := by
  apply originalBlowup_pair_injective hs hπ
  have hP := originalBlowup_lands_incidence hs p
  have hQ := originalBlowup_lands_incidence hs q
  change (originalBlowdown hs p).rep 1 * (originalBlowupDirection hs p).rep 1 =
    (originalBlowdown hs p).rep 2 * (originalBlowupDirection hs p).rep 0 at hP
  change (originalBlowdown hs q).rep 1 * (originalBlowupDirection hs q).rep 1 =
    (originalBlowdown hs q).rep 2 * (originalBlowupDirection hs q).rep 0 at hQ
  rw [← hπ] at hQ
  exact (projectiveDirection_eq_of_incidence (originalBlowdown hs p) hp _ hP).trans
    (projectiveDirection_eq_of_incidence (originalBlowdown hs p) hp _ hQ).symm

/-- Actual original off-centre embedding into the EXISTING intrinsic UP
object. Its range is dense by that object's independently proved pulled
point-ideal invertibility, including every exceptional direction. -/
def nativePointOffCentreEmbedding
    (x : {x : SGPT.Projective.ComplexProjectiveSpace 2 //
      x ∉ ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))}) :
    NativeProjectivePointBlowup := BlowupConstruction.offPoint x.val x.property

theorem denseRange_nativePointOffCentreEmbedding : DenseRange nativePointOffCentreEmbedding := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨p, hp, hnot⟩ := BlowupConstruction.exists_not_mem_of_isOpen
    nativeProjectivePointBlowup_isBlowupAlong.2.2.1
    nativeProjectivePointBlowup_isBlowupAlong.2.2.2.1 hU hne
  refine ⟨p, hp, ⟨⟨nativeProjectivePointBlowupProjection p, hnot⟩, ?_⟩⟩
  exact (BlowupConstruction.eq_offPoint hnot).symm

/-- The actual native off-centre density controls maps on EVERY actual
open subset of the existing intrinsic blowup, without incoming density or
geometric compatibility certificates. -/
theorem nativePoint_eqOn_of_denseOffCentre {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (U : Set NativeProjectivePointBlowup) (hU : IsOpen U)
    (f g : NativeProjectivePointBlowup → Y) (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hOff : ∀ x, nativePointOffCentreEmbedding x ∈ U →
      f (nativePointOffCentreEmbedding x) = g (nativePointOffCentreEmbedding x)) : EqOn f g U := by
  have heq : EqOn f g (nativePointOffCentreEmbedding ''
      (nativePointOffCentreEmbedding ⁻¹' U)) := by
    rintro q ⟨x, hx, rfl⟩
    exact hOff x hx
  exact heq.of_subset_closure hf hg (image_preimage_subset _ _)
    (denseRange_nativePointOffCentreEmbedding.subset_closure_image_preimage_of_isOpen hU)

end SGPT.Toric.BlowdownDraft

end
/- END NativeBlowupDenseOffCentreDraft -/
end PointBlowupCanonicalFragment006

section PointBlowupCanonicalFragment007
/- BEGIN OriginalNativeBlowupEquivDraft; original source SHA256 4d6ae94769e8f37746b4dde21e4fdaac1e11d64188acaa5fa99e4004465e163a -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Manifold ContDiff

/-- Internal finite chart-cover choice on the ACTUAL intrinsic UP object. -/
def nativeBlowupChartSourceIndex (q : NativeProjectivePointBlowup) : Fin 4 :=
  (nativeProjectivePointChart_cover q).choose

theorem nativeBlowupChartSourceIndex_mem (q : NativeProjectivePointBlowup) :
    q ∈ (nativeProjectivePointChart (nativeBlowupChartSourceIndex q)).source :=
  (nativeProjectivePointChart_cover q).choose_spec

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual inverse comparison, manufactured on the SAME native intrinsic
UP object using its genuine four-chart cover. -/
def nativePointBlowupToOriginal (q : NativeProjectivePointBlowup) :
    PolytopeToricVariety blowupGenerator hs :=
  nativeToOriginalBlowupLocal hs (nativeBlowupChartSourceIndex q) q

/-- Native point-ideal invertibility gives genuine off-centre density;
together with actual original off-centre injectivity it proves ALL local
inverse overlaps, including the entire native exceptional fibre. -/
theorem nativePointBlowupToOriginal_eq_local (k : Fin 4)
    {q : NativeProjectivePointBlowup} (hq : q ∈ (nativeProjectivePointChart k).source) :
    nativePointBlowupToOriginal hs q = nativeToOriginalBlowupLocal hs k q := by
  let w := nativeBlowupChartSourceIndex q
  have hw : q ∈ (nativeProjectivePointChart w).source := nativeBlowupChartSourceIndex_mem q
  let U := (nativeProjectivePointChart w).source ∩ (nativeProjectivePointChart k).source
  have hU : IsOpen U := (nativeProjectivePointChart w).open_source.inter
    (nativeProjectivePointChart k).open_source
  have hf : ContinuousOn (nativeToOriginalBlowupLocal hs w) U :=
    (contMDiffOn_nativeToOriginalBlowupLocal hs w).continuousOn.mono inter_subset_left
  have hg : ContinuousOn (nativeToOriginalBlowupLocal hs k) U :=
    (contMDiffOn_nativeToOriginalBlowupLocal hs k).continuousOn.mono inter_subset_right
  have heq := nativePoint_eqOn_of_denseOffCentre U hU _ _ hf hg (by
    intro x hx
    apply originalBlowdown_injective_off_origin hs
    · rw [nativeToOriginalBlowupLocal_projection hs w hx.1,
        nativeToOriginalBlowupLocal_projection hs k hx.2]
    · rw [nativeToOriginalBlowupLocal_projection hs w hx.1]
      intro hbad
      exact x.property (Set.mem_singleton_iff.mpr hbad))
  exact heq ⟨hw, hq⟩

/-- The ACTUAL intrinsic-to-original inverse comparison is holomorphic on
the ENTIRE native UP object, retaining all native chart/boundary points. -/
theorem contMDiff_nativePointBlowupToOriginal :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (nativePointBlowupToOriginal hs) := by
  intro q
  let k := nativeBlowupChartSourceIndex q
  have hq : q ∈ (nativeProjectivePointChart k).source := nativeBlowupChartSourceIndex_mem q
  apply ((contMDiffOn_nativeToOriginalBlowupLocal hs k).contMDiffAt
    ((nativeProjectivePointChart k).open_source.mem_nhds hq)).congr_of_eventuallyEq
  filter_upwards [(nativeProjectivePointChart k).open_source.mem_nhds hq] with u hu
  exact nativePointBlowupToOriginal_eq_local hs k hu

theorem nativePointBlowupToOriginal_projection (q : NativeProjectivePointBlowup) :
    originalBlowdown hs (nativePointBlowupToOriginal hs q) = nativeProjectivePointBlowupProjection q :=
  nativeToOriginalBlowupLocal_projection hs (nativeBlowupChartSourceIndex q)
    (nativeBlowupChartSourceIndex_mem q)

/-- The actual original-to-native and native-to-original maps are inverse
on ALL original points; every full original affine chart is retained. -/
theorem nativePointBlowupToOriginal_originalToNative (p : PolytopeToricVariety blowupGenerator hs) :
    nativePointBlowupToOriginal hs (originalToNativePointBlowup hs p) = p := by
  obtain ⟨k, z, rfl⟩ := blowupOriginalChartPoint_cover hs p
  rw [originalToNativePointBlowup_chart,
    nativePointBlowupToOriginal_eq_local hs k (nativeProjectivePointChartPoint_mem k z),
    nativeToOriginalBlowupLocal_chart]

/-- The other composite is the identity on the ENTIRE actual native
intrinsic point blowup, including every native exceptional direction. -/
theorem originalToNative_nativePointBlowupToOriginal (q : NativeProjectivePointBlowup) :
    originalToNativePointBlowup hs (nativePointBlowupToOriginal hs q) = q := by
  obtain ⟨k, hq⟩ := nativeProjectivePointChart_cover q
  obtain ⟨z, rfl⟩ := exists_nativeProjectivePointChartPoint_of_mem k q hq
  rw [nativePointBlowupToOriginal_eq_local hs k (nativeProjectivePointChartPoint_mem k z),
    nativeToOriginalBlowupLocal_chart, originalToNativePointBlowup_chart]

/-- Genuine source-produced equivalence with the EXISTING intrinsic native
UP object, rather than an assumed model identification. -/
def originalNativePointBlowupEquiv : PolytopeToricVariety blowupGenerator hs ≃ NativeProjectivePointBlowup where
  toFun := originalToNativePointBlowup hs
  invFun := nativePointBlowupToOriginal hs
  left_inv := nativePointBlowupToOriginal_originalToNative hs
  right_inv := originalToNative_nativePointBlowupToOriginal hs

/-- ACTUAL biholomorphic identification over P² with the EXISTING intrinsic
point-ideal universal-property blowup. Both topologies and both complex
atlases are independently constructed native geometries. -/
def originalNativePointBlowupHomeomorph : PolytopeToricVariety blowupGenerator hs ≃ₜ NativeProjectivePointBlowup where
  toEquiv := originalNativePointBlowupEquiv hs
  continuous_toFun := (contMDiff_originalToNativePointBlowup hs).continuous
  continuous_invFun := (contMDiff_nativePointBlowupToOriginal hs).continuous

/-- Literal projection identity for the actual intrinsic blowup comparison. -/
theorem originalNativePointBlowupHomeomorph_over (p : PolytopeToricVariety blowupGenerator hs) :
    nativeProjectivePointBlowupProjection (originalNativePointBlowupHomeomorph hs p) = originalBlowdown hs p :=
  originalToNativePointBlowup_projection hs p

theorem contMDiff_originalNativePointBlowupHomeomorph :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalNativePointBlowupHomeomorph hs) :=
  contMDiff_originalToNativePointBlowup hs

theorem contMDiff_originalNativePointBlowupHomeomorph_symm :
    ContMDiff 𝓘(ℂ, ComplexModel 2) 𝓘(ℂ, ComplexModel 2) ∞ (originalNativePointBlowupHomeomorph hs).symm :=
  contMDiff_nativePointBlowupToOriginal hs

end SGPT.Toric.BlowdownDraft

end
/- END OriginalNativeBlowupEquivDraft -/
end PointBlowupCanonicalFragment007

section PointBlowupCanonicalFragment008
/- BEGIN OriginalNativePointBlowupUniversalDraft; original source SHA256 19a4a17d6769adc5eb343b41217bfc3698b96afce12e4f369ac7bbb37a0ab4ac -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric.BlowdownDraft
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

/-- The actual independently constructed native geometries give a genuine
complex diffeomorphism, rather than any supplied model-identification field. -/
def originalNativePointBlowupDiffeomorph :
    PolytopeToricVariety blowupGenerator hs ≃ₘ⟮𝓘(ℂ, ComplexModel 2), 𝓘(ℂ, ComplexModel 2)⟯
      NativeProjectivePointBlowup where
  toEquiv := originalNativePointBlowupEquiv hs
  contMDiff_toFun := contMDiff_originalToNativePointBlowup hs
  contMDiff_invFun := contMDiff_nativePointBlowupToOriginal hs

/-- The full INTRINSIC native point-ideal universal property now holds for
THE SAME ACTUAL original global blowdown itself. Existing source-biholomorphism
transport is instantiated only after both genuine inverse comparisons were
proved. No blowup or comparison certificate is incoming. -/
theorem originalBlowdown_isBlowupAlong :
    IsBlowupAlong 2 ({blowdownOrigin} : Set (SGPT.Projective.ComplexProjectiveSpace 2))
      (originalBlowdown hs) := by
  let X := BlowupTowers.CMfd.of (n := 2) (SGPT.Projective.ComplexProjectiveSpace 2)
  let Y := BlowupTowers.CMfd.of (n := 2) NativeProjectivePointBlowup
  let Y' := BlowupTowers.CMfd.of (n := 2) (PolytopeToricVariety blowupGenerator hs)
  have h := HironakaSharpActualCurveSuccessorLocalBlowup.isBlowupAlong_comp_diffeomorph
    (X := X) (Y := Y) (Y' := Y') (originalNativePointBlowupDiffeomorph hs)
      nativeProjectivePointBlowup_isBlowupAlong
  have hmap : nativeProjectivePointBlowupProjection ∘ originalNativePointBlowupDiffeomorph hs =
      originalBlowdown hs := by
    funext p
    exact originalToNativePointBlowup_projection hs p
  rwa [hmap] at h

end SGPT.Toric.BlowdownDraft

end
/- END OriginalNativePointBlowupUniversalDraft -/
end PointBlowupCanonicalFragment008


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden : Array Name := #[`OriginalMonomialProjectiveMapDraft, `OriginalBlowdownMapDraft, `OriginalBlowupDirectionDraft, `OriginalBlowdownDivisorsDraft, `OriginalBlowupIncidenceDraft, `OriginalBlowupReconstructionDraft, `OriginalIncidenceHomeomorphDraft, `OriginalIncidenceNaturalOpensDraft, `OriginalIncidenceAnalyticManifoldDraft, `OriginalIncidenceRatioChartsDraft, `NativeProjectivePointBlowupDraft, `NativeProjectivePointFourChartsDraft, `OriginalBlowdownCartierTransitionDraft, `OriginalNativeBlowupLocalMapsDraft, `OriginalNativeBlowupGlobalMapDraft, `NativeOriginalBlowupInverseLocalDraft, `NativeBlowupDenseOffCentreDraft, `OriginalNativeBlowupEquivDraft, `OriginalNativePointBlowupUniversalDraft, `OriginalHyperplanePhysicalMapDraft, `OriginalHyperplaneHolomorphicEquivDraft, `SourceOriginalBlowupOkounkovDraft, `PhysicalPowerFlagValuationDraft, `PhysicalPowerOkounkovBodyDraft]
  for m in env.header.moduleNames do
    if forbidden.contains m || m.toString.startsWith "wip." then
      throwError "Forbidden flat/private provider in proper toric point-blowup module: {m}"
