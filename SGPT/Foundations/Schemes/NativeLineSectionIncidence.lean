import SGPT.Foundations.Schemes.NativePowerSectionIntegrality
import SGPT.Foundations.Schemes.NativeLineTotalSpaceZeroDivisor
/-!
# NativeLineSectionIncidence

Genuine global degree-one sections define the actual relative incidence map. A unit coefficient gives a true closed line immersion. Literal cartesian restrictions and genuine unit-generating covers prove global closed immersion.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The actual linear fiber evaluation defined by a family of regular coefficients. -/
def nativeAffineLineVector (U : Scheme.{u}) {I : Type u} (r : I → Γ(U, ⊤)) :
    nativeAffineLine U ⟶ AffineSpace I U :=
  AffineSpace.homOfVector (nativeAffineLineProjection U)
    (fun i ↦ (nativeAffineLineProjection U).appTop (r i) * nativeAffineLineCoordinate U)

@[reassoc (attr := simp)]
theorem nativeAffineLineVector_projection (U : Scheme.{u}) {I : Type u}
    (r : I → Γ(U, ⊤)) :
    nativeAffineLineVector U r ≫ AffineSpace I U ↘ U = nativeAffineLineProjection U :=
  AffineSpace.homOfVector_over _ _

@[simp]
theorem nativeAffineLineVector_coordinate (U : Scheme.{u}) {I : Type u}
    (r : I → Γ(U, ⊤)) (i : I) :
    (nativeAffineLineVector U r).appTop (AffineSpace.coord U i) =
      (nativeAffineLineProjection U).appTop (r i) * nativeAffineLineCoordinate U :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- A unit among the genuine coefficients gives an actual closed line incidence immersion. -/
theorem nativeAffineLineVector_isClosedImmersion (U : Scheme.{u}) {I : Type u}
    (r : I → Γ(U, ⊤)) (i : I) (hi : IsUnit (r i)) :
    IsClosedImmersion (nativeAffineLineVector U r) := by
  obtain ⟨v, hv⟩ := hi
  let g : AffineSpace I U ⟶ nativeAffineLine U :=
    AffineSpace.homOfVector (AffineSpace I U ↘ U)
      (fun _ ↦ (AffineSpace I U ↘ U).appTop (↑v⁻¹ : Γ(U, ⊤)) * AffineSpace.coord U i)
  have hgp : g ≫ nativeAffineLineProjection U = AffineSpace I U ↘ U :=
    AffineSpace.homOfVector_over _ _
  have : IsSeparated g := by
    have : IsSeparated (g ≫ nativeAffineLineProjection U) := by
      rw [hgp]
      infer_instance
    exact IsSeparated.of_comp g (nativeAffineLineProjection U)
  have hfg : nativeAffineLineVector U r ≫ g = 𝟙 (nativeAffineLine U) := by
    apply nativeAffineLine_hom_ext
    · simp [Category.assoc, hgp]
    · change (nativeAffineLineVector U r).appTop
        (g.appTop (nativeAffineLineCoordinate U)) = nativeAffineLineCoordinate U
      rw [show g.appTop (nativeAffineLineCoordinate U) =
        (AffineSpace I U ↘ U).appTop (↑v⁻¹ : Γ(U, ⊤)) * AffineSpace.coord U i from
          AffineSpace.homOfVector_appTop_coord _ _ _]
      rw [map_mul, nativeAffineLineVector_coordinate]
      have hp (z : Γ(U, ⊤)) : (nativeAffineLineVector U r).appTop
          ((AffineSpace I U ↘ U).appTop z) = (nativeAffineLineProjection U).appTop z :=
        congrArg (fun f ↦ f.appTop z) (nativeAffineLineVector_projection U r)
      rw [hp, ← mul_assoc, ← map_mul, ← hv]
      simp
  have : IsClosedImmersion (nativeAffineLineVector U r ≫ g) := by
    rw [hfg]
    infer_instance
  exact IsClosedImmersion.of_comp _ g

variable {X : Scheme.{u}}

/-- Degree-one genuine sections give their actual evaluation into relative affine space. -/
def IntrinsicLineBundle.nativeSectionIncidence (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) :
    nativeDualLineTotalSpace L.atlas ⟶ AffineSpace I X :=
  AffineSpace.homOfVector (nativeDualLineProjection L.atlas)
    (fun i ↦ L.nativeTotalEvaluation (L.ofSection 1 (s i)))

@[reassoc (attr := simp)]
theorem IntrinsicLineBundle.nativeSectionIncidence_projection (L : IntrinsicLineBundle X)
    {I : Type u} (s : I → bundlePowerGlobalSections L.sheaf 1) :
    L.nativeSectionIncidence s ≫ AffineSpace I X ↘ X = nativeDualLineProjection L.atlas :=
  AffineSpace.homOfVector_over _ _

/-- Its actual local coordinate vector is the true section coefficient times the fiber coordinate. -/
theorem IntrinsicLineBundle.nativeSectionIncidence_on_open (L : IntrinsicLineBundle X)
    {I : Type u} (s : I → bundlePowerGlobalSections L.sheaf 1)
    (c : NativeFramedOpen L.atlas) :
    nativeFramedChart L.atlas c ≫ L.nativeSectionIncidence s =
      nativeAffineLineVector c.2.1.toScheme (fun i ↦ nativeFramedSectionCoefficient L.atlas 1 (s i) c) ≫
        AffineSpace.map I c.2.1.ι := by
  apply AffineSpace.hom_ext
  · simp [Category.assoc, nativeFramedChart_projection]
  · intro i
    change (nativeFramedChart L.atlas c).appTop
      ((L.nativeSectionIncidence s).appTop (AffineSpace.coord X i)) =
      (nativeAffineLineVector c.2.1.toScheme _).appTop
        ((AffineSpace.map I c.2.1.ι).appTop (AffineSpace.coord X i))
    have he := L.nativeTotalEvaluation_ofSection_on_open c 1 (s i)
    change (nativeFramedChart L.atlas c).appTop
      (L.nativeTotalEvaluation (L.ofSection 1 (s i))) = _ at he
    rw [show (L.nativeSectionIncidence s).appTop (AffineSpace.coord X i) =
      L.nativeTotalEvaluation (L.ofSection 1 (s i)) from AffineSpace.homOfVector_appTop_coord _ _ _,
      he, AffineSpace.map_appTop_coord,
      nativeAffineLineVector_coordinate]
    simp [nativeFramedHomogeneousFunction]

/-- Every actual smaller framed chart has exactly the expected inverse-image range. -/
theorem nativeFramedChart_opensRange {M : X.Modules} (a : LineBundleAtlas M)
    (c : NativeFramedOpen a) :
    (nativeFramedChart a c).opensRange = nativeDualLineProjection a ⁻¹ᵁ c.2.1 := by
  ext x
  change (∃ y, nativeFramedChart a c y = x) ↔ nativeDualLineProjection a x ∈ c.2.1
  constructor
  · rintro ⟨y, rfl⟩
    have he := congrArg (fun f ↦ f y) (nativeFramedChart_projection a c)
    change nativeDualLineProjection a (nativeFramedChart a c y) =
      (nativeAffineLineProjection c.2.1.toScheme y).1 at he
    rw [he]
    exact (nativeAffineLineProjection c.2.1.toScheme y).2
  · intro hx
    obtain ⟨i, y, hy⟩ := (nativeDualLineAtlasChartCover a).exists_eq x
    let d : NativeFramedOpen a := ⟨i, ⟨a.opens i, le_rfl⟩⟩
    let l : NativeFramedOpen a := ⟨i, ⟨a.opens i ⊓ c.2.1, inf_le_left⟩⟩
    let hd : l ⟶ d := InducedCategory.homMk (homOfLE inf_le_left)
    let hc : l ⟶ c := InducedCategory.homMk (homOfLE inf_le_right)
    have hb := congrArg (fun f ↦ f y) (nativeDualLineChart_projection a i)
    have hyc : (nativeAffineLineProjection (a.opens i).toScheme y).1 ∈ c.2.1 := by
      change nativeDualLineProjection a (nativeDualLineChart a i y) =
        (nativeAffineLineProjection (a.opens i).toScheme y).1 at hb
      rw [← hb]
      change nativeDualLineProjection a ((nativeDualLineAtlasChartCover a).f i y) ∈ c.2.1
      rwa [hy]
    obtain ⟨z, hz⟩ := (nativeFramedMap_mem_range a hd y).mpr
      ⟨(nativeAffineLineProjection (a.opens i).toScheme y).2, hyc⟩
    refine ⟨nativeFramedMap a hc z, ?_⟩
    have hec := congrArg (fun f ↦ f z) (colimit.w (nativeDualLineDiagram a) hc)
    have hed := congrArg (fun f ↦ f z) (colimit.w (nativeDualLineDiagram a) hd)
    change nativeFramedChart a c (nativeFramedMap a hc z) = nativeFramedChart a l z at hec
    change nativeFramedChart a d (nativeFramedMap a hd z) = nativeFramedChart a l z at hed
    rw [hz] at hed
    exact hec.trans (hed.symm.trans hy)

/-- Smaller actual framed charts are genuine cartesian restrictions of the line projection. -/
theorem nativeFramedChart_isPullback {M : X.Modules} (a : LineBundleAtlas M)
    (c : NativeFramedOpen a) :
    IsPullback (nativeFramedChart a c) (nativeAffineLineProjection c.2.1.toScheme)
      (nativeDualLineProjection a) c.2.1.ι := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact nativeFramedChart_projection a c
  · rw [Scheme.Opens.opensRange_ι, nativeFramedChart_opensRange]

/-- The incidence map restricted to an actual base open is its true coefficient vector map. -/
theorem IntrinsicLineBundle.nativeSectionIncidence_isPullback (L : IntrinsicLineBundle X)
    {I : Type u} (s : I → bundlePowerGlobalSections L.sheaf 1)
    (c : NativeFramedOpen L.atlas) :
    IsPullback (nativeFramedChart L.atlas c)
      (nativeAffineLineVector c.2.1.toScheme
        (fun i ↦ nativeFramedSectionCoefficient L.atlas 1 (s i) c))
      (L.nativeSectionIncidence s) (AffineSpace.map I c.2.1.ι) := by
  apply IsPullback.flip
  apply IsPullback.of_right ?_ (L.nativeSectionIncidence_on_open s c).symm
    (AffineSpace.isPullback_map (n := I) c.2.1.ι).flip
  simpa only [nativeAffineLineVector_projection, L.nativeSectionIncidence_projection] using
    (nativeFramedChart_isPullback L.atlas c).flip

/-- The actual affine-space base change of an open immersion is an open immersion. -/
instance nativeAffineSpaceMap_isOpenImmersion {U V : Scheme.{u}} {I : Type u}
    (f : U ⟶ V) [IsOpenImmersion f] : IsOpenImmersion (AffineSpace.map I f) :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map f).flip inferInstance

/-- Its range is the literal inverse image of the genuine base range. -/
theorem nativeAffineSpaceMap_opensRange {U V : Scheme.{u}} {I : Type u}
    (f : U ⟶ V) [IsOpenImmersion f] :
    (AffineSpace.map I f).opensRange = (AffineSpace I V ↘ V) ⁻¹ᵁ f.opensRange := by
  let h := AffineSpace.isPullback_map (n := I) f
  calc
    (AffineSpace.map I f).opensRange =
        (h.isoPullback.hom ≫ pullback.fst (AffineSpace I V ↘ V) f).opensRange := by
      simp only [h.isoPullback_hom_fst]
    _ = (pullback.fst (AffineSpace I V ↘ V) f).opensRange :=
      Scheme.Hom.opensRange_comp_of_isIso _ _
    _ = _ := Scheme.Hom.opensRange_pullbackFst _ _

/-- The actual generating condition: local unit coefficients of genuine global sections cover the base. -/
def IntrinsicLineBundle.NativeSectionsGenerate (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) : Prop :=
  ∀ x : X, ∃ c : NativeFramedOpen L.atlas, x ∈ c.2.1 ∧
    ∃ i, IsUnit (nativeFramedSectionCoefficient L.atlas 1 (s i) c)

/-- Genuine generating sections give a true open cover of the relative affine target. -/
def IntrinsicLineBundle.nativeGeneratingTargetCover (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) (hs : L.NativeSectionsGenerate s) :
    (AffineSpace I X).OpenCover where
  I₀ := {c : NativeFramedOpen L.atlas // ∃ i,
    IsUnit (nativeFramedSectionCoefficient L.atlas 1 (s i) c)}
  X c := AffineSpace I c.1.2.1.toScheme
  f c := AffineSpace.map I c.1.2.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, inferInstance⟩
    obtain ⟨c, hc, i, hi⟩ := hs ((AffineSpace I X ↘ X) y)
    refine ⟨⟨c, i, hi⟩, ?_⟩
    change y ∈ (AffineSpace.map I c.2.1.ι).opensRange
    rw [nativeAffineSpaceMap_opensRange, Scheme.Opens.opensRange_ι]
    exact hc

/-- Actual local generation proves that the genuine relative incidence map is a closed immersion. -/
theorem IntrinsicLineBundle.nativeSectionIncidence_isClosedImmersion
    (L : IntrinsicLineBundle X) {I : Type u}
    (s : I → bundlePowerGlobalSections L.sheaf 1) (hs : L.NativeSectionsGenerate s) :
    IsClosedImmersion (L.nativeSectionIncidence s) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (L.nativeGeneratingTargetCover s hs)]
  intro c
  change IsClosedImmersion (pullback.snd (L.nativeSectionIncidence s)
    (AffineSpace.map I c.1.2.1.ι))
  let h := L.nativeSectionIncidence_isPullback s c.1
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion h.isoPullback.hom,
    h.isoPullback_hom_snd]
  obtain ⟨i, hi⟩ := c.2
  exact nativeAffineLineVector_isClosedImmersion _ _ i hi

end
end SGPT.Foundations.Schemes
