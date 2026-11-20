import SGPT.Foundations.Schemes.NativeLineTotalSpaceEvaluation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Geometry of the native dual-line total space

The genuine glued affine-line charts are precisely the inverse images of their
base opens. Their native cartesian squares establish the affine projection and
the closed zero section without additional geometric certificates.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}}

/-- The literal zero of any native affine line is a closed immersion. -/
instance nativeAffineLineZero_isClosedImmersion (U : Scheme.{u}) :
    IsClosedImmersion (nativeAffineLineZero U) := by
  have : IsClosedImmersion (nativeAffineLineZero U ≫ nativeAffineLineProjection U) := by
    rw [nativeAffineLineZero_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (nativeAffineLineZero U) (nativeAffineLineProjection U)

/-- The actual chart image is exactly the inverse image of its base open. -/
theorem nativeDualLineChart_opensRange {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    (nativeDualLineChart a i).opensRange = nativeDualLineProjection a ⁻¹ᵁ a.opens i := by
  ext x
  change x ∈ Set.range (nativeDualLineChart a i) ↔ nativeDualLineProjection a x ∈ a.opens i
  constructor
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun q ↦ q y) (nativeDualLineChart_projection a i)
    change nativeDualLineProjection a (nativeDualLineChart a i y) =
      (nativeAffineLineProjection (a.opens i).toScheme y).1 at h
    rw [h]
    exact (nativeAffineLineProjection (a.opens i).toScheme y).2
  · intro hx
    obtain ⟨c, y, hy⟩ :=
      Scheme.IsLocallyDirected.ι_jointly_surjective (nativeDualLineDiagram a) x
    change nativeAffineLine c.2.1.toScheme at y
    have hb := congrArg (fun q ↦ q y) (nativeDualLineProjection_on_open a c)
    change nativeDualLineProjection a (colimit.ι (nativeDualLineDiagram a) c y) =
      (nativeAffineLineProjection c.2.1.toScheme y).1 at hb
    have hyi : (nativeAffineLineProjection c.2.1.toScheme y).1 ∈ a.opens i := by
      rw [← hb, hy]
      exact hx
    let d : NativeFramedOpen a := ⟨i, ⟨a.opens i, le_rfl⟩⟩
    let l : NativeFramedOpen a :=
      ⟨c.1, ⟨c.2.1 ⊓ a.opens i, inf_le_left.trans c.2.2⟩⟩
    let hc : l ⟶ c := InducedCategory.homMk (homOfLE inf_le_left)
    let hd : l ⟶ d := InducedCategory.homMk (homOfLE inf_le_right)
    obtain ⟨z, hz⟩ := (nativeFramedMap_mem_range a hc y).mpr
      ⟨(nativeAffineLineProjection c.2.1.toScheme y).2, hyi⟩
    refine ⟨nativeFramedMap a hd z, ?_⟩
    change (nativeFramedMap a hd ≫ colimit.ι (nativeDualLineDiagram a) d) z = x
    have hzd := congrArg (fun q ↦ q z) (colimit.w (nativeDualLineDiagram a) hd)
    have hzc := congrArg (fun q ↦ q z) (colimit.w (nativeDualLineDiagram a) hc)
    change colimit.ι (nativeDualLineDiagram a) c (nativeFramedMap a hc z) =
      colimit.ι (nativeDualLineDiagram a) l z at hzc
    rw [hz, hy] at hzc
    exact hzd.trans hzc.symm

/-- Each actual total-space chart square over its base open is cartesian. -/
theorem nativeDualLineChart_isPullback {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    IsPullback (nativeDualLineChart a i)
      (nativeAffineLineProjection (a.opens i).toScheme)
      (nativeDualLineProjection a) (a.opens i).ι := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact nativeDualLineChart_projection a i
  · rw [Scheme.Opens.opensRange_ι, nativeDualLineChart_opensRange]

/-- The genuine chart identifies the native base change of the projection. -/
def nativeDualLineChartPullbackIso {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    nativeAffineLine (a.opens i).toScheme ≅
      pullback (nativeDualLineProjection a) (a.opens i).ι :=
  (nativeDualLineChart_isPullback a i).isoPullback

@[reassoc (attr := simp)]
theorem nativeDualLineChartPullbackIso_hom_fst {L : X.Modules}
    (a : LineBundleAtlas L) (i : a.I) :
    (nativeDualLineChartPullbackIso a i).hom ≫
      pullback.fst (nativeDualLineProjection a) (a.opens i).ι =
      nativeDualLineChart a i :=
  (nativeDualLineChart_isPullback a i).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem nativeDualLineChartPullbackIso_hom_snd {L : X.Modules}
    (a : LineBundleAtlas L) (i : a.I) :
    (nativeDualLineChartPullbackIso a i).hom ≫
      pullback.snd (nativeDualLineProjection a) (a.opens i).ι =
      nativeAffineLineProjection (a.opens i).toScheme :=
  (nativeDualLineChart_isPullback a i).isoPullback_hom_snd

/-- The actual dual-line projection is affine, locally the native affine line. -/
instance nativeDualLineProjection_isAffineHom {L : X.Modules} (a : LineBundleAtlas L) :
    IsAffineHom (nativeDualLineProjection a) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom)
    (nativeLineAtlasBaseCover a)]
  intro i
  change IsAffineHom (pullback.snd (nativeDualLineProjection a) (a.opens i).ι)
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsAffineHom
    (nativeDualLineChartPullbackIso a i).hom]
  rw [nativeDualLineChartPullbackIso_hom_snd]
  infer_instance

/-- The actual dual-line projection is separated because it is affine. -/
instance nativeDualLineProjection_isSeparated {L : X.Modules} (a : LineBundleAtlas L) :
    IsSeparated (nativeDualLineProjection a) :=
  inferInstance

/-- The literal glued zero section is a native closed immersion. -/
instance nativeDualLineZero_isClosedImmersion {L : X.Modules} (a : LineBundleAtlas L) :
    IsClosedImmersion (nativeDualLineZero a) := by
  have : IsClosedImmersion (nativeDualLineZero a ≫ nativeDualLineProjection a) := by
    rw [nativeDualLineZero_projection]
    infer_instance
  exact IsClosedImmersion.of_comp (nativeDualLineZero a) (nativeDualLineProjection a)

/-- Pulling the actual zero section back to a chart gives the literal local zero. -/
theorem nativeDualLineZero_chart_isPullback {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    IsPullback (a.opens i).ι (nativeAffineLineZero (a.opens i).toScheme)
      (nativeDualLineZero a) (nativeDualLineChart a i) := by
  apply IsPullback.mk' (nativeDualLineZero_on_chart a i)
  · intro T φ φ' h _
    exact (cancel_mono (a.opens i).ι).mp h
  · intro T g h w
    refine ⟨h ≫ nativeAffineLineProjection (a.opens i).toScheme, ?_, ?_⟩
    · have hw := congrArg (fun q ↦ q ≫ nativeDualLineProjection a) w
      simpa only [Category.assoc, nativeDualLineZero_projection, Category.comp_id,
        nativeDualLineChart_projection] using hw.symm
    · apply (cancel_mono (nativeDualLineChart a i)).mp
      rw [Category.assoc, ← nativeDualLineZero_on_chart]
      have hw := congrArg (fun q ↦ q ≫ nativeDualLineProjection a) w
      have hb : h ≫ nativeAffineLineProjection (a.opens i).toScheme ≫ (a.opens i).ι = g := by
        simpa only [Category.assoc, nativeDualLineZero_projection, Category.comp_id,
          nativeDualLineChart_projection] using hw.symm
      have hbz : h ≫ nativeAffineLineProjection (a.opens i).toScheme ≫
          (a.opens i).ι ≫ nativeDualLineZero a = g ≫ nativeDualLineZero a := by
        simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ nativeDualLineZero a) hb
      exact hbz.trans w

/-- The actual ideal sheaf of the zero section, as a native morphism kernel. -/
def nativeDualLineZeroIdeal {L : X.Modules} (a : LineBundleAtlas L) :
    (nativeDualLineTotalSpace a).IdealSheafData :=
  (nativeDualLineZero a).ker

/-- Its native closed support is precisely the actual zero-section image. -/
theorem nativeDualLineZeroIdeal_support {L : X.Modules} (a : LineBundleAtlas L) :
    (nativeDualLineZeroIdeal a).support = Set.range (nativeDualLineZero a) := by
  rw [nativeDualLineZeroIdeal, Scheme.Hom.support_ker]
  exact (nativeDualLineZero a).isClosedEmbedding.isClosed_range.closure_eq

/-- The genuine ideal pullback to each chart is the literal affine-line zero ideal. -/
theorem nativeDualLineZeroIdeal_chart {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    (nativeDualLineZeroIdeal a).comap (nativeDualLineChart a i) =
      (nativeAffineLineZero (a.opens i).toScheme).ker := by
  let pb := (nativeDualLineZero_chart_isPullback a i).flip
  let e := pb.isoPullback
  change (nativeDualLineZero a).ker.comap (nativeDualLineChart a i) = _
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso e.hom]
  change (pb.isoPullback.hom ≫
    pullback.fst (nativeDualLineChart a i) (nativeDualLineZero a)).ker = _
  rw [pb.isoPullback_hom_fst]

/-- On a chart, a point lies in the global zero image exactly when it lies in
the literal local zero image. -/
theorem nativeDualLineZero_range_chart {L : X.Modules} (a : LineBundleAtlas L)
    (i : a.I) :
    (nativeDualLineChart a i) ⁻¹' Set.range (nativeDualLineZero a) =
      Set.range (nativeAffineLineZero (a.opens i).toScheme) := by
  have hs := Scheme.IdealSheafData.support_comap (nativeDualLineZeroIdeal a)
    (nativeDualLineChart a i)
  rw [nativeDualLineZeroIdeal_chart] at hs
  have h := congrArg (fun Z : TopologicalSpace.Closeds
    (nativeAffineLine (a.opens i).toScheme) ↦ Z.1) hs
  change ((nativeAffineLineZero (a.opens i).toScheme).ker.support : Set _) =
    (nativeDualLineChart a i) ⁻¹' (nativeDualLineZeroIdeal a).support at h
  rw [nativeDualLineZeroIdeal_support, Scheme.Hom.support_ker,
    (nativeAffineLineZero (a.opens i).toScheme).isClosedEmbedding.isClosed_range.closure_eq] at h
  exact h.symm

end

end SGPT.Foundations.Schemes
