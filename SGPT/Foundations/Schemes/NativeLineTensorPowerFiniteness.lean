import SGPT.Foundations.Schemes.NativeAffineLinePowerFiniteness
import SGPT.Foundations.Schemes.NativeLineTensorPowerMap
import SGPT.Foundations.Schemes.NativeLineTotalSpaceGeometry
/-!
# NativeLineTensorPowerFiniteness

Genuine cartesian base changes and actual open covers extend native power finiteness to arbitrary bases and the literal dual-line tensor-power total-space map. Positive powers are proper, preserve the actual zero sections and retain the nonzero-coordinate basic open. Full cone contraction and crepancy remain separate source obligations.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite Module
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- The actual fiber power square is cartesian under every genuine base change. -/
theorem nativeAffineLinePower_isPullback {U V : Scheme.{u}} (f : U ⟶ V) (q : ℕ) :
    IsPullback (nativeAffineLinePower U q) (nativeAffineLineMap f)
      (nativeAffineLineMap f) (nativeAffineLinePower V q) := by
  apply IsPullback.of_right ?_ (nativeAffineLinePower_naturality f q)
    (nativeAffineLineMap_isPullback f).flip
  simpa only [nativeAffineLinePower_projection] using (nativeAffineLineMap_isPullback f).flip

/-- Actual affine base charts induce a genuine open cover of the native affine line. -/
def nativeAffineLineBaseCover (U : Scheme.{u}) : (nativeAffineLine U).OpenCover where
  I₀ := U.affineCover.I₀
  X i := nativeAffineLine (U.affineCover.X i)
  f i := nativeAffineLineMap (U.affineCover.f i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun y ↦ ?_, inferInstance⟩
    obtain ⟨i, z, hz⟩ := U.affineCover.exists_eq (nativeAffineLineProjection U y)
    have hy : y ∈ Set.range (nativeAffineLineMap (U.affineCover.f i)) := by
      change y ∈ (nativeAffineLineMap (U.affineCover.f i)).opensRange
      rw [nativeAffineLineMap_opensRange]
      exact ⟨z, hz⟩
    exact ⟨i, hy⟩

/-- Positive fiber powers on the actual native affine line are finite over any base scheme. -/
theorem nativeAffineLinePower_isFinite (U : Scheme.{u}) (q : ℕ) (hq : 0 < q) :
    IsFinite (nativeAffineLinePower U q) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) (nativeAffineLineBaseCover U)]
  intro i
  change IsFinite (pullback.snd (nativeAffineLinePower U q)
    (nativeAffineLineMap (U.affineCover.f i)))
  let h := (nativeAffineLinePower_isPullback (U.affineCover.f i) q).flip
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite h.isoPullback.hom]
  rw [h.isoPullback_hom_snd]
  exact nativeAffineLinePower_isFinite_affine (U.affineCover.X i) q hq

variable {X : Scheme.{u}} {L : X.Modules}

/-- The genuine total-space tensor-power map is over the original base scheme. -/
theorem nativeDualLineTensorPowerMap_projection (a : LineBundleAtlas L) (q : ℕ) :
    nativeDualLineTensorPowerMap a q ≫ nativeDualLineProjection (a.tensorPower q) =
      nativeDualLineProjection a := by
  apply colimit.hom_ext
  intro c
  change nativeFramedChart a c ≫ nativeDualLineTensorPowerMap a q ≫
    nativeDualLineProjection (a.tensorPower q) = nativeFramedChart a c ≫ nativeDualLineProjection a
  rw [← Category.assoc, nativeDualLineTensorPowerMap_on_chart, Category.assoc,
    nativeFramedChart_projection, ← Category.assoc, nativeAffineLinePower_projection,
    nativeFramedChart_projection]

/-- Original actual atlas charts form a genuine open cover of the glued total space. -/
def nativeDualLineAtlasChartCover (a : LineBundleAtlas L) : (nativeDualLineTotalSpace a).OpenCover where
  I₀ := a.I
  X i := nativeAffineLine (a.opens i).toScheme
  f i := nativeDualLineChart a i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨nativeDualLineChart_jointly_surjective a, inferInstance⟩

/-- The actual total-space power map has the literal local fiber power as its base change to each target chart. -/
theorem nativeDualLineTensorPowerMap_chart_isPullback (a : LineBundleAtlas L) (q : ℕ)
    (i : a.I) :
    IsPullback (nativeDualLineChart a i) (nativeAffineLinePower (a.opens i).toScheme q)
      (nativeDualLineTensorPowerMap a q) (nativeDualLineChart (a.tensorPower q) i) := by
  apply IsPullback.flip
  apply IsPullback.of_right ?_ (nativeDualLineTensorPowerMap_on_chart a q
    ⟨i, ⟨a.opens i, le_rfl⟩⟩).symm (nativeDualLineChart_isPullback (a.tensorPower q) i).flip
  change IsPullback (nativeAffineLinePower (a.opens i).toScheme q ≫
    nativeAffineLineProjection (a.opens i).toScheme) (nativeDualLineChart a i)
    (a.opens i).ι (nativeDualLineTensorPowerMap a q ≫ nativeDualLineProjection (a.tensorPower q))
  rw [nativeAffineLinePower_projection, nativeDualLineTensorPowerMap_projection]
  exact (nativeDualLineChart_isPullback a i).flip

/-- The real positive fiber power between the actual dual line total spaces is finite. -/
theorem nativeDualLineTensorPowerMap_isFinite (a : LineBundleAtlas L) (q : ℕ) (hq : 0 < q) :
    IsFinite (nativeDualLineTensorPowerMap a q) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite)
    (nativeDualLineAtlasChartCover (a.tensorPower q))]
  intro i
  change IsFinite (pullback.snd (nativeDualLineTensorPowerMap a q)
    (nativeDualLineChart (a.tensorPower q) i))
  let h := nativeDualLineTensorPowerMap_chart_isPullback a q i
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite h.isoPullback.hom]
  rw [h.isoPullback_hom_snd]
  exact nativeAffineLinePower_isFinite (a.opens i).toScheme q hq

/-- The actual finite tensor-power total-space morphism is proper for every positive power. -/
theorem nativeDualLineTensorPowerMap_isProper (a : LineBundleAtlas L) (q : ℕ) (hq : 0 < q) :
    IsProper (nativeDualLineTensorPowerMap a q) := by
  have := nativeDualLineTensorPowerMap_isFinite a q hq
  infer_instance

/-- A positive actual fiber power preserves the true zero section. -/
theorem nativeAffineLineZero_power (U : Scheme.{u}) (q : ℕ) (hq : 0 < q) :
    nativeAffineLineZero U ≫ nativeAffineLinePower U q = nativeAffineLineZero U := by
  apply nativeAffineLine_hom_ext
  · simp
  · simp [hq.ne']

/-- Positive actual fiber powers preserve the literal nonzero-coordinate open. -/
theorem nativeAffineLinePower_preimage_coordinateOpen (U : Scheme.{u}) (q : ℕ) (hq : 0 < q) :
    nativeAffineLinePower U q ⁻¹ᵁ (nativeAffineLine U).basicOpen (nativeAffineLineCoordinate U) =
      (nativeAffineLine U).basicOpen (nativeAffineLineCoordinate U) := by
  rw [Scheme.Hom.preimage_basicOpen_top, nativeAffineLinePower_coordinate, Scheme.basicOpen_pow _ _ hq]

/-- The genuine descended positive power sends the actual zero section to the actual tensor-power zero section. -/
theorem nativeDualLineZero_tensorPowerMap (a : LineBundleAtlas L) (q : ℕ) (hq : 0 < q) :
    nativeDualLineZero a ≫ nativeDualLineTensorPowerMap a q = nativeDualLineZero (a.tensorPower q) := by
  apply (nativeLineAtlasBaseCover a).hom_ext
  intro i
  change a.I at i
  have hi := nativeDualLineTensorPowerMap_on_chart a q ⟨i, ⟨a.opens i, le_rfl⟩⟩
  change nativeDualLineChart a i ≫ nativeDualLineTensorPowerMap a q =
    nativeAffineLinePower (a.opens i).toScheme q ≫ nativeDualLineChart (a.tensorPower q) i at hi
  change (a.opens i).ι ≫ (nativeDualLineZero a ≫ nativeDualLineTensorPowerMap a q) =
    (a.opens i).ι ≫ nativeDualLineZero (a.tensorPower q)
  rw [← Category.assoc, nativeDualLineZero_on_chart, Category.assoc,
    hi,
    ← Category.assoc, nativeAffineLineZero_power _ q hq]
  exact (nativeDualLineZero_on_chart (a.tensorPower q) i).symm

end
end SGPT.Foundations.Schemes
