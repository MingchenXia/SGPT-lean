import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalCarrierComparisonCurves
import SGPT.Foundations.Envelope.AlgGeom.SchemeDominantImageFactorization
import SGPT.Foundations.Envelope.AlgGeom.CurveProperDominantFinite
import SGPT.Foundations.Envelope.AlgGeom.FiniteDominantSchemeDimension
import SGPT.Foundations.Envelope.AlgGeom.CurveFiniteDominantLineDegrees
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveGeneratedLineClasses

/-! # Actual projective curve maps compared with their original closed images

This module will establish the integer degree-kernel comparison by a genuine
point-image versus one-dimensional-image argument. No kernel equality, finiteness
of the image map, or class-matching certificate is an incoming premise.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonImage

/-- Cover-local invertibility gives an actual whole-line trivialization on
any nonempty one-point scheme, with no trivialization supplied by the caller. -/
theorem invertible_nonempty_iso_unit_of_subsingleton
    {S : Scheme.{u}} [Nonempty S] [Subsingleton S]
    {M : S.Modules} (hM : IsInvertible M) : Nonempty (M ≅ unitObj S) := by
  classical
  let x : S := Classical.choice inferInstance
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hUi : U i = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = x := Subsingleton.elim _ _
    simpa only [hy] using hi
  obtain ⟨e⟩ : Nonempty ((Scheme.Modules.pullback (⊤ : S.Opens).ι).obj M ≅
      unitObj (⊤ : S.Opens).toScheme) := hUi ▸ htriv i
  let j := S.topIso.inv
  have hj : j ≫ (⊤ : S.Opens).ι = 𝟙 S := S.topIso.inv_hom_id
  exact ⟨(pullbackId S).symm.app M ≪≫ (pullbackCongr hj).symm.app M ≪≫
    (pullbackComp j (⊤ : S.Opens).ι).symm.app M ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫ pullbackUnitIso j⟩

open NativeNumericalCarrierComparisonCurves NativeClosedCurveDegrees
variable {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProjective p] (C : IntegralCurveMap p)

private local instance curve_integral : IsIntegral C.carrier := C.integral

/-- The ORIGINAL curve map is proper by its original structure triangle. -/
theorem morphism_isProper : IsProper C.morphism := by
  let : IsProper p := (ProjectiveFactorizationRingIso.of_isProjective p).isProper
  let : IsProper C.structureMorphism := C.projective.isProper
  let : IsProper (C.morphism ≫ p) := by rw [C.triangle]; infer_instance
  exact IsProper.of_comp C.morphism p

omit [IsProjective p] in
private theorem curve_isNoetherian : AlgebraicGeometry.IsNoetherian C.carrier := by
  let : IsProper C.structureMorphism := C.projective.isProper
  let : IsLocallyNoetherian C.carrier :=
    LocallyOfFiniteType.isLocallyNoetherian C.structureMorphism
  let : CompactSpace C.carrier :=
    QuasiCompact.compactSpace_of_compactSpace C.structureMorphism
  exact { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }

/-- The actual scheme image of the unchanged original curve map is integral. -/
theorem image_isIntegral : IsIntegral C.morphism.image := by
  let : IsProper C.morphism := morphism_isProper p C
  exact SchemeDominantImageFactorization.image_isIntegral C.morphism

/-- The actual original canonical map to its scheme image is proper. -/
theorem toImage_isProper : IsProper C.morphism.toImage := by
  let : IsProper C.morphism := morphism_isProper p C
  let : IsProper (C.morphism.toImage ≫ C.morphism.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  exact IsProper.of_comp C.morphism.toImage C.morphism.imageι

/-- In the nonconstant branch the ORIGINAL canonical image map is finite,
proved from original curve topology, with no incoming finite-map certificate. -/
theorem toImage_isFinite [Nontrivial C.morphism.image] : IsFinite C.morphism.toImage := by
  let : IsProper C.morphism := morphism_isProper p C
  let : IsIntegral C.morphism.image := image_isIntegral p C
  let : AlgebraicGeometry.IsNoetherian C.carrier := curve_isNoetherian p C
  let : IsProper C.morphism.toImage := toImage_isProper p C
  let : IsDominant C.morphism.toImage := inferInstance
  exact CurveProperDominantFinite.isFinite C.morphism.toImage C.dimension.le

/-- The SAME actual image has true dimension one, derived from finiteness
and the genuine specialization chain of its nontrivial integral point space. -/
theorem image_dimension [Nontrivial C.morphism.image] :
    topologicalKrullDim C.morphism.image = 1 := by
  let : IsProper C.morphism := morphism_isProper p C
  let : IsIntegral C.morphism.image := image_isIntegral p C
  let : IsFinite C.morphism.toImage := toImage_isFinite p C
  let : IsDominant C.morphism.toImage := inferInstance
  have hle : topologicalKrullDim C.morphism.image ≤ 1 :=
    FiniteDominantSchemeDimension.target_dimension_le C.morphism.toImage 1 C.dimension.le
  have hge : 1 ≤ topologicalKrullDim C.morphism.image := by
    change 1 ≤ Order.krullDim (IrreducibleCloseds C.morphism.image)
    rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C.morphism.image))]
    obtain ⟨x, hx⟩ := exists_ne (⊤ : C.morphism.image)
    have hlt : x < (⊤ : C.morphism.image) := by
      refine lt_iff_le_not_ge.mpr ⟨le_top, ?_⟩
      intro h
      apply hx
      exact ((show x ⤳ genericPoint C.morphism.image from h).antisymm
        (genericPoint_specializes x)).eq
    exact Order.one_le_krullDim_iff.mpr ⟨x, ⊤, hlt⟩
  exact le_antisymm hle hge

/-- The actual ORIGINAL scheme image is an original closed integral curve. -/
def closedImage [Nontrivial C.morphism.image] : ClosedIntegralCurve X where
  carrier := C.morphism.image
  integral := image_isIntegral p C
  inclusion := C.morphism.imageι
  closed := inferInstance
  dimension := image_dimension p C

/-- The true image factorization retains the unchanged original coefficient triangle. -/
theorem image_structure_triangle [Nontrivial C.morphism.image] :
    C.morphism.toImage ≫ (closedImage p C).structureMorphism p = C.structureMorphism := by
  change C.morphism.toImage ≫ (C.morphism.imageι ≫ p) = C.structureMorphism
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, C.triangle]

end SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonImage
