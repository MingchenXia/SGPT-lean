import SGPT.Checks.Comparison.BJIntersectPositivity
import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalCarrierComparisonNef

/-!
# Pull-backs of relatively nef line bundles (lane BJ-PROJ, step (c) of the general R7)

Let `X` be projective over a field `k`, `f : Y ⟶ X` a morphism from a projective `k`-scheme, `N`
an invertible sheaf on `X` and `W ⊆ X`. If `N` is nef on `W` (nonnegative degree on every closed
integral curve of `X` inside `W`, `IsNefOn`), then `f^*N` is nef on `f⁻¹ W`
(`IsNefOn.pullback_morphism`). For a closed integral curve `C ⊆ Y` over `W`, either `f(C)` is a
point and `deg(f^*N|_C) = 0`, or `C → f(C)` is a finite surjection of integral curves and
`deg(f^*N|_C) = deg(C → f(C)) · deg(N|_{f(C)}) ≥ 0`; both cases are SGPT.Foundations.Envelope's curve-map
degree factorization, and `f(C)` lies in `W` because `C → f(C)` is surjective.

This is step (c) of `claude-bj-intersect:plan-hodge`: pull-backs of relatively nef classes to an
alteration stay relatively nef. Blueprint: `claude-bj-proj.tex` (`claude-bj-proj:nef-pullback`).
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules

universe u

namespace SGPT.NAPotential.BJIntersect

open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonCurves
  SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonImage
  SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonNef

variable {k : Type u} [Field k]

/-- **Pull-backs of nef line bundles are nef.** If `N` is nef on `W ⊆ X`, then `f^*N` is nef on
`f⁻¹ W`, for every morphism `f : Y ⟶ X` of projective `k`-schemes. -/
theorem IsNefOn.pullback_morphism {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    {p : X ⟶ Spec (.of k)} [IsProjective p] (f : Y ⟶ X) [IsProjective (f ≫ p)]
    {N : X.Modules} (hN : IsInvertible N) {W : Set X} (h : IsNefOn p N W) :
    IsNefOn (f ≫ p) ((Scheme.Modules.pullback f).obj N) (f ⁻¹' W) := by
  intro C hC
  let : IsClosedImmersion C.inclusion := C.closed
  let : IsIntegral C.carrier := C.integral
  let D : IntegralCurveMap p :=
    { carrier := C.carrier
      integral := C.integral
      structureMorphism := C.inclusion ≫ f ≫ p
      projective := (ProjectiveFactorizationRingIso.of_isProjective (f ≫ p)).comp_isClosedImmersion
        C.inclusion C.closed
      dimension := C.dimension
      morphism := C.inclusion ≫ f
      triangle := Category.assoc _ _ _ }
  let : IsProper D.structureMorphism := D.projective.isProper
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace D.structureMorphism
  have hdeg : CurveLineDegrees.degree (C.inclusion ≫ f ≫ p)
      ((Scheme.Modules.pullback C.inclusion).obj ((Scheme.Modules.pullback f).obj N)) =
      Multiplicative.toAdd (CurvePicardDegrees.curveDegreeHom D.structureMorphism D.projective
        D.dimension.le D.morphism (CurvePicardDegrees.lineClass N hN)) := by
    rw [CurvePicardDegrees.curveDegreeHom_lineClass]
    exact CurveLineDegrees.degree_eq_of_iso _
      ((Scheme.Modules.pullbackComp C.inclusion f).app N)
  change 0 ≤ CurveLineDegrees.degree (C.inclusion ≫ f ≫ p)
    ((Scheme.Modules.pullback C.inclusion).obj ((Scheme.Modules.pullback f).obj N))
  rw [hdeg]
  by_cases hs : Subsingleton D.morphism.image
  · rw [curveMapIntegerDegree_eq_zero_of_subsingleton_image p D]
  · have : Nontrivial D.morphism.image := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨n, hn⟩ := curveMapIntegerDegree_image_factor p D
    rw [hn]
    let E := closedImage p D
    -- the image curve lies in `W`
    have hsurj : Function.Surjective D.morphism.toImage := by
      let : IsProper D.morphism := morphism_isProper p D
      let : IsProper D.morphism.toImage := toImage_isProper p D
      have hclosed : IsClosed (Set.range D.morphism.toImage) :=
        D.morphism.toImage.isClosedMap.isClosed_range
      have hdense : DenseRange D.morphism.toImage := D.morphism.toImage.denseRange
      rw [← Set.range_eq_univ, ← hclosed.closure_eq, hdense.closure_range]
    have hE : Set.range E.inclusion ⊆ W := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := hsurj z
      change (D.morphism.toImage ≫ D.morphism.imageι) c ∈ W
      rw [Scheme.Hom.toImage_imageι]
      exact hC ⟨c, rfl⟩
    have hEdeg := h E hE
    let : IsProper (E.structureMorphism p) := (E.projectiveFactorization p).isProper
    let : CompactSpace E.carrier :=
      QuasiCompact.compactSpace_of_compactSpace (E.structureMorphism p)
    have hpd := E.picardDegree_lineClass p N hN
    have h0 : 0 ≤ Multiplicative.toAdd (E.picardDegree p (CurvePicardDegrees.lineClass N hN)) := by
      rw [hpd]
      exact hEdeg
    positivity

end SGPT.NAPotential.BJIntersect
