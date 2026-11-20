import SGPT.Foundations.Schemes.SchemeAnalyticSeparation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Closed algebraic carriers commute with the actual map of complex points. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace

/-- The image on complex points of a closed algebraic carrier is the complex-point carrier of the
scheme-theoretic underlying set image. -/
theorem schemeComplexPointMap_image_closedCarrier {V X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (p : V ⟶ X) [LocallyOfFiniteType (p ≫ f)]
    {S : Set V} (hS : IsClosed S) :
    schemeComplexPointMap (p ≫ f) f p rfl '' (schemeComplexPointImage (p ≫ f) ⁻¹' S) =
      schemeComplexPointImage f ⁻¹' (p '' S) := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨schemeComplexPointImage (p ≫ f) v, hv, rfl⟩
  · rintro ⟨x, hxS, hx⟩
    let : JacobsonSpace V := LocallyOfFiniteType.jacobsonSpace (p ≫ f)
    let : IsClosedImmersion q.val := isClosedImmersion_of_comp_eq_id f q.val q.property
    have hq : IsClosed ({schemeComplexPointImage f q} : Set X) := by
      rw [← schemeComplexPoint_range f q]
      exact q.val.isClosedEmbedding.isClosed_range
    let T := S ∩ p ⁻¹' ({schemeComplexPointImage f q} : Set X)
    have hT : IsClosed T := hS.inter (hq.preimage p.continuous)
    have hTne : T.Nonempty := ⟨x, hxS, hx⟩
    obtain ⟨z, hzT, hzc⟩ := nonempty_inter_closedPoints hTne hT.isLocallyClosed
    let v : SchemeComplexPoint (p ≫ f) :=
      ⟨pointOfClosedPoint (p ≫ f) z hzc, pointOfClosedPoint_comp (p ≫ f) z hzc⟩
    have hv : schemeComplexPointImage (p ≫ f) v = z :=
      pointOfClosedPoint_apply (p ≫ f) z hzc _
    have hz : p z = schemeComplexPointImage f q := by
      have hmem : z ∈ p ⁻¹' ({schemeComplexPointImage f q} : Set X) := hzT.2
      exact mem_singleton_iff.mp (mem_preimage.mp hmem)
    refine ⟨v, ?_, schemeComplexPointImage_injective f ?_⟩
    · change schemeComplexPointImage (p ≫ f) v ∈ S
      rw [hv]
      exact hzT.1
    · change p (schemeComplexPointImage (p ≫ f) v) = schemeComplexPointImage f q
      exact (congrArg p hv).trans hz

/-- For a proper map, the image of the complex carrier of a specialization closure is the
complex carrier of the specialization closure of the image point. -/
theorem schemeComplexPointMap_image_pointClosure {V X : Scheme.{0}}
    (f : X ⟶ Spec (.of ℂ)) (p : V ⟶ X) [LocallyOfFiniteType (p ≫ f)] [IsProper p]
    (η : V) :
    schemeComplexPointMap (p ≫ f) f p rfl ''
        (schemeComplexPointImage (p ≫ f) ⁻¹' closure ({η} : Set V)) =
      schemeComplexPointImage f ⁻¹' closure ({p η} : Set X) := by
  rw [schemeComplexPointMap_image_closedCarrier f p isClosed_closure]
  have himage : p '' closure ({η} : Set V) = closure ({p η} : Set X) := by
    apply le_antisymm
    · simpa only [image_singleton] using
        (image_closure_subset_closure_image (s := ({η} : Set V)) p.continuous)
    · apply closure_minimal _ (p.isClosedMap _ isClosed_closure)
      exact singleton_subset_iff.mpr ⟨η, subset_closure rfl, rfl⟩
  rw [himage]

end SGPT.Okounkov
