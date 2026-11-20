import SGPT.Projective.AlgebraicSectionZeroStalk
import Mathlib.AlgebraicGeometry.Artinian

/-! FULL ORIGINAL stalk lengths and entire finite length sums under ACTUAL
original scheme isomorphisms. Blueprint: artinian-scheme-iso-length.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry
open scoped BigOperators

/-- Actual original scheme isomorphism internally manufactures actual same-point stalk iso. -/
theorem schemeIso_stalk_selfLength {X Y : Scheme.{0}} (e : X ≅ Y) (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (e.hom x)) (Y.presheaf.stalk (e.hom x)) := by
  let er := (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  have h := SGPT.NAPotential.GraphDivisorOrderTransport.ord_ringEquiv er 0
  simpa only [map_zero, Ring.ord_zero] using h

/-- Actual entire Artinian scheme length sum is invariant under ACTUAL original scheme iso. -/
theorem artinian_selfLength_sum_eq_of_iso {X Y : Scheme.{0}}
    [IsArtinianScheme X] [IsArtinianScheme Y] (e : X ≅ Y) :
    let : Fintype X := Fintype.ofFinite _
    let : Fintype Y := Fintype.ofFinite _
    (∑ x : X, Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)) =
      ∑ y : Y, Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) := by
  let : Fintype X := Fintype.ofFinite _
  let : Fintype Y := Fintype.ofFinite _
  dsimp only
  let ep : X ≃ Y := e.hom.homeomorph.toEquiv
  calc
    _ = ∑ x : X, Module.length (Y.presheaf.stalk (ep x)) (Y.presheaf.stalk (ep x)) :=
      Finset.sum_congr rfl (fun x _ => schemeIso_stalk_selfLength e x)
    _ = _ := ep.sum_comp (fun y : Y => Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y))

end SGPT.Projective.NumEq.AlgebraicCurveDegree
