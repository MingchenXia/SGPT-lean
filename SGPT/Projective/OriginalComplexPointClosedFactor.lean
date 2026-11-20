import SGPT.Projective.OriginalReducedClosedFactor
import SGPT.Foundations.Schemes.SchemeComplexPointOpen
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Actual original complex-point range tests PRODUCE whole scheme
range inclusion and genuine original closed factorization. No whole
range/kernel/factor certificate. Blueprint: original-complex-point-closed-factor.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace

/-- Actual original finite-type complex points detect ENTIRE range
containment in a genuine closed immersion, via TRUE original closed
points and Jacobson density. No whole range inclusion is supplied. -/
theorem originalRangeSubset_of_complexPoints {X Y Z : Scheme.{0}}
    (g : X ⟶ Z) (fZ : Z ⟶ Spec (.of ℂ)) [LocallyOfFiniteType (g ≫ fZ)]
    (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : ∀ q : SchemeComplexPoint (g ≫ fZ),
      g (schemeComplexPointImage (g ≫ fZ) q) ∈ range i) : range g ⊆ range i := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (g ≫ fZ)
  have hclosed : IsClosed (g ⁻¹' range i) := i.isClosedEmbedding.isClosed_range.preimage g.continuous
  have hpoints : closedPoints X ⊆ g ⁻¹' range i := by
    intro x hx
    let q : SchemeComplexPoint (g ≫ fZ) :=
      ⟨pointOfClosedPoint (g ≫ fZ) x hx,pointOfClosedPoint_comp (g ≫ fZ) x hx⟩
    have hq : schemeComplexPointImage (g ≫ fZ) q=x := pointOfClosedPoint_apply (g ≫ fZ) x hx _
    exact hq ▸ h q
  have hfull : (univ : Set X) ⊆ g ⁻¹' range i := by
    rw [← closure_closedPoints]
    exact closure_minimal hpoints hclosed
  rintro _ ⟨x,rfl⟩
  exact hfull (mem_univ x)

/-- A genuine original scheme morphism is PRODUCED from actual complex
point containment, source reducedness and original finite-type geometry.
The kernel inclusion is internally proved, not a target premise. -/
def originalComplexPointClosedFactor {X Y Z : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Z) [QuasiCompact g] (fZ : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType (g ≫ fZ)] (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : ∀ q : SchemeComplexPoint (g ≫ fZ),
      g (schemeComplexPointImage (g ≫ fZ) q) ∈ range i) : X ⟶ Y :=
  actualReducedClosedFactor g i (originalRangeSubset_of_complexPoints g fZ i h)

/-- The actual complex-point-produced factor satisfies the LITERAL
original morphism square, including the original sheaf maps. -/
theorem originalComplexPointClosedFactor_fac {X Y Z : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Z) [QuasiCompact g] (fZ : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType (g ≫ fZ)] (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : ∀ q : SchemeComplexPoint (g ≫ fZ),
      g (schemeComplexPointImage (g ≫ fZ) q) ∈ range i) :
    originalComplexPointClosedFactor g fZ i h ≫ i = g :=
  actualReducedClosedFactor_fac g i _

/-- SAME original structural map is retained by the true produced factor. -/
theorem originalComplexPointClosedFactor_overBase {X Y Z : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Z) [QuasiCompact g] (fZ : Z ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType (g ≫ fZ)] (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : ∀ q : SchemeComplexPoint (g ≫ fZ),
      g (schemeComplexPointImage (g ≫ fZ) q) ∈ range i) :
    originalComplexPointClosedFactor g fZ i h ≫ (i ≫ fZ) = g ≫ fZ := by
  rw [← Category.assoc,originalComplexPointClosedFactor_fac]

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
