import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties

/-! Genuine original closed factorization from reduced source and actual
range inclusion, proving the kernel condition rather than assuming it.
Blueprint: original-reduced-closed-factor.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry Set

/-- The actual original kernel ideal sheaf of ANY quasi-compact morphism from a
reduced original scheme is radical. No kernel/radical equality is input. -/
theorem actualReducedSource_kernel_radical {X Y : Scheme.{0}} [IsReduced X] (g : X ⟶ Y) [QuasiCompact g] :
    g.ker.radical = g.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal,Scheme.Hom.ker_apply]
  apply Ideal.IsRadical.radical
  intro r hr
  obtain ⟨d,hd⟩ := hr
  change (g.app U).hom (r^d)=0 at hd
  have hnil : IsNilpotent ((g.app U).hom r) := ⟨d,by simpa only [map_pow] using hd⟩
  exact hnil.eq_zero

/-- For reduced source, actual topological range inclusion into an
original closed immersion PRODUCES the actual kernel ideal inclusion. -/
theorem actualReducedSource_closedKernel_le_of_rangeSubset {X Y Z : Scheme.{0}}
    [IsReduced X] (g : X ⟶ Z) [QuasiCompact g]
    (i : Y ⟶ Z) [IsClosedImmersion i] (h : range g ⊆ range i) : i.ker ≤ g.ker := by
  have hs : g.ker.support ≤ i.ker.support := by
    change (g.ker.support : Set Z) ⊆ (i.ker.support : Set Z)
    simpa only [Scheme.Hom.support_ker] using closure_mono h
  have hi := Scheme.IdealSheafData.vanishingIdeal_antimono hs
  rw [Scheme.IdealSheafData.vanishingIdeal_support,Scheme.IdealSheafData.vanishingIdeal_support,
    actualReducedSource_kernel_radical g] at hi
  exact (show i.ker ≤ i.ker.radical from fun U => Ideal.le_radical).trans hi

/-- Genuine original scheme factor, obtained from the PROVED actual
kernel inclusion. This is a morphism, rather than a point-set lift. -/
def actualReducedClosedFactor {X Y Z : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Z) [QuasiCompact g] (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : range g ⊆ range i) : X ⟶ Y :=
  IsClosedImmersion.lift i g (actualReducedSource_closedKernel_le_of_rangeSubset g i h)

/-- The actual original factor satisfies the LITERAL original morphism
square, with no coefficient or factorization certificate input. -/
theorem actualReducedClosedFactor_fac {X Y Z : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Z) [QuasiCompact g] (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : range g ⊆ range i) : actualReducedClosedFactor g i h ≫ i = g :=
  IsClosedImmersion.lift_fac i g _

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
