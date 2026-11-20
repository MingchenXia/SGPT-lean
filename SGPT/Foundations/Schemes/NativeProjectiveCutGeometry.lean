import SGPT.Foundations.Schemes.RegularSectionDimensionDrop

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The genuine native pulled projective O(1), with its actual coordinate atlas. -/
def nativeProjectivePositiveLine (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) : IntrinsicLineBundle X where
  sheaf := (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf
  atlas := nativePolynomialPullbackAtlas K N f

/-- Literal first tensor power is identified by the genuine sheaf tensor left unit. -/
def nativeProjectivePositiveLinePowerOneIso (K : Type) [Field K] (N : ℕ) {X : Scheme}
    (f : X ⟶ polynomialProj K N) :
    bundleTensorPower (nativeProjectivePositiveLine K N f).sheaf 1 ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K N).sheaf :=
  bundleTensorLeftUnitIso _

/-- The ACTUAL zero closed immersion followed by the original embedding,
retaining the exact original composite structural map and ambient dimension. -/
def ClosedProjectiveEmbedding.sectionZero {X : Scheme} {p : X ⟶ Spec (.of ℂ)}
    (P : ClosedProjectiveEmbedding p) {L : X.Modules} (a : LineBundleAtlas L)
    (s : Γ(L, ⊤)) : ClosedProjectiveEmbedding (sectionZeroι a s ≫ p) where
  ambientDimension := P.ambientDimension
  map := sectionZeroι a s ≫ P.map
  closedImmersion := inferInstance
  over_base := by rw [Category.assoc, P.over_base]

end
end SGPT.Foundations.Schemes
