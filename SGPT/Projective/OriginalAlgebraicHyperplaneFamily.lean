import SGPT.Projective.OriginalOrdinaryNativeSection
import SGPT.Projective.OriginalOpenSectionZero
import SGPT.Projective.OriginalPhysicalMetricOverBase
import SGPT.Projective.SourceFiniteSectionMap
import SGPT.NAPotential.ProjectiveGraphProjectiveHomeomorph
import SGPT.NAPotential.FSPosMetric

/-! The ACTUAL original algebraic map pulls back actual ordinary coordinate
sections; their native family reads the SAME original algebraic map.
Blueprint: original-algebraic-hyperplane-family.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.FSPos SGPT.GAGA.H0S
open SGPT.GAGA.ChowBl SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectiveHomeomorph
open SGPT.NAPotential.AlgPrimes3.ProjectiveGraphProjectivePoint
open HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} {N : ℕ} (α : X ⟶ polynomialProj ℂ N)

/-- The actual original line sheaf, using the genuine original hyperplane line. -/
def originalMapHyperplaneBundle : X.Modules :=
  (Scheme.Modules.pullback α).obj (hyperplaneBundle (identityEmbedding N))

/-- Actual inherited original frames on the true inverse-image opens. -/
def originalMapHyperplaneAtlas : LineBundleAtlas (originalMapHyperplaneBundle α) :=
  matePullbackAtlas α (hyperplaneAtlas (identityEmbedding N))

/-- The actual ordinary original coordinate section, through the true adjunction unit. -/
def originalMapCoordinateSection (j : Fin (N+1)) : Γ(originalMapHyperplaneBundle α,⊤) :=
  originalPulledSection α (coordSection (identityEmbedding N) j ⊤)

/-- Every actual original coordinate coefficient is the actual pulled ratio. -/
theorem originalMapCoordinateSection_coefficients (i j : Fin (N+1)) :
    ((originalMapHyperplaneAtlas α).frame i).coefficients (𝟙 _)
      ((originalMapHyperplaneBundle α).val.map ((originalMapHyperplaneAtlas α).opens i).leTop.op
        (originalMapCoordinateSection α j)) =
      α.app (coordOpen (identityEmbedding N) i) (ratio (identityEmbedding N) i j) := by
  have h := originalPulledSection_coefficients α (coordSection (identityEmbedding N) j ⊤)
    ((hyperplaneAtlas (identityEmbedding N)).frame i) (𝟙 _)
  rw [coordSection_restrict] at h
  exact h.trans (congrArg (α.app (coordOpen (identityEmbedding N) i))
    (coordCoef_atlas (identityEmbedding N) i j))

variable (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f] (E : ClosedProjectiveEmbedding f)
  (H : SchemeLineBundleMetric f n E (originalMapHyperplaneBundle α))
local instance mapFamilyTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance mapFamilyCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance mapFamilyManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance mapFamilyTargetTopology : TopologicalSpace (SchemeComplexPoint (polynomialProjStructureMap ℂ N)) := schemeAnalyticPointTopology _

/-- The same actual ordinary original coordinate section gives a true native section. -/
def originalMapCoordinateNativeSection (j : Fin (N+1)) :
    HolomorphicSections (n:=n)
      (schemeHermitianLineBundle f n E (originalMapHyperplaneAtlas α) H).Fiber :=
  nativeSectionOfOriginalOrdinary f n E (originalMapHyperplaneAtlas α) H
    (originalMapCoordinateSection α j)

/-- The actual native original coefficient is the actual original target ratio. -/
theorem originalMapCoordinateNativeSection_frame (hα : α≫polynomialProjStructureMap ℂ N=f)
    (i j : Fin (N+1)) (x : SchemeComplexPoint f)
    (hx : schemeComplexPointImage f x ∈ (originalMapHyperplaneAtlas α).opens i) :
    sectionCoefficient (schemeHermitianLineBundle f n E (originalMapHyperplaneAtlas α) H).Fiber
      (schemeHermitianAtlasFrame f n E (originalMapHyperplaneAtlas α) H
        ((originalMapHyperplaneAtlas α).frame i)).val
      (originalMapCoordinateNativeSection α f n E H j) x =
    schemeOpenRegularFunction (polynomialProjStructureMap ℂ N) N (identityEmbedding N)
      (coordOpen (identityEmbedding N) i) (ratio (identityEmbedding N) i j)
      (schemeComplexPointMap f (polynomialProjStructureMap ℂ N) α hα x) := by
  rw [originalMapCoordinateNativeSection,nativeSectionOfOriginalOrdinary_frame _ _ _ _ _ _ _ _ hx,
    originalMapCoordinateSection_coefficients]
  cases hα
  exact originalRegularFunction_pullback (polynomialProjStructureMap ℂ N) α n N E
    (identityEmbedding N) (coordOpen (identityEmbedding N) i) (ratio (identityEmbedding N) i j) x hx

/-- The actual original pulled coordinates generate at EVERY actual native point. -/
theorem originalMapCoordinateNativeSection_generating (hα : α≫polynomialProjStructureMap ℂ N=f) :
    ∀x : SchemeComplexPoint f, ∃ j : Fin (N+1),
      originalMapCoordinateNativeSection α f n E H j x≠0 := by
  intro x
  obtain ⟨i,hi⟩ := (originalMapHyperplaneAtlas α).covers (schemeComplexPointImage f x)
  refine ⟨i,?_⟩
  intro hz
  have hc := originalMapCoordinateNativeSection_frame α f n E H hα i i x hi
  rw [ratio_self,schemeOpenRegularFunction_one] at hc
  · change (schemeHermitianAtlasFrame f n E (originalMapHyperplaneAtlas α) H
      ((originalMapHyperplaneAtlas α).frame i)).val.linearEquivAt ℂ x hi
        (originalMapCoordinateNativeSection α f n E H i x) = 1 at hc
    rw [hz,map_zero] at hc
    exact zero_ne_one hc
  · exact hi

/-- The actual original coordinate family reads EXACTLY the same algebraic map,
without a point-map or family comparison premise. -/
theorem originalMapCoordinateNativeSection_projectiveMap (hα : α≫polynomialProjStructureMap ℂ N=f)
    (x : SchemeComplexPoint f) :
    sourceNativeFiniteSectionProjectiveMap
      (schemeHermitianLineBundle f n E (originalMapHyperplaneAtlas α) H)
      (originalMapCoordinateNativeSection α f n E H)
      (originalMapCoordinateNativeSection_generating α f n E H hα) x =
    originalProjectiveHomeomorph N
      (schemeComplexPointMap f (polynomialProjStructureMap ℂ N) α hα x) := by
  obtain ⟨i,hi⟩ := (originalMapHyperplaneAtlas α).covers (schemeComplexPointImage f x)
  have hiTarget : schemeComplexPointImage (polynomialProjStructureMap ℂ N)
      (schemeComplexPointMap f (polynomialProjStructureMap ℂ N) α hα x) ∈
        coordOpen (identityEmbedding N) i := hi
  rw [sourceNativeFiniteSectionProjectiveMap_frame _ _ _
    (schemeHermitianAtlasFrame f n E (originalMapHyperplaneAtlas α) H
      ((originalMapHyperplaneAtlas α).frame i)) x hi,
    originalProjectiveHomeomorph_apply,
    projectivePoint_eq (polynomialProjStructureMap ℂ N) (identityEmbedding N) N i hiTarget]
  congr 1
  funext j
  exact originalMapCoordinateNativeSection_frame α f n E H hα i j x hi
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
