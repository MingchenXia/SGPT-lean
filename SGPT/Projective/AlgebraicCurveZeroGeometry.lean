import SGPT.Projective.AlgebraicCurveNativeMultiplicity
import SGPT.Foundations.Analysis.Pending.ChartPartition

/-! Whole SAME original zero geometry and genuine finite smooth partition,
chosen before any test/current comparison. Blueprint: algebraic-curve-zero-geometry.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Bundle
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov SGPT.NAPotential.GAGAMult SGPT.BDivisor.NSKodaira
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft HermitianHolomorphicLineBundle
open SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI DivisorRegularLocus
open scoped Topology Manifold BigOperators
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  (E : ClosedProjectiveEmbedding f) [SmoothOfRelativeDimension 1 f]
  [IsSeparated f] [QuasiCompact f]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f 1 E L)
local instance geometryPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance geometryPointCharts : ChartedSpace (ComplexModel 1) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 1
local instance geometryPointManifold : IsComplexManifold 1 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 1
local instance geometryPointHausdorff : T2Space (SchemeComplexPoint f) := schemeAnalyticPoint_t2Space f

/-- Actual original point/frame/presentation OUTPUT of the fixed original section.
No current, degree, period, measure or desired pairing field occurs. -/
structure AlgebraicCurveZeroGeometry (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) where
  point : sectionZeroSubscheme (a.tensorPower (k + 1)) σ → SchemeComplexPoint f
  image : ∀ z, schemeComplexPointImage f (point z) = sectionZeroι (a.tensorPower (k + 1)) σ z
  index : sectionZeroSubscheme (a.tensorPower (k + 1)) σ → a.I
  inFrame : ∀ z, schemeComplexPointImage f (point z) ∈ a.opens (index z)
  presentation : ∀ z, RegularPresentation
    (sectionCoefficient (positivePower (schemeHermitianLineBundle f 1 E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame (index z))) k).val
      (nativeSectionOfAlgebraicPositivePower f 1 E a H k σ) ∘
        (complexChartAt (n := 1) (point z)).val.symm)
    ((complexChartAt (n := 1) (point z)).val (point z))
  length_eq : ∀ z, Module.length
    ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z)
    ((sectionZeroSubscheme (a.tensorPower (k + 1)) σ).presheaf.stalk z) = ((presentation z).m : ℕ∞)
  isolated : ∀ z w, w ∈ (presentation z).U →
    (sectionCoefficient (positivePower (schemeHermitianLineBundle f 1 E a H) k).Fiber
      (positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame (index z))) k).val
      (nativeSectionOfAlgebraicPositivePower f 1 E a H k σ) ∘
        (complexChartAt (n := 1) (point z)).val.symm) w = 0 →
      w = (complexChartAt (n := 1) (point z)).val (point z)

/-- The original fixed section PRODUCES every actual point/frame/presentation and length reader. -/
def algebraicCurveZeroGeometry (k : ℕ) (σ : bundlePowerGlobalSections L (k + 1)) (hσ : σ ≠ 0) :
    AlgebraicCurveZeroGeometry f E a H k σ := by
  choose p hp i hi P hlen hisol using exists_algebraic_curve_native_multiplicity f E a H k σ hσ
  exact ⟨p, hp, i, hi, P, hlen, hisol⟩

namespace AlgebraicCurveZeroGeometry
variable {f E a H} {k : ℕ} {σ : bundlePowerGlobalSections L (k + 1)}
  (G : AlgebraicCurveZeroGeometry f E a H k σ)

/-- Actual physical native bundle of the SAME original section. -/
abbrev nativeBundle (_G : AlgebraicCurveZeroGeometry f E a H k σ) := positivePower (schemeHermitianLineBundle f 1 E a H) k
/-- Actual physical native section of the SAME fixed original algebraic sigma. -/
abbrev nativeSection (_G : AlgebraicCurveZeroGeometry f E a H k σ) := nativeSectionOfAlgebraicPositivePower f 1 E a H k σ
/-- Original frame of the chosen actual zero, with no new frame choice. -/
abbrev frame (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) : AtlasFrame (G.nativeBundle) :=
  positivePowerAtlasFrame (schemeHermitianAtlasFrame f 1 E a H (a.frame (G.index z))) k
/-- SAME preferred actual original chart of the actual selected zero point. -/
abbrev chart (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) : ComplexChart 1 (SchemeComplexPoint f) :=
  complexChartAt (n := 1) (G.point z)

omit [IsIntegral X] in
theorem point_injective : Function.Injective G.point := by
  intro z w h
  apply (sectionZeroι (a.tensorPower (k + 1)) σ).isClosedEmbedding.injective
  exact (G.image z).symm.trans ((congrArg (schemeComplexPointImage f) h).trans (G.image w))

omit [IsIntegral X] in
theorem point_range : Set.range G.point = {p : SchemeComplexPoint f | G.nativeSection p = 0} := by
  have hrange : Set.range (sectionZeroι (a.tensorPower (k + 1)) σ) =
      ((sectionZeroIdealSheaf (a.tensorPower (k + 1)) σ).support : Set X) :=
    Scheme.IdealSheafData.range_subschemeι _
  have hzero (p : SchemeComplexPoint f) : schemeComplexPointImage f p ∈
      Set.range (sectionZeroι (a.tensorPower (k + 1)) σ) ↔ G.nativeSection p = 0 :=
    (Iff.of_eq (congrArg (fun S : Set X => schemeComplexPointImage f p ∈ S) hrange)).trans
      (sectionZero_support_iff_native_zero f 1 E a H k σ p)
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (hzero _).mp ⟨z, (G.image z).symm⟩
  · intro hp
    obtain ⟨z, hz⟩ := (hzero p).mpr hp
    exact ⟨z, schemeComplexPointImage_injective f ((G.image z).trans hz)⟩

theorem zeroSet_closed (hσ : σ ≠ 0) : IsClosed (Set.range G.point) := by
  let := sectionZero_isArtinian f E (a.tensorPower (k + 1)) σ hσ
  exact (Set.finite_range G.point).isClosed

/-- ACTUAL cover indices: every whole original zero-scheme point, and every ambient point. -/
abbrev CoverIndex (_G : AlgebraicCurveZeroGeometry f E a H k σ) := sectionZeroSubscheme (a.tensorPower (k + 1)) σ ⊕ SchemeComplexPoint f

def coverFrame : G.CoverIndex → AtlasFrame G.nativeBundle
  | .inl z => G.frame z
  | .inr x => ⟨trivializationAt ℂ G.nativeBundle.Fiber x, inferInstance⟩

def coverChart : G.CoverIndex → ComplexChart 1 (SchemeComplexPoint f)
  | .inl z => G.chart z
  | .inr x => complexChartAt (n := 1) x

/-- The original zero windows or true off-zero frame/chart opens. -/
def coverDomain (hσ : σ ≠ 0) : G.CoverIndex → TopologicalSpace.Opens (SchemeComplexPoint f)
  | .inl z => ⟨(G.frame z).val.baseSet ∩
      ((G.chart z).val.source ∩ (G.chart z).val ⁻¹' (G.presentation z).U),
      (G.frame z).val.open_baseSet.inter
        ((G.chart z).val.isOpen_inter_preimage (G.presentation z).isOpen)⟩
  | .inr x => ⟨((G.coverFrame (.inr x)).val.baseSet ∩
      (G.coverChart (.inr x)).val.source) ∩ (Set.range G.point)ᶜ,
      ((G.coverFrame (.inr x)).val.open_baseSet.inter
        (G.coverChart (.inr x)).val.open_source).inter (G.zeroSet_closed hσ).isOpen_compl⟩

theorem coverDomain_subset_frame_chart (hσ : σ ≠ 0) (j : G.CoverIndex) :
    (G.coverDomain hσ j : Set (SchemeComplexPoint f)) ⊆
      (G.coverFrame j).val.baseSet ∩ (G.coverChart j).val.source := by
  cases j with
  | inl z => exact fun _ hy => ⟨hy.1, hy.2.1⟩
  | inr x => exact fun _ hy => hy.1

theorem coverDomain_zero_contains (hσ : σ ≠ 0)
    (z : sectionZeroSubscheme (a.tensorPower (k + 1)) σ) : G.point z ∈ G.coverDomain hσ (.inl z) := by
  exact ⟨mem_positivePowerAtlasFrame_baseSet _ (G.inFrame z) k,
    mem_complexChartAt_source _, (G.presentation z).mem⟩

theorem cover_covers (hσ : σ ≠ 0) (p : SchemeComplexPoint f) :
    ∃ j : G.CoverIndex, p ∈ G.coverDomain hσ j := by
  classical
  by_cases hp : p ∈ Set.range G.point
  · obtain ⟨z, rfl⟩ := hp
    exact ⟨.inl z, G.coverDomain_zero_contains hσ z⟩
  · exact ⟨.inr p, ⟨⟨mem_baseSet_trivializationAt ℂ G.nativeBundle.Fiber p,
      mem_complexChartAt_source p⟩, hp⟩⟩

/-- All original geometric choices and true finite weights precede ANY smooth test/current. -/
theorem exists_partition (hσ : σ ≠ 0) :
    ∃ (r : ℕ) (χ : Fin r → SchemeComplexPoint f → ℝ) (idx : Fin r → G.CoverIndex),
      (∀ i, ChartSmooth (n := 1) (χ i)) ∧ (∀ i p, 0 ≤ χ i p) ∧
      (∀ i, tsupport (χ i) ⊆ (G.coverDomain hσ (idx i) : Set (SchemeComplexPoint f))) ∧
      (∀ i, IsCompact (tsupport (χ i))) ∧ ∀ p, ∑ i, χ i p = 1 := by
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact ChartPartition.exists_chartSmooth_partitionOfUnity (G.coverDomain hσ) (G.cover_covers hσ)

end AlgebraicCurveZeroGeometry
end SGPT.Projective.NumEq.AlgebraicCurveDegree
