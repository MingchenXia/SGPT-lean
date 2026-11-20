import SGPT.Projective.SmoothSchemeClopenComponents
import SGPT.Projective.ActualOpenNativeIsomorphism
import SGPT.Projective.ActualClopenPeriodSum

/-! ENTIRE original smooth projective scheme: literal actual component
native maps manufacture ALL hypotheses of genuine period sum.
Blueprint: original-component-period.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses NefMixedMass ModificationMassInvariance
open SGPT.Okounkov SGPT.NAPotential.NativeSchemeImmersion
open scoped Topology Manifold BigOperators ContDiff
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
  (E : ClosedProjectiveEmbedding f)

local instance componentPeriodTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance componentPeriodCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance componentPeriodManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance componentPeriodMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance componentPeriodBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance actualComponentSmooth (C : ↥(irreducibleComponents X)) :
    SmoothOfRelativeDimension n ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f) :=
  smoothProjective_component_smoothDimension f n E C.val C.property
local instance actualComponentSeparated (C : ↥(irreducibleComponents X)) :
    IsSeparated ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f) :=
  (smoothProjective_componentEmbedding f n E C.val C.property).isSeparated
local instance actualComponentQuasiCompact (C : ↥(irreducibleComponents X)) :
    QuasiCompact ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f) :=
  (smoothProjective_componentEmbedding f n E C.val C.property).quasiCompact
local instance actualComponentTopology (C : ↥(irreducibleComponents X)) :
    TopologicalSpace (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) :=
  schemeAnalyticPointTopology _
local instance actualComponentCharts (C : ↥(irreducibleComponents X)) :
    ChartedSpace (ComplexModel n) (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) :=
  schemeAnalyticTNChartedSpace _ n
local instance actualComponentManifold (C : ↥(irreducibleComponents X)) :
    IsComplexManifold n (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) :=
  schemeAnalyticTN_isComplexManifold _ n
local instance actualComponentMeasurable (C : ↥(irreducibleComponents X)) :
    MeasurableSpace (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) := borel _
local instance actualComponentBorel (C : ↥(irreducibleComponents X)) :
    BorelSpace (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) := ⟨rfl⟩
local instance actualComponentCompact (C : ↥(irreducibleComponents X)) :
    CompactSpace (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)) :=
  (smoothProjective_componentEmbedding f n E C.val C.property).analyticCompact

/-- ALL actual original components preserve the SAME original entire native period. -/
theorem originalProjectiveComponent_slotIntegral_sum
    (w : KahlerBackground n (SchemeComplexPoint f))
    (w' : ∀ C : ↥(irreducibleComponents X), KahlerBackground n
      (SchemeComplexPoint ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f)))
    (theta : Fin n → ClosedRealOneOneForm n (SchemeComplexPoint f)) :
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : Finite ↥(irreducibleComponents X) := smoothProjective_componentIndex_finite f E
    let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
    (∑ C : ↥(irreducibleComponents X), slotIntegral (w' C)
      (pullbackTuple (schemeComplexPointMap_contMDiff f
        (smoothProjectiveComponentOpen f n E C.val C.property).ι n n ∞) theta)) =
      slotIntegral w theta := by
  classical
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let := smoothProjective_componentIndex_finite f E
  let : Fintype ↥(irreducibleComponents X) := Fintype.ofFinite _
  let π (C : ↥(irreducibleComponents X)) := schemeComplexPointMap
    ((smoothProjectiveComponentOpen f n E C.val C.property).ι ≫ f) f
      (smoothProjectiveComponentOpen f n E C.val C.property).ι rfl
  let hπ (C : ↥(irreducibleComponents X)) := schemeComplexPointMap_contMDiff f
    (smoothProjectiveComponentOpen f n E C.val C.property).ι n n ∞
  let U (C : ↥(irreducibleComponents X)) : Set (SchemeComplexPoint f) := schemeComplexPointImage f ⁻¹' C.val
  have hU (C : ↥(irreducibleComponents X)) : IsOpen (U C) :=
    (smoothProjective_component_isClopen f n E C.val C.property).2.preimage
      (schemeComplexPointImage_continuous f)
  have hiso (C : ↥(irreducibleComponents X)) :
      SGPT.Foundations.Analysis.FirstPass.BlowupSequences.IsIsomorphismOver n (π C) (U C) := by
    simpa only [π, U, smoothProjectiveComponentOpen, Scheme.Opens.range_ι, Opens.coe_mk] using
      actualOpenNative_isIsomorphismOver f (smoothProjectiveComponentOpen f n E C.val C.property).ι n
  have hfull (C : ↥(irreducibleComponents X)) : π C ⁻¹' U C = univ := by
    have he : U C = Set.range (π C) := by
      simpa only [π, U, smoothProjectiveComponentOpen, Scheme.Opens.range_ι, Opens.coe_mk] using
        (actualOpenNative_pointMap_range f (smoothProjectiveComponentOpen f n E C.val C.property).ι).symm
    rw [he]
    ext p
    exact iff_of_true ⟨p, rfl⟩ (mem_univ p)
  have hd : Pairwise (fun C D => Disjoint (U C) (U D)) := by
    intro C D hCD
    apply Set.disjoint_left.mpr
    intro p hpC hpD
    have hne : C.val ≠ D.val := fun h => hCD (Subtype.ext h)
    exact Set.disjoint_left.mp (smoothScheme_components_pairwiseDisjoint f n C.property D.property hne) hpC hpD
  have hcover : (⋃ C, U C) = univ := by
    apply Set.eq_univ_of_forall
    intro p
    obtain ⟨C, hC⟩ := smoothProjective_componentOpens_cover f n E (schemeComplexPointImage f p)
    exact Set.mem_iUnion.mpr ⟨C, hC⟩
  exact slotIntegral_sum_fullOpen π hπ U hU hiso hfull hd hcover w w' theta

end SGPT.Projective.NumEq.AlgebraicCurveDegree
