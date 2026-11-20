import SGPT.PSH.AtlasThetaHolomorphicPullback
import SGPT.PSH.GrauertRemmertBounded

/-! # Actual varying-dimension analytic modification pullback -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Genuine all-chart holomorphy on a specified part of the original source. -/
def IsHolomorphicOn (A : VariableComplexAtlas X) (B : VariableComplexAtlas Y)
    (f : X → Y) (U : Set X) : Prop :=
  ContinuousOn f U ∧ ∀ i : A.Index, ∀ j : B.Index,
    DifferentiableOn ℂ (atlasCoordinateMap A B f i j)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        (U ∩ f ⁻¹' (B.chart j).source))

/-- Actual proper bimeromorphic geometry. The inverse is required only on
an analytic complement; no PSH or non-pole component condition is a field. -/
def IsAtlasAnalyticModification (A : VariableComplexAtlas X)
    (B : VariableComplexAtlas Y) (f : X → Y) : Prop :=
  A.IsHolomorphic B f ∧ IsProperMap f ∧
    ∃ (E : Set X) (S : Set Y) (s : Y → X),
      A.HasAnalyticChartEquations E ∧ interior E = ∅ ∧
      B.HasAnalyticChartEquations S ∧ interior S = ∅ ∧
      f ⁻¹' S = E ∧ B.IsHolomorphicOn A s Sᶜ ∧
      (∀ y ∉ S, f (s y) = y) ∧ ∀ x ∉ E, s (f x) = x

/-- The actual off-exceptional inverse and target original QPSH manufacture
a non-pole point in every original source component. -/
theorem IsAtlasAnalyticModification.exists_component_nonbot
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f)
    {u : Y → EReal} (hu : B.IsQPSH u) (x : X) :
    ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥ := by
  obtain ⟨_hf, _hp, E, S, s, _hE, hEint, hS, _hSint, hpre, hs, hright, hleft⟩ := hf
  have hC : IsOpen (connectedComponent x) := A.isOpen_component x
  have hEdense : Dense Eᶜ := interior_eq_empty_iff_dense_compl.mp hEint
  obtain ⟨a, haE, haC⟩ := hEdense.exists_mem_open hC ⟨x, mem_connectedComponent⟩
  have hbS : f a ∉ S := by
    intro haS
    apply haE
    rw [← hpre]
    exact haS
  let O := Sᶜ ∩ s ⁻¹' connectedComponent x
  have hO : IsOpen O := hs.1.isOpen_inter_preimage hS.isClosed.isOpen_compl hC
  have hbO : f a ∈ O := by
    refine ⟨hbS, ?_⟩
    change s (f a) ∈ connectedComponent x
    rw [hleft a haE]
    exact haC
  obtain ⟨y, hyO, hny⟩ := hu.locallyNondegenerate (f a) O hO hbO
  refine ⟨s y, hyO.2, ?_⟩
  rw [hright y hyO.1]
  exact hny

/-- The whole actual pulled background satisfies every original local-potential
PSH test; its component nondegeneracy is produced from modification geometry. -/
theorem IsThetaPSH.comp_atlasAnalyticModification
    {θ : AtlasClosedRealOneOneForm B} {u : Y → EReal} (hu : B.IsThetaPSH θ u)
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) :
    A.IsThetaPSH (θ.holomorphicPullback hf.1) (u ∘ f) :=
  (hu.comp_holomorphic_iff_component_nonbot hf.1).mpr
    (hf.exists_component_nonbot ⟨θ, hu⟩)

/-- Actual varying-dimension proper modification pullback of original QPSH. -/
theorem IsQPSH.comp_atlasAnalyticModification {u : Y → EReal}
    (hu : B.IsQPSH u) {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) :
    A.IsQPSH (u ∘ f) :=
  (hu.comp_holomorphic_iff_component_nonbot hf.1).mpr (hf.exists_component_nonbot hu)

/-- Literal local rational analytic type retains its coefficient, composed
generators and bounded remainder on the actual connected refinements. -/
theorem HasRationalAnalyticType.comp_atlasAnalyticModification
    {u : Y → EReal} (hu : B.HasRationalAnalyticType u)
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) :
    A.HasRationalAnalyticType (u ∘ f) := hu.comp_atlasHolomorphic hf.1

end SGPT.PSH.VariableComplexAtlas
