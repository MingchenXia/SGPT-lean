import SGPT.PSH.AtlasComponentScalarNative
import SGPT.PSH.AtlasPrimeComponentProjection

/-! Full original/native component germ dictionaries for actual source local
logarithmic equations. Empty component restrictions are retained. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  {A : VariableComplexAtlas X}

/-- BOTH entire reduced-ideal memberships for EVERY original set and EVERY
actual component scalar. No regular-point or native-ideal certificate. -/
theorem original_reducedIdeal_component_iff (S : Set X) (x : X)
    (q : A.componentOpen x) (g : A.componentOpen x → ℂ) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (atlasVanishingIdeal A S).mem q.val (extendOpens (A.componentOpen x) g) ↔
      (vanishingIdeal (n := A.pointDimension x) ((Subtype.val : A.componentOpen x → X) ⁻¹' S)).mem q g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact (atlasVanishingIdeal_openRestriction_mem_iff A (A.componentOpen x) S q g).symm.trans
    (atlasVanishingIdeal_component_mem_iff_native A x _ g q)

/-- BOTH entire original principal-span memberships retain the SAME actual
restricted equation and EVERY genuine native cofactor at EVERY stalk. -/
theorem original_principalSpan_component_iff (f : X → ℂ) (x : X)
    (q : A.componentOpen x) (g : A.componentOpen x → ℂ) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    A.AtlasIsInSpanAt (· = f) q.val (extendOpens (A.componentOpen x) g) ↔
      IsInSpanAt (n := A.pointDimension x) (· = f ∘ Subtype.val) q g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  have h := atlasIsInSpanAt_comp_open_val_iff A (A.componentOpen x)
    (S := (· = f)) (p := q) (g := g)
  have hfam : (fun s' : A.componentOpen x → ℂ =>
      ∃ s,s=f ∧ s'=s ∘ Subtype.val)=(· = f ∘ Subtype.val) := by
    funext s'
    apply propext
    constructor
    · rintro ⟨s,rfl,hs⟩
      exact hs
    · intro hs
      exact ⟨f,rfl,hs⟩
  rw [hfam] at h
  exact h.symm.trans (atlasIsInSpanAt_component_iff_native A x _ g q)

/-- The literal ORIGINAL full equation ideal manufactures the SAME actual
native reduced-ideal generator, including EVERY singular scalar stalk. -/
theorem original_generator_component
    (S : Set X) (f : X → ℂ)
    (hgen : ∀ y b,(atlasVanishingIdeal A S).mem y b ↔ A.AtlasIsInSpanAt (· = f) y b)
    (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ q : A.componentOpen x,∀ g : A.componentOpen x → ℂ,
      (vanishingIdeal (n := A.pointDimension x) ((Subtype.val : A.componentOpen x → X) ⁻¹' S)).mem q g ↔
        IsInSpanAt (n := A.pointDimension x) (· = f ∘ Subtype.val) q g := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro q g
  exact (original_reducedIdeal_component_iff S x q g).symm.trans
    ((hgen q.val _).trans (original_principalSpan_component_iff f x q g))

/-- Actual all-chart source holomorphy manufactures true native holomorphy
on the SAME component; neither model nor holomorphy is supplied separately. -/
theorem original_holomorphic_component (f : X → ℂ)
    (hf : A.ChartHolomorphicOn f univ) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ q : A.componentOpen x,HolomorphicAt (A.pointDimension x) (f ∘ Subtype.val) q := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro q
  have ho : A.AtlasHolomorphicAt f q.val := ⟨univ,isOpen_univ,mem_univ _,hf⟩
  exact (atlasHolomorphicAt_component_iff_native A x _ q).mp
    ((atlasHolomorphicAt_comp_open_val_iff A (A.componentOpen x)).mpr ho)

/-- An ORIGINAL prime restricts to an actual native prime with the SAME
image or to the GENUINE empty set. Original disconnected opens are retained. -/
theorem original_prime_component_cases (P : AtlasGeometricPrimeCarrier A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (∃ Q : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
      (Subtype.val : A.componentOpen x → X) ⁻¹' P.val=Q.val ∧
      Subtype.val '' Q.val=P.val) ∨
    (Subtype.val : A.componentOpen x → X) ⁻¹' P.val=∅ := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  by_cases hmeet : (P.val ∩ connectedComponent x).Nonempty
  · obtain ⟨Q,hQ⟩ := P.exists_native_component x hmeet
    exact Or.inl ⟨Q,by rw [←hQ]; exact Set.preimage_image_eq Q.val Subtype.val_injective,hQ⟩
  · right
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact hmeet ⟨q.val,hq,q.property⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
