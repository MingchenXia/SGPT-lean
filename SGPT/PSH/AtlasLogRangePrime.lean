import SGPT.PSH.AtlasLogRangeComponent

/-! Actual native primes on a component open produce literal ORIGINAL
range primes; dimensions, connected component and prime witness are internal. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open scoped Topology Manifold ContDiff Classical
universe u

/-- Pure substitution of a genuinely proved dimension equality retains the
actual native prime preimage; it introduces no geometric witness premise. -/
def primePreimageOfDimensionEq {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a=b) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm)
    (P : GeometricPrimeCarrier b N) : GeometricPrimeCarrier a M := by
  subst b
  exact biholomorphic_geometricPrimeCarrier_preimage e he hei P

/-- The SAME literal entire carrier under dimension substitution. -/
theorem primePreimageOfDimensionEq_carrier
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a=b) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm)
    (P : GeometricPrimeCarrier b N) :
    (primePreimageOfDimensionEq h e he hei P).val=e ⁻¹' P.val := by
  subst b
  rfl

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  (A : VariableComplexAtlas X) (x : X)

/-- An ACTUAL native prime on an original component-open internally gives
an ACTUAL ORIGINAL prime on its literal range, with the SAME entire carrier.
No source prime catalog, connectedness or dimension witness is supplied. -/
theorem exists_original_prime_on_range (O : Opens (A.componentOpen x)) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ P : GeometricPrimeCarrier (A.pointDimension x) O,
    let U := flattenOpen (A.componentOpen x) O
    letI := A.openRestriction_paracompactSpace U
    ∃ W : AtlasGeometricPrimeCarrier (A.openRestriction U),
      W.val=flattenHomeomorph (A.componentOpen x) O '' P.val := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro P
  let U := flattenOpen (A.componentOpen x) O
  let B := A.openRestriction U
  let e := flattenHomeomorph (A.componentOpen x) O
  let := A.openRestriction_paracompactSpace U
  obtain ⟨q,hq⟩ := P.nonempty
  let p := e q
  let := B.componentChartedSpace p
  let := B.componentComplexManifold_of_paracompact p
  let C := nativeConnectedOpen (n := A.pointDimension x) q
  have hC : IsClopen (C : Set O) := ⟨isClosed_connectedComponent,C.isOpen⟩
  have hPC : P.val⊆(C : Set O) := by
    have hpconn : IsPreconnected P.val := by
      rw [←P.subvariety_carrier]
      exact CodimOneSupport.isPreconnected_of_isComplexAnalyticallyIrreducible P.subvariety.irreducible_carrier
    exact hpconn.subset_connectedComponent hq
  obtain ⟨PC,hPCcarrier⟩ := exists_prime_on_clopen_of_subset P C hC hPC
  let r : B.componentOpen p ≃ₜ C := connectedComponentHomeomorph e q
  let PB := primePreimageOfDimensionEq (range_component_dimension A x O q) r
    (range_component_contMDiff A x O q) (range_component_symm_contMDiff A x O q) PC
  let W := B.nativePrimeOriginalCarrier p PB
  refine ⟨W,?_⟩
  change Subtype.val '' PB.val=e '' P.val
  rw [primePreimageOfDimensionEq_carrier,hPCcarrier]
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(r z).val,hz,?_⟩
    exact e.apply_symm_apply z.val
  · rintro ⟨z,hz,rfl⟩
    let c : C := ⟨z,hPC hz⟩
    refine ⟨r.symm c,?_,rfl⟩
    change (r (r.symm c)).val∈P.val
    rw [r.apply_symm_apply]
    exact hz

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
