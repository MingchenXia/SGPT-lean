import SGPT.PSH.AtlasPrimeComponentProjection

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- ONE actual original representative per EXISTING connected-component
quotient class, chosen internally from genuine quotient surjectivity. -/
def componentAnchor (c : ConnectedComponents X) : X :=
  Classical.choose (ConnectedComponents.surjective_coe c)

theorem componentAnchor_spec (c : ConnectedComponents X) :
    ConnectedComponents.mk (componentAnchor c) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

variable {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

/-- ALL genuine primes on the SAME internally represented actual component.
No chosen prime catalog or native structure is an input. -/
def componentNativePrime (A : VariableComplexAtlas X) (c : ConnectedComponents X) :=
  letI := A.componentChartedSpace (componentAnchor c)
  letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
  GeometricPrimeCarrier (A.pointDimension (componentAnchor c))
    (A.componentOpen (componentAnchor c))

/-- The entire dependent component-prime index maps by literal ORIGINAL image. -/
def componentPrimeOriginalCarrier (A : VariableComplexAtlas X)
    (t : (c : ConnectedComponents X) × A.componentNativePrime c) :
    AtlasGeometricPrimeCarrier A :=
  A.nativePrimeOriginalCarrier (componentAnchor t.1) t.2

private theorem componentPrimeOriginalCarrier_class
    (t : (c : ConnectedComponents X) × A.componentNativePrime c)
    {z : X} (hz : z ∈ (A.componentPrimeOriginalCarrier t).val) :
    ConnectedComponents.mk z = t.1 := by
  change z ∈ Subtype.val '' t.2.val at hz
  obtain ⟨p, _hp, rfl⟩ := hz
  exact ((ConnectedComponents.coe_eq_coe').mpr p.property).trans (componentAnchor_spec t.1)

/-- Nonempty SAME carriers force equal quotient components; the full prescribed
component dictionary supplies surjectivity, even for anchors outside a prime. -/
theorem componentPrimeOriginalCarrier_bijective (A : VariableComplexAtlas X) :
    Function.Bijective A.componentPrimeOriginalCarrier := by
  constructor
  · rintro ⟨c, P⟩ ⟨d, Q⟩ h
    obtain ⟨z, hz⟩ := (A.componentPrimeOriginalCarrier ⟨c, P⟩).nonempty
    have hcd : c = d :=
      (componentPrimeOriginalCarrier_class ⟨c, P⟩ hz).symm.trans
        (componentPrimeOriginalCarrier_class ⟨d, Q⟩ (by rwa [← h]))
    subst d
    have hPQ : P = Q := A.nativePrimeOriginalCarrier_injective (componentAnchor c) h
    cases hPQ
    rfl
  · intro P
    obtain ⟨z, hz⟩ := P.nonempty
    let c := ConnectedComponents.mk z
    have hza : z ∈ connectedComponent (componentAnchor c) :=
      (ConnectedComponents.coe_eq_coe').mp (componentAnchor_spec c).symm
    obtain ⟨Q, hQ⟩ := P.exists_native_component (componentAnchor c) ⟨z, hz, hza⟩
    exact ⟨⟨c, Q⟩, AtlasGeometricPrimeCarrier.ext hQ⟩

/-- Genuine equivalence of the ENTIRE original prime index with the disjoint
sum of ALL actual component primes. Inverse choices follow the proved bijection. -/
def componentPrimeEquiv (A : VariableComplexAtlas X) :
    ((c : ConnectedComponents X) × A.componentNativePrime c) ≃
      AtlasGeometricPrimeCarrier A :=
  Equiv.ofBijective A.componentPrimeOriginalCarrier A.componentPrimeOriginalCarrier_bijective

end SGPT.PSH.VariableComplexAtlas
