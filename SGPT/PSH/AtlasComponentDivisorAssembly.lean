import SGPT.PSH.AtlasComponentPrimeEquivalence
import SGPT.PSH.LocallyFiniteClopenImage
import SGPT.PSH.LocallyFiniteSubordinate

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]
  {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

/-- An actual native divisor on ONE internally represented genuine component. -/
def componentNativeDivisor (A : VariableComplexAtlas X) (c : ConnectedComponents X) :=
  letI := A.componentChartedSpace (componentAnchor c)
  letI := A.componentComplexManifold_of_paracompact (componentAnchor c)
  EffectiveGeometricQDivisor (A.pointDimension (componentAnchor c))
    (A.componentOpen (componentAnchor c))

/-- Only the EXISTING internally derived component structures, local to this
module's dependent-family elaboration. No structure is an extra premise. -/
local instance componentAssemblyChartedSpace (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c)))
      (A.componentOpen (componentAnchor c)) := A.componentChartedSpace (componentAnchor c)

local instance componentAssemblyComplexManifold (c : ConnectedComponents X) :
    IsComplexManifold (A.pointDimension (componentAnchor c))
      (A.componentOpen (componentAnchor c)) :=
  A.componentComplexManifold_of_paracompact (componentAnchor c)

omit [T2Space X] [ParacompactSpace X] in
private theorem locallyFinite_actual_component_carriers (A : VariableComplexAtlas X) :
    LocallyFinite (fun c : ConnectedComponents X =>
      (A.componentOpen (componentAnchor c) : Set X)) := by
  intro x
  refine ⟨connectedComponent x, (A.isOpen_component x).mem_nhds mem_connectedComponent,
    (Set.finite_singleton (ConnectedComponents.mk x)).subset ?_⟩
  intro c hc
  obtain ⟨z, hza, hzx⟩ := hc
  apply Set.mem_singleton_iff.mpr
  exact (componentAnchor_spec c).symm.trans
    (((ConnectedComponents.coe_eq_coe').mpr hza).symm.trans
      ((ConnectedComponents.coe_eq_coe').mpr hzx))

private theorem locallyFinite_native_component_nonzero_images
    (D : ∀ c : ConnectedComponents X, A.componentNativeDivisor c) :
    LocallyFinite (fun t : (c : ConnectedComponents X) × A.componentNativePrime c =>
      if (D t.1).coefficient t.2 = 0 then ∅
      else (A.componentPrimeOriginalCarrier t).val) := by
  classical
  apply locallyFinite_sigma_of_subordinate
    (fun c : ConnectedComponents X => (A.componentOpen (componentAnchor c) : Set X))
    (fun c P => if (D c).coefficient P = 0 then ∅
      else (A.nativePrimeOriginalCarrier (componentAnchor c) P).val)
    (locallyFinite_actual_component_carriers A)
  · intro c
    let := A.componentChartedSpace (componentAnchor c)
    let := A.componentComplexManifold_of_paracompact (componentAnchor c)
    have h := locallyFinite_clopen_subtype_images
      (A.componentOpen (componentAnchor c)) isClosed_connectedComponent
      (fun P => if (D c).coefficient P = 0 then ∅ else P.val) (D c).locallyFinite
    convert h using 1
    funext P
    by_cases hzero : (D c).coefficient P = 0
    · simp only [if_pos hzero, Set.image_empty]
    · simp only [if_neg hzero]
      rfl
  · intro c P y hy
    by_cases hzero : (D c).coefficient P = 0
    · simp only [if_pos hzero, mem_empty_iff_false] at hy
    · simp only [if_neg hzero] at hy
      obtain ⟨p, _hp, rfl⟩ := hy
      exact p.property

/-- Honest generic assembly from genuine native divisors on EVERY internally
represented actual component. Original modification consumers must supply
these internally; this generic family is not an original-source certificate. -/
def divisorOfNativeComponents
    (D : ∀ c : ConnectedComponents X, A.componentNativeDivisor c) :
    AtlasEffectiveGeometricQDivisor A := by
  classical
  let e := A.componentPrimeEquiv
  refine {
    coefficient := fun P => (D (e.symm P).1).coefficient (e.symm P).2
    coefficient_nonneg := fun P => (D (e.symm P).1).coefficient_nonneg (e.symm P).2
    locallyFinite := ?_ }
  have h := (locallyFinite_native_component_nonzero_images D).comp_injective e.symm.injective
  convert h using 1
  funext P
  change (if (D (e.symm P).1).coefficient (e.symm P).2 = 0 then ∅ else P.val) =
    (if (D (e.symm P).1).coefficient (e.symm P).2 = 0 then ∅
      else (A.componentPrimeOriginalCarrier (e.symm P)).val)
  have hindex : A.componentPrimeOriginalCarrier (e.symm P) = P := e.apply_symm_apply P
  rw [hindex]

/-- EVERY actual native coefficient survives on EXACTLY its original image. -/
theorem divisorOfNativeComponents_coefficient
    (D : ∀ c : ConnectedComponents X, A.componentNativeDivisor c)
    (t : (c : ConnectedComponents X) × A.componentNativePrime c) :
    (divisorOfNativeComponents D).coefficient (A.componentPrimeOriginalCarrier t) =
      (D t.1).coefficient t.2 := by
  change (fun s : (c : ConnectedComponents X) × A.componentNativePrime c =>
    (D s.1).coefficient s.2) (A.componentPrimeEquiv.symm (A.componentPrimeEquiv t)) = _
  rw [A.componentPrimeEquiv.symm_apply_apply]

/-- ENTIRE original support is the literal union of the genuine component
supports, with no finiteness or global denominator premise. -/
theorem divisorOfNativeComponents_support
    (D : ∀ c : ConnectedComponents X, A.componentNativeDivisor c) :
    (divisorOfNativeComponents D).support =
      ⋃ c, Subtype.val '' (D c).support := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, hpos, hxP⟩ := ((divisorOfNativeComponents D).mem_support x).mp hx
    let t := A.componentPrimeEquiv.symm P
    have hindex : A.componentPrimeOriginalCarrier t = P :=
      A.componentPrimeEquiv.apply_symm_apply P
    have htpos : 0 < (D t.1).coefficient t.2 := by
      rw [← divisorOfNativeComponents_coefficient D t, hindex]
      exact hpos
    rw [← hindex] at hxP
    change x ∈ Subtype.val '' t.2.val at hxP
    obtain ⟨p, hp, rfl⟩ := hxP
    apply Set.mem_iUnion.mpr
    exact ⟨t.1, ⟨p, ((D t.1).mem_support p).mpr ⟨t.2, htpos, hp⟩, rfl⟩⟩
  · intro hx
    obtain ⟨c, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨Q, hpos, hpQ⟩ := ((D c).mem_support p).mp hp
    apply ((divisorOfNativeComponents D).mem_support p.val).mpr
    refine ⟨A.componentPrimeOriginalCarrier ⟨c, Q⟩, ?_, ⟨p, hpQ, rfl⟩⟩
    rw [divisorOfNativeComponents_coefficient]
    exact hpos

private theorem atlas_divisor_eq_of_coefficient_eq
    {D E : AtlasEffectiveGeometricQDivisor A}
    (h : ∀ P, D.coefficient P = E.coefficient P) : D = E := by
  rcases D with ⟨d, hd, hdf⟩
  rcases E with ⟨e, he, hef⟩
  have hde : d = e := funext h
  cases hde
  rfl

/-- ORIGINAL D ALONE reconstructs exactly from its internally produced native
projections, retaining EVERY original coefficient and the entire support. -/
theorem AtlasEffectiveGeometricQDivisor.of_nativeComponents
    (D : AtlasEffectiveGeometricQDivisor A) :
    divisorOfNativeComponents (fun c => D.nativeComponent (componentAnchor c)) = D := by
  apply atlas_divisor_eq_of_coefficient_eq
  intro P
  obtain ⟨t, rfl⟩ := A.componentPrimeOriginalCarrier_bijective.surjective P
  exact (divisorOfNativeComponents_coefficient
    (fun c => D.nativeComponent (componentAnchor c)) t).trans
      (D.nativeComponent_coefficient (componentAnchor t.1) t.2)

end SGPT.PSH.VariableComplexAtlas
