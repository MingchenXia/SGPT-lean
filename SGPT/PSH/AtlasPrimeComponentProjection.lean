import SGPT.PSH.AtlasGeometricQDivisor
import SGPT.PSH.BiholomorphicPrimeTransport
import SGPT.PSH.AtlasNativeComponentHolomorphicOn

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]
  {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

private theorem prime_preimage_of_dimension_eq
    {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]
    (h : n = m) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ e.symm)
    (P : GeometricPrimeCarrier m N) :
    ∃ Q : GeometricPrimeCarrier n M, Q.val = e ⁻¹' P.val := by
  subst m
  exact ⟨biholomorphic_geometricPrimeCarrier_preimage e he hei P,
    biholomorphic_geometricPrimeCarrier_preimage_carrier e he hei P⟩

/-- A genuine native prime gives its canonical literal ORIGINAL carrier;
all native component structures are internally derived. -/
def nativePrimeOriginalCarrier (A : VariableComplexAtlas X) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x) →
      AtlasGeometricPrimeCarrier A := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  exact fun P => ⟨Subtype.val '' P.val, ⟨x, P, rfl⟩⟩

/-- Equality of ORIGINAL image carriers retains the ENTIRE native prime. -/
theorem nativePrimeOriginalCarrier_injective (A : VariableComplexAtlas X) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    Function.Injective (A.nativePrimeOriginalCarrier x) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro P Q h
  apply GeometricPrimeCarrier.ext
  have hval := congrArg Subtype.val h
  exact (Set.image_injective.mpr Subtype.val_injective) hval

omit [T2Space X] [ParacompactSpace X] in
/-- ORIGINAL identity holomorphy uses the SAME actual atlas transitions. -/
private theorem original_identity_holomorphic (A : VariableComplexAtlas X) :
    A.IsHolomorphicOn A id univ := by
  refine ⟨continuous_id.continuousOn, ?_⟩
  intro i j
  simpa only [atlasCoordinateMap, preimage_id, univ_inter, Function.comp_id,
    Function.id_comp, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] using A.holomorphic i j

/-- An ORIGINAL carrier meeting ANY prescribed actual component has a
true native prime there. The prescribed anchor need not lie in the carrier. -/
theorem AtlasGeometricPrimeCarrier.exists_native_component
    (P : AtlasGeometricPrimeCarrier A) (x : X)
    (hmeet : (P.val ∩ connectedComponent x).Nonempty) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∃ Q : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
      Subtype.val '' Q.val = P.val := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨a, ha⟩ := P.property
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  obtain ⟨Qa, hQa⟩ := ha
  obtain ⟨z, hzP, hzx⟩ := hmeet
  have hza : z ∈ connectedComponent a := by
    rw [← hQa] at hzP
    obtain ⟨p, _hp, rfl⟩ := hzP
    exact p.property
  have hcomp : connectedComponent a = connectedComponent x :=
    (connectedComponent_eq hza).trans (connectedComponent_eq hzx).symm
  have hax : a ∈ connectedComponent x := hcomp ▸ mem_connectedComponent
  have hdim : A.pointDimension x = A.pointDimension a :=
    (A.pointDimension_eq_on_connectedComponent x hax).symm
  let e : A.componentOpen x ≃ₜ A.componentOpen a :=
    { toFun := fun p => ⟨p.val, by change p.val ∈ connectedComponent a; rw [hcomp]; exact p.property⟩
      invFun := fun p => ⟨p.val, by change p.val ∈ connectedComponent x; rw [← hcomp]; exact p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val.subtype_mk
        (fun p => by change p.val ∈ connectedComponent a; rw [hcomp]; exact p.property)
      continuous_invFun := continuous_subtype_val.subtype_mk
        (fun p => by change p.val ∈ connectedComponent x; rw [← hcomp]; exact p.property) }
  have he : ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension x))
      𝓘(ℂ, ComplexModel (A.pointDimension a)) ∞ e := by
    simpa only [preimage_univ, contMDiffOn_univ] using
      (original_identity_holomorphic A).component_restriction_contMDiffOn
        isOpen_univ x a e (fun _ _ => rfl)
  have hei : ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension a))
      𝓘(ℂ, ComplexModel (A.pointDimension x)) ∞ e.symm := by
    simpa only [preimage_univ, contMDiffOn_univ] using
      (original_identity_holomorphic A).component_restriction_contMDiffOn
        isOpen_univ a x e.symm (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := prime_preimage_of_dimension_eq hdim e he hei Qa
  refine ⟨Q, ?_⟩
  rw [← hQa]
  apply Set.Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨e p, ?_, rfl⟩
    simpa only [hQ, mem_preimage] using hp
  · rintro y ⟨p, hp, rfl⟩
    refine ⟨e.symm p, ?_, rfl⟩
    rw [hQ]
    change e (e.symm p) ∈ Qa.val
    simpa only [e.apply_symm_apply] using hp

namespace AtlasEffectiveGeometricQDivisor

/-- ORIGINAL D,x ALONE produce the genuine native rational divisor on SAME
component, retaining EVERY original coefficient through the literal image. -/
def nativeComponent (D : AtlasEffectiveGeometricQDivisor A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    EffectiveGeometricQDivisor (A.pointDimension x) (A.componentOpen x) := by
  classical
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  refine {
    coefficient := fun P => D.coefficient (A.nativePrimeOriginalCarrier x P)
    coefficient_nonneg := fun P => D.coefficient_nonneg (A.nativePrimeOriginalCarrier x P)
    locallyFinite := ?_ }
  have hindex := D.locallyFinite.comp_injective (A.nativePrimeOriginalCarrier_injective x)
  have hpre := hindex.preimage_continuous
    (continuous_subtype_val : Continuous (Subtype.val : A.componentOpen x → X))
  convert hpre using 1
  funext P
  change (if D.coefficient (A.nativePrimeOriginalCarrier x P) = 0 then ∅ else P.val) =
    Subtype.val ⁻¹' (if D.coefficient (A.nativePrimeOriginalCarrier x P) = 0 then ∅
      else (A.nativePrimeOriginalCarrier x P).val)
  by_cases hzero : D.coefficient (A.nativePrimeOriginalCarrier x P) = 0
  · simp only [if_pos hzero, Set.preimage_empty]
  · simp only [if_neg hzero]
    exact (Set.preimage_image_eq P.val Subtype.val_injective).symm

/-- Literal original coefficient, without any reindexing choices. -/
theorem nativeComponent_coefficient (D : AtlasEffectiveGeometricQDivisor A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ P : GeometricPrimeCarrier (A.pointDimension x) (A.componentOpen x),
      (D.nativeComponent x).coefficient P =
        D.coefficient (A.nativePrimeOriginalCarrier x P) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro P
  rfl

/-- ENTIRE support agrees with ORIGINAL component preimage, including empty
families and zero-dimensional components. -/
theorem nativeComponent_support (D : AtlasEffectiveGeometricQDivisor A) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    (D.nativeComponent x).support = Subtype.val ⁻¹' D.support := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  ext p
  constructor
  · intro hp
    obtain ⟨Q, hpos, hpQ⟩ := ((D.nativeComponent x).mem_support p).mp hp
    apply (D.mem_support p.val).mpr
    exact ⟨A.nativePrimeOriginalCarrier x Q, hpos, ⟨p, hpQ, rfl⟩⟩
  · intro hp
    obtain ⟨P, hpos, hpP⟩ := (D.mem_support p.val).mp hp
    obtain ⟨Q, hQ⟩ := P.exists_native_component x ⟨p.val, hpP, p.property⟩
    have hindex : A.nativePrimeOriginalCarrier x Q = P :=
      AtlasGeometricPrimeCarrier.ext hQ
    apply ((D.nativeComponent x).mem_support p).mpr
    refine ⟨Q, ?_, ?_⟩
    · rw [D.nativeComponent_coefficient, hindex]
      exact hpos
    · rw [← hQ] at hpP
      obtain ⟨q, hq, hqp⟩ := hpP
      have hqp' : q = p := Subtype.ext hqp
      simpa only [hqp'] using hq

end AtlasEffectiveGeometricQDivisor
end SGPT.PSH.VariableComplexAtlas
