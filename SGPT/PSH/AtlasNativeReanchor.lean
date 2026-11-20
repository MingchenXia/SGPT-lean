import SGPT.PSH.AtlasPrimeComponentProjection
import SGPT.PSH.BiholomorphicGeometricQPreimage

open Lean in
local macro "pinnedOriginalAtlasIdentityKernel" : term =>
  pure (mkIdent (Name.append
    (Name.num `_private.SGPT.PSH.AtlasPrimeComponentProjection 0)
    `SGPT.PSH.VariableComplexAtlas.original_identity_holomorphic))

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

universe u

/-- Honest PURE substitution of the actual native dimension equality; both
original chart structures/maps and the entire original divisor are retained. -/
def geometricQDivisorBiholomorphicPreimageOfDimensionEq
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a = b) (D : EffectiveGeometricQDivisor b N) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ e.symm) :
    EffectiveGeometricQDivisor a M := by
  subst b
  exact geometricQDivisorBiholomorphicPreimage D e he hei


private theorem native_divisor_eq_preimage_of_coefficient
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a = b) (D : EffectiveGeometricQDivisor a M) (E : EffectiveGeometricQDivisor b N)
    (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, ComplexModel a) 𝓘(ℂ, ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel a) ∞ e.symm)
    (hcoeff : ∀ (P : GeometricPrimeCarrier b N) (Q : GeometricPrimeCarrier a M),
      Q.val = e ⁻¹' P.val → D.coefficient Q = E.coefficient P) :
    D = geometricQDivisorBiholomorphicPreimageOfDimensionEq h E e he hei := by
  subst b
  have hext (F G : EffectiveGeometricQDivisor a M) (h : F.coefficient = G.coefficient) : F = G := by
    cases F
    cases G
    cases h
    rfl
  apply hext
  funext Q
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  change D.coefficient Q = E.coefficient (K.symm Q)
  apply hcoeff (K.symm Q) Q
  exact (congrArg (fun P : GeometricPrimeCarrier a M => P.val) (K.apply_symm_apply Q)).symm


namespace VariableComplexAtlas
variable {X : Type u} [TopologicalSpace X]

/-- Exact already accepted original identity proof. Literal private kernel
name/type/proof/direct occurrence are pinned; no stronger premise is added.
Origin and maintenance dependency: atlas-native-reanchor-identity-mother-pin.json. -/
theorem originalAtlasIdentity_isHolomorphicOn (A : VariableComplexAtlas X) :
    A.IsHolomorphicOn A id univ := pinnedOriginalAtlasIdentityKernel A

/-- The actual SAME original component, using the existing equal-set
homeomorphism. No chart/model/reanchor or prime certificate is an input. -/
def componentReanchorHomeomorph (A : VariableComplexAtlas X) (x y : X)
    (hy : y ∈ connectedComponent x) : A.componentOpen x ≃ₜ A.componentOpen y :=
  Homeomorph.setCongr (connectedComponent_eq hy :
    (A.componentOpen x : Set X) = (A.componentOpen y : Set X))

theorem componentReanchorHomeomorph_val (A : VariableComplexAtlas X) (x y : X)
    (hy : y ∈ connectedComponent x) (p : A.componentOpen x) :
    (A.componentReanchorHomeomorph x y hy p).val = p.val := rfl

/-- BOTH component models are independently derived from the ORIGINAL atlas. -/
theorem componentReanchorHomeomorph_contMDiff (A : VariableComplexAtlas X) (x y : X)
    (hy : y ∈ connectedComponent x) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    letI := A.componentChartedSpace y
    letI := A.componentIsManifold y
    ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension x))
      𝓘(ℂ, ComplexModel (A.pointDimension y)) ∞ (A.componentReanchorHomeomorph x y hy) := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  let := A.componentChartedSpace y
  let := A.componentIsManifold y
  simpa only [preimage_univ, contMDiffOn_univ] using
    (A.originalAtlasIdentity_isHolomorphicOn).component_restriction_contMDiffOn
      isOpen_univ x y (A.componentReanchorHomeomorph x y hy) (fun _ _ => rfl)

theorem componentReanchorHomeomorph_symm_contMDiff (A : VariableComplexAtlas X) (x y : X)
    (hy : y ∈ connectedComponent x) :
    letI := A.componentChartedSpace x
    letI := A.componentIsManifold x
    letI := A.componentChartedSpace y
    letI := A.componentIsManifold y
    ContMDiff 𝓘(ℂ, ComplexModel (A.pointDimension y))
      𝓘(ℂ, ComplexModel (A.pointDimension x)) ∞ (A.componentReanchorHomeomorph x y hy).symm := by
  let := A.componentChartedSpace x
  let := A.componentIsManifold x
  let := A.componentChartedSpace y
  let := A.componentIsManifold y
  simpa only [preimage_univ, contMDiffOn_univ] using
    (A.originalAtlasIdentity_isHolomorphicOn).component_restriction_contMDiffOn
      isOpen_univ y x (A.componentReanchorHomeomorph x y hy).symm (fun _ _ => rfl)

variable {A : VariableComplexAtlas X} [T2Space X] [ParacompactSpace X]

/-- ORIGINAL D,x,y and actual same-component membership internally supply
EVERY reanchor coefficient comparison, actual dimensions and BOTH native maps.
The ENTIRE actual native divisors are equal, including all zero coefficients. -/
theorem AtlasEffectiveGeometricQDivisor.nativeComponent_reanchor
    (D : AtlasEffectiveGeometricQDivisor A) (x y : X) (hy : y ∈ connectedComponent x) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    letI := A.componentChartedSpace y
    letI := A.componentComplexManifold_of_paracompact y
    D.nativeComponent x = geometricQDivisorBiholomorphicPreimageOfDimensionEq
      (A.pointDimension_eq_on_connectedComponent x hy).symm (D.nativeComponent y)
      (A.componentReanchorHomeomorph x y hy)
      (A.componentReanchorHomeomorph_contMDiff x y hy)
      (A.componentReanchorHomeomorph_symm_contMDiff x y hy) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  let := A.componentChartedSpace y
  let := A.componentComplexManifold_of_paracompact y
  apply native_divisor_eq_preimage_of_coefficient
  intro P Q hQ
  rw [D.nativeComponent_coefficient, D.nativeComponent_coefficient]
  apply congrArg D.coefficient
  apply AtlasGeometricPrimeCarrier.ext
  change Subtype.val '' Q.val = Subtype.val '' P.val
  let e := A.componentReanchorHomeomorph x y hy
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨e p, ?_, rfl⟩
    rw [hQ] at hp
    exact hp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨e.symm p, ?_, rfl⟩
    rw [hQ]
    change e (e.symm p) ∈ P.val
    simpa only [e.apply_symm_apply] using hp

end VariableComplexAtlas
end SGPT.PSH
