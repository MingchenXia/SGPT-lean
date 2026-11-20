import SGPT.PSH.AtlasComponentCohomologyEquivalence
import SGPT.PSH.AtlasSmoothPotentialGluing
import SGPT.PSH.AtlasBiholomorphicDerivative
import SGPT.PSH.AtlasNefClass

/-! Actual native approximating smooth potentials GLUE to the literal
GLOBAL source nef criterion on the SAME original theta and background. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
universe u

private theorem native_closedForm_eq_of_coeff_eq {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {F G : ClosedRealOneOneForm n M} (h : F.val.coeff=G.val.coeff) : F=G := by
  rcases F with ⟨⟨f,hf,hc⟩,hF⟩
  rcases G with ⟨⟨g,hg,hcg⟩,hG⟩
  change f=g at h
  cases h
  rfl

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
variable (A : VariableComplexAtlas X)
local instance originalNefFamilyCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (actualComponentDimension A c)) (actualComponentPoint A c) :=
  actualComponentChartedSpace A c
local instance originalNefFamilyComplex (c : ConnectedComponents X) :
    IsComplexManifold (actualComponentDimension A c) (actualComponentPoint A c) :=
  actualComponentComplexManifold A c
local instance originalNefAnchorCharted (c : ConnectedComponents X) :
    ChartedSpace (ComplexModel (A.pointDimension (componentAnchor c)))
      (A.componentOpen (componentAnchor c)) := A.componentChartedSpace (componentAnchor c)
local instance originalNefAnchorComplex (c : ConnectedComponents X) :
    IsComplexManifold (A.pointDimension (componentAnchor c))
      (A.componentOpen (componentAnchor c)) := A.componentComplexManifold_of_paracompact (componentAnchor c)

/-- ENTIRE original native closed-form readback, not just the same class:
all genuine coefficient functions are exactly the original component pullback. -/
theorem originalNativeComponentForm_sigma_readback
    (theta : AtlasClosedRealOneOneForm A) (c : ConnectedComponents X) :
    sigmaRestrictedForm (theta.holomorphicPullback (actualComponentHomeomorph_isHolomorphic A)) c=
      originalNativeComponentForm theta (componentAnchor c) := by
  apply native_closedForm_eq_of_coeff_eq
  funext e z
  rfl

/-- A genuine ORIGINAL global Kahler form produces an ACTUAL native
Kahler background on each internally produced independently dimensional component. -/
def originalComponentBackground (omega : AtlasClosedRealOneOneForm A)
    (homega : OriginalFormIsKahler omega) (c : ConnectedComponents X) :
    KahlerBackground (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c)) := by
  have hsig := homega.biholomorphicPullback (actualComponentHomeomorph A)
    (actualComponentHomeomorph_isHolomorphic A) (actualComponentHomeomorph_inverse_isHolomorphic A)
  have hnative := sigmaRestrictedForm_isKahler hsig c
  exact ⟨originalNativeComponentForm omega (componentAnchor c),
    (originalNativeComponentForm_sigma_readback A omega c) ▸ hnative⟩

omit [T2Space X] [ParacompactSpace X] in
/-- Exact targetwise coefficient equality preserves the literal global nef
criterion with SAME actual scalar epsilon potentials, without output flags. -/
theorem originalNef_congr_coefficients
    {omega theta omega' theta' : AtlasClosedRealOneOneForm A}
    (hnef : OriginalNefWithRespectTo omega theta)
    (homega : ∀ i z,z∈(A.chart i).target → omega.coeff i z=omega'.coeff i z)
    (htheta : ∀ i z,z∈(A.chart i).target → theta.coeff i z=theta'.coeff i z) :
    OriginalNefWithRespectTo omega' theta' := by
  intro epsilon hepsilon
  obtain ⟨h,hh,hpos⟩ := hnef epsilon hepsilon
  refine ⟨h,hh,?_⟩
  intro i z hz
  rw [←htheta i z hz,←homega i z hz]
  exact hpos i z hz

/-- GENUINE original global nefness from actual native approximations:
for EACH epsilon the smooth native potentials GLUE into ONE actual globally
smooth original potential. The full tensor round trips identify EXACTLY
SAME original theta and omega, with no common dimension/connectedness premise. -/
theorem original_nef_of_native_components
    (omega theta : AtlasClosedRealOneOneForm A) (homega : OriginalFormIsKahler omega)
    (hnef : ∀ c : ConnectedComponents X,
      NefWithRespectTo (originalComponentBackground A omega homega c)
        (originalNativeComponentForm theta (componentAnchor c))) :
    OriginalNefWithRespectTo omega theta := by
  let os := omega.holomorphicPullback (actualComponentHomeomorph_isHolomorphic A)
  let ts := theta.holomorphicPullback (actualComponentHomeomorph_isHolomorphic A)
  have hsigK : OriginalFormIsKahler os := homega.biholomorphicPullback (actualComponentHomeomorph A)
    (actualComponentHomeomorph_isHolomorphic A) (actualComponentHomeomorph_inverse_isHolomorphic A)
  have hsigN : OriginalNefWithRespectTo os ts := by
    apply sigma_original_nef_of_native os ts (fun c => sigmaRestrictedForm_isKahler hsigK c)
    intro c
    have ho := originalNativeComponentForm_sigma_readback A omega c
    have ht := originalNativeComponentForm_sigma_readback A theta c
    intro epsilon hepsilon
    obtain ⟨h,hh,hpos⟩ := hnef c epsilon hepsilon
    refine ⟨h,hh,?_⟩
    intro e z hz
    have hoc := congrArg (fun F : ClosedRealOneOneForm
      (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c)) => F.val.coeff e z) ho
    have htc := congrArg (fun F : ClosedRealOneOneForm
      (A.pointDimension (componentAnchor c)) (A.componentOpen (componentAnchor c)) => F.val.coeff e z) ht
    change CoefficientSemipositive ((sigmaRestrictedForm ts c).val.coeff e z+
      smoothDDC (fun y => h (e.val.symm y)) z+epsilon • (sigmaRestrictedForm os c).val.coeff e z)
    rw [show (sigmaRestrictedForm ts c).val.coeff e z=
        (originalNativeComponentForm theta (componentAnchor c)).val.coeff e z from htc,
      show (sigmaRestrictedForm os c).val.coeff e z=
        (originalNativeComponentForm omega (componentAnchor c)).val.coeff e z from hoc]
    exact hpos e z hz
  have hback := hsigN.holomorphicPullback (actualComponentHomeomorph_inverse_isHolomorphic A)
  apply originalNef_congr_coefficients A hback
  · intro i z hz
    exact original_biholomorphic_pullback_roundtrip_coeff omega (actualComponentHomeomorph A).symm
      (actualComponentHomeomorph_inverse_isHolomorphic A) (actualComponentHomeomorph_isHolomorphic A) i hz
  · intro i z hz
    exact original_biholomorphic_pullback_roundtrip_coeff theta (actualComponentHomeomorph A).symm
      (actualComponentHomeomorph_inverse_isHolomorphic A) (actualComponentHomeomorph_isHolomorphic A) i hz

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
