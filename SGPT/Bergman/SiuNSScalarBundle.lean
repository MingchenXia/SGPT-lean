import SGPT.Bergman.SiuNSCartierCocycle
import SGPT.Bergman.SiuNSMetricPotential
import SGPT.LineBundle.TMetricBare

/-! Actual native one-dimensional bundles constructed from holomorphic
scalar cocycles, with prescribed compatible smooth metric weights. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.BDivisor.NSKodaira
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.LineBundle.TMetric
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Standard local gluing data for an actual rank-one holomorphic bundle. -/
structure ScalarLineCocycle (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] where
  dom : X → Set X
  open_dom : ∀ i, IsOpen (dom i)
  mem_dom : ∀ i, i ∈ dom i
  transition : X → X → X → ℂ
  hol : ∀ i j, ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
    (transition i j) (dom i ∩ dom j)
  nonzero : ∀ i j p, p ∈ dom i ∩ dom j → transition i j p ≠ 0
  refl : ∀ i p, p ∈ dom i → transition i i p = 1
  mul : ∀ i j k p, p ∈ dom i → p ∈ dom j → p ∈ dom k →
    transition i j p * transition j k p = transition i k p

namespace ScalarLineCocycle
variable (C : ScalarLineCocycle n X)

/-- The actual native vector bundle core uses the original scalar changes. -/
def core : VectorBundleCore ℂ X ℂ X where
  baseSet := C.dom
  isOpen_baseSet := C.open_dom
  indexAt := id
  mem_baseSet_at := C.mem_dom
  coordChange i j p := (ContinuousLinearMap.id ℂ ℂ).smulRight (C.transition i j p)
  coordChange_self i p hp z := by simp [C.refl i p hp]
  continuousOn_coordChange i j :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).continuous.comp_continuousOn
      (C.hol i j).continuousOn
  coordChange_comp i j k p hp z := by
    change (z * C.transition i j p) * C.transition j k p = z * C.transition i k p
    rw [mul_assoc, C.mul i j k p hp.1.1 hp.1.2 hp.2]

instance core_holomorphic : C.core.IsContMDiff 𝓘(ℂ, ComplexModel n) ∞ where
  contMDiffOn_coordChange i j :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (ContinuousLinearMap.id ℂ ℂ)).contMDiff.comp_contMDiffOn
      (C.hol i j)

variable [CompactSpace X]

/-- The existing partition constructor supplies an actual smooth physical
Hermitian metric on the actual native cocycle bundle. -/
def partition : FramePartition n C.core.Fiber :=
  (exists_framePartition (n := n) C.core.Fiber).some

def nativeBundle : HermitianHolomorphicLineBundle n X := C.partition.toHHLB

theorem nativeBundle_smooth : IsSourceSmoothHermitianMetric C.nativeBundle :=
  C.partition.isSourceSmoothHermitianMetric_toHHLB

/-- An original cocycle trivialization is an actual native atlas frame. -/
def nativeFrame (i : X) : AtlasFrame C.nativeBundle :=
  ⟨C.core.localTriv i, ⟨i, rfl⟩⟩

@[simp] theorem nativeFrame_dom (i : X) : (C.nativeFrame i).val.baseSet = C.dom i := rfl

/-- Native frame coefficients recover the exact original scalar cocycle. -/
theorem nativeFrame_transition (i j : X) {p : X} (hp : p ∈ C.dom i ∩ C.dom j) :
    frameTransition (C.nativeFrame i) (C.nativeFrame j) p = C.transition i j p := by
  change (C.core.localTriv i).coordChangeL ℂ (C.core.localTriv j) p 1 = _
  rw [C.core.localTriv_coordChange_eq i j hp]
  change 1 * C.transition i j p = _
  exact one_mul _

end ScalarLineCocycle

/-- The original Cartier atlas produces the actual scalar cocycle. -/
def CartierAtlas.toScalarCocycle {D : EffectiveDivisor n X} (A : CartierAtlas D) :
    ScalarLineCocycle n X where
  dom := A.dom
  open_dom := A.open_dom
  mem_dom := A.mem_dom
  transition := A.transition
  hol := A.transition_contMDiffOn
  nonzero := fun i j _ hp => A.transition_ne_zero i j hp
  refl := fun i _ hp => A.transition_self i hp
  mul := fun i j k _ hi hj hk => A.transition_mul i j k hi hj hk

end SGPT.BDivisor.NSKodaira
