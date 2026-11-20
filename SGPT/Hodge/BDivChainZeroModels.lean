import SGPT.Hodge.BDivChainZero
import SGPT.BDivisor.VolumeBDivisor

/-!
# Actual model class volumes in dimension zero

This is an application of the source-volume calculation to the literal
`Modification.classVolume` of each actual analytic modification. It does not
construct a zero-dimensional b-divisor or its volume.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.BDivisor

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

/-- Every actual class on every actual modification of a connected compact
zero-dimensional complex manifold has the book's class volume one. -/
theorem modelClassVolume_eq_one_of_dim_zero (π : Modification 0 X)
    (α : RealBottChern 0 π.carrier) : π.classVolume α = 1 := by
  let : MeasurableSpace π.carrier := borel π.carrier
  let : BorelSpace π.carrier := ⟨rfl⟩
  exact sourceClassVolume_eq_one_of_dim_zero α

end SGPT.Hodge.BDivChain
