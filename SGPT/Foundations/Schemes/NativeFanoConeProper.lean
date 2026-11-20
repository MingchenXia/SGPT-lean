import SGPT.Foundations.Schemes.NativeProjectiveConeProper
import SGPT.Foundations.Schemes.NativeProjectiveFano
/-!
# NativeFanoConeProper

The actual positive anticanonical tensor power of a smooth projective Fano input is a genuine pullback of polynomial-Proj O(1). Its proved generating-section contraction and the literal fiber-power cone square give properness of the original full anticanonical cone contraction. Off-zero isomorphism, normality, crepancy and the original analytic Fano/main theorem interfaces remain separate obligations.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} [IsIntegral X] {K I : Type u} [Field K]

/-- Actual positive projective positivity and actual properness produce proper contraction to the full section-ring cone. -/
theorem nativePositiveProjectiveLineConeMap_isProper (L : IntrinsicLineBundle X)
    (q : ℕ) (hq : 0 < q) (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule I K))
    (e : (L.tensorPower q).sheaf ≅ (Scheme.Modules.pullback f).obj
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) 1))
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) [IsProper p] : IsProper L.nativeConeMap := by
  have := nativeProjectiveLineConeMap_isProper f (L.tensorPower q) e p
  exact L.nativeConeMap_isProper_of_power q hq

/-- The genuine anticanonical total-space evaluation of an actual smooth projective Fano input is proper. -/
theorem SmoothProjectiveFano.nativeAnticanonicalConeMap_isProper {n : ℕ}
    (F : SmoothProjectiveFano n) :
    IsProper (smoothAnticanonicalLineBundle F.structureMap n).nativeConeMap := by
  have := F.isProper
  exact nativePositiveProjectiveLineConeMap_isProper
    (smoothAnticanonicalLineBundle F.structureMap n)
    F.anticanonicalPower F.anticanonicalPower_positive F.projective.map
    F.positivityIso F.structureMap

end
end SGPT.Foundations.Schemes
