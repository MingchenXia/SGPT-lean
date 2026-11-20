import SGPT.Foundations.Schemes.NativePolynomialPullbackPower
import SGPT.Foundations.Schemes.NativeLineTensorPowerComparison
import SGPT.Foundations.Schemes.NativeProjectiveTwistedGlobalSectionComparison
/-!
# NativePolarizedResidueComparison

Actual original-atlas tensor-power addition/multiplication, actual positivity and genuine polynomial pullback-power comparisons identify L^(qm+r) with f*O(m) tensor L^r. True canonical projective projection gives actual pushforward residue/tensor-twist isomorphisms.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {X : Scheme} (L : IntrinsicLineBundle X)
    {K : Type} [Field K] (n : ℕ) (f : X ⟶ polynomialProj K n) (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The actual positive power isomorphism gives the genuine polarized sheaf comparison in every Veronese degree. -/
def nativePolarizedLinePowerIso (m : ℕ) :
    bundleTensorPower L.sheaf (q * m) ≅
      (Scheme.Modules.pullback f).obj
        (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m) :=
  nativeLineTensorPowerMulIso L.atlas q m ≪≫ nativeLineTensorPowerIso e m ≪≫
    (nativePolynomialPullbackPowerIso K n f m).symm ≪≫
      (Scheme.Modules.pullback f).mapIso (nativePolynomialTwistingPowerIso K n m)

/-- Actual original tensor-power addition and actual positivity give the real polarized residue sheaf comparison. -/
def nativePolarizedLineResidueIso (m r : ℕ) :
    bundleTensorPower L.sheaf (q * m + r) ≅
      bundleTensor ((Scheme.Modules.pullback f).obj
        (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m))
        (bundleTensorPower L.sheaf r) :=
  nativeLineTensorPowerAddIso L.atlas (q * m) r ≪≫
    bundleTensorIso (nativePolarizedLinePowerIso L n f q e m) (Iso.refl _)

/-- The canonical actual projective projection formula identifies the true pushforward residue sheaf with the original O(m) twist of the true residue pushforward. -/
def nativePolarizedResiduePushforwardIso (m r : ℕ) :
    (Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf (q * m + r)) ≅
      bundleTensor
        (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m)
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) := by
  have := nativePolynomialTwistingProjectionMap_isIso f m (bundleTensorPower L.sheaf r)
  exact (Scheme.Modules.pushforward f).mapIso (nativePolarizedLineResidueIso L n f q e m r) ≪≫
    (asIso (nativeSchemeProjectionMap f
      (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m)
      (bundleTensorPower L.sheaf r))).symm

/-- The real residue pushforward is exactly the genuine tensor twist used by the fixed finite graded-span/global-section comparison. -/
def nativePolarizedResiduePushforwardTensorTwistIso (m r : ℕ) :
    (Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf (q * m + r)) ≅
      polynomialProjModuleTensorTwist K n
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m :=
  nativePolarizedResiduePushforwardIso L n f q e m r ≪≫
    bundleTensorIso (nativePolynomialTwistingPowerIso K n m).symm (Iso.refl _)

end
end SGPT.Foundations.Schemes
