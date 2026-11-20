import SGPT.Foundations.Schemes.NativePositiveProjectiveCoordinateSections
import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateAction

/-!
# Original positive coordinates in every coordinate frame

The coefficient of the original coordinate section indexed by j in the positive
frame indexed by i is the literal pullback of the projective ratio X_j / X_i.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual j-coordinate morphism has literal ratio X_j/X_i in the
actual i-coordinate frame of the original projective twisting line. -/
theorem polynomialCoordinateGlobalHom_cross_coefficients (i j : Fin (n + 1)) :
    ((polynomialProjTwistingLine K n).atlas.frame i).coefficients (𝟙 _)
      ((homogeneousPolynomialCoordinateGlobalHom (K := K) j).val.app
        (.op (polynomialProjCoordinateOpen K n i)) (1 : Γ(polynomialProj K n, _))) =
      homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j) := by
  change projectiveTwistingChartSectionsFrame
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (polynomialProjCoordinateOpen K n i) le_rfl
      (projectiveTwistingCoordinateMul
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
        ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
        (polynomialProjCoordinateOpen K n i) 1) = _
  rw [projectiveTwistingCoordinateMul, LinearMap.toSpanSingleton_apply, one_smul,
    ← polynomialProjTwistingCoordinateMul_ratio K n j i]
  exact (projectiveTwistingChartSectionsFrame
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) 1
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    (polynomialProjCoordinateOpen K n i) le_rfl).apply_symm_apply _

variable {X : Scheme} (f : X ⟶ polynomialProj K n)

/-- Pulling back the literal coordinate morphism retains its literal ratio
coefficient through the actual structural scheme morphism. -/
theorem nativePolynomialPullbackCoordinate_cross_coefficients (i j : Fin (n + 1)) :
    ((nativePolynomialPullbackAtlas K n f).frame i).coefficients (𝟙 _)
      ((nativePullbackGlobalHom f (homogeneousPolynomialCoordinateGlobalHom (K := K) j)).val.app
        (.op (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)) (1 : Γ(X, _))) =
    f.app (polynomialProjCoordinateOpen K n i)
      (homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j)) := by
  let U := polynomialProjCoordinateOpen K n i
  let α := homogeneousPolynomialCoordinateGlobalHom (K := K) i
  let β := homogeneousPolynomialCoordinateGlobalHom (K := K) j
  have := (nativeModuleHom_over_isIso_iff_restrict α U).mp inferInstance
  have := nativePullbackGlobalHom_restrict_isIso f α U
  have := (nativeModuleHom_over_isIso_iff_restrict (nativePullbackGlobalHom f α)
    (f ⁻¹ᵁ U)).mpr inferInstance
  let s := β.val.app (.op U) (1 : Γ(polynomialProj K n, U))
  have hu := congrArg (fun γ ↦ γ.val.app (.op U) (1 : Γ(polynomialProj K n, U)))
    (nativePullbackGlobalHom_unit_square f β)
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (polynomialProjTwistingLine K n).sheaf).val.app (.op U) s =
    (nativePullbackGlobalHom f β).val.app (.op (f ⁻¹ᵁ U))
      (f.app U (1 : Γ(polynomialProj K n, U))) at hu
  rw [map_one] at hu
  have hc := nativeGeneratorPullback_coefficient_square f α U U (𝟙 _) s
  change ((nativePolynomialPullbackAtlas K n f).frame i).coefficients (𝟙 _)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (polynomialProjTwistingLine K n).sheaf).val.app (.op U) s) =
    f.app U ((nativeGlobalGeneratorFrame α U).coefficients (𝟙 _) s) at hc
  rw [nativePolynomialCoordinateHom_generatorFrame] at hc
  rw [hu] at hc
  exact hc.trans (congrArg (fun z ↦ f.app U z)
    (polynomialCoordinateGlobalHom_cross_coefficients K n i j))

variable (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- In every positive chart, the original degree-q j-coordinate
section has the actual structural pullback of the ratio X_j/X_i. -/
theorem nativePositiveProjectiveCoordinateSection_cross_coefficients (i j : Fin (n + 1)) :
    (nativePositiveProjectiveCoordinateFrame K n f L q e i).coefficients (𝟙 _)
      ((bundleTensorPower L.sheaf q).val.map
        (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i).leTop.op
        (nativePositiveProjectiveCoordinateSection K n f L q e j)) =
    f.app (polynomialProjCoordinateOpen K n i)
      (homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j)) := by
  let U := f ⁻¹ᵁ polynomialProjCoordinateOpen K n i
  let α := nativeProjectiveCoordinateGenerator f (L.tensorPower q) e j
  let β := nativePullbackGlobalHom f (homogeneousPolynomialCoordinateGlobalHom (K := K) j)
  let d := (nativePolynomialPullbackAtlas K n f).frame i
  have hi := congrArg (fun γ ↦ γ.val.app (.op U) (β.val.app (.op U) (1 : Γ(X, U))))
    e.inv_hom_id
  change e.hom.val.app (.op U) (α.val.app (.op U) (1 : Γ(X, U))) =
    β.val.app (.op U) (1 : Γ(X, U)) at hi
  change d.coefficients (𝟙 _) (e.hom.val.app (.op U)
    ((bundleTensorPower L.sheaf q).val.map U.leTop.op
      (α.val.app (.op ⊤) (1 : Γ(X, ⊤))))) = _
  exact (congrArg (fun t ↦ d.coefficients (𝟙 _) (e.hom.val.app (.op U) t))
    (nativeGlobalHom_one_restrict α U)).trans
      ((congrArg (d.coefficients (𝟙 _)) hi).trans
        (nativePolynomialPullbackCoordinate_cross_coefficients K n f i j))

/-- Every subordinate original positive-coordinate open retains the same
literal pulled-back cross-coordinate ratio. -/
theorem nativePositiveProjectiveCoordinateSection_cross_coefficients_subordinate
    (i j : Fin (n + 1)) {W : X.Opens}
    (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) :
    (nativePositiveProjectiveCoordinateFrame K n f L q e i).coefficients h
      ((bundleTensorPower L.sheaf q).val.map W.leTop.op
        (nativePositiveProjectiveCoordinateSection K n f L q e j)) =
    X.sheaf.obj.map h.op
      (f.app (polynomialProjCoordinateOpen K n i)
        (homogeneousPolynomialBasicOpenAwayEquiv i (polynomialProjCoordinateRatio K n i j))) := by
  let U := f ⁻¹ᵁ polynomialProjCoordinateOpen K n i
  let s := nativePositiveProjectiveCoordinateSection K n f L q e j
  have hc := (nativePositiveProjectiveCoordinateFrame K n f L q e i).coefficients_restrict
    (𝟙 _) h ((bundleTensorPower L.sheaf q).val.map U.leTop.op s)
  have hr : (bundleTensorPower L.sheaf q).val.map h.op
      ((bundleTensorPower L.sheaf q).val.map U.leTop.op s) =
      (bundleTensorPower L.sheaf q).val.map W.leTop.op s := by
    rw [← PresheafOfModules.map_comp_apply]
    rfl
  rw [Category.comp_id, hr] at hc
  exact hc.trans (congrArg (X.sheaf.obj.map h.op)
    (nativePositiveProjectiveCoordinateSection_cross_coefficients K n f L q e i j))

end
end SGPT.Foundations.Schemes
