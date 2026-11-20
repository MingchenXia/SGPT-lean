import SGPT.Bergman.SiuNSScalarBundle
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Determinant
import SGPT.Foundations.Analysis.FirstPass.MongeAmpere

/-! The original inverse-Jacobian canonical cocycle and its native fibres.

All transitions come from the actual tangent bundle core of the original
manifold. No canonical bundle, invertible Jacobian, or cocycle certificate
is supplied as an input. Hypersurface adjunction and Hodge normalization
remain separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.BDivisor.NSKodaira SGPT.LineBundle.TMetric

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- The actual complex determinant is holomorphic in every original
holomorphic family of finite-dimensional endomorphisms. -/
theorem contMDiffOn_nativeDeterminant {D : Set X}
    {A : X → ComplexModel n →L[ℂ] ComplexModel n}
    (hA : ContMDiffOn 𝓘(ℂ, ComplexModel n)
      𝓘(ℂ, ComplexModel n →L[ℂ] ComplexModel n) ∞ A D) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => LinearMap.det (A x).toLinearMap) D := by
  classical
  have hentry (i j : Fin n) : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => (A x (MongeAmpere.coordinateVector j)) i) D :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff.comp_contMDiffOn
      (hA.clm_apply contMDiffOn_const)
  have heq : (fun x => LinearMap.det (A x).toLinearMap) = fun x =>
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ a : Fin n, (A x (MongeAmpere.coordinateVector a)) (σ a) := by
    funext x
    rw [← MongeAmpere.det_standardMatrix, Matrix.det_apply]
    simp only [MongeAmpere.standardMatrix_apply]
    rfl
  rw [heq]
  apply contMDiffOn_finsetSum
  intro σ _
  have hp : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => ∏ a : Fin n, (A x (MongeAmpere.coordinateVector a)) (σ a)) D := by
    apply contMDiffOn_finsetProd
    intro a _
    exact hentry (σ a) a
  have hprod : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞
      (fun x => (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
        ∏ a : Fin n, (A x (MongeAmpere.coordinateVector a)) (σ a)) D := by
    convert (contMDiffOn_const (c := (((Equiv.Perm.sign σ : ℤ) : ℂ)))).mul hp using 1
    rfl
  simpa only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul] using hprod

/-- The original canonical scalar cocycle is the inverse-orientation
determinant of the actual original tangent-coordinate changes. -/
def nativeCanonicalJacobianCocycle : ScalarLineCocycle n X where
  dom i := (chartAt (ComplexModel n) i).source
  open_dom i := (chartAt (ComplexModel n) i).open_source
  mem_dom i := mem_chart_source (ComplexModel n) i
  transition i j x := LinearMap.det
    ((tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
      (achart (ComplexModel n) j) (achart (ComplexModel n) i) x).toLinearMap
  hol i j := by
    have : IsManifold 𝓘(ℂ, ComplexModel n) (∞ + 1) X := by
      simpa using (inferInstance : IsManifold 𝓘(ℂ, ComplexModel n) ∞ X)
    have hcore : (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).IsContMDiff
        𝓘(ℂ, ComplexModel n) ∞ := tangentBundleCore.isContMDiff
    exact (contMDiffOn_nativeDeterminant
      (hcore.contMDiffOn_coordChange (achart (ComplexModel n) j)
        (achart (ComplexModel n) i))).mono (fun _ h => ⟨h.2, h.1⟩)
  nonzero i j x hx := by
    let T := tangentBundleCore 𝓘(ℂ, ComplexModel n) X
    have hc := T.coordChange_linear_comp (achart (ComplexModel n) j)
      (achart (ComplexModel n) i) (achart (ComplexModel n) j) x ⟨⟨hx.2, hx.1⟩, hx.2⟩
    have hi : T.coordChange (achart (ComplexModel n) j) (achart (ComplexModel n) j) x =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
      apply ContinuousLinearMap.ext
      intro v
      exact T.coordChange_self (achart (ComplexModel n) j) x hx.2 v
    rw [hi] at hc
    have hd := congrArg (fun A : ComplexModel n →L[ℂ] ComplexModel n =>
      LinearMap.det A.toLinearMap) hc
    change LinearMap.det ((T.coordChange (achart (ComplexModel n) i)
      (achart (ComplexModel n) j) x).toLinearMap.comp
      (T.coordChange (achart (ComplexModel n) j) (achart (ComplexModel n) i) x).toLinearMap) = _ at hd
    rw [LinearMap.det_comp] at hd
    have hid : (ContinuousLinearMap.id ℂ (ComplexModel n)).toLinearMap = LinearMap.id := rfl
    rw [hid, LinearMap.det_id] at hd
    exact (mul_ne_zero_iff.mp (hd ▸ one_ne_zero)).2
  refl i x hx := by
    have hi : (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) i) (achart (ComplexModel n) i) x =
        ContinuousLinearMap.id ℂ (ComplexModel n) := by
      apply ContinuousLinearMap.ext
      intro v
      exact (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange_self
        (achart (ComplexModel n) i) x hx v
    rw [hi]
    exact LinearMap.det_id
  mul i j k x hi hj hk := by
    let T := tangentBundleCore 𝓘(ℂ, ComplexModel n) X
    have hc := T.coordChange_linear_comp (achart (ComplexModel n) k)
      (achart (ComplexModel n) j) (achart (ComplexModel n) i) x ⟨⟨hk, hj⟩, hi⟩
    have hd := congrArg (fun A : ComplexModel n →L[ℂ] ComplexModel n =>
      LinearMap.det A.toLinearMap) hc
    change LinearMap.det ((T.coordChange (achart (ComplexModel n) j)
      (achart (ComplexModel n) i) x).toLinearMap.comp
      (T.coordChange (achart (ComplexModel n) k) (achart (ComplexModel n) j) x).toLinearMap) = _ at hd
    rw [LinearMap.det_comp] at hd
    exact hd

/-- Top-degree actual alternating covectors are identified with scalars by
evaluation on the genuine standard complex basis, with determinant inverse. -/
def complexTopFormScalarEquiv (n : ℕ) :
    ((ComplexModel n) [⋀^Fin n]→ₗ[ℂ] ℂ) ≃ₗ[ℂ] ℂ where
  toFun α := α (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  invFun a := a • (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det
  left_inv α := (α.eq_smul_basis_det (EuclideanSpace.basisFun (Fin n) ℂ).toBasis).symm
  right_inv a := by
    change a * (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis = a
    rw [Module.Basis.det_self, mul_one]
  map_add' α β := rfl
  map_smul' a α := rfl

variable [CompactSpace X]

/-- The actual original canonical cocycle produces a genuine native
Hermitian holomorphic line bundle, with an internally produced smooth metric. -/
def nativeCanonicalBundle : HermitianHolomorphicLineBundle n X :=
  (nativeCanonicalJacobianCocycle (n := n) (X := X)).nativeBundle

theorem nativeCanonicalBundle_smooth :
    SGPT.Bergman.PolynomialH0Growth.IsSourceSmoothHermitianMetric
      (nativeCanonicalBundle (n := n) (X := X)) :=
  (nativeCanonicalJacobianCocycle (n := n) (X := X)).nativeBundle_smooth

def nativeCanonicalFrame (i : X) : AtlasFrame (nativeCanonicalBundle (n := n) (X := X)) :=
  (nativeCanonicalJacobianCocycle (n := n) (X := X)).nativeFrame i

theorem nativeCanonicalFrame_transition (i j : X) {x : X}
    (hx : x ∈ (chartAt (ComplexModel n) i).source ∩ (chartAt (ComplexModel n) j).source) :
    frameTransition (nativeCanonicalFrame (n := n) i) (nativeCanonicalFrame (n := n) j) x =
      LinearMap.det ((tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) j) (achart (ComplexModel n) i) x).toLinearMap :=
  (nativeCanonicalJacobianCocycle (n := n) (X := X)).nativeFrame_transition i j hx

/-- The native fibre is the actual top alternating complex cotangent line
at the ORIGINAL point; no arbitrary target canonical line is an input. -/
def nativeCanonicalFiberEquiv (x : X) :
    (nativeCanonicalBundle (n := n) (X := X)).Fiber x ≃ₗ[ℂ]
      ((TangentSpace 𝓘(ℂ, ComplexModel n) x) [⋀^Fin n]→ₗ[ℂ] ℂ) :=
  ((nativeCanonicalFrame (n := n) x).val.linearEquivAt ℂ x
    (mem_chart_source (ComplexModel n) x)).trans (complexTopFormScalarEquiv n).symm

/-- Original chart coordinates of the actual native covector are exactly
its actual original native frame coefficient times coordinate volume. -/
theorem nativeCanonicalFiberEquiv_coordinates (i x : X)
    (_hx : x ∈ (chartAt (ComplexModel n) i).source)
    (u : (nativeCanonicalBundle (n := n) (X := X)).Fiber x)
    (v : Fin n → ComplexModel n) :
    nativeCanonicalFiberEquiv (n := n) x u (fun a =>
      (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) i) (achart (ComplexModel n) x) x (v a)) =
      ((nativeCanonicalFrame (n := n) i).val ⟨x, u⟩).2 *
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det v := by
  let C := nativeCanonicalJacobianCocycle (n := n) (X := X)
  have hcoeff : ((nativeCanonicalFrame (n := n) i).val ⟨x, u⟩).2 =
      ((nativeCanonicalFrame (n := n) x).val ⟨x, u⟩).2 * C.transition x i x := by
    change (show ℂ from u) * C.transition x i x =
      ((show ℂ from u) * C.transition x x x) * C.transition x i x
    rw [C.refl x x (mem_chart_source (ComplexModel n) x), mul_one]
  change (((nativeCanonicalFrame (n := n) x).val.linearEquivAt ℂ x
    (mem_chart_source (ComplexModel n) x) u) •
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det) _ = _
  have hdet := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det_comp
    ((tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
      (achart (ComplexModel n) i) (achart (ComplexModel n) x) x).toLinearMap v
  change ((nativeCanonicalFrame (n := n) x).val ⟨x, u⟩).2 *
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det
      (((tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) i) (achart (ComplexModel n) x) x).toLinearMap ∘ v) = _
  rw [hdet, hcoeff]
  change ((nativeCanonicalFrame (n := n) x).val ⟨x, u⟩).2 *
    (C.transition x i x * _) = (((nativeCanonicalFrame (n := n) x).val ⟨x, u⟩).2 *
      C.transition x i x) * _
  exact (mul_assoc _ _ _).symm

end SGPT.Trace.Bertini
