import SGPT.Foundations.Analysis.Pending.DistributionComplexTestBridge
import SGPT.Foundations.Analysis.Pending.ClosedDistributionTwoFormLocalPrimitive
import SGPT.Foundations.Analysis.Pending.LocalCurrents

set_option autoImplicit false

/-! Arbitrary signed closed (1,1) distribution forms receive local scalar
potentials. ENTIRE BP proofs precede this source; native normalization is
retained. Global chart covariance and Bott--Chern smoothing remain separate. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Complex
open scoped ContDiff Distributions Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionLocalDdcPotential
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open CauchyGreen LelongPoincareDivisor

variable {n : ℕ}
private abbrev E (n : ℕ) := EuclideanSpace ℂ (Fin n)
variable {Ω U : Opens (E n)}
private abbrev D (v : E n) := Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (Ω := Ω) (F := ℝ) v
private abbrev lift (T : 𝓓'(Ω,ℝ)) : 𝓓'(Ω,ℂ) := Distribution.mapCLM ofRealCLM T
private def beta (L : E n →ₗ[ℝ] 𝓓'(Ω,ℝ)) (v : E n) : 𝓓'(Ω,ℂ) :=
  (2:ℂ)⁻¹ • (lift (L v) + I • lift (L (I • v)))

private theorem beta_closed (L : E n →ₗ[ℝ] 𝓓'(Ω,ℝ))
    (h11 : IsOneOne (exteriorDerivative (oneForm L))) (u v : E n) :
    DistributionComplexTestBridge.dbar u (beta L v) =
      DistributionComplexTestBridge.dbar v (beta L u) := by
  ext φ
  have hr := congrArg (fun T : 𝓓'(Ω,ℝ) => T φ) (h11 u v)
  have hi := congrArg (fun T : 𝓓'(Ω,ℝ) => T φ)
    (LocalCurrents.oneOne_pairing_symmetric (exteriorDerivative (oneForm L)) h11 u v)
  simp only [exteriorDerivative_oneForm, _root_.sub_apply, Distribution.lineDerivCLM_apply] at hr hi
  apply Complex.ext
  · simp [DistributionComplexTestBridge.dbar,beta,Distribution.lineDerivCLM_apply,
      Distribution.mapCLM_apply,Complex.mul_re,Complex.mul_im]
    linarith
  · simp [DistributionComplexTestBridge.dbar,beta,Distribution.lineDerivCLM_apply,
      Distribution.mapCLM_apply,Complex.mul_re,Complex.mul_im]
    linarith

private theorem real_imag_solution (L : E n →ₗ[ℝ] 𝓓'(Ω,ℝ)) (g : 𝓓'(Ω,ℂ)) (v : E n)
    (hg : DistributionComplexTestBridge.dbar v g = beta L v) :
    D v (Distribution.mapCLM reCLM g) - D (I • v) (Distribution.mapCLM imCLM g) = L v ∧
    D v (Distribution.mapCLM imCLM g) + D (I • v) (Distribution.mapCLM reCLM g) = L (I • v) := by
  constructor <;> ext φ
  · have h := congrArg (fun T : 𝓓'(Ω,ℂ) => (T φ).re) hg
    simp [DistributionComplexTestBridge.dbar,beta,Distribution.lineDerivCLM_apply,
      Distribution.mapCLM_apply,Complex.mul_re,Complex.mul_im] at h ⊢
    linarith
  · have h := congrArg (fun T : 𝓓'(Ω,ℂ) => (T φ).im) hg
    simp [DistributionComplexTestBridge.dbar,beta,Distribution.lineDerivCLM_apply,
      Distribution.mapCLM_apply,Complex.mul_re,Complex.mul_im] at h ⊢
    linarith

private def J : E n →ₗ[ℝ] E n where
  toFun v := I • v
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

private def grad (p : 𝓓'(Ω,ℝ)) : E n →ₗ[ℝ] 𝓓'(Ω,ℝ) := directionalLM.flip p

private theorem linear_eq_of_coordinates (L R : E n →ₗ[ℝ] 𝓓'(Ω,ℝ))
    (h : ∀ i : Fin n, L (basisVec i) = R (basisVec i) ∧
      L (I • basisVec i) = R (I • basisVec i)) : L = R := by
  ext v : 1
  have hv : v = ∑ i : Fin n, ((v i).re • basisVec i + (v i).im • (I • basisVec i)) := by
    calc v = ∑ i : Fin n, v i • basisVec i := by
           simpa [EuclideanSpace.basisFun_apply] using
             (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr v |>.symm
         _ = _ := by
           apply Finset.sum_congr rfl
           intro i _
           nth_rw 1 [← re_add_im (v i)]
           rw [add_smul,mul_smul]
           rfl
  rw [hv,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [map_add,map_smul,(h i).1,(h i).2]

private theorem restrict_beta (L : E n →ₗ[ℝ] 𝓓'(Ω,ℝ)) (hU : U ≤ Ω) (v : E n) :
    DistributionComplexTestBridge.restrict (beta L v) hU =
      beta ((restrictLM hU).comp L) v := by
  ext φ
  rfl

/-- Type of the actual differential internally supplies a scalar distribution
potential, with the original factor 4*pi and complete alternating equality. -/
theorem exists_covector_scalar_potential (L : E n →ₗ[ℝ] 𝓓'(Ω,ℝ))
    (h11 : IsOneOne (exteriorDerivative (oneForm L))) (x : E n) (hx : x ∈ Ω) :
    ∃ (U : Opens (E n)) (hU : U ≤ Ω) (p : 𝓓'(U,ℝ)), x ∈ U ∧
      ddC p = restrictForm (exteriorDerivative (oneForm L)) hU := by
  classical
  obtain ⟨U,hU,g,hxU,hg⟩ := DistributionComplexTestBridge.exists_local_primitive
    (fun i => beta L (basisVec i)) (fun i j => beta_closed L h11 _ _) x hx
  let L' : E n →ₗ[ℝ] 𝓓'(U,ℝ) := (restrictLM hU).comp L
  let p : 𝓓'(U,ℝ) := Distribution.mapCLM reCLM g
  let q : 𝓓'(U,ℝ) := Distribution.mapCLM imCLM g
  have hcoords (i : Fin n) :
      L' (basisVec i) = (grad p - (grad q).comp J) (basisVec i) ∧
      L' (I • basisVec i) = (grad p - (grad q).comp J) (I • basisVec i) := by
    have he := hg i
    rw [restrict_beta] at he
    obtain ⟨hr,hi⟩ := real_imag_solution L' g (basisVec i) he
    constructor
    · exact hr.symm
    · have hn : I • (I • basisVec i) = -basisVec i := by simp [smul_smul]
      change L' (I • basisVec i) = D (I • basisVec i) p - D (I • (I • basisVec i)) q
      have hdn : D (-basisVec i) q = -D (basisVec i) q := by
        have he := congrArg (fun F : 𝓓'(U,ℝ) →L[ℝ] 𝓓'(U,ℝ) => F q)
          (Distribution.lineDerivCLM_smul (n := ⊤) (k := ⊤) (Ω := U) (F := ℝ)
            (v := basisVec i) (c := (-1:ℝ)))
        simpa only [neg_one_smul,_root_.neg_apply] using he
      rw [hn,hdn,sub_neg_eq_add]
      change L' (I • basisVec i) = D (I • basisVec i) p + D (basisVec i) q
      exact hi.symm.trans (add_comm _ _)
  have hL : L' = grad p - (grad q).comp J := linear_eq_of_coordinates _ _ hcoords
  refine ⟨U,hU,(4*Real.pi:ℝ) • q,hxU,?_⟩
  have hform : restrictForm (oneForm L) hU = oneForm L' := by
    ext v φ
    rfl
  rw [restrictForm_exteriorDerivative, hform,hL]
  ext v φ
  have hv : v = ![v 0,v 1] := by ext i; fin_cases i <;> rfl
  rw [hv,ddC_apply,exteriorDerivative_oneForm]
  have hp := LocalCurrents.distribution_derivatives_commute U p (v 0) (v 1)
  have hpφ := congrArg (fun T : 𝓓'(U,ℝ) => T φ) hp
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,grad,J,LinearMap.flip_apply,
    LinearMap.coe_mk,directionalLM_apply]
  simp only [map_sub,map_smul,_root_.sub_apply,_root_.smul_apply,smul_eq_mul]
  rw [show (D (v 0) (D (v 1) p)) φ = (D (v 1) (D (v 0) p)) φ from hpφ]
  field_simp
  ring_nf
  rfl

private def covector (C : DistributionForm Ω 1) : E n →ₗ[ℝ] 𝓓'(Ω,ℝ) :=
  C.toMultilinearMap.toLinearMap (fun _ => 0) 0

private theorem covector_apply (C : DistributionForm Ω 1) (v : E n) :
    covector C v = C (fun _ => v) := by
  change C (Function.update (fun _ => 0) (0:Fin 1) v) = _
  congr 1
  ext i
  fin_cases i
  simp

private theorem oneForm_covector (C : DistributionForm Ω 1) : oneForm (covector C) = C := by
  ext v : 1
  rw [oneForm_apply,covector_apply]
  congr 1
  ext i
  fin_cases i
  rfl

/-- Every arbitrary closed signed (1,1) distribution-valued two-form has a
local scalar potential on the original real tests, in every dimension. -/
theorem exists_local_scalar_potential (A : DistributionForm Ω 2) (hA : IsClosed A)
    (h11 : IsOneOne A) (x : E n) (hx : x ∈ Ω) :
    ∃ (U : Opens (E n)) (hU : U ≤ Ω) (p : 𝓓'(U,ℝ)), x ∈ U ∧ ddC p = restrictForm A hU := by
  obtain ⟨W,hW,C,hxW,hC⟩ := ClosedDistributionTwoFormLocalPrimitive.exists_local_primitive
    volume A hA x hx
  have ht : IsOneOne (exteriorDerivative (oneForm (covector C))) := by
    rw [oneForm_covector,hC]
    intro v w
    ext φ
    simpa only [restrictForm_apply] using
      congrArg (fun T : 𝓓'(Ω,ℝ) => T (TestFunction.monoCLM ℝ φ)) (h11 v w)
  obtain ⟨U,hU,p,hxU,hp⟩ := exists_covector_scalar_potential (covector C) ht x hxW
  refine ⟨U,hU.trans hW,p,hxU,?_⟩
  rw [oneForm_covector,hC] at hp
  rw [hp]
  ext v φ
  simp only [restrictForm_apply]
  congr 1
  ext y
  simp [TestFunction.monoCLM_apply,hU,hW,hU.trans hW]

end SGPT.Foundations.Analysis.Pending.DistributionLocalDdcPotential
