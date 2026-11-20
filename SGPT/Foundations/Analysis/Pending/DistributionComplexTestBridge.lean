import SGPT.Foundations.Analysis.Pending.DistributionDolbeaultOne
import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false

/-! Actual original real-test distributions and complex-test duals.
ENTIRE BP proofs precede this source; no scalar ddC/global class assumed. -/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace Complex
open scoped ContDiff Distributions Topology
namespace SGPT.Foundations.Analysis.Pending.DistributionComplexTestBridge

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω U : Opens E}

private def realTest (φ : 𝓓(Ω,ℂ)) : 𝓓(Ω,ℝ) := TestFunction.postcompCLM reCLM φ
private def imagTest (φ : 𝓓(Ω,ℂ)) : 𝓓(Ω,ℝ) := TestFunction.postcompCLM imCLM φ
private def embedTest (φ : 𝓓(Ω,ℝ)) : 𝓓(Ω,ℂ) := TestFunction.postcompCLM ofRealCLM φ

/-- Every original real-test distribution is extended by its actual real and
imaginary LF test components. Continuity and complex linearity are proved. -/
def complexify (T : 𝓓'(Ω,ℂ)) : 𝓓(Ω,ℂ) →L[ℂ] ℂ := by
  let b : 𝓓(Ω,ℂ) →L[ℝ] ℂ :=
    T.comp (TestFunction.postcompCLM reCLM) +
      (ContinuousLinearMap.mul ℝ ℂ I).comp (T.comp (TestFunction.postcompCLM imCLM))
  refine { toFun := b, map_add' := b.map_add, map_smul' := ?_, cont := b.continuous }
  intro c φ
  have hr : realTest (c • φ) = c.re • realTest φ - c.im • imagTest φ := by
    ext y
    simp [realTest,imagTest,smul_eq_mul,mul_re]
  have hi : imagTest (c • φ) = c.im • realTest φ + c.re • imagTest φ := by
    ext y
    simp [realTest,imagTest,smul_eq_mul,mul_im]
    ring
  change T (realTest (c • φ)) + I*T (imagTest (c • φ)) =
    c * (T (realTest φ)+I*T (imagTest φ))
  rw [hr,hi,map_sub,map_add,map_smul,map_smul,map_smul,map_smul]
  simp only [Complex.real_smul]
  conv_rhs => rw [← re_add_im c]
  ring_nf
  rw [I_sq]
  ring

/-- Restriction to actual real tests, without a chosen extension certificate. -/
def realify (S : 𝓓(Ω,ℂ) →L[ℂ] ℂ) : 𝓓'(Ω,ℂ) :=
  (S.restrictScalars ℝ).comp (TestFunction.postcompCLM ofRealCLM)

@[simp] theorem complexify_apply (T : 𝓓'(Ω,ℂ)) (φ : 𝓓(Ω,ℂ)) :
    complexify T φ = T (TestFunction.postcompCLM reCLM φ) +
      I*T (TestFunction.postcompCLM imCLM φ) := rfl

@[simp] theorem realify_complexify (T : 𝓓'(Ω,ℂ)) : realify (complexify T) = T := by
  ext φ
  change T (realTest (embedTest φ)) + I*T (imagTest (embedTest φ)) = T φ
  have hr : realTest (embedTest φ) = φ := by ext y; simp [realTest,embedTest]
  have hi : imagTest (embedTest φ) = 0 := by ext y; simp [imagTest,embedTest]
  rw [hr,hi,map_zero,mul_zero,add_zero]

@[simp] theorem complexify_realify (S : 𝓓(Ω,ℂ) →L[ℂ] ℂ) : complexify (realify S) = S := by
  ext φ
  change S (embedTest (realTest φ)) + I*S (embedTest (imagTest φ)) = S φ
  rw [← smul_eq_mul, ← map_smul, ← map_add]
  congr 1
  ext y
  change ((φ y).re:ℂ) + I*((φ y).im:ℂ) = φ y
  simpa [mul_comm] using re_add_im (φ y)

private theorem realify_injective : Function.Injective (realify (Ω := Ω)) := by
  intro S T h
  simpa only [complexify_realify] using congrArg complexify h

/-- Restriction remains the original real LF-test inclusion. -/
def restrict (T : 𝓓'(Ω,ℂ)) (_hU : U ≤ Ω) : 𝓓'(U,ℂ) :=
  T.comp (TestFunction.monoCLM ℝ)

private theorem inclusion_apply (hU : U ≤ Ω) (φ : 𝓓(U,ℂ)) :
    ((TestFunction.monoCLM ℂ φ : 𝓓(Ω,ℂ)) : E→ℂ) = φ := by
  simp [TestFunction.monoCLM_apply,hU]

private theorem real_inclusion_apply (hU : U ≤ Ω) (φ : 𝓓(U,ℝ)) :
    ((TestFunction.monoCLM ℝ φ : 𝓓(Ω,ℝ)) : E→ℝ) = φ := by
  simp [TestFunction.monoCLM_apply,hU]

private theorem realify_restrict (S : 𝓓(Ω,ℂ) →L[ℂ] ℂ) (hU : U ≤ Ω) :
    realify (S.comp (TestFunction.monoCLM ℂ)) = restrict (realify S) hU := by
  ext φ
  change S (TestFunction.monoCLM ℂ (embedTest φ)) = S (embedTest (TestFunction.monoCLM ℝ φ))
  congr 1
  ext y
  rw [inclusion_apply hU]
  simp only [embedTest,TestFunction.postcompCLM_apply,Function.comp_apply,ofRealCLM_apply]
  rw [real_inclusion_apply hU]

@[simp] theorem complexify_restrict (T : 𝓓'(Ω,ℂ)) (hU : U ≤ Ω) :
    complexify (restrict T hU) = (complexify T).comp (TestFunction.monoCLM ℂ) := by
  apply realify_injective
  rw [realify_complexify,realify_restrict,realify_complexify]

end Real

section Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Opens E}
open DistributionCauchyGreenTranspose CauchyGreen

/-- The original real-test distributional Wirtinger operator uses actual
mathlib transpose real-direction derivatives and its original complex values. -/
def dbar (v : E) (T : 𝓓'(Ω,ℂ)) : 𝓓'(Ω,ℂ) :=
  (2:ℂ)⁻¹ • (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) v T +
    I • Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (I • v) T)

private theorem derivative_apply (v : E) (φ : 𝓓(Ω,ℂ)) (y : E) :
    dbarTestCLM v φ y = dbarDir v φ y := by
  change (2:ℂ)⁻¹*((TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) y +
    I*(TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ (I • v) φ) y) = _
  simp only [TestFunction.lineDerivCLM_apply,le_top,↓reduceIte]
  rw [(φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  simp only [dbarDir]
  ring

private theorem derivative_embed (v : E) (φ : 𝓓(Ω,ℝ)) :
    dbarTestCLM v (embedTest φ) = (2:ℂ)⁻¹ •
      (embedTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) +
        I • embedTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (I • v) φ)) := by
  ext y
  rw [derivative_apply]
  have he : (embedTest φ : E→ℂ) = fun z => (φ z:ℂ) := rfl
  rw [he]
  have hd := ofRealCLM.hasFDerivAt.comp y
    (φ.contDiff.differentiable (by simp) y).hasFDerivAt
  have hd' : HasFDerivAt (fun z => (φ z:ℂ)) (ofRealCLM.comp (fderiv ℝ φ y)) y := hd
  simp only [dbarDir,hd'.fderiv,ContinuousLinearMap.comp_apply,ofRealCLM_apply]
  simp only [_root_.smul_apply,_root_.add_apply,embedTest,
    TestFunction.postcompCLM_apply,Function.comp_apply,ofRealCLM_apply,
    TestFunction.lineDerivCLM_apply,le_top,↓reduceIte,smul_eq_mul]
  rw [(φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv,
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv]
  ring

private theorem realify_dbar (S : 𝓓(Ω,ℂ) →L[ℂ] ℂ) (v : E) :
    realify (-(S.comp (dbarTestCLM v))) = dbar v (realify S) := by
  ext φ
  change -S (dbarTestCLM v (embedTest φ)) =
    (2:ℂ)⁻¹*(-S (embedTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)) +
      I*(-S (embedTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (I • v) φ))))
  rw [derivative_embed,map_smul,map_add,map_smul]
  simp only [smul_eq_mul]
  ring

@[simp] theorem complexify_dbar (T : 𝓓'(Ω,ℂ)) (v : E) :
    complexify (dbar v T) = -((complexify T).comp (dbarTestCLM v)) := by
  apply realify_injective
  rw [realify_complexify,realify_dbar,realify_complexify]
end Complex

section Euclidean
variable {n : ℕ} {Ω : Opens (EuclideanSpace ℂ (Fin n))}
open CauchyGreen

/-- Arbitrary closed (0,1) coefficient distributions in the ORIGINAL real-test
convention have an internally supplied local primitive, including n=0. -/
theorem exists_local_primitive (a : Fin n → 𝓓'(Ω,ℂ))
    (hclosed : ∀ i j, dbar (basisVec i) (a j) = dbar (basisVec j) (a i))
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Ω) :
    ∃ (U : Opens (EuclideanSpace ℂ (Fin n))) (hU : U ≤ Ω) (f : 𝓓'(U,ℂ)),
      x ∈ U ∧ ∀ i, dbar (basisVec i) f = restrict (a i) hU := by
  have hclosedC (i j : Fin n) :
      DistributionDolbeaultOne.dbar (basisVec i) (complexify (a j)) =
        DistributionDolbeaultOne.dbar (basisVec j) (complexify (a i)) := by
    change -((complexify (a j)).comp (DistributionCauchyGreenTranspose.dbarTestCLM (basisVec i))) =
      -((complexify (a i)).comp (DistributionCauchyGreenTranspose.dbarTestCLM (basisVec j)))
    rw [← complexify_dbar,← complexify_dbar,hclosed i j]
  obtain ⟨U,hU,g,hxU,hg⟩ := DistributionDolbeaultOne.exists_local_primitive
    (fun i => complexify (a i)) hclosedC x hx
  refine ⟨U,hU,realify g,hxU,fun i => ?_⟩
  rw [← realify_dbar]
  change realify (DistributionDolbeaultOne.dbar (basisVec i) g) = _
  rw [hg i]
  change realify ((complexify (a i)).comp (TestFunction.monoCLM ℂ)) = _
  rw [realify_restrict,realify_complexify]
end Euclidean
end SGPT.Foundations.Analysis.Pending.DistributionComplexTestBridge
