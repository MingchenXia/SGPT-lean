import SGPT.Unibranch.Resolution
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPower
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedCanonicalClosure
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationPointwisePowerFinite

/-! Actual analytic regular complement clears ALL original canonical branches at each point.
Blueprint: prime-nov16-analytic-normalization-original-whole-power.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWholePower
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalIntegralPower
open PrimeNov16AnalyticNormalizationReducedAlgebra
open PrimeNov16AnalyticNormalizationReducedCanonicalClosure
open PrimeNov16AnalyticNormalizationPointwisePowerFinite
open HironakaActualAnalyticSubspace

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_original_whole_branch_power (C : Set M)
    (hC : IsComplexAnalyticSubset (n := d+t) C) (Q : M → ℂ)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q)
    (hregular : ∀ y ∈ C,Q y ≠ 0 → RegularAtDim (n := d+t) C y d) (x : C) :
    let A := ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier
    let q : A := originalFunctionImage C x Q (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y)
    ∃ N : ℕ,∀ b : NormalBranchAlgebra A,∃ a : A,normalBranchMap A (q^N)*b=normalBranchMap A a := by
  let X := SourceReducedComplexSpace.ofClosedAnalytic (n := d+t) C hC
  let A := ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier
  let q : A := originalFunctionImage C x Q (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y)
  let E : NormalBranchAlgebra A ≃ₐ[A] integralClosure A (FractionRing A) :=
    original_stalk_canonical_closure_equiv X (show X.obj.left from x)
  have hfinite : Module.Finite A (NormalBranchAlgebra A) := original_normal_branch_algebra_finite X (show X.obj.left from x)
  let := hfinite
  apply exists_whole_power_of_elementwise q
  intro b
  obtain ⟨N,a,ha⟩ := exists_original_integral_power C hC Q hQ hregular x (E b)
  refine ⟨N,a,E.injective ?_⟩
  rw [map_mul]
  have hcoeff (r : A) : E (algebraMap A (NormalBranchAlgebra A) r)=algebraMap A (integralClosure A (FractionRing A)) r :=
    E.commutes r
  rw [hcoeff,hcoeff]
  apply Subtype.ext
  exact ha

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWholePower
