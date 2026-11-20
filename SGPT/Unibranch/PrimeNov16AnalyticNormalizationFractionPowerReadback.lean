import SGPT.Unibranch.PrimeNov16AnalyticNormalizationDivisionIdealReadback
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus

/-! Literal analytic carrier-ideal powers become integers in the SAME actual total fraction ring.
Blueprint: prime-nov16-analytic-normalization-fraction-power-readback.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionPowerReadback
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationDivisionIdealReadback
open PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open RestrictedIdealExtension HironakaActualAnalyticSubspace

theorem actual_total_fraction_power_readback {A : Type*} [CommRing A]
    (b : FractionRing A) (g q a : A) (d : nonZeroDivisors A) (N : ℕ)
    (hb : IsLocalization.mk' (FractionRing A) g d=b) (ha : g*q^N=d.val*a) :
    algebraMap A (FractionRing A) (q^N)*b=algebraMap A (FractionRing A) a := by
  let f := algebraMap A (FractionRing A)
  have hdg : f d.val*b=f g := by
    rw [← hb]
    exact IsLocalization.mk'_spec' (FractionRing A) g d
  apply (IsLocalization.map_units (FractionRing A) d).mul_left_cancel
  calc
    f d.val*(f (q^N)*b) = f (q^N)*(f d.val*b) := by ring
    _ = f (q^N)*f g := by rw [hdg]
    _ = f d.val*f a := by rw [← map_mul,mul_comm (q^N) g,ha,map_mul]

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_functional_power_fraction_readback (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x : C) (D G Q : M → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D)
    (hG : HolomorphicAt n G x.val) (hQ : HolomorphicAt n Q x.val)
    (b : FractionRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)
    (g : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)
    (d : nonZeroDivisors ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)
    (hb : IsLocalization.mk' _ g d=b)
    (hDd : originalFunctionImage C x D (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)=d.val)
    (hGg : originalFunctionImage C x G hG=g) (N : ℕ)
    (hmem : (sumIdeal (principalIdeal (n := n) D) (vanishingIdeal (n := n) C)).mem x.val
      (fun y => G y*Q y^N)) :
    ∃ a : ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier,
      algebraMap _ (FractionRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)
        ((originalFunctionImage C x Q hQ)^N)*b=algebraMap _ _ a := by
  have hF := hG.mul (holomorphic_pow x.val Q hQ N)
  obtain ⟨a,ha⟩ := (original_functional_mem_iff_division C hC x D _ hD hF).mp hmem
  have hraw : g*(originalFunctionImage C x Q hQ)^N=d.val*a := by
    rw [originalFunctionImage_mul C x G (fun y => Q y^N) hG (holomorphic_pow x.val Q hQ N),
      originalFunctionImage_pow C x Q hQ N,hGg,hDd] at ha
    exact ha
  exact ⟨a,actual_total_fraction_power_readback b g _ a d N hb hraw⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionPowerReadback
