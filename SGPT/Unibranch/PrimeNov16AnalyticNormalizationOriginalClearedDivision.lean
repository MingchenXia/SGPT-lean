import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationClearedMonicDivision

/-! Primitive whole carrier equations, actual regularity, and true original ideal division.
Blueprint: prime-nov16-analytic-normalization-original-cleared-division.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClearedDivision
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
open PrimeNov16AnalyticNormalizationRegularOriginalStalk
open PrimeNov16AnalyticNormalizationClearedMonicDivision
open PrimeNov16AnalyticNormalizationCoherentChartProducts RestrictedIdealExtension
open HironakaActualAnalyticSubspace
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_carrier_cleared_relation (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (x : C) {k : ℕ} (D G : M → ℂ) (c : Fin k → M → ℂ)
    (hD : HolomorphicAt n D x.val) (hG : HolomorphicAt n G x.val)
    (hc : ∀ i,HolomorphicAt n (c i) x.val)
    (hrel : ∀ᶠ y in 𝓝 x.val,y ∈ C → G y^k+∑ i : Fin k,c i y*D y^(k-i.val)*G y^i.val=0) :
    (originalFunctionImage C x G hG)^k + ∑ i : Fin k,
      originalFunctionImage C x (c i) (hc i)*(originalFunctionImage C x D hD)^(k-i.val)*
        (originalFunctionImage C x G hG)^i.val=0 := by
  let F : M → ℂ := fun y => G y^k+∑ i : Fin k,c i y*D y^(k-i.val)*G y^i.val
  have ht (i : Fin k) : HolomorphicAt n (fun y => c i y*D y^(k-i.val)*G y^i.val) x.val :=
    ((hc i).mul (holomorphic_pow x.val D hD _)).mul (holomorphic_pow x.val G hG _)
  have hF : HolomorphicAt n F x.val :=
    (holomorphic_pow x.val G hG _).add (HolomorphicAt.sum Finset.univ fun i _ => ht i)
  have hz : originalFunctionImage C x F hF=0 :=
    (original_function_image_zero_iff C hC x F hF).mpr ⟨hF,hrel⟩
  have hread (i : Fin k) : originalFunctionImage C x
      (fun y => c i y*D y^(k-i.val)*G y^i.val) (ht i) =
      originalFunctionImage C x (c i) (hc i)*(originalFunctionImage C x D hD)^(k-i.val)*
        (originalFunctionImage C x G hG)^i.val := by
    rw [originalFunctionImage_mul C x (fun y => c i y*D y^(k-i.val))
      (fun y => G y^i.val) ((hc i).mul (holomorphic_pow x.val D hD _))
      (holomorphic_pow x.val G hG _),
      originalFunctionImage_mul C x (c i) (fun y => D y^(k-i.val))
        (hc i) (holomorphic_pow x.val D hD _),
      originalFunctionImage_pow C x D hD (k-i.val),originalFunctionImage_pow C x G hG i.val]
  dsimp only [F] at hz
  rw [originalFunctionImage_add C x (fun y => G y^k)
    (fun y => ∑ i : Fin k,c i y*D y^(k-i.val)*G y^i.val)
    (holomorphic_pow x.val G hG _) (HolomorphicAt.sum Finset.univ fun i _ => ht i),
    originalFunctionImage_pow C x G hG k,
    originalFunctionImage_sum C x (fun i : Fin k => fun y => c i y*D y^(k-i.val)*G y^i.val) ht] at hz
  simpa only [hread] using hz

theorem actual_regular_cleared_function_division {d t : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    (C : Set X) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d) {k : ℕ} (D G : X → ℂ) (c : Fin k → X → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ D)
    (hG : HolomorphicAt (d+t) G x) (hc : ∀ i,HolomorphicAt (d+t) (c i) x)
    (hDn : originalFunctionImage C ⟨x,hreg.2.1⟩ D
      (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y) ≠ 0)
    (hrel : ∀ᶠ y in 𝓝 x,y ∈ C → G y^k+∑ i : Fin k,c i y*D y^(k-i.val)*G y^i.val=0) :
    (sumIdeal (principalIdeal (n := d+t) D) (vanishingIdeal (n := d+t) C)).mem x G := by
  let p : C := ⟨x,hreg.2.1⟩
  let hDx : HolomorphicAt (d+t) D x := Eventually.of_forall fun y => hD.mdifferentiable (by simp) y
  have hraw := original_carrier_cleared_relation C hC p D G c hDx hG hc hrel
  obtain ⟨hd,hn⟩ := actual_regular_original_stalk_normal C x hreg
  let := hd
  let := hn
  have hdiv := exists_divisor_of_cleared_relation
    (fun i => originalFunctionImage C p (c i) (hc i))
    (originalFunctionImage C p G hG) (originalFunctionImage C p D hDx) hDn hraw
  exact original_division_functional_mem C hC p D G hD hG hdiv

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClearedDivision
