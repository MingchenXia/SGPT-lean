import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralFractionEquation

/-! ANY actual original integral fraction internally spreads its SAME monic equation on ONE open.
Blueprint: prime-nov16-analytic-normalization-original-integral-fraction-spread.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Polynomial
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralFractionSpread
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalFunctionRepresentatives
open PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
open PrimeNov16AnalyticNormalizationIntegralFractionEquation
open HironakaActualAnalyticSubspace HironakaSmoothCentreRealDomainActualSheafStalk
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_original_integral_fraction_spread (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x : C)
    (b : integralClosure ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier
      (FractionRing ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier)) :
    let A := ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier
    ∃ (g : A) (d : nonZeroDivisors A) (p : A[X]),
      IsLocalization.mk' (FractionRing A) g d=b.val ∧ p.Monic ∧ aeval b.val p=0 ∧
      ∃ (D G : M → ℂ) (hD : HolomorphicAt n D x.val) (hG : HolomorphicAt n G x.val)
        (c : Fin p.natDegree → M → ℂ) (hc : ∀ i,HolomorphicAt n (c i) x.val) (U : Set M),
        IsOpen U ∧ x.val ∈ U ∧ originalFunctionImage C x D hD=d.val ∧
        originalFunctionImage C x G hG=g ∧
        (∀ i,originalFunctionImage C x (c i) (hc i)=p.coeff i.val) ∧
        ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D U ∧
        ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ G U ∧
        (∀ i,ContMDiffOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (c i) U) ∧
        ∀ y ∈ C,y ∈ U → G y^p.natDegree + ∑ i : Fin p.natDegree,
          c i y*D y^(p.natDegree-i.val)*G y^i.val=0 := by
  let A := ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier
  obtain ⟨g,d,p,hgd,hp,hroot,hrel⟩ := exists_actual_integral_fraction_equation A b
  obtain ⟨D,hD,hDd⟩ := exists_original_stalk_function_representative C x d.val
  obtain ⟨G,hG,hGg⟩ := exists_original_stalk_function_representative C x g
  choose c hc hcp using fun i : Fin p.natDegree =>
    exists_original_stalk_function_representative C x (p.coeff i.val)
  let F : M → ℂ := fun y => G y^p.natDegree + ∑ i : Fin p.natDegree,
    c i y*D y^(p.natDegree-i.val)*G y^i.val
  have hterm (i : Fin p.natDegree) : HolomorphicAt n
      (fun y => c i y*D y^(p.natDegree-i.val)*G y^i.val) x.val :=
    ((hc i).mul (holomorphic_pow x.val D hD _)).mul (holomorphic_pow x.val G hG _)
  have hF : HolomorphicAt n F x.val :=
    (holomorphic_pow x.val G hG _).add (HolomorphicAt.sum Finset.univ fun i _ => hterm i)
  have hread (i : Fin p.natDegree) : originalFunctionImage C x
      (fun y => c i y*D y^(p.natDegree-i.val)*G y^i.val) (hterm i) =
      p.coeff i.val*d.val^(p.natDegree-i.val)*g^i.val := by
    rw [originalFunctionImage_mul C x (fun y => c i y*D y^(p.natDegree-i.val))
      (fun y => G y^i.val) ((hc i).mul (holomorphic_pow x.val D hD _))
      (holomorphic_pow x.val G hG _)]
    rw [originalFunctionImage_mul C x (c i) (fun y => D y^(p.natDegree-i.val))
      (hc i) (holomorphic_pow x.val D hD _)]
    rw [originalFunctionImage_pow C x D hD (p.natDegree-i.val),
      originalFunctionImage_pow C x G hG i.val,hcp,hDd,hGg]
  have hFzero : originalFunctionImage C x F hF=0 := by
    dsimp only [F]
    rw [originalFunctionImage_add C x (fun y => G y^p.natDegree)
      (fun y => ∑ i : Fin p.natDegree,c i y*D y^(p.natDegree-i.val)*G y^i.val)
      (holomorphic_pow x.val G hG _) (HolomorphicAt.sum Finset.univ fun i _ => hterm i),
      originalFunctionImage_pow C x G hG p.natDegree,
      originalFunctionImage_sum C x
        (fun i : Fin p.natDegree => fun y => c i y*D y^(p.natDegree-i.val)*G y^i.val) hterm,hGg]
    simp only [hread]
    rw [Fin.sum_univ_eq_sum_range
      (fun j => p.coeff j*d.val^(p.natDegree-j)*g^j) p.natDegree]
    exact hrel
  have hvan := ((original_function_image_zero_iff C hC x F hF).mp hFzero).2
  have hDs : ∀ᶠ y in 𝓝 x.val,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D y :=
    hD.eventually.mono fun _y hy => contMDiffAt_of_eventually_mdifferentiableAt hy
  have hGs : ∀ᶠ y in 𝓝 x.val,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ G y :=
    hG.eventually.mono fun _y hy => contMDiffAt_of_eventually_mdifferentiableAt hy
  have hcs : ∀ᶠ y in 𝓝 x.val,∀ i,ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (c i) y :=
    eventually_all.mpr fun i => (hc i).eventually.mono fun _y hy =>
      contMDiffAt_of_eventually_mdifferentiableAt hy
  obtain ⟨U,hUe,hU,hxU⟩ := mem_nhds_iff.mp (hDs.and (hGs.and (hcs.and hvan)))
  refine ⟨g,d,p,hgd,hp,hroot,D,G,hD,hG,c,hc,U,hU,hxU,hDd,hGg,hcp,?_,?_,?_,?_⟩
  · exact fun y hy => (hUe hy).1.contMDiffWithinAt
  · exact fun y hy => (hUe hy).2.1.contMDiffWithinAt
  · exact fun i y hy => ((hUe hy).2.2.1 i).contMDiffWithinAt
  · exact fun y hyC hyU => (hUe hyU).2.2.2 hyC

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralFractionSpread
