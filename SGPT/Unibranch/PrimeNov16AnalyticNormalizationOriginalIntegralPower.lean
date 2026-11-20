import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralFractionSpread
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenRegularity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationMonicColonSupportPower
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionPowerReadback

/-! Genuine analytic regular complement manufactures powers for EVERY original integral fraction.
Blueprint: prime-nov16-analytic-normalization-original-integral-power.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPower
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalIntegralFractionSpread
open PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
open PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open PrimeNov16AnalyticNormalizationOriginalOpenRegularity
open PrimeNov16AnalyticNormalizationMonicColonSupportPower
open PrimeNov16AnalyticNormalizationDivisionIdealReadback
open PrimeNov16AnalyticNormalizationFractionPowerReadback
open PrimeNov16AnalyticNormalizationOriginalFunctionCalculus
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_original_integral_power (C : Set M)
    (hC : IsComplexAnalyticSubset (n := d+t) C) (Q : M → ℂ)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q)
    (hregular : ∀ y ∈ C,Q y ≠ 0 → RegularAtDim (n := d+t) C y d) (x : C)
    (b : integralClosure ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier
      (FractionRing ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier)) :
    ∃ N : ℕ,∃ a : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier,
      algebraMap _ (FractionRing ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier)
        ((originalFunctionImage C x Q (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y))^N)*b.val =
          algebraMap _ _ a := by
  let A := ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier
  obtain ⟨g,den,p,hgb,hp,hroot,D,G,hD,hG,c,hc,U,hU,hxU,hDd,hGg,hcp,hDOn,hGOn,hcOn,hrel⟩ :=
    exists_original_integral_fraction_spread C hC x b
  let V : Opens M := ⟨U,hU⟩
  let C1 : Set V := (Subtype.val : V → M) ⁻¹' C
  let x1 : C1 := ⟨⟨x.val,hxU⟩,x.property⟩
  let E1 : A ≃+* ((actualSubspaceSheaf (n := d+t) C1).presheaf.stalk x1).carrier :=
    actualOpenSubspaceStalkEquiv (n := d+t) C V x1
  let D1 : V → ℂ := D ∘ Subtype.val
  let G1 : V → ℂ := G ∘ Subtype.val
  let Q1 : V → ℂ := Q ∘ Subtype.val
  let c1 : Fin p.natDegree → V → ℂ := fun i => c i ∘ Subtype.val
  have hC1 : IsComplexAnalyticSubset (n := d+t) C1 :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC V
  have hD1 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ D1 := fun y =>
    contMDiffAt_subtype_iff.mpr (hDOn.contMDiffAt (hU.mem_nhds y.property))
  have hG1 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ G1 := fun y =>
    contMDiffAt_subtype_iff.mpr (hGOn.contMDiffAt (hU.mem_nhds y.property))
  have hQ1 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q1 := hQ.comp contMDiff_subtype_val
  have hc1 : ∀ i,ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ (c1 i) := fun i y =>
    contMDiffAt_subtype_iff.mpr ((hcOn i).contMDiffAt (hU.mem_nhds y.property))
  let hD1x : HolomorphicAt (d+t) D1 x1.val := Eventually.of_forall fun y => hD1.mdifferentiable (by simp) y
  have hDread1 : E1 den.val=originalFunctionImage C1 x1 D1 hD1x := by
    rw [← hDd]
    exact original_open_function_image C V x1 D hD
  have hDreg1 : ∀ r : ((actualSubspaceSheaf (n := d+t) C1).presheaf.stalk x1).carrier,
      originalFunctionImage C1 x1 D1 hD1x*r=0 → r=0 := by
    intro r hr
    apply E1.symm.injective
    rw [map_zero]
    apply mem_nonZeroDivisors_iff_left.mp den.property
    apply E1.injective
    rw [map_mul,hDread1,E1.apply_symm_apply,map_zero]
    exact hr
  obtain ⟨W0,hW0,hxW,hDW⟩ := exists_original_open_entire_stalk_regular C1 hC1 x1 D1 hD1 hDreg1
  let W : Opens V := ⟨W0,hW0⟩
  let C2 : Set W := (Subtype.val : W → V) ⁻¹' C1
  let x2 : C2 := ⟨⟨x1.val,hxW⟩,x1.property⟩
  let E2 := actualOpenSubspaceStalkEquiv (n := d+t) C1 W x2
  let E := E1.trans E2
  let D2 : W → ℂ := D1 ∘ Subtype.val
  let G2 : W → ℂ := G1 ∘ Subtype.val
  let Q2 : W → ℂ := Q1 ∘ Subtype.val
  let c2 : Fin p.natDegree → W → ℂ := fun i => c1 i ∘ Subtype.val
  have hC2 : IsComplexAnalyticSubset (n := d+t) C2 :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC1 W
  have hD2 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ D2 := hD1.comp contMDiff_subtype_val
  have hG2 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ G2 := hG1.comp contMDiff_subtype_val
  have hQ2 : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q2 := hQ1.comp contMDiff_subtype_val
  have hc2 : ∀ i,ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ (c2 i) := fun i => (hc1 i).comp contMDiff_subtype_val
  have hDreg2 : ∀ y : C2,∀ r : ((actualSubspaceSheaf (n := d+t) C2).presheaf.stalk y).carrier,
      originalFunctionImage C2 y D2 (Eventually.of_forall fun z => hD2.mdifferentiable (by simp) z)*r=0 → r=0 := by
    intro y
    apply original_open_multiplier_regular C1 W y D1
      (Eventually.of_forall fun z => hD1.mdifferentiable (by simp) z)
    exact hDW ((actualOpenSubspaceMap (n := d+t) C1 W).base y) y.val.property
  have hregular2 : ∀ y ∈ C2,Q2 y ≠ 0 → RegularAtDim (n := d+t) C2 y d := by
    intro y hy hyQ
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    exact hregular y.val.val hy hyQ
  have hrel2 : ∀ y ∈ C2,G2 y^p.natDegree + ∑ i : Fin p.natDegree,
      c2 i y*D2 y^(p.natDegree-i.val)*G2 y^i.val=0 := by
    intro y hy
    exact hrel y.val.val hy y.val.property
  obtain ⟨_hK,_hzero,O,hO,hxO,N,_hN,hpow⟩ := exists_original_monic_colon_support_power
    C2 hC2 D2 G2 Q2 c2 hD2 hG2 hQ2 hc2 hDreg2 hregular2 hrel2 x2.val
  let hG2x : HolomorphicAt (d+t) G2 x2.val := Eventually.of_forall fun y => hG2.mdifferentiable (by simp) y
  let hQ2x : HolomorphicAt (d+t) Q2 x2.val := Eventually.of_forall fun y => hQ2.mdifferentiable (by simp) y
  let hD2x : HolomorphicAt (d+t) D2 x2.val := Eventually.of_forall fun y => hD2.mdifferentiable (by simp) y
  let hQx : HolomorphicAt (d+t) Q x.val := Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y
  let q : A := originalFunctionImage C x Q hQx
  have hQread1 : E1 q=originalFunctionImage C1 x1 Q1
      (Eventually.of_forall fun y => hQ1.mdifferentiable (by simp) y) :=
    original_open_function_image C V x1 Q hQx
  have hGread1 : E1 g=originalFunctionImage C1 x1 G1
      (Eventually.of_forall fun y => hG1.mdifferentiable (by simp) y) := by
    rw [← hGg]
    exact original_open_function_image C V x1 G hG
  have hDread : E den.val=originalFunctionImage C2 x2 D2 hD2x :=
    (congrArg E2 hDread1).trans (original_open_function_image C1 W x2 D1 hD1x)
  have hGread : E g=originalFunctionImage C2 x2 G2 hG2x :=
    (congrArg E2 hGread1).trans (original_open_function_image C1 W x2 G1
      (Eventually.of_forall fun y => hG1.mdifferentiable (by simp) y))
  have hQread : E q=originalFunctionImage C2 x2 Q2 hQ2x :=
    (congrArg E2 hQread1).trans (original_open_function_image C1 W x2 Q1
      (Eventually.of_forall fun y => hQ1.mdifferentiable (by simp) y))
  obtain ⟨a2,ha2⟩ := (original_functional_mem_iff_division C2 hC2 x2 D2 _ hD2
    (hG2x.mul (holomorphic_pow x2.val Q2 hQ2x N))).mp (hpow x2.val hxO)
  rw [originalFunctionImage_mul C2 x2 G2 (fun y => Q2 y^N) hG2x (holomorphic_pow x2.val Q2 hQ2x N),
    originalFunctionImage_pow C2 x2 Q2 hQ2x N] at ha2
  have hraw : g*q^N=den.val*E.symm a2 := by
    apply E.injective
    rw [map_mul,map_mul,map_pow,hGread,hQread,hDread,E.apply_symm_apply]
    exact ha2
  exact ⟨N,E.symm a2,actual_total_fraction_power_readback b.val g q _ den N hgb hraw⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPower
