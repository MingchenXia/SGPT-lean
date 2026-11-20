import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatorSpreadComplete
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedRegularWindow
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchWindow

/-! SAME finite original branches manufacture ONE common separator/entire-stalk regular window.
Blueprint: prime-nov16-analytic-normalization-original-complete-separated-window.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCompleteSeparatedWindow
open AnalyticGermDecomposition
open PrimeNov16AnalyticNormalizationOriginalSeparatorSpreadComplete
open PrimeNov16AnalyticNormalizationOriginalReducedRegularWindow
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationLocalGraph
open HironakaActualAnalyticSubspace

private theorem zero_mem_original_irreducible_germ {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) : (0 : ComplexModel n) ∈ Z := by
  by_contra h0
  obtain ⟨s,G,hG,hset⟩ := hZ.1
  have hn : ¬ ∀ i,G i 0=0 := fun h => h0 (hset.self_of_nhds.mpr h)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hne : ∀ᶠ z in 𝓝 (0 : ComplexModel n),G i z ≠ 0 :=
    ((hG i).self_of_nhds.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hi
  apply hZ.2.1
  apply eventuallyEq_set.mpr
  filter_upwards [hset,hne] with z hz hzi
  constructor
  · intro hzZ
    exact (hzi ((hz.mp hzZ) i)).elim
  · intro hzE
    exact hzE.elim


theorem exists_original_complete_separated_window {n k : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : IsAnalyticGerm Z) (h0 : (0 : ComplexModel n) ∈ Z)
    (B : Fin k → Set (ComplexModel n)) (hB : ∀ i,IsIrreducibleGerm (B i))
    (hcover : Z =ᶠ[𝓝 (0 : ComplexModel n)] (⋃ i,B i))
    (hpair : Pairwise fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j))
    (H : Fin k → ComplexModel n → ℂ)
    (hH : ∀ i,∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (H i) z)
    (hne : ∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → H i z=0)
    (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (T : Fin k → ComplexModel n → ℂ) (r : ℝ)
      (_ : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z})
      (_ : ∀ i,IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ B i}),
      let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*H i z
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ i,DifferentiableOn ℂ (T i) (ball 0 r)) ∧
      (∀ i,DifferentiableOn ℂ (H i) (ball 0 r)) ∧
      DifferentiableOn ℂ Q (ball 0 r) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ Q z) ∧
      (∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → Q z=0) ∧
      ∃ hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (Q ∘ Subtype.val : ballDomain (n := n) r → ℂ),
      ∃ V : Set (ballDomain (n := n) r),IsOpen V ∧
      (∃ p0 : ballDomain (n := n) r,p0.val=0 ∧ p0 ∈ V) ∧
      (∀ y : {z : ballDomain (n := n) r | z.val ∈ Z},y.val ∈ V →
        originalFunctionImage _ y (Q ∘ Subtype.val)
          (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0) ∧
      (∀ i,∀ y : {z : ballDomain (n := n) r | z.val ∈ B i},y.val ∈ V →
        originalFunctionImage _ y (Q ∘ Subtype.val)
          (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0) ∧
      (∀ y : {z : ballDomain (n := n) r | z.val ∈ Z},y.val ∈ V →
        y ∈ closure {z : {z : ballDomain (n := n) r | z.val ∈ Z} | Q z.val.val ≠ 0}) ∧
      (∀ i,∀ y : {z : ballDomain (n := n) r | z.val ∈ B i},y.val ∈ V →
        y ∈ closure {z : {z : ballDomain (n := n) r | z.val ∈ B i} | Q z.val.val ≠ 0}) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i,z ∈ B i → Q z=T i z*H i z) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i j,j ≠ i → z ∈ B j → T i z=0) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i j,i ≠ j → z ∈ B i → z ∈ B j → Q z=0) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i,z ∈ B i → Q z ≠ 0 →
        H i z ≠ 0 ∧ ∀ j,j ≠ i → z ∉ B j) := by
  obtain ⟨r0,hr0,hC0⟩ := exists_analytic_ball hZ
  choose ri hri hCi using fun i => exists_analytic_ball (hB i).1
  have hballs : ∀ᶠ z in 𝓝 (0 : ComplexModel n),∀ i,z ∈ ball 0 (ri i) :=
    eventually_all.mpr fun i => ball_mem_nhds 0 (hri i)
  have hNN : {z : ComplexModel n | z ∈ N ∧ z ∈ ball 0 r0 ∧ ∀ i,z ∈ ball 0 (ri i)} ∈ 𝓝 0 :=
    Filter.inter_mem hN (Filter.inter_mem (ball_mem_nhds 0 hr0) hballs)
  obtain ⟨T,r,hr,hrN,hT,hHi,hQOn,hQg,hQne,hrel,hvan,hzero,hunique⟩ :=
    exists_original_separator_spread_complete B hB hpair H hH hne hNN
  let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*H i z
  have hU0 : ballDomain (n := n) r ≤ ballDomain (n := n) r0 := fun z hz => (hrN hz).2.1
  have hUi (i : Fin k) : ballDomain (n := n) r ≤ ballDomain (n := n) (ri i) :=
    fun z hz => (hrN hz).2.2 i
  have hC : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z} :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion hU0) hC0
  have hBC (i : Fin k) : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ B i} :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion (hUi i)) (hCi i)
  have hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (Q ∘ Subtype.val : ballDomain (n := n) r → ℂ) :=
    (contDiffOn_of_differentiableOn_complex hQOn (isOpen_ball)).contMDiffOn.comp_contMDiff
      contMDiff_subtype_val (fun z => z.property)
  let p0 : {z : ballDomain (n := n) r | z.val ∈ Z} := ⟨⟨0,mem_ball_self hr⟩,h0⟩
  obtain ⟨V0,hV0,hp0,hNZ,hReg,hDense⟩ := exists_original_reduced_regular_dense_window
    B hB hcover (ballDomain (n := n) r) hC p0 rfl Q hQg hQne hD
  have branch (i : Fin k) := exists_original_reduced_regular_dense_window
    (fun _ : Fin 1 => B i) (fun _ => hB i)
    (Eventually.of_forall fun z => by
      apply propext
      change z ∈ B i ↔ z ∈ ⋃ _ : Fin 1,B i
      simp only [mem_iUnion]
      exact ⟨fun hz => ⟨0,hz⟩,fun ⟨_,hz⟩ => hz⟩)
    (ballDomain (n := n) r) (hBC i)
    (⟨⟨0,mem_ball_self hr⟩,zero_mem_original_irreducible_germ (hB i)⟩ : {z : ballDomain (n := n) r | z.val ∈ B i})
    rfl Q hQg (fun _ => hQne i) hD
  choose Vi hVi h0Vi hNZi _hRegi hDensei using branch
  let V : Set (ballDomain (n := n) r) := V0 ∩ ⋂ i,Vi i
  have hV : IsOpen V := hV0.inter (isOpen_iInter_of_finite hVi)
  refine ⟨T,r,hC,hBC,hr,fun z hz => (hrN hz).1,hT,hHi,hQOn,hQg,hQne,hD,V,hV,?_,?_,?_,?_,?_,hrel,hvan,hzero,hunique⟩
  · exact ⟨⟨0,mem_ball_self hr⟩,rfl,⟨hp0,mem_iInter.mpr h0Vi⟩⟩
  · exact fun y hy => hNZ y hy.1
  · exact fun i y hy => hNZi i y (mem_iInter.mp hy.2 i)
  · exact fun y hy => hDense y hy.1
  · exact fun i y hy => hDensei i y (mem_iInter.mp hy.2 i)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCompleteSeparatedWindow
