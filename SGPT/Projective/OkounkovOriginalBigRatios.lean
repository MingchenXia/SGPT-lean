import SGPT.Projective.OkounkovOriginalRationalPairs
import SGPT.Okounkov.ValGen2Twisted

/-! Actual original equal-degree big-line ratios: Step2 of prop:Okounbiglbdl.
Blueprint: okounkov-original-big-ratios.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalRationalPairs
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite TopologicalSpace Filter
open SGPT.Okounkov SGPT.Okounkov.ValGen2 SGPT.Okounkov.AlgebraicValuation
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
variable {X : Scheme.{0}} [IsIntegral X] {L T : X.Modules}
  (a : LineBundleAtlas L) (aT : LineBundleAtlas T)

omit [IsIntegral X] in
/-- Actual original evaluation transitions cancel the SAME original dual-line unit. -/
theorem originalEvaluationSection_transitions (k : ℕ) :
    ∀ i j (W : X.Opens) (h : W ⟶ twistCover a aT i) (l : W ⟶ twistCover a aT j),
      localBundleFrameTransition
        ((rightRestrictedFrame a aT i).tensor
          ((rightRestrictedFrame a aT i).dual.tensor ((leftRestrictedFrame a aT i).tensorPower k)))
        ((rightRestrictedFrame a aT j).tensor
          ((rightRestrictedFrame a aT j).dual.tensor ((leftRestrictedFrame a aT j).tensorPower k))) h l =
      localBundleFrameTransition ((leftRestrictedFrame a aT i).tensorPower k)
        ((leftRestrictedFrame a aT j).tensorPower k) h l := by
  intro i j W h l
  rw [localBundleFrameTransition_tensor, localBundleFrameTransition_tensor,
    localBundleFrameTransition_dual, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Genuinely descended ORIGINAL evaluation section, on the SAME original power L^k. -/
def originalEvaluationSection (k : ℕ) (s : Γ(T,⊤))
    (t : Γ(bundleTensor (bundleDual T) (bundleTensorPower L k),⊤)) : bundlePowerGlobalSections L k :=
  coverProduct (twistCover a aT) (twistCover_covers a aT)
    (fun i => rightRestrictedFrame a aT i)
    (fun i => (rightRestrictedFrame a aT i).dual.tensor ((leftRestrictedFrame a aT i).tensorPower k))
    (fun i => (leftRestrictedFrame a aT i).tensorPower k)
    (originalEvaluationSection_transitions a aT k) s t

/-- Its actual generic coefficient is the SAME literal original product. -/
theorem originalEvaluationSection_genericCoefficient (k : ℕ) (i : a.I × aT.I)
    [Nonempty (twistCover a aT i)] (s : Γ(T,⊤))
    (t : Γ(bundleTensor (bundleDual T) (bundleTensorPower L k),⊤)) :
    globalSectionToFunctionField ((leftRestrictedFrame a aT i).tensorPower k)
      (originalEvaluationSection a aT k s t) =
      globalSectionToFunctionField (rightRestrictedFrame a aT i) s *
        globalSectionToFunctionField
          ((rightRestrictedFrame a aT i).dual.tensor ((leftRestrictedFrame a aT i).tensorPower k)) t :=
  globalSectionToFunctionField_coverProduct (twistCover a aT) (twistCover_covers a aT)
    _ _ _ (originalEvaluationSection_transitions a aT k) i s t

local instance originalBigRatioTopology (f : X ⟶ Spec (.of ℂ)) :
    TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalBigRatioCharts (f : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d f] : ChartedSpace (ComplexModel d) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f d
local instance originalBigRatioManifold (f : X ⟶ Spec (.of ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d f] [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold d (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f d

include a in
/-- EVERY actual original rational function is a quotient of SAME-degree nonzero original big-L sections. -/
theorem exists_bigLine_equalDegree_sectionPair
    (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
    {m : ℕ} [SmoothOfRelativeDimension (m+1) f] [Nonempty (SchemeComplexPoint f)]
    (Y : Fin (m+1+1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
    (hbig : SGPT.LineBundle.IsBig f L (m+1)) (r : X.functionField) (hr : r ≠ 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ s t : bundlePowerGlobalSections L k,
      s ≠ 0 ∧ t ≠ 0 ∧ ∀ (V : X.Opens) (hV : Nonempty V)
        (e : LocalBundleFrame (bundleTensorPower L k) V), letI := hV
        globalSectionToFunctionField e s / globalSectionToFunctionField e t = r := by
  classical
  obtain ⟨T,aT,u,w,hu,hw,huw⟩ := exists_originalSectionPair_of_functionField f E r hr
  have hev := exists_twisted_section_ne_zero f E Y hY a hbig (hbig.volume_pos) (dualAtlas aT)
  obtain ⟨k,⟨σ,hσ⟩,hk⟩ := (hev.and (eventually_ge_atTop 1)).exists
  let bD := pairwiseTensorAtlas (dualAtlas aT) (a.tensorPower k)
  let U := twistCover a aT
  obtain ⟨i,hi⟩ := twistCover_covers a aT (genericPoint X)
  let : Nonempty (U i) := ⟨⟨genericPoint X,hi⟩⟩
  let eT := rightRestrictedFrame a aT i
  let eD := eT.dual.tensor ((leftRestrictedFrame a aT i).tensorPower k)
  let eL := (leftRestrictedFrame a aT i).tensorPower k
  have hσc : globalSectionToFunctionField eD σ ≠ 0 := by
    intro h0
    apply hσ
    exact globalSectionToFunctionField_injective bD eD (h0.trans (map_zero _).symm)
  have huc : globalSectionToFunctionField eT u ≠ 0 := by
    intro h0
    apply hu
    exact globalSectionToFunctionField_injective aT eT (h0.trans (map_zero _).symm)
  have hwc : globalSectionToFunctionField eT w ≠ 0 := by
    intro h0
    apply hw
    exact globalSectionToFunctionField_injective aT eT (h0.trans (map_zero _).symm)
  let s := originalEvaluationSection a aT k u σ
  let t := originalEvaluationSection a aT k w σ
  have hsfield := originalEvaluationSection_genericCoefficient a aT k i u σ
  have htfield := originalEvaluationSection_genericCoefficient a aT k i w σ
  have hs : s ≠ 0 := by
    intro h0
    apply mul_ne_zero huc hσc
    change globalSectionToFunctionField eL s = _ at hsfield
    rw [h0,map_zero] at hsfield
    exact hsfield.symm
  have ht : t ≠ 0 := by
    intro h0
    apply mul_ne_zero hwc hσc
    change globalSectionToFunctionField eL t = _ at htfield
    rw [h0,map_zero] at htfield
    exact htfield.symm
  refine ⟨k,hk,s,t,hs,ht,?_⟩
  intro V hV e
  let := hV
  refine (originalSectionRatio_frame_independent eL e s t).trans ?_
  rw [hsfield,htfield,mul_div_mul_right _ _ hσc]
  exact huw (U i) inferInstance eT

end SGPT.Okounkov.OriginalRationalPairs
