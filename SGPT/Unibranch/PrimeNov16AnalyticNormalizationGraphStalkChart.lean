import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkCoordinates

/-! Exact full original chart and ambient-function readback, not a dictionary field.
Blueprint: prime-nov16-analytic-normalization-graph-stalk-chart.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspaceOpenRestriction
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphStalkFinite
open PrimeNov16AnalyticNormalizationStalkCalculus
open PrimeNov16AnalyticNormalizationGraphOriginalStalk
open PrimeNov16AnalyticNormalizationGraphStalkCoordinates

def intrinsicGermMap {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    (C : Set M) (p : C) : HolGerm (ComplexModel m) →+*
      ((actualSubspaceSheaf (n := m) C).presheaf.stalk p).carrier :=
  (actualSubspaceStalkChartEquiv (n := m) C p).symm.toRingHom.comp
    (Ideal.Quotient.mk (wholeChartStalkIdeal (vanishingIdeal (n := m) C)
      p.val p.val (mem_chart_source (ComplexModel m) p.val)))

theorem intrinsicGermMap_carrier_eq {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    (S T : Set M) (h : S=T) (p : S) (f : HolGerm (ComplexModel m)) :
    stalkEquiv_of_carrier_eq S T h p (intrinsicGermMap S p f) =
      intrinsicGermMap T (⟨p.val,h ▸ p.property⟩ : T) f := by
  subst T
  rfl

theorem graphGermMap_eq_intrinsic {n k : ℕ} (U : Opens (ComplexModel n))
    (C : Set U) (H : ComplexModel n → ℂ) (G : Fin k → ComplexModel n → ℂ)
    (p : graphClosure U C H G) (f : HolGerm (ComplexModel (n+k))) :
    graphGermMap U C H G p f = intrinsicGermMap (graphClosure U C H G) p f := by
  let T := (Subtype.val : wideDomain k U → ComplexModel (n+k)) ⁻¹' nativeCarrier U C H G
  let pT : T := ⟨p.val,⟨p.val,p.property,rfl⟩⟩
  have hopen : actualOpenSubspaceStalkEquiv (n := n+k) (nativeCarrier U C H G) (wideDomain k U) pT
      ((translatedStalkEquiv (nativeCarrier U C H G) (nativePoint U C H G p)).symm
        (Ideal.Quotient.mk
          (AnalyticGermDecomposition.vanishingIdeal
            {v : ComplexModel (n+k) | v+p.val.val ∈ nativeCarrier U C H G}) f)) =
      intrinsicGermMap T pT f := by
    simp only [actualOpenSubspaceStalkEquiv,translatedStalkEquiv,RingEquiv.trans_apply,
      RingEquiv.symm_trans_apply,Ideal.quotEquivOfEq_symm]
    change (actualSubspaceStalkChartEquiv (n := n+k) T pT).symm
      ((Ideal.quotEquivOfEq _)
        ((actualSubspaceStalkChartEquiv (n := n+k) (nativeCarrier U C H G) (nativePoint U C H G p))
          ((actualSubspaceStalkChartEquiv (n := n+k) (nativeCarrier U C H G) (nativePoint U C H G p)).symm
            (Ideal.Quotient.mk _ f)))) = _
    rw [RingEquiv.apply_symm_apply,Ideal.quotEquivOfEq_mk]
    rfl
  change stalkEquiv_of_carrier_eq T (graphClosure U C H G) (nativeCarrier_preimage U C H G) pT
    (actualOpenSubspaceStalkEquiv (n := n+k) (nativeCarrier U C H G) (wideDomain k U) pT _) = _
  exact (congrArg (stalkEquiv_of_carrier_eq T (graphClosure U C H G)
    (nativeCarrier_preimage U C H G) pT) hopen).trans
      (intrinsicGermMap_carrier_eq T _ (nativeCarrier_preimage U C H G) pT f)

theorem intrinsicGermMap_original_function {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    (C : Set M) (p : C) (f : M → ℂ) (hf : HolomorphicAt m f p.val) :
    intrinsicGermMap C p (chartTranslatedGerm p.val p.val (mem_chart_source (ComplexModel m) p.val) f hf) =
      (actualSubspaceInclusion (n := m) C).stalkMap p
        (actualOriginalFunctionGerm p.val f hf) := by
  apply (actualSubspaceStalkChartEquiv (n := m) C p).injective
  rw [show actualSubspaceStalkChartEquiv (n := m) C p
      (intrinsicGermMap C p (chartTranslatedGerm p.val p.val (mem_chart_source (ComplexModel m) p.val) f hf)) =
      Ideal.Quotient.mk _ (chartTranslatedGerm p.val p.val (mem_chart_source (ComplexModel m) p.val) f hf)
    from (actualSubspaceStalkChartEquiv (n := m) C p).apply_symm_apply _]
  change _ = (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := m) p.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := m) C) p.val).symm)
    (actualSubspaceStalkWholeEquiv (n := m) C p
      ((actualSubspaceInclusion (n := m) C).stalkMap p (actualOriginalFunctionGerm p.val f hf)))
  rw [actualSubspaceInclusion_stalk]
  change _ = Ideal.Quotient.mk _ (actualStalkChartEquiv (n := m) p.val (actualOriginalFunctionGerm p.val f hf))
  rw [actualOriginalFunctionGerm_chart]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkChart
