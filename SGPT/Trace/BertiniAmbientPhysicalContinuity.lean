import SGPT.Trace.BertiniAmbientPhysicalCoefficients
import SGPT.Trace.BertiniSliceNormLowerSemicontinuity

/-! Actual joint original-section coefficient/full-base PHYSICAL residue norm continuity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter Metric TensorProduct
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

private theorem actualCombinationCoefficient_continuousAt {n m : ℕ} {Y : Type} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (E : HermitianHolomorphicLineBundle.{0,0} n Y) (e : AtlasFrame E)
    (H : Fin m → HolomorphicSections (n := n) E.Fiber) (q₀ : (Fin m → ℂ) × Y)
    (h₀ : q₀.2 ∈ e.val.baseSet) :
    ContinuousAt (fun q : (Fin m → ℂ) × Y => (e.val ⟨q.2,nativeSectionCombination E H q.1 q.2⟩).2) q₀ := by
  classical
  let := e.property
  have hc : ContinuousAt (fun q : (Fin m → ℂ) × Y => ∑ j, q.1 j * sectionCoefficient E.Fiber e.val (H j) q.2) q₀ := by
    apply tendsto_finsetSum Finset.univ
    intro j _
    have hH : ContinuousAt (sectionCoefficient E.Fiber e.val (H j)) q₀.2 :=
      ((e.val.contMDiffAt_section_iff h₀).mp ((H j).contMDiff q₀.2)).continuousAt
    exact ((continuous_apply j).continuousAt.comp continuous_fst.continuousAt).mul
      (hH.comp continuous_snd.continuousAt)
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually (e.val.open_baseSet.mem_nhds h₀)] with q hq
  change (e.val.linearEquivAt ℂ q.2 hq) (nativeSectionCombination E H q.1 q.2) = _
  let ev : HolomorphicSections (n := n) E.Fiber →ₗ[ℂ] E.Fiber q.2 := {
    toFun S := S q.2
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hsum : nativeSectionCombination E H q.1 q.2 = ∑ j, q.1 j • H j q.2 := by
    change ev (∑ j, q.1 j • H j) = _
    rw [map_sum]
    rfl
  rw [hsum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,smul_eq_mul]
  rfl

namespace SliceChart
variable {d N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  {p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) X (ComplexProjectiveSpace N) ∞}
  {φ : X → EReal} (c : SliceChart (d + 1) (p : X → ComplexProjectiveSpace N) φ)

theorem continuous_originalAmbientLValue_combination_norm (a : X)
    (ha : c.e = complexChartAt (n := d + 1) a) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {m : ℕ} (H : Fin m → HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    Continuous (fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) =>
      ‖c.originalAmbientLValue p.contMDiff q.2 L
        (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
          (nativeBertiniHyperplaneBundle p)) L) H q.1 (c.tangentPoint q.2))‖) := by
  classical
  let E := tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L
  apply continuous_iff_continuousAt.mpr
  intro q₀
  let x₀ := c.tangentPoint q₀.2
  let eK := nativeCanonicalFrame (n := d + 1) a
  let eP : AtlasFrame (nativeBertiniHyperplaneBundle p) := ⟨trivializationAt ℂ (nativeBertiniHyperplaneBundle p).Fiber x₀,inferInstance⟩
  let eL : AtlasFrame L := ⟨trivializationAt ℂ L.Fiber x₀,inferInstance⟩
  let eKP := tensorAtlasFrame eK eP
  let eT := tensorAtlasFrame eKP eL
  let := eK.property
  let := eP.property
  let := eL.property
  let := eKP.property
  let := eT.property
  have hP₀ : x₀ ∈ eP.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hL₀ : x₀ ∈ eL.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
  have hK₀ : x₀ ∈ eK.val.baseSet := by
    change x₀ ∈ (complexChartAt (n := d + 1) a).val.source
    rw [← ha]
    exact (c.tangentPoint_chart_coordinates q₀.2).1
  have hT₀ : x₀ ∈ eT.val.baseSet := ⟨⟨hK₀,hP₀⟩,hL₀⟩
  have hpoint : Continuous (fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) => c.tangentPoint q.2) :=
    c.continuous_tangentPoint.comp continuous_snd
  have hcoef := (actualCombinationCoefficient_continuousAt E eT H (q₀.1,x₀) hT₀).comp
    (f := fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) => (q.1,c.tangentPoint q.2))
    (x := q₀) (continuous_fst.prodMk hpoint).continuousAt
  let cs : X → ℂ := fun x => (eP.val ⟨x,nativeBertiniCoordinateSection p c.j x⟩).2
  have hcs : ContinuousAt cs x₀ :=
    ((eP.val.contMDiffAt_section_iff hP₀).mp ((nativeBertiniCoordinateSection p c.j).contMDiff x₀)).continuousAt
  have hpj₀ : p x₀ ∈ (affineChart c.j).source :=
    (mem_chartLiftDomain_iff p (c.tangentPoint_chart_coordinates q₀.2).1).mp
      (c.tangentPoint_chart_coordinates q₀.2).2.2
  have hcsne : cs x₀ ≠ 0 := by
    intro hz
    apply nativeBertiniCoordinateSection_ne_zero p c.j x₀ hpj₀
    apply (eP.val.linearEquivAt ℂ x₀ hP₀).injective
    exact hz.trans (map_zero _).symm
  have hcinv := (hcs.inv₀ hcsne).comp
    (f := fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) => c.tangentPoint q.2)
    (x := q₀) hpoint.continuousAt
  have hframe := ((frameNorm_continuousOn L.Fiber eL.val).continuousAt
    (eL.val.open_baseSet.mem_nhds hL₀)).comp
    (f := fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) => c.tangentPoint q.2)
    (x := q₀) hpoint.continuousAt
  let δ : ℂ := (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.det
    (Matrix.vecCons (EuclideanSpace.single c.m (1 : ℂ)) (fun j => EuclideanSpace.single (c.m.succAbove j) (1 : ℂ)))
  have hformula : ContinuousAt
      (fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) =>
        ‖(eT.val ⟨c.tangentPoint q.2,nativeSectionCombination E H q.1 (c.tangentPoint q.2)⟩).2 *
          (cs (c.tangentPoint q.2))⁻¹ * δ‖ * frameNorm L.Fiber eL.val (c.tangentPoint q.2)) q₀ :=
    ((hcoef.mul hcinv).mul continuousAt_const).norm.mul hframe
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hpoint.continuousAt.eventually (eP.val.open_baseSet.mem_nhds hP₀),
    hpoint.continuousAt.eventually (eL.val.open_baseSet.mem_nhds hL₀)] with q hP hL
  exact c.originalAmbientLValue_frameNorm a ha q.2 L eP eL hP hL
    (nativeSectionCombination E H q.1 (c.tangentPoint q.2))

theorem continuous_originalNormalDivision_combination_norm (a : X)
    (ha : c.e = complexChartAt (n := d + 1) a) (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
    {m : ℕ} (H : Fin m → HolomorphicSections (n := d + 1)
      (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) (nativeBertiniHyperplaneBundle p)) L).Fiber) :
    Continuous (fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) =>
      ‖(c.tangentNormalDenominator q.2)⁻¹ • c.originalAmbientLValue p.contMDiff q.2 L
        (nativeSectionCombination (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X))
          (nativeBertiniHyperplaneBundle p)) L) H q.1 (c.tangentPoint q.2))‖) := by
  have hi : Continuous (fun q : (Fin m → ℂ) × ((ball c.ζ₀ c.r) × c.tangentPatch) => (c.tangentNormalDenominator q.2)⁻¹) :=
    ((c.continuous_tangentNormalDenominator p.contMDiff).inv₀ (c.tangentNormalDenominator_ne_zero p.contMDiff)).comp continuous_snd
  have hn := hi.norm.mul (c.continuous_originalAmbientLValue_combination_norm a ha L H)
  apply hn.congr
  intro q
  exact (norm_smul _ _).symm

end SliceChart
end SGPT.Trace.Bertini
