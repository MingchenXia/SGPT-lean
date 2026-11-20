import SGPT.Foundations.Analysis.Pending.ActualLowerDimensionalLeviNullity
import SGPT.Foundations.Analysis.Pending.DivisorIntegrationCurrent
import SGPT.Foundations.Analysis.PlurisubharmonicPullback

set_option autoImplicit false

/-! # Actual unitary transport of directional Levi measures

All measure, compact finiteness, exact native Levi pairings and lower-
dimensional-image nullity are produced from the original unbounded psh.
No analytic stratification or divisorial whole theorem is asserted.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Laplacian ENNReal InnerProductSpace
namespace SGPT.Foundations.Analysis.Pending.ActualUnitaryDirectionalLeviMeasure
open FirstPass DivisorRegularLocus DivisorIntegrationCurrent LelongPoincareSlices

variable {n m : ℕ} {v : ComplexModel n}


private def rectangle (U : Opens ℂ) (V : Opens (ComplexModel m)) :
    Opens (ℂ × ComplexModel m) :=
  ⟨(U : Set ℂ) ×ˢ (V : Set (ComplexModel m)), U.isOpen.prod V.isOpen⟩

private def splitImage (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    (U : Opens ℂ) (V : Opens (ComplexModel m)) : Opens (ComplexModel n) :=
  ⟨splitHomeomorph hv S '' (rectangle U V : Set (ℂ × ComplexModel m)),
    (splitHomeomorph hv S).isOpenMap _ (rectangle U V).isOpen⟩

private def complexSplitMap (S : Splitting v (ComplexModel m)) :
    ℂ × ComplexModel m →L[ℂ] ComplexModel n :=
  (ContinuousLinearMap.fst ℂ ℂ (ComplexModel m)).smulRight v +
    S.ι.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ ℂ (ComplexModel m))

private theorem complexSplitMap_apply (S : Splitting v (ComplexModel m))
    (x : ℂ × ComplexModel m) : complexSplitMap S x = splitMap S x := rfl

private def inverseSplitCLM (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m)) :
    ComplexModel n →L[ℝ] ℂ × ComplexModel m :=
  ((splitIsometry hv S).symm.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ (ComplexModel m))).toContinuousLinearMap

private theorem inverseSplitCLM_apply (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    (x : ComplexModel n) : inverseSplitCLM hv S x = (splitHomeomorph hv S).symm x := rfl

private def pullTest (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    {U : Opens ℂ} {V : Opens (ComplexModel m)} (φ : 𝓓(splitImage hv S U V, ℝ)) :
    𝓓(rectangle U V, ℝ) where
  toFun x := φ (splitMap S x)
  contDiff' := φ.contDiff.comp (splitMap S).contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (splitHomeomorph hv S)
  tsupport_subset' := by
    change tsupport (φ ∘ splitHomeomorph hv S) ⊆ rectangle U V
    rw [tsupport_comp_eq_preimage]
    intro x hx
    obtain ⟨y, hy, hyx⟩ := φ.tsupport_subset hx
    exact (splitHomeomorph hv S).injective hyx ▸ hy

private theorem leviForm_pullTest (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    {U : Opens ℂ} {V : Opens (ComplexModel m)} (φ : 𝓓(splitImage hv S U V, ℝ))
    (x : ℂ × ComplexModel m) :
    leviForm (pullTest hv S φ) x (1, (0 : ComplexModel m)) =
      leviForm φ (splitMap S x) v := by
  change leviForm (φ ∘ splitMap S) x (1, (0 : ComplexModel m)) = _
  rw [leviForm_splitMap S φ.contDiff,
    sliceLaplacian_eq ((φ.contDiff.comp (splitMap S).contDiff).of_le ENat.LEInfty.out)]
  simp only [leviForm, realHessian, Prod.smul_mk, smul_eq_mul,
    mul_one, smul_zero]

/-- Original psh and actual unitary geometry produce an original-coordinate
Levi measure and its nullity on every lower-dimensional C1 parameter image. -/
theorem exists_unitary_directional_measure_null_smooth_images
    (hv : ‖v‖ = 1) (S : Splitting v (ComplexModel m))
    (U : Opens ℂ) (V : Opens (ComplexModel m)) (f : ComplexModel n → EReal)
    (hf : PlurisubharmonicOn f
      (splitHomeomorph hv S '' ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m)))))
    (hΩ : IsPreconnected ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))))
    (hne : ∃ a ∈ splitHomeomorph hv S '' ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))),
      f a ≠ ⊥) :
    let Q : Opens (ComplexModel n) :=
      ⟨splitHomeomorph hv S '' ((U : Set ℂ) ×ˢ (V : Set (ComplexModel m))),
        (splitHomeomorph hv S).isOpenMap _ (U.isOpen.prod V.isOpen)⟩
    ∃ (hQ : IsPreconnected (Q : Set (ComplexModel n))) (μ : Measure (ComplexModel n)),
      μ (Q : Set (ComplexModel n))ᶜ = 0 ∧
      (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ Q → μ K < ⊤) ∧
      (∀ φ : 𝓓(Q, ℝ), (∫ x, φ x ∂μ) =
        distributionalLeviCLM v (pshRegularDistribution hf volume hQ hne) φ) ∧
      ∀ (k : ℕ) (D : Set (ComplexModel k)), IsOpen D →
        ∀ (g : ComplexModel k → ComplexModel n), ContDiffOn ℝ 1 g D → k < m →
          μ (g '' D) = 0 := by
  change ∃ (hQ : IsPreconnected (splitImage hv S U V : Set (ComplexModel n)))
      (μ : Measure (ComplexModel n)),
    μ (splitImage hv S U V : Set (ComplexModel n))ᶜ = 0 ∧
    (∀ K : Set (ComplexModel n), IsCompact K → K ⊆ splitImage hv S U V → μ K < ⊤) ∧
    (∀ φ : 𝓓(splitImage hv S U V, ℝ), (∫ x, φ x ∂μ) =
      distributionalLeviCLM v (pshRegularDistribution hf volume hQ hne) φ) ∧
    ∀ (k : ℕ) (D : Set (ComplexModel k)), IsOpen D →
      ∀ (g : ComplexModel k → ComplexModel n), ContDiffOn ℝ 1 g D → k < m → μ (g '' D) = 0
  have hQ : IsPreconnected (splitImage hv S U V : Set (ComplexModel n)) :=
    hΩ.image _ (splitHomeomorph hv S).continuous.continuousOn
  have hF : PlurisubharmonicOn (fun x => f (splitMap S x)) (rectangle U V) := by
    have h := hf.comp_continuousLinearMap (complexSplitMap S)
    apply h.mono
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hneF : ∃ a ∈ rectangle U V, f (splitMap S a) ≠ ⊥ := by
    obtain ⟨a, ⟨z, hz, hza⟩, hfa⟩ := hne
    refine ⟨z, hz, ?_⟩
    simpa only [splitHomeomorph_apply] using hza.symm ▸ hfa
  obtain ⟨ν, _, hloc, hrep, hnull⟩ :=
    ActualDirectionalLeviNullColumns.exists_directional_measure_with_null_columns U V
      (fun x => f (splitMap S x)) hF hΩ hneF
  let ν' : Measure (rectangle U V) := ν
  let _ : IsLocallyFiniteMeasure ν' := hloc
  have hrep' : ∀ φ : 𝓓(rectangle U V, ℝ), (∫ x : rectangle U V, φ x.val ∂ν') =
      distributionalLeviCLM (1, (0 : ComplexModel m))
        (pshRegularDistribution hF volume hΩ hneF) φ := hrep
  have hnull' : ∀ E : Set (ComplexModel m), volume E = 0 →
      ν' {x : rectangle U V | x.val.2 ∈ E} = 0 := hnull
  let j : rectangle U V → ComplexModel n := fun x => splitHomeomorph hv S x.val
  have hj : MeasurableEmbedding j :=
    (splitHomeomorph hv S).measurableEmbedding.comp
      (MeasurableEmbedding.subtype_coe (rectangle U V).isOpen.measurableSet)
  have hjtop : Topology.IsEmbedding j :=
    (splitHomeomorph hv S).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let μ : Measure (ComplexModel n) := ν'.map j
  refine ⟨hQ, μ, ?_, ?_, ?_, ?_⟩
  · change ν'.map j _ = 0
    rw [hj.map_apply]
    have he : j ⁻¹' (splitImage hv S U V : Set (ComplexModel n))ᶜ = ∅ := by
      ext x
      simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
      intro h
      exact h ⟨x.val, x.property, rfl⟩
    rw [he, measure_empty]
  · intro K hK hKQ
    change ν'.map j K < ⊤
    rw [hj.map_apply]
    have hrange : K ⊆ range j := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hKQ hx
      exact ⟨⟨z, hz⟩, hzx⟩
    have hK' : IsCompact (j ⁻¹' K) :=
      (hjtop.isInducing.isCompact_preimage_iff hrange).mpr hK
    exact hK'.measure_lt_top
  · intro φ
    change (∫ x, φ x ∂ν'.map j) = _
    rw [hj.integral_map]
    change (∫ x : rectangle U V, pullTest hv S φ x.val ∂ν') = _
    rw [hrep' (pullTest hv S φ)]
    unfold pshRegularDistribution
    rw [distributionalLeviCLM_regularDistribution_apply,
      distributionalLeviCLM_regularDistribution_apply]
    simp_rw [leviForm_pullTest]
    simpa only [Measure.volume_eq_prod] using
      (measurePreserving_splitMap hv S).integral_comp
        (measurableEmbedding_splitMap hv S)
        (fun x : ComplexModel n => (f x).toReal * leviForm φ x v)
  · intro k D hD g hg hkm
    change ν'.map j (g '' D) = 0
    rw [hj.map_apply]
    have hc : ContDiffOn ℝ 1
        (fun z => (inverseSplitCLM hv S (g z)).2) D :=
      (contDiff_snd.comp (inverseSplitCLM hv S).contDiff).comp_contDiffOn hg
    have he := ActualLowerDimensionalLeviNullity.volume_image_eq_zero_of_lower_dimensional_contDiffOn
      hD hc hkm
    apply measure_mono_null _ (hnull' _ he)
    rintro x ⟨z, hz, hzx⟩
    refine ⟨z, hz, ?_⟩
    change (inverseSplitCLM hv S (g z)).2 = x.val.2
    rw [hzx, inverseSplitCLM_apply]
    exact congrArg Prod.snd ((splitHomeomorph hv S).symm_apply_apply x.val)

end SGPT.Foundations.Analysis.Pending.ActualUnitaryDirectionalLeviMeasure
