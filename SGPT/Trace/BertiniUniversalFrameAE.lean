import SGPT.Trace.BertiniUniversalMemberAE
import SGPT.Trace.BertiniNativeFiniteFrameFibre

/-! Actual original quotient-frame energies are AE finite, from ORIGINAL
multiplier reps and true full-base Hodge finiteness. No AE premise. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem exists_original_fullBase_quotientFrame_ae_finite
    (ℓ₀ : HyperplaneSpace (k + 1)) (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀)
    (W : TopologicalSpace.Opens (ComplexModel (k + 1))) (hW : affineChart (chartIndex ℓ₀) ℓ₀ ∈ W)
    (hsW : ∀ ζ : W, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val)) :
    ∃ (V : TopologicalSpace.Opens (ComplexModel (k + 1))) (_hV : affineChart (chartIndex ℓ₀) ℓ₀ ∈ V)
      (hVW : V ≤ W),
      ∀ (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X) (r : ℕ)
        (S : Fin r → nativeMultiplierSections
          (tensor (tensor (nativeCanonicalBundle (n := d + 1) (X := X)) L) (nativeBertiniHyperplaneBundle p)) φ)
        (μ : Measure X) (_hμ : SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1.IsSmoothPositiveVolume (n := d + 1) μ),
        ∀ j : Fin r, ∀ᵐ ζ ∂volume.restrict (V : Set (ComplexModel (k + 1))),
          nativeBertiniQuotientFrameEnergy p (chartIndex ℓ₀) V
            (fun z => hsW ⟨z.val,hVW z.property⟩) L hφ S ζ (Pi.single j (1 : ℂ)) ≠ ⊤ := by
  classical
  obtain ⟨V₀,hV₀,hs₀,hAE⟩ := exists_original_fullBase_adjunctionHodge_ae_finite p hφ ℓ₀ hsm₀
  let V : TopologicalSpace.Opens (ComplexModel (k + 1)) := ⟨(V₀ : Set _) ∩ W,V₀.isOpen.inter W.isOpen⟩
  have hVV₀ : (V : Set (ComplexModel (k + 1))) ⊆ (V₀ : Set (ComplexModel (k + 1))) := fun _ h => h.1
  have hVW : V ≤ W := fun _ h => h.2
  refine ⟨V,⟨hV₀,hW⟩,hVW,?_⟩
  intro L r S μ hμ j
  let K := nativeCanonicalBundle (n := d + 1) (X := X)
  let P := nativeBertiniHyperplaneBundle p
  let T := nativeMultiplierSwapLastSectionMap K L P hφ (S j)
  have hFin := (hAE L T μ hμ).filter_mono (ae_mono (Measure.restrict_mono hVV₀ le_rfl))
  filter_upwards [hFin] with ζ hfinite
  by_cases hζ : ζ ∈ V
  · let hsV : ∀ z : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) z.val) :=
      fun z => hsW ⟨z.val,hVW z.property⟩
    rw [nativeBertiniQuotientFrameEnergy_apply p (chartIndex ℓ₀) V hsV L hφ S ⟨ζ,hζ⟩ (Pi.single j 1),
      nativeBertiniPhysicalQuotientHodgeEnergy_combination p L hφ (chartIndex ℓ₀) ζ (hsV ⟨ζ,hζ⟩) r S (Pi.single j 1)]
    have hsingle : nativeSectionCombination (OriginalAmbientPhysicalBundle p L)
        (fun l => NativeTensorSwap.swapLastSection K L P (S l).val) (Pi.single j (1 : ℂ)) = T.val := by
      unfold nativeSectionCombination
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_apply,ite_true,one_smul]
        rfl
      · intro l _ hlj
        simp only [Pi.single_apply,if_neg hlj]
        ext x
        change (0 : ℂ) • (NativeTensorSwap.swapLastSection K L P (S l).val) x = 0
        exact zero_smul ℂ _
      · simp
    rw [hsingle]
    exact ne_top_of_lt (hfinite (hVV₀ hζ))
  · simp only [nativeBertiniQuotientFrameEnergy,dif_neg hζ]
    exact ENNReal.zero_ne_top

end SGPT.Trace.BertiniUniversal
