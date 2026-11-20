import SGPT.Trace.BertiniUniversalCutoffAE
import SGPT.Trace.BertiniUniversalCutoffHodge
import SGPT.Trace.BertiniHodgeWeightLinearity

/-! ORIGINAL global I(phi) H0 -> actual FULL intrinsic member Hodge finite
AE on a produced FULL affine-base neighborhood, with genuine finite cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Bundle Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Trace.Bertini
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle
open SGPT.Toric.F1IntersectionDraft

variable {k d : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (d + 1)) X] [IsComplexManifold (d + 1) X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel (k + 1)) X (ComplexProjectiveSpace (k + 1)) ∞)
  {φ : X → EReal}

theorem exists_original_fullBase_adjunctionHodge_ae_finite
    (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ) (ℓ₀ : HyperplaneSpace (k + 1))
    (hsm₀ : IsSmoothHypersurfaceMember (d + 1) p ℓ₀) :
    ∃ V : TopologicalSpace.Opens (ComplexModel (k + 1)), affineChart (chartIndex ℓ₀) ℓ₀ ∈ V ∧
      ∃ hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val),
      ∀ (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) X)
        (T : nativeMultiplierSections (OriginalAmbientPhysicalBundle p L) φ)
        (μ : Measure X) (_hμ : IsSmoothPositiveVolume (n := d + 1) μ),
        ∀ᵐ ζ ∂(volume.restrict (V : Set _)), ∀ hζ : ζ ∈ V,
          nativeBertiniAdjunctionHodgeEnergy p (chartIndex ℓ₀) ζ (hsV ⟨ζ,hζ⟩) L φ T.val < ⊤ := by
  classical
  obtain ⟨m,c,a,V₀,β,hV₀,hc,hs,hball,hβ,hβcompact,hsub,hone⟩ :=
    exists_originalPreferredSliceCutoffs p hφ.1 ℓ₀ hsm₀
  let b := affineChart (chartIndex ℓ₀) ℓ₀
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp V₀.isOpen b hV₀
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  let C := closedBall b δ
  have hCV : C ⊆ V₀ := (closedBall_subset_ball (by dsimp only [δ]; linarith)).trans hrV
  let V : TopologicalSpace.Opens (ComplexModel (k + 1)) := ⟨ball b δ,isOpen_ball⟩
  have hVC : (V : Set _) ⊆ C := ball_subset_closedBall
  have hVV : (V : Set (ComplexModel (k + 1))) ⊆ (V₀ : Set (ComplexModel (k + 1))) := fun _ hz => hCV (hVC hz)
  let hsV : ∀ ζ : V, IsSmoothHypersurfaceMember (d + 1) p (affinePoint (chartIndex ℓ₀) ζ.val) :=
    fun ζ => hs ζ.val (hVV ζ.property)
  refine ⟨V,mem_ball_self hδ,hsV,?_⟩
  intro L T μ hμ
  let w : X → ℝ≥0∞ := fun x => multiplierWeight 1 (φ x)
  have hAE (j : Fin m) : ∀ᵐ ζ ∂(volume.restrict C),
      (∫⁻ u : ComplexModel d, originalCutoffResidueSourceDensity p (c j) L T.val (β j) w
        (prodModelEquiv (k + 1) d (ζ,u))) < ⊤ :=
    ae_originalCutoffResidue_tangent_integral_lt_top p (c j) (a j) (hc j).2.1 L
      (isCompact_closedBall _ _) (fun ζ hζ => hball ζ (hCV hζ) j) (β j) (β j).continuous
      (hβcompact j) (fun x => (hβ j x).2) (fun ζ hζ => hsub ζ (hCV hζ) j) hφ T μ hμ
  have hAEall : ∀ᵐ ζ ∂(volume.restrict C), ∀ j : Fin m,
      (∫⁻ u : ComplexModel d, originalCutoffResidueSourceDensity p (c j) L T.val (β j) w
        (prodModelEquiv (k + 1) d (ζ,u))) < ⊤ := (ae_all_iff).2 hAE
  have hAEV := hAEall.filter_mono (ae_mono (Measure.restrict_mono hVC le_rfl))
  filter_upwards [hAEV] with ζ hfinite
  intro hζ
  let i := chartIndex ℓ₀
  let hsm := hsV ⟨ζ,hζ⟩
  let := nativeBertiniMemberChartedSpace p i ζ hsm
  let := nativeBertiniMemberComplex p i ζ hsm
  let := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
  let : MeasurableSpace (member p (affinePoint i ζ)) := borel _
  let : BorelSpace (member p (affinePoint i ζ)) := ⟨rfl⟩
  let LH := nativeHolomorphicPullbackBundle L (nativeBertiniMemberInclusionMap p i ζ hsm)
  let R := nativeBertiniPhysicalAdjunctionSection p i ζ hsm L T.val
  let W : member p (affinePoint i ζ) → ℝ≥0∞ := fun y => w y.val
  let α : Fin m → member p (affinePoint i ζ) → ℝ≥0∞ := fun j y => ENNReal.ofReal (β j y.val)
  have hW : Measurable W := ((lowerSemicontinuous_originalMultiplierWeight hφ.1).comp continuous_subtype_val).measurable
  have hα (j : Fin m) : Measurable (α j) :=
    (ENNReal.continuous_ofReal.comp ((β j).continuous.comp continuous_subtype_val)).measurable
  have hsum (y : member p (affinePoint i ζ)) : ∑ j, α j y = 1 := by
    change (∑ j, ENNReal.ofReal (β j y.val)) = 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hβ j y.val).1),
      hone ζ (hVV hζ) y.val y.property,ENNReal.ofReal_one]
  have hpartition := nativePhysicalHodgeEnergy_weight_partition LH R W hW α hα hsum
  change nativePhysicalHodgeEnergy LH R W < ⊤
  rw [hpartition]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  have hEq := originalCutoffResidue_tangent_integral_eq_commonHodge p (c j) i (hc j).1 ζ
    (hball ζ (hVV hζ) j) hsm L T.val (β j) w (hsub ζ (hVV hζ) j)
  exact hEq ▸ hfinite j

end SGPT.Trace.BertiniUniversal
