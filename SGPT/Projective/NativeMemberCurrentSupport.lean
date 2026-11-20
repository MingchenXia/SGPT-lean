import SGPT.Projective.NativeSectionWeightedCurrentArea
import SGPT.Projective.NativeBertiniWholeMember

/-! Actual original weighted current area supported on the SAME whole
native member. Blueprint: `native-member-current-support.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.AnalyticSectionProducts
open HermitianHolomorphicLineBundle SGPT.BDivisor.NSKodaira
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms StronglyPositiveForms
open ActualCompactGlobalPairingCalibration
open _root_.SGPT.Foundations.Analysis.LocalCurrents
open SGPT.Trace.Bertini SGPT.Projective.ComplexProjectiveSpace

variable {m N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (s : Fin (N + 1) → HolomorphicSections (n := m + 1) L.Fiber)
  (hgen : ∀ x : X, ∃ j, s j x ≠ 0) (l : HyperplaneSpace N)

/-- The unchanged original scalar divisor density/test vanishes off the
ambient chart image of the SAME whole native member and original support. -/
theorem divisorShuffleDensity_eq_zero_off_native_member {q : ℕ}
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X)
    (χ : X → ℝ) (hdom : tsupport χ ⊆ E.val.baseSet ∩ c.val.source)
    {Ω : Opens (ComplexModel (m + 1))} (η : TestForm Ω q)
    (hs : tsupport (η : ComplexModel (m + 1) → RealForm (m + 1) q) ⊆ c.val '' tsupport χ)
    (v : Fin 2 ⊕ Fin q → ComplexModel (m + 1)) (z : ComplexModel (m + 1))
    (hz : z ∉ c.val '' (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l ∩ tsupport χ)) :
    divisorShuffleDensity (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm)
      v η z = 0 := by
  classical
  by_cases hzS : z ∈ tsupport (η : ComplexModel (m + 1) → RealForm (m + 1) q)
  · obtain ⟨x, hx, rfl⟩ := hs hzS
    have hxdom := hdom hx
    have hxW : x ∉ member (sourceNativeFiniteSectionProjectiveMap L s hgen) l := by
      intro hxW
      exact hz ⟨x, ⟨hxW, hx⟩, rfl⟩
    have hzR : c.val x ∉ DivisorRegularLocus.regularLocus
        (sectionCoefficient L.Fiber E.val (linearSection L s l) ∘ c.val.symm) := by
      intro hzR
      have hg0 := DivisorRegularLocus.eq_zero_of_mem_regularLocus hzR
      have hcoef : sectionCoefficient L.Fiber E.val (linearSection L s l) x = 0 := by
        simpa only [Function.comp_apply, c.val.left_inv hxdom.2] using hg0
      have hs0 : linearSection L s l x = 0 := by
        let := E.property
        apply (E.val.linearEquivAt ℂ x hxdom.1).injective
        exact hcoef.trans (map_zero _).symm
      exact hxW ((linearSection_zero_iff L s hgen l x).mp hs0)
    apply divisorShuffleDensity_eq_zero_off_regular
    exact fun h => hzR h.1
  · have hη0 : η z = 0 := image_eq_zero_of_notMem_tsupport hzS
    simp [divisorShuffleDensity, hη0]

variable [CompactSpace X]

/-- Actual full weighted global member-current area is on exactly the
SAME original entire member support. Test, coefficients and support are
produced from the SAME actual physical native section. -/
theorem exists_native_member_current_area_support
    (hL : IsSourceSmoothHermitianMetric L)
    (hl : IsSmoothHypersurfaceMember (m + 1)
      (sourceNativeFiniteSectionProjectiveMap L s hgen) l)
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X)
    (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hχc : IsCompact (tsupport χ)) (hχdom : tsupport χ ⊆ E.val.baseSet ∩ c.val.source)
    (γ : SmoothRealForm (m + 1) X (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    let S := linearSection L s l
    let hs := linearSection_dense_nonzero (Nat.succ_pos m) L s hgen l
      (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl
    let P := nativeSectionFramePresentation L hL S hs E
    ∃ η : TestForm (P.chartDomain c) (Module.finrank ℝ (ComplexModel (m + 1)) - 2),
      (∀ z, η z = c.val.target.indicator (fun y => χ (c.val.symm y) • γ.coeff c y) z) ∧
      tsupport (η : ComplexModel (m + 1) →
        RealForm (m + 1) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) ⊆ c.val '' tsupport χ ∧
      pairingLM
        (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (nativeSectionDivisorMetric L hL S hs)) (smulFun χ hχ γ) =
        ∫ z in c.val '' (member (sourceNativeFiniteSectionProjectiveMap L s hgen) l ∩ tsupport χ),
          divisorShuffleDensity (P.chartG c ⟨0, by change 0 < 1; omega⟩)
            (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η z
            ∂(μHE[2 * (m + 1) - 2] : Measure (ComplexModel (m + 1))) := by
  let S := linearSection L s l
  let hs := linearSection_dense_nonzero (Nat.succ_pos m) L s hgen l
    (sourceNativeFiniteSectionProjectiveMap_contMDiff L s hgen) hl
  let P := nativeSectionFramePresentation L hL S hs E
  obtain ⟨η, hη, hsupport, hread⟩ :=
    exists_nativeSection_weighted_area_action L hL S hs E c χ hχ hχc hχdom γ
  refine ⟨η, hη, hsupport, ?_⟩
  rw [hread]
  apply Eq.symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact divisorShuffleDensity_eq_zero_off_native_member L s hgen l E c χ hχdom
    η hsupport _ z hz

end SGPT.Projective.NumEq.CompleteIntersections
