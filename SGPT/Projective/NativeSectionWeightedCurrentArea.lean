import SGPT.Projective.NativeSectionCurrentArea
import SGPT.Foundations.Analysis.Pending.ActualCompactGlobalPairingCalibration

/-! The actual original weighted global current uses its SAME manufactured
native frame/chart Hausdorff test. Blueprint: `native-section-weighted-current-area.tex`. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Projective.NumEq.CompleteIntersections

open Set Filter Bundle MeasureTheory
open scoped Topology Manifold ContDiff BigOperators Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.PolynomialH0Growth SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle SGPT.BDivisor.NSKodaira
open LelongPoincareDivisor CanonicalCurrentFrame ProductTestForms StronglyPositiveForms
open ActualCompactGlobalPairingCalibration
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X] [CompactSpace X]
  (L : HermitianHolomorphicLineBundle.{0,0} (m + 1) X)
  (hL : IsSourceSmoothHermitianMetric L) (s : HolomorphicSections (n := m + 1) L.Fiber)
  (hdense : ∀ U : Set X, IsOpen U → U.Nonempty → ∃ y ∈ U, s y ≠ 0)

/-- Actual original weighted global current paired against the unchanged
global form gives the SAME physical equation's actual area integral.
The original local test, coefficients and support are outputs. -/
theorem exists_nativeSection_weighted_area_action
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X)
    (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hχc : IsCompact (tsupport χ)) (hχdom : tsupport χ ⊆ E.val.baseSet ∩ c.val.source)
    (γ : SmoothRealForm (m + 1) X (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    let P := nativeSectionFramePresentation L hL s hdense E
    ∃ η : TestForm (P.chartDomain c) (Module.finrank ℝ (ComplexModel (m + 1)) - 2),
      (∀ z, η z = c.val.target.indicator (fun y => χ (c.val.symm y) • γ.coeff c y) z) ∧
      tsupport (η : ComplexModel (m + 1) →
        RealForm (m + 1) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) ⊆ c.val '' tsupport χ ∧
      pairingLM
        (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
          (nativeSectionDivisorMetric L hL s hdense)) (smulFun χ hχ γ) =
        ∫ x, divisorShuffleDensity
            (P.chartG c ⟨0, by change 0 < 1; omega⟩)
            (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η x
          ∂(μHE[2 * (m + 1) - 2] : Measure (ComplexModel (m + 1))) := by
  let P := nativeSectionFramePresentation L hL s hdense E
  let T := integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
    (nativeSectionDivisorMetric L hL s hdense)
  obtain ⟨η, hη, hs, hpair⟩ := exists_testForm_with_pairing T γ c χ hχ hχc
    (fun _ hx => (hχdom hx).2)
  have hηdom : tsupport (η : ComplexModel (m + 1) →
      RealForm (m + 1) (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) ⊆ P.chartDomain c := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hs hz
    have hxdom := hχdom hx
    change c.val x ∈ c.val.target ∩ c.val.symm ⁻¹' E.val.baseSet
    refine ⟨c.val.map_source hxdom.2, ?_⟩
    rw [mem_preimage, c.val.left_inv hxdom.2]
    exact hxdom.1
  let η' : TestForm (P.chartDomain c) (Module.finrank ℝ (ComplexModel (m + 1)) - 2) :=
    ⟨η, η.contDiff, η.hasCompactSupport, hηdom⟩
  have hext : (TestFunction.monoCLM ℝ η' : TestForm (chartTarget c)
      (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) = η := by
    ext z
    rw [testForm_inclusion_apply (P.chartDomain_le c) η']
    rfl
  have hact : pairingLM T (smulFun χ hχ γ) =
      T.restrictChart c (P.chartDomain_le c) η' := by
    rw [hpair]
    change T.inChart c η = T.inChart c (TestFunction.monoCLM ℝ η')
    rw [hext]
  refine ⟨η', hη, hs, ?_⟩
  exact hact.trans (nativeSectionFrameCurrent_area_action L hL s hdense E c η')

/-- An actual weight supported where the SAME physical section is nonzero
has zero pairing with its complete original integration current. -/
theorem nativeSection_weighted_pairing_eq_zero_of_nonzero
    (E : AtlasFrame L) (c : ComplexChart (m + 1) X)
    (χ : X → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hχc : IsCompact (tsupport χ)) (hχdom : tsupport χ ⊆ E.val.baseSet ∩ c.val.source)
    (hne : ∀ x ∈ tsupport χ, s x ≠ 0)
    (γ : SmoothRealForm (m + 1) X (Module.finrank ℝ (ComplexModel (m + 1)) - 2)) :
    pairingLM
      (integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
        (nativeSectionDivisorMetric L hL s hdense)) (smulFun χ hχ γ) = 0 := by
  classical
  let P := nativeSectionFramePresentation L hL s hdense E
  obtain ⟨η, _hη, hs, hread⟩ :=
    exists_nativeSection_weighted_area_action L hL s hdense E c χ hχ hχc hχdom γ
  rw [hread]
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hzR : z ∈ DivisorRegularLocus.regularLocus
      (P.chartG c ⟨0, by change 0 < 1; omega⟩)
  · have hη0 : η z = 0 := by
      by_cases hzS : z ∈ tsupport (η : ComplexModel (m + 1) →
          RealForm (m + 1) (Module.finrank ℝ (ComplexModel (m + 1)) - 2))
      · obtain ⟨x, hx, rfl⟩ := hs hzS
        have hxdom := hχdom hx
        have hg0 := DivisorRegularLocus.eq_zero_of_mem_regularLocus hzR
        have hcoef : sectionCoefficient L.Fiber E.val s x = 0 := by
          simpa only [P, LocalPresentation.chartG, nativeSectionFramePresentation,
            c.val.left_inv hxdom.2] using hg0
        have hs0 : s x = 0 := by
          let := E.property
          apply (E.val.linearEquivAt ℂ x hxdom.1).injective
          exact hcoef.trans (map_zero _).symm
        exact (hne x hx hs0).elim
      · exact image_eq_zero_of_notMem_tsupport hzS
    simp [divisorShuffleDensity, hη0]
  · apply divisorShuffleDensity_eq_zero_off_regular
    exact fun hz => hzR hz.1

end SGPT.Projective.NumEq.CompleteIntersections
