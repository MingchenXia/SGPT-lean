import SGPT.Trace.BertiniResidueCoordinates

/-!+# Actual conormal division and Fatou for the original weighted sections

This uses the derived nonzero original conormal derivative and the actual
(n-1)-dimensional patch Lebesgue measure. The vector being divided remains in
the original native bundle; identifying it with a canonical-bundle adjunction
residue and proving the global source Hodge normalization is still separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E : HermitianHolomorphicLineBundle n X) {r : ℕ}
  {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  (S : Fin r → HolomorphicSections (n := n) E.Fiber)
  (F : A × B → X) (J : A × B → ℂ) (φ : X → EReal)

/-- Literal original vector norm after division by the specified actual
normal derivative, with the same original extended potential. -/
def nativeMovingNormalDivisionDensity (p : A × (Fin r → ℂ)) (b : B) : ℝ≥0∞ :=
  ENNReal.ofReal (‖(J (p.1, b))⁻¹ • nativeSectionCombination E S p.2 (F (p.1, b))‖ ^ 2) *
    multiplierWeight 1 (φ (F (p.1, b)))

/-- Joint lower semicontinuity of the actual normal-divided original density.
Continuity/nonvanishing are geometric inputs for a general moving map; the
genuine slice theorem below PRODUCES them for its actual conormal derivative. -/
theorem lowerSemicontinuous_nativeMovingNormalDivisionDensity
    (hF : Continuous F) (hJ : Continuous J) (hJ0 : ∀ q, J q ≠ 0)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun q : (A × (Fin r → ℂ)) × B =>
      nativeMovingNormalDivisionDensity E S F J φ q.1 q.2) := by
  have harg : Continuous (fun q : (A × (Fin r → ℂ)) × B => (q.1.1, q.2)) :=
    (continuous_fst.fst).prodMk continuous_snd
  have hpoint := hF.comp harg
  have hnorm : Continuous (fun q : (A × (Fin r → ℂ)) × B =>
      ‖nativeSectionCombination E S q.1.2 (F (q.1.1, q.2))‖) :=
    (continuous_nativeSectionCombinationNorm E S).comp
      ((continuous_fst.snd).prodMk hpoint)
  have hden : Continuous (fun q : (A × (Fin r → ℂ)) × B => ‖J (q.1.1, q.2)‖⁻¹) :=
    (hJ.comp harg).norm.inv₀ (fun q => norm_ne_zero_iff.mpr (hJ0 (q.1.1, q.2)))
  have hdiv : Continuous (fun q : (A × (Fin r → ℂ)) × B =>
      ‖(J (q.1.1, q.2))⁻¹ • nativeSectionCombination E S q.1.2 (F (q.1.1, q.2))‖) := by
    convert hden.mul hnorm using 1
    funext q
    simp only [norm_smul, norm_inv, Pi.mul_apply]
  have hweight := (lowerSemicontinuous_originalMultiplierWeight hφ).comp hpoint
  intro q
  exact SGPT.PSH.DirImg2.lowerSemicontinuousAt_mul
    ((ENNReal.continuous_ofReal.comp (hdiv.pow 2)).lowerSemicontinuous q) (hweight q)

/-- Actual Fatou for the extended normal-divided native section integral. -/
theorem lowerSemicontinuous_nativeMovingNormalDivisionMass
    [FirstCountableTopology A] [MeasurableSpace B] [BorelSpace B]
    (μ : Measure B) (hF : Continuous F) (hJ : Continuous J) (hJ0 : ∀ q, J q ≠ 0)
    (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) :
    LowerSemicontinuous (fun p : A × (Fin r → ℂ) =>
      ∫⁻ b, nativeMovingNormalDivisionDensity E S F J φ p b ∂μ) := by
  have hl := lowerSemicontinuous_nativeMovingNormalDivisionDensity E S F J φ hF hJ hJ0 hφ
  apply lowerSemicontinuousOn_univ_iff.mp
  apply SGPT.BBJ.lowerSemicontinuousOn_lintegral μ
    (fun b p => nativeMovingNormalDivisionDensity E S F J φ p b) Set.univ
  · intro p
    exact (hl.comp (continuous_const.prodMk continuous_id)).measurable
  · intro b
    exact (hl.comp (continuous_id.prodMk continuous_const)).lowerSemicontinuousOn Set.univ

namespace SliceChart

variable {d N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y]
  {p : Y → SGPT.Projective.ComplexProjectiveSpace N} {φ : Y → EReal}
  (c : SliceChart (d + 1) p φ)

/-- The actual original normal derivative in the genuine n-1 coordinates. -/
def tangentNormalDenominator (q : (ball c.ζ₀ c.r) × c.tangentPatch) : ℂ :=
  c.normalDenominator (q.1, ⟨c.tangentLift q.2.val, q.2.property⟩)

theorem tangentNormalDenominator_ne_zero
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) : c.tangentNormalDenominator q ≠ 0 :=
  c.normalDenominator_ne_zero hp _

theorem continuous_tangentNormalDenominator
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p) :
    Continuous c.tangentNormalDenominator := by
  have hl : Continuous (fun b : c.tangentPatch =>
      (⟨c.tangentLift b.val, b.property⟩ : ball c.z₀ c.r)) :=
    (c.continuous_tangentLift.comp continuous_subtype_val).subtype_mk _
  have hpair : Continuous (fun q : (ball c.ζ₀ c.r) × c.tangentPatch =>
      (q.1, (⟨c.tangentLift q.2.val, q.2.property⟩ : ball c.z₀ c.r))) :=
    continuous_fst.prodMk (hl.comp continuous_snd)
  exact Continuous.comp
    (g := c.normalDenominator)
    (f := fun q : (ball c.ζ₀ c.r) × c.tangentPatch =>
      (q.1, (⟨c.tangentLift q.2.val, q.2.property⟩ : ball c.z₀ c.r)))
    (c.continuous_normalDenominator hp) hpair

/-- Exact original-fibre cancellation of the PRODUCED conormal denominator.
The output remains an actual vector in E, not an assumed residue-bundle map. -/
theorem tangentNormalDivision_cancel
    (E : HermitianHolomorphicLineBundle (d + 1) Y) {r : ℕ}
    (S : Fin r → HolomorphicSections (n := d + 1) E.Fiber)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (q : (ball c.ζ₀ c.r) × c.tangentPatch) (v : Fin r → ℂ) :
    c.tangentNormalDenominator q •
        ((c.tangentNormalDenominator q)⁻¹ • nativeSectionCombination E S v (c.tangentPoint q)) =
      nativeSectionCombination E S v (c.tangentPoint q) :=
  smul_inv_smul₀ (c.tangentNormalDenominator_ne_zero hp q) _

/-- Joint lower semicontinuity of the ACTUAL conormal-divided native norm
with the actual original weight and genuine n-1-dimensional Lebesgue measure.
There is no incoming metric-lsc, normal-nonvanishing or frame certificate. -/
theorem lowerSemicontinuous_nativeTangentNormalDivisionMass
    (E : HermitianHolomorphicLineBundle (d + 1) Y) {r : ℕ}
    (S : Fin r → HolomorphicSections (n := d + 1) E.Fiber)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hφ : ManifoldQuasiPlurisubharmonic (n := d + 1) φ) :
    LowerSemicontinuous (fun q : (ball c.ζ₀ c.r) × (Fin r → ℂ) =>
      ∫⁻ b, nativeMovingNormalDivisionDensity E S c.tangentPoint c.tangentNormalDenominator φ q b
        ∂c.tangentPatchVolume) :=
  lowerSemicontinuous_nativeMovingNormalDivisionMass E S c.tangentPoint c.tangentNormalDenominator φ
    c.tangentPatchVolume c.continuous_tangentPoint (c.continuous_tangentNormalDenominator hp)
    (c.tangentNormalDenominator_ne_zero hp) hφ

end SliceChart

end SGPT.Trace.Bertini
