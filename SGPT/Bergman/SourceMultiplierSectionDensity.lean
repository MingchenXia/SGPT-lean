import SGPT.Bergman.SourceTensorIdealGlobalSections
import SGPT.Bergman.SourceCompactHolomorphicSections
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

/-!
# MultiplierSectionDensity

The weighted density `|s|² e^{-cφ}` of a section and its expression in local frames.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.MultiplierSectionsDraft

open Bundle Set Filter TopologicalSpace CategoryTheory Opposite TensorProduct MeasureTheory Metric
open scoped Manifold ContDiff Topology TensorProduct ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
  SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualIdealPresheaf

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (V : X → Type) [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℂ (V x)]
  [TopologicalSpace (TotalSpace ℂ V)] [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))]

/-- The actual ORIGINAL all-section point density, retaining every pole and zero-times-infinity convention. -/
def originalSectionDensity (φ : X → EReal) (c : ℝ)
    (s : HolomorphicSections (n := n) V) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight c (φ x)

omit [IsComplexManifold n X] [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Exact SAME-frame whole-fiber readback, with the SAME original potential and exponent c. -/
theorem originalSectionDensity_frame (φ : X → EReal) (c : ℝ)
    (e : OriginalFrame V) (s : HolomorphicSections (n := n) V) {x : X} (hx : x ∈ e.val.baseSet) :
    originalSectionDensity (n := n) V φ c s x =
      ENNReal.ofReal (frameNorm V e.val x ^ 2) *
        multiplierDensity φ c (sectionCoefficient V e.val s) x := by
  let := e.property
  rw [originalSectionDensity, norm_eq_coefficient_mul_frameNorm V e.val s hx, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  simp only [multiplierDensity, mul_assoc]
  exact mul_left_comm _ _ _

omit [IsComplexManifold n X] [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Literal source scaled-potential readback at ALL degrees, including k=0 and poles. -/
theorem originalSectionDensity_scaled_one (φ : X → EReal) (k : ℕ)
    (s : HolomorphicSections (n := n) V) :
    originalSectionDensity (n := n) V (fun x => ((k : ℝ) : EReal) * φ x) 1 s =
      originalSectionDensity (n := n) V φ k s := by
  funext x
  simp [originalSectionDensity, multiplierWeight]

omit [IsComplexManifold n X] in
/-- Every original local coefficient extension has the SAME genuine full coefficient germ. -/
theorem localFrameCoefficient_extension_eventually (e : OriginalFrame V)
    (s : HolomorphicSections (n := n) V) {x : X} (hx : x ∈ e.val.baseSet) :
    sectionExtension (frameOpen V (⊤ : Opens X) e)
      (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s)) =ᶠ[𝓝 x]
        sectionCoefficient V e.val s := by
  filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
  rw [sectionExtension_apply (frameOpen V (⊤ : Opens X) e)
    (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s)) y
    (show y ∈ frameOpen V (⊤ : Opens X) e from ⟨Set.mem_univ y, hy⟩)]
  rfl

omit [IsComplexManifold n X] in
/-- The genuine coefficient of every native holomorphic section is holomorphic near every original frame point. -/
theorem originalSectionCoefficient_holomorphicAt (e : OriginalFrame V)
    (s : HolomorphicSections (n := n) V) {x : X} (hx : x ∈ e.val.baseSet) :
    HolomorphicAt n (sectionCoefficient V e.val s) x :=
  HolomorphicAt.congr (sectionExtension_holomorphicAt
    (frameOpen V (⊤ : Opens X) e)
    (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s))
    x ⟨Set.mem_univ x, hx⟩) (localFrameCoefficient_extension_eventually (n := n) V e s hx)

/-- BOTH whole ORIGINAL stalk directions use the SAME true full coefficient representative. -/
theorem localFrameCoefficientGerm_mem_iff_originalCoefficient (A : GermIdeal n X)
    (hA : A.IsCoherent) (e : OriginalFrame V) (s : HolomorphicSections (n := n) V)
    {x : X} (hx : x ∈ e.val.baseSet) :
    localFrameCoefficientGerm (n := n) V (⊤ : Opens X) e
        (globalSectionSheafEquiv (n := n) V s) ⟨x, Set.mem_univ x⟩ hx ∈ actualWholeSheafStalkIdeal A x ↔
      A.mem x (sectionCoefficient V e.val s) := by
  have hg := actualOriginalFunctionGerm_eq_section
    (frameOpen V (⊤ : Opens X) e) x ⟨Set.mem_univ x, hx⟩
    (localFrameCoefficient (n := n) V ⊤ e (globalSectionSheafEquiv (n := n) V s))
    (sectionCoefficient V e.val s) (originalSectionCoefficient_holomorphicAt (n := n) V e s hx)
    (localFrameCoefficient_extension_eventually (n := n) V e s hx)
  change (actualComplexStructureSheaf (n := n) X).presheaf.germ
    (frameOpen V (⊤ : Opens X) e) x ⟨Set.mem_univ x, hx⟩ _ ∈ _ ↔ _
  rw [← hg]
  exact originalFunctionGerm_mem_whole_iff A hA x _ _

/-- ALL original full H0 ideal sections are exactly the SAME all-point preferred coefficient multiplier conditions. -/
theorem fullHolomorphicIdealSections_iff_preferredCoefficient (A : GermIdeal n X)
    (hA : A.IsCoherent) (s : HolomorphicSections (n := n) V) :
    s ∈ fullHolomorphicIdealSections (n := n) V A ↔
      ∀ x : X, A.mem x (sectionCoefficient V (preferredOriginalFrame V x).val s) := by
  change globalSectionSheafEquiv (n := n) V s ∈ idealOpenSectionSubmodule (n := n) V A ⊤ ↔ _
  rw [mem_idealOpenSectionSubmodule_iff_preferred]
  constructor
  · intro h x
    exact (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) V A hA
      (preferredOriginalFrame V x) s (mem_baseSet_trivializationAt ℂ V x)).mp (h ⟨x, Set.mem_univ x⟩)
  · intro h x
    exact (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) V A hA
      (preferredOriginalFrame V x.val) s (mem_baseSet_trivializationAt ℂ V x.val)).mpr (h x.val)

variable [MeasurableSpace X] [BorelSpace X] [ContinuousFiberNorm V]

omit [TopologicalSpace X] [BorelSpace X] in
/-- Every genuine original multiplier weight is measurable, with c=0 handled literally. -/
theorem measurable_originalMultiplierWeight {φ : X → EReal} (hφ : Measurable φ) (c : ℝ) :
    Measurable (fun x => multiplierWeight c (φ x)) := by
  by_cases hc : c = 0
  · subst c
    simp only [multiplierWeight, EReal.coe_zero, zero_mul, neg_zero, EReal.exp_zero]
    exact measurable_const
  · exact EReal.measurable_exp.comp ((continuous_eReal_const_mul hc).measurable.comp hφ).neg

omit [IsComplexManifold n X] [∀ x, NormedSpace ℂ (V x)] [VectorBundle ℂ ℂ V]
  [ContMDiffVectorBundle ∞ ℂ V (𝓘(ℂ, ComplexModel n))] in
/-- Actual continuous Hermitian norm and actual measurable phi produce the full extended density, even on poles. -/
theorem measurable_originalSectionDensity {φ : X → EReal} (hφ : Measurable φ)
    (c : ℝ) (s : HolomorphicSections (n := n) V) :
    Measurable (originalSectionDensity (n := n) V φ c s) :=
  (ENNReal.continuous_ofReal.comp ((sectionNormMap V s).continuous.pow 2)).measurable.mul
    (measurable_originalMultiplierWeight hφ c)

end SGPT.Bergman.MultiplierSectionsDraft
