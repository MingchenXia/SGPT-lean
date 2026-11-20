import SGPT.Bergman.SourceMultiplierSectionCompactMass

/-!
# MultiplierSectionGlobalMass

On a compact manifold, `s ∈ H⁰(X, E ⊗ I(kφ))` iff `∫_X |s|² e^{-kφ} dV < ∞`.

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

variable [MeasurableSpace X] [BorelSpace X] [ContinuousFiberNorm V]

/-- Compactness selects an actual finite cover of produced finite-mass neighborhoods. -/
theorem lintegral_lt_top_of_finite_open_neighborhoods [CompactSpace X]
    {μ : Measure X} {f : X → ℝ≥0∞} (hf : Measurable f)
    (hloc : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ (∫⁻ y in W, f y ∂μ) < ⊤) :
    (∫⁻ y, f y ∂μ) < ⊤ := by
  classical
  choose W hW hxW hfin using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => mem_iUnion.mpr ⟨x, hxW x⟩)
  have hb : (∫⁻ y, f y ∂μ) ≤ ∑ x ∈ t, ∫⁻ y in W x, f y ∂μ := by
    calc
      _ ≤ ∫⁻ y, ∑ x ∈ t, (W x).indicator f y ∂μ := by
        apply lintegral_mono
        intro y
        obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
        calc
          f y = (W x).indicator f y := (indicator_of_mem hy f).symm
          _ ≤ ∑ x ∈ t, (W x).indicator f y :=
            Finset.single_le_sum (f := fun x => (W x).indicator f y) (fun _ _ => zero_le) hx
      _ = _ := by
        rw [lintegral_finsetSum _ (fun x _ => hf.indicator (hW x).measurableSet)]
        exact Finset.sum_congr rfl (fun x _ => lintegral_indicator (hW x).measurableSet f)
  exact hb.trans_lt (ENNReal.sum_lt_top.mpr (fun x _ => hfin x))

/-- LITERAL all-original-stalk multiplier sections are exactly the genuine finite original phi-weighted
L2 sections on compact X, for SAME continuous metric and actual smooth positive volume. ALL degrees
including zero are retained. Coherence, measurability, both local integral bounds and the finite cover
are internally produced, with no desired integral/finiteness certificate. -/
theorem fullHolomorphicDegreeIdealSections_iff_finite_integral [CompactSpace X]
    (k : ℕ) {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (s : HolomorphicSections (n := n) V) {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    s ∈ fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) k φ) ↔
      (∫⁻ x, originalSectionDensity (n := n) V φ k s x ∂μ) < ⊤ := by
  let φk : X → EReal := fun x => ((k : ℝ) : EReal) * φ x
  have hφm : Measurable φ := hφ.1.upperSemicontinuous.measurable
  have hφkm : Measurable φk := by
    by_cases hk : k = 0
    · subst k
      simp only [φk, Nat.cast_zero, EReal.coe_zero, zero_mul]
      exact measurable_const
    · exact (continuous_eReal_const_mul (Nat.cast_ne_zero.mpr hk)).measurable.comp hφm
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) V _
    (sourceDegreeMultiplierIdeal_isCoherent k hφ) s,
    ← originalSectionDensity_scaled_one (n := n) V φ k s]
  change (∀ x : X, (multiplierIdeal (n := n) 1 φk).mem x
    (sectionCoefficient V (preferredOriginalFrame V x).val s)) ↔
      (∫⁻ x, originalSectionDensity (n := n) V φk 1 s x ∂μ) < ⊤
  constructor
  · intro hs
    apply lintegral_lt_top_of_finite_open_neighborhoods
      (measurable_originalSectionDensity (n := n) V hφkm 1 s)
    intro x
    exact (originalSection_local_finite_iff (n := n) V hφkm one_pos s hμ x).mp (hs x)
  · intro hs x
    apply (originalSection_local_finite_iff (n := n) V hφkm one_pos s hμ x).mpr
    exact ⟨univ, isOpen_univ, mem_univ x, by simpa only [Measure.restrict_univ] using hs⟩

/-- The exact original theta-PSH source domain supplies every analytic hypothesis internally. -/
theorem fullHolomorphicThetaDegreeIdealSections_iff_finite_integral [CompactSpace X]
    {θ : SmoothRealForm n X 2} (k : ℕ) {φ : X → EReal} (hφ : IsThetaPshPotential θ φ)
    (s : HolomorphicSections (n := n) V) {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) :
    s ∈ fullHolomorphicIdealSections (n := n) V (sourceDegreeMultiplierIdeal (n := n) k φ) ↔
      (∫⁻ x, originalSectionDensity (n := n) V φ k s x ∂μ) < ⊤ :=
  fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n) V k hφ.quasiPshPotential s hμ

end SGPT.Bergman.MultiplierSectionsDraft
