import SGPT.Bergman.SourceUniversalEnvelopeApproximation

/-! Both ACTUAL original real partial equilibrium energy limits for the SAME
universal smooth pair. All approximation and finiteness are produced.
Complete proof precedes this file in global-weight-approximation.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.GlobalWeightApproximation

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeIComparison
open SGPT.Bergman.PartialEquilibriumEnergy SGPT.Bergman.GlobalWeightSmoothApproximation
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The SAME smooth global weight as an original continuous weight on X. -/
def globalContinuousWeight (g : M → ℝ) (hg : Continuous g) : C((univ : Set M), ℝ) :=
  ⟨fun x => g x.val, hg.comp continuous_subtype_val⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The original nonPP subset internally certifies nonPP of X. -/
theorem wholeSpace_nonPluripolar (W : Weighted (n := n) (M := M)) :
    (ofFixedModel n M).NonPluripolar univ :=
  fun h => W.nonPluripolar_carrier (h.mono (subset_univ _))

/-- BOTH genuine real energy limits, deduced by evaluating the already
universal ordinary approximation at the ACTUAL positive PIphi reference.
This stronger derived consumer needs no I-good algebra or new source I-variant. -/
theorem fixed_pair_energy_limits (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    (W : Weighted (n := n) (M := M))
    {a b : ℕ → M → ℝ} (ha : ∀ j, Continuous (a j)) (hb : ∀ j, Continuous (b j))
    (ham : Monotone a) (hbm : Antitone b)
    (hab : ∀ j x, a j x ≤ lowerObstacle θ ω W x)
    (hbu : ∀ j x, upperObstacle θ ω W x ≤ b j x)
    (halim : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (lowerObstacle θ ω W x)))
    (hblim : ∀ x, Tendsto (fun j => b j x) atTop (𝓝 (upperObstacle θ ω W x))) :
    Tendsto (fun j => partialEquilibriumEnergy ω hφ hφpos isClosed_univ
      (wholeSpace_nonPluripolar W) (globalContinuousWeight (a j) (ha j))) atTop
      (𝓝 (partialEquilibriumEnergy ω hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight)) ∧
    Tendsto (fun j => partialEquilibriumEnergy ω hφ hφpos isClosed_univ
      (wholeSpace_nonPluripolar W) (globalContinuousWeight (b j) (hb j))) atTop
      (𝓝 (partialEquilibriumEnergy ω hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight)) := by
  let Q := sourceIEnvelope θ φ
  let hQmodel : SourceModelPotential θ Q := iEnvelope_model_of_positive ω hφ hφpos
  have hQ := hQmodel.thetaPSH
  have hQpos : 0 < sourcePotentialNonPluripolarMeasure θ Q hQ univ := hQmodel.choose_spec.2
  have hzero : perturbedForm θ ω 0 = θ := by
    simp only [perturbedForm, zero_smul, add_zero, sourceAtlasNativeForm_roundTrip]
  have hQ0 : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω 0) Q := hzero.symm ▸ hQ
  have hQ0pos : 0 < sourcePotentialNonPluripolarMeasure (perturbedForm θ ω 0) Q hQ0 univ := by
    simpa only [hzero] using hQpos
  have hi := increasing_global_ae ω (θ := θ) (δ := 0) zero_le_one hQ0 hQ0pos W ha ham hab halim
  have hd := decreasing_global_original ω hbig (δ := 0) zero_le_one hQ0 hQ0pos W hb hbm hbu hblim
  simp only [hzero] at hi hd
  dsimp only [Q] at hi hd
  simp_rw [← partialIEnvelope_eq_partialEnvelope_iEnvelope hφ] at hi hd
  have hfinite {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
      (v : C(K, ℝ)) : SourceRelativeFiniteEnergy θ Q
        (partialIEnvelope θ φ K (fun x => (v x : EReal))) hQmodel := by
    apply (sourceRelativeFiniteEnergy_iff_native θ Q _ hQmodel).mpr
    exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity ω
      ((sourceRelativeEInfinity_iff_native θ Q _).mp
        (partialIEnvelope_eInfinity_continuous ω hφ hφpos hKc hK v))
  have hread {K : Set M} (hKc : IsClosed K) (hK : (ofFixedModel n M).NonPluripolar K)
      (v : C(K, ℝ)) :
      (sourceRelativeEnergy θ Q (partialIEnvelope θ φ K (fun x => (v x : EReal))) hQmodel).toReal =
        partialEquilibriumEnergy ω hφ hφpos hKc hK v := by
    rw [← partialEquilibriumEnergy_coe_eq_extended ω hφ hφpos hKc hK v]
    exact EReal.toReal_coe _
  have htarget := hfinite W.isClosed_carrier W.nonPluripolar_carrier W.weight
  have hia := fun j => hfinite isClosed_univ (wholeSpace_nonPluripolar W)
    (globalContinuousWeight (a j) (ha j))
  have hib := fun j => hfinite isClosed_univ (wholeSpace_nonPluripolar W)
    (globalContinuousWeight (b j) (hb j))
  have hEi := sourceRelativeFiniteEnergy_increasing_ae_net ω hia htarget
    (fun x i j hij => hi.1 hij x) hi.2.2
  have hEd := sourceRelativeFiniteEnergy_decreasing_net ω hib htarget
    (fun x i j hij => hd.1 hij x) (by
      funext x
      have h := congrFun hd.2.1 x
      change partialIEnvelope θ φ W.carrier W.erealWeight x =
        ⨅ j, partialIEnvelope θ φ univ (fun y => (b j y.val : EReal)) x
      simpa only [iInf_apply] using h.symm)
  have hreadA := fun j => hread isClosed_univ (wholeSpace_nonPluripolar W)
    (globalContinuousWeight (a j) (ha j))
  have hreadB := fun j => hread isClosed_univ (wholeSpace_nonPluripolar W)
    (globalContinuousWeight (b j) (hb j))
  have hreadT := hread W.isClosed_carrier W.nonPluripolar_carrier W.weight
  constructor
  · simpa only [hreadA, hreadT] using hEi.2
  · simpa only [hreadB, hreadT] using hEd.2



/-- WHOLE ORIGINAL lma:global_env_approx (Bergman 533-650). ONE internally
produced smooth pair with ONE fixed-data bound precedes EVERY positive
original reference and EVERY delta in [0,1]. Both actual original real energy
limits are retained for EVERY additionally original I-good reference. -/
theorem global_weight_approximation (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (W : Weighted (n := n) (M := M)) :
    ∃ (a b : ℕ → M → ℝ)
      (ha : ∀ j, ChartSmooth (n := n) (a j)) (hb : ∀ j, ChartSmooth (n := n) (b j)),
      Monotone a ∧ Antitone b ∧
      (∀ j x, |a j x| ≤ smoothPairBound θ ω W ∧ |b j x| ≤ smoothPairBound θ ω W) ∧
      (∀ (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ),
        0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        (Antitone (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (b j x.val : EReal))) ∧
          (⨅ j, partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (b j x.val : EReal))) =
            partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight ∧
          ∀ x, Tendsto (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun y => (b j y.val : EReal)) x)
            atTop (𝓝 (partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight x))) ∧
        (Monotone (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (a j x.val : EReal))) ∧
          uscRegularization (⨆ j, partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (a j x.val : EReal))) =
            partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight ∧
          ∀ᵐ x ∂sourceKahlerVolume ω,
            Tendsto (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun y => (a j y.val : EReal)) x)
              atTop (𝓝 (partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight x)))) ∧
      ∀ (φ : M → EReal) (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
        (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ),
        sourceIGood (n := n) φ →
        Tendsto (fun j => partialEquilibriumEnergy ω hφ hφpos isClosed_univ
          (wholeSpace_nonPluripolar W)
          (globalContinuousWeight (a j) (continuous_of_chartSmooth (ha j)))) atTop
          (𝓝 (partialEquilibriumEnergy ω hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight)) ∧
        Tendsto (fun j => partialEquilibriumEnergy ω hφ hφpos isClosed_univ
          (wholeSpace_nonPluripolar W)
          (globalContinuousWeight (b j) (continuous_of_chartSmooth (hb j)))) atTop
          (𝓝 (partialEquilibriumEnergy ω hφ hφpos W.isClosed_carrier W.nonPluripolar_carrier W.weight)) := by
  obtain ⟨a, b, ha, hb, ham, hbm, hbound, habu, halim, hblim⟩ := exists_fixed_smooth_pair ω θ hbig W
  have hac := fun j => continuous_of_chartSmooth (ha j)
  have hbc := fun j => continuous_of_chartSmooth (hb j)
  refine ⟨a, b, ha, hb, ham, hbm, hbound, ?_, ?_⟩
  · intro φ hφ hφpos δ hδ0 hδ1
    have hφT := perturbedForm_genuine ω hφ hδ0
    have hφTpos := perturbedForm_positive ω hφ hφpos hδ0
    exact ⟨decreasing_global_original ω hbig hδ1 hφT hφTpos W hbc hbm
        (fun j x => (habu j x).2) hblim,
      increasing_global_ae ω hδ1 hφT hφTpos W hac ham (fun j x => (habu j x).1) halim⟩
  · intro φ hφ hφpos _hgood
    exact fixed_pair_energy_limits ω hbig hφ hφpos W hac hbc ham hbm
      (fun j x => (habu j x).1) (fun j x => (habu j x).2) halim hblim

end SGPT.Bergman.GlobalWeightApproximation
