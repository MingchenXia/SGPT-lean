import SGPT.Bergman.SourceGlobalWeightApproximation
import SGPT.Bergman.SourcePartialEnvelopeEverywhere
import SGPT.PSH.ThetaDecreasingNets
import SGPT.PSH.SourceTestCurveScalingProjection
import SGPT.Foundations.Analysis.Pending.KahlerVolumeChartAEEquivalence

/-! Universal consumers of the internally constructed fixed smooth pair.
The complete original-source route is in global-weight-approximation.tex.
No desired envelope equality, mass or convergence is an incoming certificate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.GlobalWeightApproximation

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeSameType SGPT.Bergman.PartialEnvelopeUniformBound
open SGPT.Bergman.PartialEnvelopeEverywhere SGPT.Bergman.PartialPOrder
open SGPT.Bergman.GlobalWeightSmoothApproximation SGPT.Bergman.PartialEquilibriumMeasure
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Literal theta+delta omega, without choosing a new potential representative. -/
def perturbedForm (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (δ : ℝ) : AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  nativeClosedFormToAtlas (atlasClosedFormToNative θ + δ • ω.form)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
theorem perturbedForm_genuine (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) φ := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [show atlasClosedFormToNative (perturbedForm θ ω δ) =
    atlasClosedFormToNative θ + δ • ω.form from sourceNativeAtlasForm_roundTrip _]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφ)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive hδ)

/-- Original positivity handles delta=0; the actual positive-background mass
polynomial produces positivity for every strictly positive delta. -/
theorem perturbedForm_positive (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure θ φ hφ univ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    0 < sourcePotentialNonPluripolarMeasure (perturbedForm θ ω δ) φ
      (perturbedForm_genuine ω hφ hδ) univ := by
  by_cases h0 : δ = 0
  · subst δ
    simpa only [perturbedForm, zero_smul, add_zero,
      sourceAtlasNativeForm_roundTrip] using hφpos
  · change DiagonalMass.HasPositivePotentialMass
      (atlasClosedFormToNative (perturbedForm θ ω δ)) φ _
    simpa only [perturbedForm, sourceNativeAtlasForm_roundTrip] using
      SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul ω
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp hφ) (lt_of_le_of_ne hδ (Ne.symm h0))

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- Actual semipositivity of (1-delta) omega puts EVERY perturbed-background
competitor into the SAME total background used to choose the sequences. -/
theorem perturbedForm_to_total (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η : M → EReal}
    {δ : ℝ} (hδ : δ ≤ 1)
    (hη : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) η) :
    (ofFixedModel n M).IsThetaPSH (totalForm θ ω) η := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  have h := LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential (perturbedForm θ ω δ) _).mp hη)
    (KahlerDomination.isSemipositive_smul ω.isSemipositive (sub_nonneg.mpr hδ))
  have heq : atlasClosedFormToNative (perturbedForm θ ω δ) + (1 - δ) • ω.form =
      atlasClosedFormToNative (totalForm θ ω) := by
    simp only [perturbedForm, totalForm, sourceNativeAtlasForm_roundTrip]
    module
  simpa only [heq] using h

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Compactness upgrades the pointwise monotone real approximation to one
stage dominating a genuine USC competitor after ANY positive finite shift. -/
theorem exists_stage_above_usc {η : M → EReal} (hη : UpperSemicontinuous η)
    {a : ℕ → M → ℝ} (ha : ∀ j, Continuous (a j)) (ham : Monotone a)
    {f : M → ℝ} (halim : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (f x)))
    (hηf : ∀ x, η x ≤ (f x : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∃ j, ∀ x, η x ≤ ((a j x + ε : ℝ) : EReal) := by
  let U : ℕ → Set M := fun j => {x | η x < ((a j x + ε : ℝ) : EReal)}
  have ho (j) : IsOpen (U j) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hx
    have hcont : ContinuousAt (fun y => a j y + ε) x := ((ha j).add continuous_const).continuousAt
    have hreal : r < a j x + ε := EReal.coe_lt_coe_iff.mp hr2
    filter_upwards [hη x (r : EReal) hr1,
      hcont.preimage_mem_nhds (Ioi_mem_nhds hreal)] with y hy1 hy2
    exact hy1.trans (EReal.coe_lt_coe_iff.mpr hy2)
  have hcover : (univ : Set M) ⊆ ⋃ j, U j := by
    intro x _
    have hlim : Tendsto (fun j => a j x + ε) atTop (𝓝 (f x + ε)) :=
      (halim x).add_const ε
    have hevent := hlim.eventually (Ioi_mem_nhds (show f x < f x + ε by linarith))
    obtain ⟨j, hj⟩ := hevent.exists
    exact mem_iUnion.mpr ⟨j, (hηf x).trans_lt (EReal.coe_lt_coe_iff.mpr hj)⟩
  have hd : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro x hx
      change η x < ((a _ x + ε : ℝ) : EReal) at hx ⊢
      exact hx.trans_le (EReal.coe_le_coe_iff.mpr (add_le_add (ham (le_max_left i j) x) (le_refl ε)))
    · intro x hx
      change η x < ((a _ x + ε : ℝ) : EReal) at hx ⊢
      exact hx.trans_le (EReal.coe_le_coe_iff.mpr (add_le_add (ham (le_max_right i j) x) (le_refl ε)))
  obtain ⟨j, hj⟩ := isCompact_univ.elim_directed_cover U ho hcover hd
  exact ⟨j, fun x => (hj (mem_univ x)).le⟩



omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- QE restriction uses the SAME pluripolar exceptional set. -/
theorem partialEnvelope_univ_le {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (φ : M → EReal) (K : Set M) (f : K → EReal) (g : M → EReal)
    (hgf : ∀ x : K, g x.val ≤ f x) :
    partialEnvelope θ φ univ (fun x => g x.val) ≤ partialEnvelope θ φ K f := by
  apply uscRegularization_le (upperSemicontinuous_partialEnvelope θ φ K f)
  intro x
  apply iSup_le
  intro v
  obtain ⟨S, hS, hvS⟩ := (partialObstacle_iff_exists_pluripolar _ _ _).mp v.property.2.1
  have hvK : partialObstacle (n := n) K f v.val := by
    apply (partialObstacle_iff_exists_pluripolar _ _ _).mpr
    exact ⟨S, hS, fun y hy => (hvS ⟨y.val, mem_univ _⟩ hy).trans (hgf y)⟩
  exact le_partialEnvelope v.property.1 hvK v.property.2.2 x

omit [MeasurableSpace M] [BorelSpace M] in
/-- Any original everywhere partial competitor is below the SAME fixed lower
obstacle; the actual uniform total-background bound handles X\K. -/
theorem everywhereCompetitor_le_lowerObstacle (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {δ : ℝ} (hδ : δ ≤ 1)
    (W : Weighted (n := n) (M := M)) {η : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) η)
    (hηK : ∀ x : W.carrier, η x.val ≤ W.erealWeight x) :
    ∀ x, η x ≤ (lowerObstacle θ ω W x : EReal) := by
  obtain ⟨_hlsc, _hbnd, hK, hoff⟩ := lowerObstacle_data ω θ W
  have hbound := le_uniformUpperBound (totalForm θ ω) W.nonPluripolar_carrier (weightNorm W)
    (perturbedForm_to_total ω hδ hη)
    (partialObstacle_mono (partialObstacle_of_forall hηK)
      (fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (weightNorm_bound W x)).2))
  intro x
  by_cases hx : x ∈ W.carrier
  · rw [hK ⟨x, hx⟩]
    exact hηK ⟨x, hx⟩
  · rw [hoff x hx]
    exact (hbound x).trans (EReal.coe_le_coe_iff.mpr
      ((le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)))

/-- Exact regularized-sup equality of the universal lower smooth sequence,
for EVERY positive reference in ANY original delta-background, same pair. -/
theorem increasing_global_regularized (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {δ : ℝ} (hδ : δ ≤ 1)
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (perturbedForm θ ω δ) φ hφ univ)
    (W : Weighted (n := n) (M := M))
    {a : ℕ → M → ℝ} (ha : ∀ j, Continuous (a j)) (ham : Monotone a)
    (hab : ∀ j x, a j x ≤ lowerObstacle θ ω W x)
    (halim : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (lowerObstacle θ ω W x))) :
    Monotone (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ
      (fun x => (a j x.val : EReal))) ∧
    uscRegularization (⨆ j, partialEnvelope (perturbedForm θ ω δ) φ univ
      (fun x => (a j x.val : EReal))) =
      partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight := by
  let T := perturbedForm θ ω δ
  let A := partialEnvelope T φ W.carrier W.erealWeight
  let G : ℕ → M → EReal := fun j => partialEnvelope T φ univ (fun x => (a j x.val : EReal))
  let S := uscRegularization (fun x => ⨆ j, G j x)
  have hmG : Monotone G := fun i j hij => partialEnvelope_mono_obstacle T φ univ
    (fun x => EReal.coe_le_coe_iff.mpr (ham hij x.val))
  have hloK := (lowerObstacle_data ω θ W).2.2.1
  have hGA (j) : G j ≤ A := partialEnvelope_univ_le φ W.carrier W.erealWeight
    (fun x => (a j x : EReal)) (fun x => by
      apply EReal.coe_le_coe_iff.mpr
      exact (hab j x.val).trans_eq (hloK x))
  have hSA : S ≤ A := uscRegularization_le (upperSemicontinuous_partialEnvelope _ _ _ _)
    (fun x => iSup_le fun j => hGA j x)
  have hAS : A ≤ S := by
    obtain ⟨L, U, hL, _hU⟩ := W.partialEnvelope_weight_bounds
    change partialEnvelope T φ W.carrier W.erealWeight ≤ S
    rw [(partialEnvelope_eq_everywhere ω hφ hφpos ⟨L, hL⟩).1]
    apply uscRegularization_le (upperSemicontinuous_uscRegularization _)
    intro x
    apply iSup_le
    intro η
    have hηlow := everywhereCompetitor_le_lowerObstacle ω hδ W η.property.1 η.property.2.1
    have hηusc := ((isThetaPSH_iff_nativeThetaPotential T _).mp η.property.1).1.quasiPlurisubharmonic.upperSemicontinuous
    have hshift (ε : ℝ) (hε : 0 < ε) : η.val x ≤ S x + (ε : EReal) := by
      obtain ⟨j, hj⟩ := exists_stage_above_usc hηusc ha ham halim hηlow hε
      let χ : M → EReal := fun y => η.val y + ((-ε : ℝ) : EReal)
      have hχ := sourceThetaPSH_add_const η.property.1 (-ε)
      have hχa : ∀ y : (univ : Set M), χ y.val ≤ (a j y.val : EReal) := by
        intro y
        change η.val y.val + ((-ε : ℝ) : EReal) ≤ _
        have h := add_le_add (hj y.val) (le_refl ((-ε : ℝ) : EReal))
        simpa only [← EReal.coe_add, add_neg_cancel_right] using h
      have hord : SGPT.PSH.SingularityLE χ φ :=
        (show SGPT.PSH.SingularityLE χ η.val from ⟨-ε, fun _ _ => le_rfl⟩).trans η.property.2.2
      have hχG := le_partialEnvelope hχ (partialObstacle_of_forall hχa) hord x
      have hχS : χ x ≤ S x := hχG.trans
        ((le_iSup (fun j => G j x) j).trans (le_uscRegularization (fun y => ⨆ j, G j y) x))
      have h := add_le_add hχS (le_refl (ε : EReal))
      simpa only [χ, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h
    have heps : Tendsto (fun ε : ℝ => (ε : EReal)) (𝓝[>] 0) (𝓝 (0 : EReal)) :=
      (continuous_coe_real_ereal.tendsto 0).mono_left nhdsWithin_le_nhds
    have hadd : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (S x, (0 : EReal)) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    have hlim : Tendsto (fun ε : ℝ => S x + (ε : EReal)) (𝓝[>] 0) (𝓝 (S x)) := by
      simpa only [add_zero, Function.comp_def] using hadd.tendsto.comp (tendsto_const_nhds.prodMk_nhds heps)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (eventually_nhdsWithin_of_forall fun ε hε => hshift ε hε)
  refine ⟨hmG, ?_⟩
  change uscRegularization (⨆ j, G j) = A
  have hraw : (⨆ j, G j) = fun y => ⨆ j, G j y := by
    funext y
    simp only [iSup_apply]
  rw [hraw]
  exact le_antisymm hSA hAS



/-- Genuine original global outputs come from compact continuous real weights;
all finite obstacle witnesses and nonPP of X are manufactured internally. -/
theorem globalEnvelope_genuine (_ω : KahlerBackground n M)
    {T : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH T φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure T φ hφ univ)
    (W : Weighted (n := n) (M := M)) {g : M → ℝ} (hg : Continuous g) :
    (ofFixedModel n M).IsThetaPSH T (partialEnvelope T φ univ (fun x => (g x.val : EReal))) := by
  let c : C(M, ℝ) := ⟨g, hg⟩
  have hb (x : (univ : Set M)) : |g x.val| ≤ ‖c‖ := by
    simpa only [Real.norm_eq_abs, c, ContinuousMap.coe_mk] using ContinuousMap.norm_coe_le_norm c x.val
  have hX : (ofFixedModel n M).NonPluripolar univ :=
    fun h => W.nonPluripolar_carrier (h.mono (subset_univ _))
  exact (partialEnvelopes_genuine_bounded hφ hφpos hX
    ⟨-‖c‖, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hb x)).1⟩
    ⟨‖c‖, fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (hb x)).2⟩).choose_spec.choose_spec.1

/-- Actual original Kahler-volume AE readback of the proved increasing
regularized equality, using the existing native chart-Haar recovery theorem. -/
theorem increasing_global_ae (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {δ : ℝ} (hδ : δ ≤ 1)
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (perturbedForm θ ω δ) φ hφ univ)
    (W : Weighted (n := n) (M := M))
    {a : ℕ → M → ℝ} (ha : ∀ j, Continuous (a j)) (ham : Monotone a)
    (hab : ∀ j x, a j x ≤ lowerObstacle θ ω W x)
    (halim : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (lowerObstacle θ ω W x))) :
    Monotone (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (a j x.val : EReal))) ∧
    uscRegularization (⨆ j, partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (a j x.val : EReal))) =
      partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight ∧
    ∀ᵐ x ∂sourceKahlerVolume ω,
      Tendsto (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun y => (a j y.val : EReal)) x)
        atTop (𝓝 (partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight x)) := by
  let T := perturbedForm θ ω δ
  let G : ℕ → M → EReal := fun j => partialEnvelope T φ univ (fun x => (a j x.val : EReal))
  let A := partialEnvelope T φ W.carrier W.erealWeight
  obtain ⟨hm, heq⟩ := increasing_global_regularized ω hδ hφ hφpos W ha ham hab halim
  have hG (j) : (ofFixedModel n M).IsThetaPSH T (G j) := globalEnvelope_genuine ω hφ hφpos W (ha j)
  obtain ⟨L, U, hL, hU⟩ := W.partialEnvelope_weight_bounds
  have hA : (ofFixedModel n M).IsThetaPSH T A :=
    (partialEnvelopes_genuine_bounded hφ hφpos W.nonPluripolar_carrier ⟨L, hL⟩ ⟨U, hU⟩).choose_spec.choose_spec.1
  have hS : (ofFixedModel n M).IsThetaPSH T (uscRegularization (⨆ j, G j)) := heq.symm ▸ hA
  have hae : ∀ᵐ x ∂IntegrationCurrent.kahlerVolume ω, (⨆ j, G j x) = A x := by
    apply (KahlerVolumeChartAEEquivalence.ae_kahlerVolume_iff_forall_chart_ae ω
      (measurableSet_eq_fun (Measurable.iSup (fun j =>
        (upperSemicontinuous_partialEnvelope T φ univ _).measurable))
        (upperSemicontinuous_partialEnvelope T φ W.carrier W.erealWeight).measurable)).mpr
    intro e
    have h := IncreasingMixedRegularizedContinuity.ae_chartFunction_iSup_eq_of_genuine
      (fun j => (isThetaPSH_iff_nativeThetaPotential T _).mp (hG j)) hm
      ((isThetaPSH_iff_nativeThetaPotential T _).mp hS) e
    rw [heq] at h
    exact h
  refine ⟨hm, heq, ?_⟩
  rw [sourceKahlerVolume_eq_native]
  filter_upwards [hae] with x hx
  change Tendsto (fun j => G j x) atTop (𝓝 (A x))
  rw [← hx]
  exact tendsto_atTop_iSup (fun j k hjk => hm hjk x)

/-- Smooth global ordinary envelopes obey their literal everywhere obstacles.
The accepted EVERYWHERE candidate identity supplies the pointwise conclusion. -/
theorem globalEnvelope_le_continuous (ω : KahlerBackground n M)
    {T : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH T φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure T φ hφ univ)
    {g : M → ℝ} (hg : Continuous g) :
    partialEnvelope T φ univ (fun x => (g x.val : EReal)) ≤ fun x => (g x : EReal) := by
  let c : C(M, ℝ) := ⟨g, hg⟩
  have hlo (x : (univ : Set M)) : ((-‖c‖ : ℝ) : EReal) ≤ (g x.val : EReal) :=
    EReal.coe_le_coe_iff.mpr (abs_le.mp (show |g x.val| ≤ ‖c‖ from by
      simpa only [Real.norm_eq_abs, c, ContinuousMap.coe_mk] using ContinuousMap.norm_coe_le_norm c x.val)).1
  rw [(partialEnvelope_eq_everywhere ω hφ hφpos ⟨-‖c‖, hlo⟩).1]
  apply uscRegularization_le (continuous_coe_real_ereal.comp hg).upperSemicontinuous
  intro x
  exact iSup_le fun v => v.property.2.1 ⟨x, mem_univ x⟩

/-- Genuine decreasing infimum and GLOBAL-P competitor closure prove the
universal upper-sequence equality. No ordinary type of phi is inferred from
P-equivalence and no fixedness of the desired output is assumed. -/
theorem decreasing_global_original (ω : KahlerBackground n M)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {δ : ℝ} (hδ : δ ≤ 1)
    {φ : M → EReal} (hφ : (ofFixedModel n M).IsThetaPSH (perturbedForm θ ω δ) φ)
    (hφpos : 0 < sourcePotentialNonPluripolarMeasure (perturbedForm θ ω δ) φ hφ univ)
    (W : Weighted (n := n) (M := M))
    {b : ℕ → M → ℝ} (hb : ∀ j, Continuous (b j)) (hbm : Antitone b)
    (hbu : ∀ j x, upperObstacle θ ω W x ≤ b j x)
    (hblim : ∀ x, Tendsto (fun j => b j x) atTop (𝓝 (upperObstacle θ ω W x))) :
    Antitone (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (b j x.val : EReal))) ∧
    (⨅ j, partialEnvelope (perturbedForm θ ω δ) φ univ (fun x => (b j x.val : EReal))) =
      partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight ∧
    ∀ x, Tendsto (fun j => partialEnvelope (perturbedForm θ ω δ) φ univ (fun y => (b j y.val : EReal)) x)
      atTop (𝓝 (partialEnvelope (perturbedForm θ ω δ) φ W.carrier W.erealWeight x)) := by
  let T := perturbedForm θ ω δ
  let A := partialEnvelope T φ W.carrier W.erealWeight
  let G : ℕ → M → EReal := fun j => partialEnvelope T φ univ (fun x => (b j x.val : EReal))
  let L : M → EReal := fun x => ⨅ j, G j x
  have hmG : Antitone G := fun i j hij => partialEnvelope_mono_obstacle T φ univ
    (fun x => EReal.coe_le_coe_iff.mpr (hbm hij x.val))
  have hG (j) : (ofFixedModel n M).IsThetaPSH T (G j) := globalEnvelope_genuine ω hφ hφpos W (hb j)
  obtain ⟨lo, up, hlo, hup⟩ := W.partialEnvelope_weight_bounds
  have hA : (ofFixedModel n M).IsThetaPSH T A :=
    (partialEnvelopes_genuine_bounded hφ hφpos W.nonPluripolar_carrier ⟨lo, hlo⟩ ⟨up, hup⟩).choose_spec.choose_spec.1
  obtain ⟨_huusc, _hubnd, hucoe, huK⟩ := upperObstacle_data ω θ hbig W
  have hAG (j) : A ≤ G j := by
    apply uscRegularization_le (upperSemicontinuous_partialEnvelope T φ univ _)
    intro x
    apply iSup_le
    intro η
    have hηH : η.val ≤ unrestrictedEnvelope θ ω W := by
      rw [show unrestrictedEnvelope θ ω W = uscSup (fun v : {v : M → EReal //
        (ofFixedModel n M).IsThetaPSH (totalForm θ ω) v ∧
          partialObstacle (n := n) W.carrier W.erealWeight v} => v.val) from
        (unrestrictedPartial_eq_native (totalForm θ ω) W.carrier W.erealWeight).symm]
      intro y
      exact (le_iSup (fun v : {v : M → EReal //
        (ofFixedModel n M).IsThetaPSH (totalForm θ ω) v ∧
          partialObstacle (n := n) W.carrier W.erealWeight v} => v.val y)
          ⟨η.val, perturbedForm_to_total ω hδ η.property.1, η.property.2.1⟩).trans
        (le_uscRegularization (fun z => ⨆ v : {v : M → EReal //
          (ofFixedModel n M).IsThetaPSH (totalForm θ ω) v ∧
            partialObstacle (n := n) W.carrier W.erealWeight v}, v.val z) y)
    have hηb : ∀ y : (univ : Set M), η.val y.val ≤ (b j y.val : EReal) := by
      intro y
      calc
        η.val y.val ≤ unrestrictedEnvelope θ ω W y.val := hηH y.val
        _ ≤ (upperObstacle θ ω W y.val : EReal) := by rw [hucoe]; exact le_max_left _ _
        _ ≤ (b j y.val : EReal) := EReal.coe_le_coe_iff.mpr (hbu j y.val)
    exact le_partialEnvelope η.property.1 (partialObstacle_of_forall hηb) η.property.2.2 x
  have hAL : A ≤ L := fun x => le_iInf fun j => hAG j x
  obtain ⟨x₀, m, hx₀, _hmax⟩ := ((isThetaPSH_iff_nativeThetaPotential T A).mp hA).exists_max
  have hsup (j) : (m : EReal) ≤ ⨆ x, G j x :=
    hx₀.symm.le.trans ((hAG j x₀).trans (le_iSup (G j) x₀))
  have hLn := (SGPT.PSH.isThetaPshPotential_iInf_of_compact_antitone_iSup_lower_bound
    (fun j => (isThetaPSH_iff_nativeThetaPotential T _).mp (hG j))
    (fun x j k hjk => hmG hjk x) m hsup).1
  have hL : (ofFixedModel n M).IsThetaPSH T L := (isThetaPSH_iff_nativeThetaPotential T _).mpr hLn
  have hLu : L ≤ fun x => (upperObstacle θ ω W x : EReal) := by
    intro x
    have hlim := (continuous_coe_real_ereal.tendsto _).comp (hblim x)
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim (fun j =>
      (iInf_le (fun j => G j x) j).trans (globalEnvelope_le_continuous ω hφ hφpos (hb j) x))
  have hLK : partialObstacle (n := n) W.carrier W.erealWeight L := partialObstacle_of_le huK hLu
  let c : C(M, ℝ) := ⟨b 0, hb 0⟩
  have hGtype := partialEnvelope_same_singularity_type ω hφ hφpos
    (show (ofFixedModel n M).NonPluripolar univ from
      fun h => W.nonPluripolar_carrier (h.mono (subset_univ _)))
    (fun x : (univ : Set M) => b 0 x.val)
    ⟨‖c‖, fun x => by simpa only [Real.norm_eq_abs, c, ContinuousMap.coe_mk] using ContinuousMap.norm_coe_le_norm c x.val⟩
  have hord : SGPT.PSH.SingularityLE L (sourceSingularityEnvelope T φ) :=
    (MoreSingularOn.of_le fun x _ => iInf_le (fun j => G j x) 0).trans hGtype.1
  have hLP := GlobalPComparison.sourcePOrder_of_moreSingular ω hLn.quasiPshPotential
    ((isThetaPSH_iff_nativeThetaPotential T _).mp (sourceOrdinaryEnvelope_genuine hφ)).quasiPshPotential hord
  have hPφ := GlobalPComparison.sourcePEquivalent_singularityEnvelope ω
    (atlasClosedFormToNative T) ((isThetaPSH_iff_nativeThetaPotential T φ).mp hφ) hφpos
  have hLφ : GlobalPComparison.sourcePOrder (n := n) L φ :=
    GlobalPComparison.sourcePOrder_trans ω hLP (by
      simpa only [sourceSingularityEnvelope_eq_native] using hPφ.2)
  have hLA : L ≤ A := by
    change L ≤ partialEnvelope T φ W.carrier W.erealWeight
    rw [(partialEnvelope_globalP_full_descriptions ω hφ hφpos ⟨lo, hlo⟩).1]
    intro x
    exact (le_iSup (fun v : partialPCompetitors T φ W.carrier W.erealWeight => v.val x)
      ⟨L, hL, hLK, hLφ⟩).trans (le_uscRegularization
        (fun y => ⨆ v : partialPCompetitors T φ W.carrier W.erealWeight, v.val y) x)
  have heq : (⨅ j, G j) = A := by
    funext x
    simpa only [iInf_apply] using congrFun (le_antisymm hLA hAL) x
  refine ⟨hmG, heq, ?_⟩
  intro x
  have hx : (⨅ j, G j x) = A x := by simpa only [iInf_apply] using congrFun heq x
  change Tendsto (fun j => G j x) atTop (𝓝 (A x))
  rw [← hx]
  exact tendsto_atTop_iInf (fun j k hjk => hmG hjk x)

end SGPT.Bergman.GlobalWeightApproximation
