import SGPT.Bergman.SourceGlobalWeightSmoothApproximation
import SGPT.Bergman.SourceFiniteSemicontinuousObstacles
import SGPT.Bergman.SourcePartialEquilibriumMeasures
import SGPT.Bergman.SourcePartialIEnvelopeComparison
import SGPT.PSH.SourcePMassCharacterization

/-! The concrete fixed weighted-subset obstacles and the universal smooth pair.
Temporary imports above are exact frozen mothers compiled only under /tmp;
ROOT owns eventual canonical import placement. No mother body is copied here.
Complete mathematical route: global-weight-approximation.tex. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.GlobalWeightApproximation

open Set Filter MeasureTheory
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope SGPT.Bergman.PartialEnvelopeRetention
open SGPT.Bergman.PartialEnvelopeSameType SGPT.Bergman.PartialEnvelopeUniformBound
open SGPT.Bergman.GlobalWeightSmoothApproximation SGPT.Bergman.GlobalWeightFiniteObstacles
open SGPT.Bergman.PartialEquilibriumMeasure
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open scoped Topology ENNReal

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

abbrev Weighted := SGPT.Bergman.WeightedSubset.WeightedSubset n M

/-- The genuine original C0 norm, with compactness of the SAME closed subtype
manufactured internally. No separate norm or boundedness witness is supplied. -/
def weightNorm (W : Weighted (n := n) (M := M)) : ℝ := by
  letI : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  exact ‖W.weight‖

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
theorem weightNorm_nonneg (W : Weighted (n := n) (M := M)) : 0 ≤ weightNorm W := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  change 0 ≤ ‖W.weight‖
  exact norm_nonneg W.weight

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
theorem weightNorm_bound (W : Weighted (n := n) (M := M)) (x : W.carrier) :
    |W.weight x| ≤ weightNorm W := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  simpa only [weightNorm, Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm W.weight x

/-- The fixed total background precedes all potential references and deltas. -/
def totalForm (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (ω : KahlerBackground n M) :
    AtlasClosedRealOneOneForm (ofFixedModel n M) :=
  nativeClosedFormToAtlas (atlasClosedFormToNative θ + ω.form)

/-- C(theta+omega,K,normv) is chosen before every reference and approximation. -/
def fixedUpperBound (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (W : Weighted (n := n) (M := M)) : ℝ :=
  uniformUpperBound (totalForm θ ω) W.nonPluripolar_carrier (weightNorm W)

/-- The final common bound has ONLY the norm, theta+omega and K as inputs. -/
def smoothPairBound (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (W : Weighted (n := n) (M := M)) : ℝ :=
  weightNorm W + fixedUpperBound θ ω W + 3

/-- The actual unrestricted roof, identified with ALL genuine original
QE-subtype candidates by the checked separate measure-lane dictionary. -/
def unrestrictedEnvelope (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (W : Weighted (n := n) (M := M)) : M → EReal :=
  rooftopEnvelope (atlasClosedFormToNative (totalForm θ ω)).val
    (extendedObstacle W.carrier W.erealWeight)

/-- The real lower cap equals the literal closed-subtype weight on K. -/
def lowerObstacle (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (W : Weighted (n := n) (M := M)) : M → ℝ :=
  fun x => (min (extendedObstacle W.carrier W.erealWeight x)
    ((max (fixedUpperBound θ ω W + 1) (weightNorm W) : ℝ) : EReal)).toReal

/-- The finite floor cuts actual negative-infinite poles before real readback. -/
def upperObstacle (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (ω : KahlerBackground n M) (W : Weighted (n := n) (M := M)) : M → ℝ :=
  fun x => (max (unrestrictedEnvelope θ ω W x)
    (((-weightNorm W - 1 : ℝ)) : EReal)).toReal

/-- All regularity, obstacle and uniform upper fields of the unrestricted
roof are internally produced from the original big class and weighted subset. -/
theorem unrestrictedEnvelope_data (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (W : Weighted (n := n) (M := M)) :
    (ofFixedModel n M).IsThetaPSH (totalForm θ ω) (unrestrictedEnvelope θ ω W) ∧
      partialObstacle (n := n) W.carrier W.erealWeight (unrestrictedEnvelope θ ω W) ∧
      unrestrictedEnvelope θ ω W ≤ fun _ => (fixedUpperBound θ ω W : EReal) := by
  let T := totalForm θ ω
  let R := weightNorm W
  let I := {v : M → EReal // (ofFixedModel n M).IsThetaPSH T v ∧
    partialObstacle (n := n) W.carrier W.erealWeight v}
  have hV := sourceMinimalEnvelope_thetaPSH ω θ hbig
  have hVT : (ofFixedModel n M).IsThetaPSH T (sourceMinimalEnvelope θ) := by
    apply (isThetaPSH_iff_nativeThetaPotential T _).mpr
    rw [show atlasClosedFormToNative T = atlasClosedFormToNative θ + ω.form from
      sourceNativeAtlasForm_roundTrip _]
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hV) ω.isSemipositive
  obtain ⟨A, hA⟩ := ((isThetaPSH_iff_nativeThetaPotential T _).mp hVT).exists_global_upper_bound
  let c : ℝ := -R - A
  let χ : M → EReal := fun x => sourceMinimalEnvelope θ x + (c : EReal)
  have hχ := sourceThetaPSH_add_const hVT c
  have hχK : partialObstacle (n := n) W.carrier W.erealWeight χ := by
    apply partialObstacle_of_forall
    intro x
    have hχbound : χ x.val ≤ ((-R : ℝ) : EReal) := by
      calc
        χ x.val ≤ (A : EReal) + (c : EReal) := add_le_add (hA x.val) le_rfl
        _ = ((-R : ℝ) : EReal) := by rw [← EReal.coe_add]; congr 1; dsimp only [c]; ring
    exact hχbound.trans (EReal.coe_le_coe_iff.mpr (abs_le.mp (weightNorm_bound W x)).1)
  let : Nonempty I := ⟨⟨χ, hχ, hχK⟩⟩
  have hweightU : ∀ x : W.carrier, W.erealWeight x ≤ (R : EReal) :=
    fun x => EReal.coe_le_coe_iff.mpr (abs_le.mp (weightNorm_bound W x)).2
  have hG := (boundedFamily_of_partialObstacle W.nonPluripolar_carrier ⟨R, hweightU⟩
    (fun v : I => v.property.1) (fun v => v.property.2)).choose_spec.2.2
  have hK := partialObstacle_uscSup W.nonPluripolar_carrier ⟨R, hweightU⟩
    (fun v : I => v.property.1) (fun v => v.property.2)
  have hbound : uscSup (fun v : I => v.val) ≤ fun _ => (fixedUpperBound θ ω W : EReal) := by
    apply uscRegularization_le upperSemicontinuous_const
    intro x
    apply iSup_le
    intro v
    exact le_uniformUpperBound T W.nonPluripolar_carrier R v.property.1
      (partialObstacle_mono v.property.2 hweightU) x
  have heq : unrestrictedEnvelope θ ω W = uscSup (fun v : I => v.val) :=
    (unrestrictedPartial_eq_native T W.carrier W.erealWeight).symm
  rw [heq]
  exact ⟨hG, hK, hbound⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- Fixed lower obstacle is real LSC, exactly the weight on K and the fixed
strictly-larger constant off K, with actual norm-only bounds. -/
theorem lowerObstacle_data (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (W : Weighted (n := n) (M := M)) :
    LowerSemicontinuous (lowerObstacle θ ω W) ∧
      (∀ x, -weightNorm W ≤ lowerObstacle θ ω W x ∧
        lowerObstacle θ ω W x ≤ max (fixedUpperBound θ ω W + 1) (weightNorm W)) ∧
      (∀ x : W.carrier, lowerObstacle θ ω W x.val = W.weight x) ∧
      ∀ x, x ∉ W.carrier → lowerObstacle θ ω W x = max (fixedUpperBound θ ω W + 1) (weightNorm W) := by
  classical
  let R := weightNorm W
  let M₀ := max (fixedUpperBound θ ω W + 1) R
  have hR0 := weightNorm_nonneg W
  have hL : ∀ x, ((-R : ℝ) : EReal) ≤ extendedObstacle W.carrier W.erealWeight x := by
    intro x
    by_cases hx : x ∈ W.carrier
    · simpa only [extendedObstacle, dif_pos hx, WeightedSubset.WeightedSubset.erealWeight, R] using
        EReal.coe_le_coe_iff.mpr (abs_le.mp (weightNorm_bound W ⟨x, hx⟩)).1
    · simp only [extendedObstacle, dif_neg hx, le_top]
  obtain ⟨g, hg, hcoe, hbnd⟩ := exists_real_lowerSemicontinuous_cap
    (extendedObstacle_lowerSemicontinuous W.isClosed_carrier W.weight) (-R) M₀
    ((neg_nonpos.mpr hR0).trans (hR0.trans (le_max_right _ _))) hL
  have heq : g = lowerObstacle θ ω W := by
    funext x
    have h := congrArg EReal.toReal (hcoe x)
    dsimp only [lowerObstacle, M₀, R, WeightedSubset.WeightedSubset.erealWeight] at h ⊢
    exact (EReal.toReal_coe (g x)).symm.trans h
  refine ⟨heq ▸ hg, heq ▸ hbnd, ?_, ?_⟩
  · intro x
    have hvM : W.erealWeight x ≤ (M₀ : EReal) :=
      (EReal.coe_le_coe_iff.mpr (abs_le.mp (weightNorm_bound W x)).2).trans
        (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
    change (min (extendedObstacle W.carrier W.erealWeight x.val) (M₀ : EReal)).toReal = _
    rw [extendedObstacle, dif_pos x.property, min_eq_left hvM]
    exact EReal.toReal_coe _
  · intro x hx
    change (min (extendedObstacle W.carrier W.erealWeight x) (M₀ : EReal)).toReal = _
    rw [extendedObstacle, dif_neg hx, min_top_left]
    exact EReal.toReal_coe _

/-- Fixed upper obstacle is real USC with actual finite bounds and the
original QE obstacle, produced before all references and deltas. -/
theorem upperObstacle_data (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (W : Weighted (n := n) (M := M)) :
    UpperSemicontinuous (upperObstacle θ ω W) ∧
      (∀ x, -weightNorm W - 1 ≤ upperObstacle θ ω W x ∧
        upperObstacle θ ω W x ≤ fixedUpperBound θ ω W) ∧
      (∀ x, (upperObstacle θ ω W x : EReal) =
        max (unrestrictedEnvelope θ ω W x) (((-weightNorm W - 1 : ℝ)) : EReal)) ∧
      partialObstacle (n := n) W.carrier W.erealWeight (fun x => (upperObstacle θ ω W x : EReal)) := by
  obtain ⟨hH, hHK, hHC⟩ := unrestrictedEnvelope_data ω θ hbig W
  have hR0 := weightNorm_nonneg W
  have hC0 := uniformUpperBound_pos (totalForm θ ω) W.nonPluripolar_carrier (weightNorm W)
  have hLC : -weightNorm W - 1 ≤ fixedUpperBound θ ω W := by
    change -weightNorm W - 1 ≤ uniformUpperBound (totalForm θ ω) W.nonPluripolar_carrier (weightNorm W)
    linarith
  obtain ⟨g, hg, hcoe, hbnd⟩ := exists_real_upperSemicontinuous_floor
    ((isThetaPSH_iff_nativeThetaPotential (totalForm θ ω) _).mp hH).1.quasiPlurisubharmonic.upperSemicontinuous
    (-weightNorm W - 1) (fixedUpperBound θ ω W) hLC hHC
  have heq : g = upperObstacle θ ω W := by
    funext x
    have h := congrArg EReal.toReal (hcoe x)
    simpa only [EReal.toReal_coe, upperObstacle] using h
  refine ⟨heq ▸ hg, heq ▸ hbnd, heq ▸ hcoe, ?_⟩
  obtain ⟨S, hS, hbound⟩ := (partialObstacle_iff_exists_pluripolar _ _ _).mp hHK
  apply (partialObstacle_iff_exists_pluripolar _ _ _).mpr
  refine ⟨S, hS, fun x hx => ?_⟩
  rw [← heq, hcoe x.val]
  exact max_le (hbound x hx) (EReal.coe_le_coe_iff.mpr (by
    have hv := (abs_le.mp (weightNorm_bound W x)).1
    linarith))




/-- ONE concrete smooth increasing/decreasing pair and ONE norm-only bound,
all chosen from original theta/omega/K/v BEFORE any phi or delta is supplied. -/
theorem exists_fixed_smooth_pair (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (W : Weighted (n := n) (M := M)) :
    ∃ a b : ℕ → M → ℝ,
      (∀ j, ChartSmooth (n := n) (a j)) ∧ (∀ j, ChartSmooth (n := n) (b j)) ∧
      Monotone a ∧ Antitone b ∧
      (∀ j x, |a j x| ≤ smoothPairBound θ ω W ∧ |b j x| ≤ smoothPairBound θ ω W) ∧
      (∀ j x, a j x ≤ lowerObstacle θ ω W x ∧ upperObstacle θ ω W x ≤ b j x) ∧
      (∀ x, Tendsto (fun j => a j x) atTop (𝓝 (lowerObstacle θ ω W x))) ∧
      ∀ x, Tendsto (fun j => b j x) atTop (𝓝 (upperObstacle θ ω W x)) := by
  obtain ⟨hlo, hlobnd, _hloK, _hloOff⟩ := lowerObstacle_data ω θ W
  obtain ⟨hup, hupbnd, _hupcoe, _hupK⟩ := upperObstacle_data ω θ hbig W
  obtain ⟨a, ha, ham, habnd, _haabs, halim⟩ :=
    exists_chartSmooth_monotone_approximation (n := n) hlo (-weightNorm W)
      (max (fixedUpperBound θ ω W + 1) (weightNorm W))
      (fun x => (hlobnd x).1) (fun x => (hlobnd x).2)
  obtain ⟨b, hb, hbm, hbbnd, _hbabs, hblim⟩ :=
    exists_chartSmooth_antitone_approximation (n := n) hup (-weightNorm W - 1)
      (fixedUpperBound θ ω W) (fun x => (hupbnd x).1) (fun x => (hupbnd x).2)
  have hR0 := weightNorm_nonneg W
  have hC0 : 0 < fixedUpperBound θ ω W :=
    uniformUpperBound_pos (totalForm θ ω) W.nonPluripolar_carrier (weightNorm W)
  refine ⟨a, b, ha, hb, ham, hbm, ?_, fun j x => ⟨(habnd j x).2.le, (hbbnd j x).1.le⟩,
    halim, hblim⟩
  intro j x
  have haL := (habnd j x).1
  have haU := (habnd j x).2.le.trans (hlobnd x).2
  have hbL := (hupbnd x).1.trans (hbbnd j x).1.le
  have hbU := (hbbnd j x).2
  have hM : max (fixedUpperBound θ ω W + 1) (weightNorm W) ≤
      weightNorm W + fixedUpperBound θ ω W + 1 := by
    apply max_le <;> linarith
  change |a j x| ≤ weightNorm W + fixedUpperBound θ ω W + 3 ∧
    |b j x| ≤ weightNorm W + fixedUpperBound θ ω W + 3
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · apply abs_le.mpr
    constructor <;> linarith


end SGPT.Bergman.GlobalWeightApproximation
