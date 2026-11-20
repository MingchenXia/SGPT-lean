/- Canonical staging of the immutable whole-original toric Bergman proof.
   Exact retained fragments/providers are recorded in fragment-provider-map.json.gz. -/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity
import SGPT.Bergman.SourceMultiplierSectionDensity
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.PSH.GlobalL2BergmanLower
import SGPT.Toric.BigToric2Laurent
import SGPT.Toric.GeodesicAction
import SGPT.Toric.NativePhysicalLineBundle
import SGPT.Toric.Toric5Multiplier
import SGPT.Toric.Toric5Weights
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive


/- BEGIN SGPT.Bergman.SourceNativePhiWeightedMeasure; source SHA256 479aa393c185d554cb2aa8e0831d4ab2bc29306549d14633c55a3f6014feaef5 -/
section ToricCanonicalFragment001

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- An INTERNAL derived measure for the SAME original singular-phi
integral. The original raw source volume is neither replaced nor normalized. -/
def nativePhiWeightedMeasure (φ : X → EReal) (k : ℕ) (μ : Measure X) : Measure X :=
  μ.withDensity (fun x => multiplierWeight (k : ℝ) (φ x))

/-- The actual original singular-phi integral norm, retaining infinity,
all poles/zeros and the true degree-zero convention. No BM hypothesis. -/
def nativePhiExtendedSectionNorm (B : HermitianHolomorphicLineBundle n X)
    (φ : X → EReal) (k : ℕ) (μ : Measure X)
    (s : HolomorphicSections (n := n) B.Fiber) : ENNReal :=
  (∫⁻ x, originalSectionDensity (n := n) B.Fiber φ k s x ∂μ) ^ (1 / 2 : ℝ)

/-- Exact raw-volume/singular-weight identity at EVERY degree, without
clipping an infinite weight to a real value or assuming a finite norm. -/
theorem lintegral_nativePhiWeightedMeasure_norm_sq
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal} (hφ : Measurable φ)
    (k : ℕ) (μ : Measure X) (s : HolomorphicSections (n := n) B.Fiber) :
    (∫⁻ x, ENNReal.ofReal (‖s x‖ ^ 2) ∂nativePhiWeightedMeasure φ k μ) =
      ∫⁻ x, originalSectionDensity (n := n) B.Fiber φ k s x ∂μ := by
  have hs : Measurable (fun x => ENNReal.ofReal (‖s x‖ ^ 2)) :=
    (ENNReal.continuous_ofReal.comp ((sectionNormMap B.Fiber s).continuous.pow 2)).measurable
  unfold nativePhiWeightedMeasure
  rw [lintegral_withDensity_eq_lintegral_mul μ (measurable_originalMultiplierWeight hφ k) hs]
  apply lintegral_congr
  intro x
  exact mul_comm _ _


/-- Genuine L2 norm of the actual real point norm for the derived measure,
proved from the ORIGINAL singular density. No continuous-phi/BM/integrability
or Hilbert certificate is input, and every infinite value is retained. -/
theorem nativePhiExtendedSectionNorm_eq_eLpNorm
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal} (hφ : Measurable φ)
    (k : ℕ) (μ : Measure X) (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ s =
      eLpNorm (fun x => ‖s x‖) 2 (nativePhiWeightedMeasure φ k μ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  unfold nativePhiExtendedSectionNorm
  congr 1
  rw [← lintegral_nativePhiWeightedMeasure_norm_sq B hφ k μ s]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal (norm_nonneg (s x)), ENNReal.rpow_two,
    ENNReal.ofReal_pow (norm_nonneg (s x))]

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment001
/- END SGPT.Bergman.SourceNativePhiWeightedMeasure -/

/- BEGIN SGPT.Bergman.SourceNativePhiNormLaws; source SHA256 7670b97d38d03bdb283b77d7ac92befe88f9c7a5f04cf63efa5022ab5744656b -/
section ToricCanonicalFragment002

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Genuine singular-phi Minkowski on ALL actual sections; infinite values
are retained and no finite-norm, continuous-phi or BM premise is supplied. -/
theorem nativePhiExtendedSectionNorm_add_le
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal} (hφ : Measurable φ)
    (k : ℕ) (μ : Measure X) (s t : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ (s + t) ≤
      nativePhiExtendedSectionNorm B φ k μ s + nativePhiExtendedSectionNorm B φ k μ t := by
  rw [nativePhiExtendedSectionNorm_eq_eLpNorm B hφ,
    nativePhiExtendedSectionNorm_eq_eLpNorm B hφ,
    nativePhiExtendedSectionNorm_eq_eLpNorm B hφ]
  calc
    _ ≤ eLpNorm ((fun x => ‖s x‖) + (fun x => ‖t x‖)) 2
        (nativePhiWeightedMeasure φ k μ) := by
      apply eLpNorm_mono
      intro x
      simp only [Pi.add_apply, Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact norm_add_le (s x) (t x)
    _ ≤ _ := eLpNorm_add_le
      (sectionNormMap B.Fiber s).continuous.aestronglyMeasurable
      (sectionNormMap B.Fiber t).continuous.aestronglyMeasurable (by norm_num)

/-- Physical complex homogeneity for the SAME singular weighted integral. -/
theorem nativePhiExtendedSectionNorm_smul
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal} (hφ : Measurable φ)
    (k : ℕ) (μ : Measure X) (c : ℂ) (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ (c • s) =
      ENNReal.ofReal ‖c‖ * nativePhiExtendedSectionNorm B φ k μ s := by
  rw [nativePhiExtendedSectionNorm_eq_eLpNorm B hφ,
    nativePhiExtendedSectionNorm_eq_eLpNorm B hφ]
  have heq : (fun x => ‖(c • s) x‖) = (‖c‖ : ℝ) • (fun x => ‖s x‖) := by
    funext x
    exact norm_smul c (s x)
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (norm_nonneg _)]

omit [BorelSpace X] in
/-- Degree zero, poles and empty spaces obey the literal zero convention. -/
theorem nativePhiExtendedSectionNorm_zero
    (B : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (μ : Measure X) :
    nativePhiExtendedSectionNorm B φ k μ 0 = 0 := by
  simp [nativePhiExtendedSectionNorm, originalSectionDensity]

omit [BorelSpace X] in
/-- Negation is an exact physical identity without any singularity restriction. -/
theorem nativePhiExtendedSectionNorm_neg
    (B : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (μ : Measure X)
    (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ (-s) = nativePhiExtendedSectionNorm B φ k μ s := by
  unfold nativePhiExtendedSectionNorm
  congr 1
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (‖-s x‖ ^ 2) * _ = ENNReal.ofReal (‖s x‖ ^ 2) * _
  rw [norm_neg]

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment002
/- END SGPT.Bergman.SourceNativePhiNormLaws -/

/- BEGIN SGPT.Bergman.SourceNativePhiNormPositivity; source SHA256 8fdb11ce72a66dc3fad1edc1620bd2ed846134196745b639a71ceaf7827213ae -/
section ToricCanonicalFragment003

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [IsComplexManifold n X] in
/-- Actual smooth positive chart densities transport arbitrary AE predicates
to chart Haar measure. No global support or probability certificate is input. -/
theorem ae_chartTarget_of_ae_smoothPositiveVolume {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (e : ComplexChart n X) {P : X → Prop}
    (hae : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂(volume.restrict e.val.target), P (e.val.symm z) := by
  obtain ⟨ρ, hρ, hpos, hmap⟩ := hμ e
  let ν := (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))
  have hac : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hinv : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hac
  have hforward : AEMeasurable e.val (μ.restrict e.val.source) :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hinvmap : AEMeasurable e.val.symm (Measure.map e.val (μ.restrict e.val.source)) := by
    rw [hmap]
    exact hinv
  have hleft : (e.val.symm ∘ e.val) =ᵐ[μ.restrict e.val.source] id :=
    (ae_restrict_mem e.val.open_source.measurableSet).mono fun x hx => e.val.left_inv hx
  have hν : μ.restrict e.val.source = Measure.map e.val.symm ν := by
    calc
      _ = Measure.map id (μ.restrict e.val.source) := Measure.map_id.symm
      _ = Measure.map (e.val.symm ∘ e.val) (μ.restrict e.val.source) :=
        (Measure.map_congr hleft).symm
      _ = Measure.map e.val.symm (Measure.map e.val (μ.restrict e.val.source)) :=
        (hinvmap.map_map_of_aemeasurable hforward).symm
      _ = _ := by rw [hmap]
  have hrestrict : ∀ᵐ x ∂(μ.restrict e.val.source), P x := hae.filter_mono ae_restrict_le
  rw [hν] at hrestrict
  have hνP : ∀ᵐ z ∂ν, P (e.val.symm z) := ae_of_ae_map hinv hrestrict
  have hd : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict e.val.target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn hρ.continuousOn).aemeasurable
      e.val.open_target.measurableSet
  have hpred := (ae_withDensity_iff' hd).mp hνP
  filter_upwards [hpred, ae_restrict_mem e.val.open_target.measurableSet] with z hz hzt
  exact hz (ENNReal.ofReal_pos.mpr (hpos z hzt)).ne'

omit [IsComplexManifold n X] in
/-- The actual positive chart densities and continuity detect every point,
including disconnected/empty bases and complex dimension zero. -/
theorem continuous_eq_zero_of_ae_smoothPositiveVolume {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {f : X → ℝ} (hf : Continuous f)
    (hae : f =ᵐ[μ] 0) : f = 0 := by
  funext x
  let e := complexChartAt (n := n) x
  have heq : EqOn (fun z => f (e.val.symm z)) (fun _ => (0 : ℝ)) e.val.target :=
    Measure.eqOn_open_of_ae_eq (ae_chartTarget_of_ae_smoothPositiveVolume hμ e hae)
      e.val.open_target (hf.comp_continuousOn e.val.continuousOn_symm) continuousOn_const
  have hx := heq (e.val.map_source (mem_complexChartAt_source x))
  simpa only [e.val.left_inv (mem_complexChartAt_source x), Pi.zero_apply] using hx

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] in
/-- A genuine qPSH value is never top, hence its nonnegative-degree weight
is never zero, including infinite weights at poles and degree zero. -/
theorem nativePhiMultiplierWeight_ne_zero (k : ℕ) {a : EReal} (ha : a ≠ ⊤) :
    multiplierWeight (k : ℝ) a ≠ 0 := by
  by_cases hk : k = 0
  · simp [hk, multiplierWeight]
  have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  cases a using EReal.rec with
  | bot => simp [multiplierWeight_bot hkp]
  | coe a =>
    rw [multiplierWeight_coe]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  | top => exact False.elim (ha rfl)

/-- The internally derived singular measure has exactly the original raw
measure class needed for positivity; no finite density is assumed. -/
theorem absolutelyContinuous_nativePhiWeightedMeasure {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (k : ℕ) (μ : Measure X) :
    μ ≪ nativePhiWeightedMeasure φ k μ :=
  withDensity_absolutelyContinuous'
    (measurable_originalMultiplierWeight hφ.1.upperSemicontinuous.measurable k).aemeasurable
    (Eventually.of_forall (fun x => nativePhiMultiplierWeight_ne_zero k (hφ.1.ne_top x)))

/-- Positive definiteness is an OUTPUT on ALL actual holomorphic sections,
from genuine qPSH/no-top and genuine smooth positive volume. -/
theorem nativePhiExtendedSectionNorm_eq_zero_iff
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) (k : ℕ) {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ s = 0 ↔ s = 0 := by
  constructor
  · intro hz
    rw [nativePhiExtendedSectionNorm_eq_eLpNorm B hφ.1.upperSemicontinuous.measurable] at hz
    have hw := (eLpNorm_eq_zero_iff
      (sectionNormMap B.Fiber s).continuous.aestronglyMeasurable (by norm_num)).mp hz
    have hraw := (absolutelyContinuous_nativePhiWeightedMeasure hφ k μ).ae_eq hw
    have heq := continuous_eq_zero_of_ae_smoothPositiveVolume hμ
      (sectionNormMap B.Fiber s).continuous hraw
    apply ContMDiffSection.ext
    intro x
    apply norm_eq_zero.mp
    exact congrFun heq x
  · rintro rfl
    exact nativePhiExtendedSectionNorm_zero B φ k μ

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment003
/- END SGPT.Bergman.SourceNativePhiNormPositivity -/

/- BEGIN SGPT.Bergman.SourceNativePhiHilbertNorm; source SHA256 aa4b62f8f28a33ee75da7e2777dfd81d19cead16dd34f7862a7fda14efb55274 -/
section ToricCanonicalFragment004

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A new norm model of the ENTIRE literal original tensor-sheaf Gamma.
No old supnorm instance or original section space is overwritten. -/
def NativePhiHilbertSections (L T : HermitianHolomorphicLineBundle n X) (k : ℕ)
    (φ : X → EReal) (_hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (μ : Measure X) (_hμ : IsSmoothPositiveVolume (n := n) μ) : Type :=
  LiteralTwistedMultiplierSections L T k φ

variable (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
  (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
  (hμ : IsSmoothPositiveVolume (n := n) μ)

instance nativePhiHilbertAddCommGroup :
    AddCommGroup (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  inferInstanceAs (AddCommGroup (LiteralTwistedMultiplierSections L T k φ))

instance nativePhiHilbertModule : Module ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  inferInstanceAs (Module ℂ (LiteralTwistedMultiplierSections L T k φ))

/-- Literal identity in BOTH directions to ALL original Gamma vectors. -/
def nativePhiOriginalGammaEquiv :
    NativePhiHilbertSections L T k φ hφ μ hμ ≃ₗ[ℂ]
      LiteralTwistedMultiplierSections L T k φ := LinearEquiv.refl ℂ _

/-- The actual original sheaf Gamma-to-holomorphic-section map. -/
def nativePhiUnderlyingSection :
    NativePhiHilbertSections L T k φ hφ μ hμ →ₗ[ℂ] twistedSections L T k :=
  (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)).subtype ∘ₗ
      (literalTwistedMultiplierSectionEquiv L T k φ).toLinearMap ∘ₗ
        (nativePhiOriginalGammaEquiv L T k hφ μ hμ).toLinearMap

omit [BorelSpace X] in
/-- The whole original Gamma map is genuinely injective. -/
theorem nativePhiUnderlyingSection_injective :
    Function.Injective (nativePhiUnderlyingSection L T k hφ μ hμ) :=
  Subtype.val_injective.comp ((literalTwistedMultiplierSectionEquiv L T k φ).injective.comp
    (nativePhiOriginalGammaEquiv L T k hφ μ hμ).injective)

variable [CompactSpace X]

/-- Actual multiplier-stalk membership internally proves finiteness of the
SAME singular integral on EVERY Gamma vector, including degree zero. -/
theorem nativePhiUnderlyingSection_integral_lt_top
    (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    (∫⁻ x, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k
      (nativePhiUnderlyingSection L T k hφ μ hμ s) x ∂μ) < ⊤ :=
  (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ _ hμ).mp
      (literalTwistedMultiplierSectionEquiv L T k φ
        (nativePhiOriginalGammaEquiv L T k hφ μ hμ s)).property

/-- Finiteness of the actual singular norm is produced from the original
ideal, rather than a BM, probability or prescribed finite-family input. -/
theorem nativePhiUnderlyingSection_norm_ne_top
    (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    nativePhiExtendedSectionNorm (twistedPower L T k) φ k μ
      (nativePhiUnderlyingSection L T k hφ μ hμ s) ≠ ⊤ := by
  apply ne_of_lt
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr
    (nativePhiUnderlyingSection_integral_lt_top L T k hφ μ hμ s)

/-- The genuine no-BM singular-phi norm on the ENTIRE literal Gamma. -/
def nativePhiAddGroupNorm : AddGroupNorm (NativePhiHilbertSections L T k φ hφ μ hμ) where
  toFun s := (nativePhiExtendedSectionNorm (twistedPower L T k) φ k μ
    (nativePhiUnderlyingSection L T k hφ μ hμ s)).toReal
  map_zero' := by rw [map_zero, nativePhiExtendedSectionNorm_zero, ENNReal.toReal_zero]
  add_le' s t := by
    have hz := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ s,
        nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ t⟩)
      (nativePhiExtendedSectionNorm_add_le (twistedPower L T k)
        hφ.1.upperSemicontinuous.measurable k μ
        (nativePhiUnderlyingSection L T k hφ μ hμ s)
        (nativePhiUnderlyingSection L T k hφ μ hμ t))
    rw [map_add]
    rwa [ENNReal.toReal_add (nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ s)
      (nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ t)] at hz
  neg' s := by rw [map_neg, nativePhiExtendedSectionNorm_neg]
  eq_zero_of_map_eq_zero' s hs := by
    apply nativePhiUnderlyingSection_injective L T k hφ μ hμ
    rw [map_zero]
    apply (nativePhiExtendedSectionNorm_eq_zero_iff (twistedPower L T k) hφ k hμ _).mp
    exact ((ENNReal.toReal_eq_zero_iff _).mp hs).resolve_right
      (nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ s)

instance nativePhiNormedAddCommGroup :
    NormedAddCommGroup (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  (nativePhiAddGroupNorm L T k hφ μ hμ).toNormedAddCommGroup

/-- Exact physical original singular norm readback for EVERY actual vector. -/
theorem nativePhi_ofReal_norm (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    ENNReal.ofReal ‖s‖ = nativePhiExtendedSectionNorm (twistedPower L T k) φ k μ
      (nativePhiUnderlyingSection L T k hφ μ hμ s) :=
  ENNReal.ofReal_toReal (nativePhiUnderlyingSection_norm_ne_top L T k hφ μ hμ s)


/-- Complex homogeneity is produced from the SAME original integral. -/
theorem nativePhi_norm_smul (c : ℂ) (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    ‖c • s‖ = ‖c‖ * ‖s‖ := by
  change (nativePhiExtendedSectionNorm (twistedPower L T k) φ k μ
    (nativePhiUnderlyingSection L T k hφ μ hμ (c • s))).toReal = _
  rw [map_smul, nativePhiExtendedSectionNorm_smul (twistedPower L T k)
    hφ.1.upperSemicontinuous.measurable, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (norm_nonneg _)]
  rfl

theorem nativePhiNormCore : NormedSpace.Core ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) where
  norm_nonneg := norm_nonneg
  norm_triangle := norm_add_le
  norm_eq_zero_iff := fun _ => norm_eq_zero
  norm_smul := nativePhi_norm_smul L T k hφ μ hμ

instance nativePhiNormedSpace : NormedSpace ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  NormedSpace.ofCore (nativePhiNormCore L T k hφ μ hμ)

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment004
/- END SGPT.Bergman.SourceNativePhiHilbertNorm -/

/- BEGIN SGPT.Bergman.SourceNativePhiParallelogram; source SHA256 12cad49241ddb20e62ddca872eff8460e69efced915595373143b62099f7de67 -/
section ToricCanonicalFragment005

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

omit [BorelSpace X] in
/-- Exact original squared norm before any finiteness restriction. -/
theorem nativePhiExtendedSectionNorm_sq (B : HermitianHolomorphicLineBundle n X)
    (φ : X → EReal) (k : ℕ) (μ : Measure X)
    (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ s ^ 2 =
      ∫⁻ x, originalSectionDensity (n := n) B.Fiber φ k s x ∂μ := by
  unfold nativePhiExtendedSectionNorm
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num

omit [MeasurableSpace X] [BorelSpace X] in
/-- The actual Hermitian fiber proves the singular density parallelogram,
including poles and zero-times-infinity; no inner product is input on Gamma. -/
theorem nativePhiDensity_parallelogram (B : HermitianHolomorphicLineBundle n X)
    (φ : X → EReal) (k : ℕ) (s t : HolomorphicSections (n := n) B.Fiber) (x : X) :
    originalSectionDensity (n := n) B.Fiber φ k (s + t) x +
      originalSectionDensity (n := n) B.Fiber φ k (s - t) x =
      2 * (originalSectionDensity (n := n) B.Fiber φ k s x +
        originalSectionDensity (n := n) B.Fiber φ k t x) := by
  change ENNReal.ofReal (‖s x + t x‖ ^ 2) * _ +
    ENNReal.ofReal (‖s x - t x‖ ^ 2) * _ = _
  rw [← add_mul, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    parallelogram_law_with_norm ℂ, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  norm_num only [ENNReal.ofReal_ofNat]
  change (2 * (ENNReal.ofReal (‖s x‖ ^ 2) + ENNReal.ofReal (‖t x‖ ^ 2))) * _ =
    2 * (ENNReal.ofReal (‖s x‖ ^ 2) * _ + ENNReal.ofReal (‖t x‖ ^ 2) * _)
  ring

/-- Integrating the genuine physical identity produces the full extended
parallelogram. This remains valid without a finite-norm hypothesis. -/
theorem nativePhiExtendedSectionNorm_parallelogram
    (B : HermitianHolomorphicLineBundle n X) {φ : X → EReal} (hφ : Measurable φ)
    (k : ℕ) (μ : Measure X) (s t : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ (s + t) ^ 2 +
      nativePhiExtendedSectionNorm B φ k μ (s - t) ^ 2 =
      2 * (nativePhiExtendedSectionNorm B φ k μ s ^ 2 +
        nativePhiExtendedSectionNorm B φ k μ t ^ 2) := by
  simp_rw [nativePhiExtendedSectionNorm_sq]
  rw [← lintegral_add_left (measurable_originalSectionDensity (n := n) B.Fiber hφ k (s + t)),
    ← lintegral_add_left (measurable_originalSectionDensity (n := n) B.Fiber hφ k s)]
  have hm : Measurable (fun x => originalSectionDensity (n := n) B.Fiber φ k s x +
      originalSectionDensity (n := n) B.Fiber φ k t x) :=
    (measurable_originalSectionDensity (n := n) B.Fiber hφ k s).add
      (measurable_originalSectionDensity (n := n) B.Fiber hφ k t)
  rw [← lintegral_const_mul (2 : ENNReal) hm]
  exact lintegral_congr (nativePhiDensity_parallelogram B φ k s t)

variable [CompactSpace X]
  (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
  (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
  (hμ : IsSmoothPositiveVolume (n := n) μ)


/-- The actual norm model obeys the parallelogram law, internally produced
from original physical fibers and original singular integrals. -/
theorem nativePhi_norm_parallelogram (s t : NativePhiHilbertSections L T k φ hφ μ hμ) :
    ‖s + t‖ ^ 2 + ‖s - t‖ ^ 2 = 2 * (‖s‖ ^ 2 + ‖t‖ ^ 2) := by
  have hz := nativePhiExtendedSectionNorm_parallelogram (twistedPower L T k)
    hφ.1.upperSemicontinuous.measurable k μ
    (nativePhiUnderlyingSection L T k hφ μ hμ s)
    (nativePhiUnderlyingSection L T k hφ μ hμ t)
  rw [← map_add, ← map_sub, ← nativePhi_ofReal_norm, ← nativePhi_ofReal_norm,
    ← nativePhi_ofReal_norm, ← nativePhi_ofReal_norm] at hz
  apply (ENNReal.ofReal_eq_ofReal_iff
    (add_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (sq_nonneg _) (sq_nonneg _)))).mp
  rw [ENNReal.ofReal_add (sq_nonneg ‖s + t‖) (sq_nonneg ‖s - t‖),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg ‖s‖) (sq_nonneg ‖t‖)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_ofNat]
  exact hz

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment005
/- END SGPT.Bergman.SourceNativePhiParallelogram -/

/- BEGIN SGPT.Bergman.SourceNativePhiHilbert; source SHA256 6958b70100aa87141d19c304c2f9c7d033de93072b58dee0cd21a3956464ec20 -/
section ToricCanonicalFragment006

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
  (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
  (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
  (hμ : IsSmoothPositiveVolume (n := n) μ)

/-- Genuine compatible complex inner product produced from the internally
proved original singular-integral parallelogram; no Hilbert/BM input. -/
instance nativePhiInnerProductSpace :
    InnerProductSpace ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  InnerProductSpace.ofNorm ℂ (fun s t => by
    simpa only [← sq] using nativePhi_norm_parallelogram L T k hφ μ hμ s t)

/-- Compact full H0 finiteness transports to the ENTIRE actual Gamma model. -/
instance nativePhiFiniteDimensional :
    FiniteDimensional ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) := by
  let := literalTwistedMultiplierSections_finiteDimensional L T k φ
  exact FiniteDimensional.of_injective
    (nativePhiOriginalGammaEquiv L T k hφ μ hμ).toLinearMap
    (nativePhiOriginalGammaEquiv L T k hφ μ hμ).injective

/-- Completeness is internally produced even for empty/zero small-degree
Gamma and dimension zero; no nonzero section is assumed. -/
instance nativePhiCompleteSpace :
    CompleteSpace (NativePhiHilbertSections L T k φ hφ μ hμ) :=
  FiniteDimensional.complete ℂ _

/-- Actual finite orthonormal basis of ALL singular-phi L2 original Gamma,
constructed only after the actual Hilbert structure. This generic basis is
not asserted to consist of toric eigenvectors. -/
def nativePhiOrthonormalBasis :
    OrthonormalBasis (Fin (Module.finrank ℂ (NativePhiHilbertSections L T k φ hφ μ hμ)))
      ℂ (NativePhiHilbertSections L T k φ hφ μ hμ) := stdOrthonormalBasis ℂ _


/-- Same original RAW Kahler volume, with smooth-positive chart density
produced internally. The volume is never probability-normalized. -/
abbrev NativePhiKahlerSections (omega : KahlerBackground n X) :=
  NativePhiHilbertSections L T k φ hφ
    (SGPT.Foundations.Analysis.Pending.IntegrationCurrent.kahlerVolume omega)
    (SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume
      omega)


end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment006
/- END SGPT.Bergman.SourceNativePhiHilbert -/

/- BEGIN SGPT.Bergman.SourceNativePhiBergmanKernel; source SHA256 842a1fb3d54f33d6dc8f6cab0a14bb335a685f3ecaf8db68e37a8bbf6fbb8054 -/
section ToricCanonicalFragment007

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeSingularPhi
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
/-- Exact integral/unit-ball equivalence, including infinite integral,
all poles, zero sections and degree zero. -/
theorem nativePhiExtendedSectionNorm_le_one_iff
    (B : HermitianHolomorphicLineBundle n X) (φ : X → EReal) (k : ℕ) (μ : Measure X)
    (s : HolomorphicSections (n := n) B.Fiber) :
    nativePhiExtendedSectionNorm B φ k μ s ≤ 1 ↔
      (∫⁻ x, originalSectionDensity (n := n) B.Fiber φ k s x ∂μ) ≤ 1 := by
  unfold nativePhiExtendedSectionNorm
  simpa only [ENNReal.one_rpow] using
    (ENNReal.rpow_le_rpow_iff (x := ∫⁻ x,
      originalSectionDensity (n := n) B.Fiber φ k s x ∂μ)
      (y := 1) (by norm_num : (0 : ℝ) < 1 / 2))

variable (L T : HermitianHolomorphicLineBundle n X) (k : ℕ) {φ : X → EReal}
  (hφ : IsGlobalQuasiPshPotential (n := n) φ) (μ : Measure X)
  (hμ : IsSmoothPositiveVolume (n := n) μ)

/-- Point evaluation of ALL original Gamma vectors in the actual fibre. -/
def nativePhiEvaluationLinear (x : X) :
    NativePhiHilbertSections L T k φ hφ μ hμ →ₗ[ℂ] (twistedPower L T k).Fiber x where
  toFun s := nativePhiUnderlyingSection L T k hφ μ hμ s x
  map_add' s t := congrArg (fun u : twistedSections L T k => u x)
    ((nativePhiUnderlyingSection L T k hφ μ hμ).map_add s t)
  map_smul' c s := congrArg (fun u : twistedSections L T k => u x)
    ((nativePhiUnderlyingSection L T k hφ μ hμ).map_smul c s)

/-- Preferred frame used at ONE fixed point, never as a holomorphic unitary
trivialization. Its actual frame norm converts coordinates to physical norm. -/
def nativePhiScalarEvaluationLinear (x : X) :
    NativePhiHilbertSections L T k φ hφ μ hμ →ₗ[ℂ] ℂ :=
  (((trivializationAt ℂ (twistedPower L T k).Fiber x).linearEquivAt ℂ x
      (mem_baseSet_trivializationAt ℂ (twistedPower L T k).Fiber x)).toLinearMap.comp
    (nativePhiEvaluationLinear L T k hφ μ hμ x)).smulRight
      (Complex.ofReal (frameNorm (twistedPower L T k).Fiber
        (trivializationAt ℂ (twistedPower L T k).Fiber x) x))

omit [BorelSpace X] [CompactSpace X] in
theorem nativePhiScalarEvaluationLinear_norm (x : X)
    (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    ‖nativePhiScalarEvaluationLinear L T k hφ μ hμ x s‖ =
      ‖nativePhiUnderlyingSection L T k hφ μ hμ s x‖ := by
  let V := (twistedPower L T k).Fiber
  let e := trivializationAt ℂ V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x
  change ‖(e.linearEquivAt ℂ x hx) (nativePhiUnderlyingSection L T k hφ μ hμ s x) •
    Complex.ofReal (frameNorm V e x)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (frameNorm_pos V e hx).le]
  exact (norm_eq_coefficient_mul_frameNorm V e _ hx).symm

/-- Continuity follows from the actual full-Gamma finite-dimensionality. -/
def nativePhiScalarEvaluation (x : X) :
    NativePhiHilbertSections L T k φ hφ μ hμ →L[ℂ] ℂ :=
  (nativePhiScalarEvaluationLinear L T k hφ μ hμ x).toContinuousLinearMap

theorem nativePhiScalarEvaluation_norm (x : X)
    (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    ‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ =
      ‖nativePhiUnderlyingSection L T k hφ μ hμ s x‖ :=
  nativePhiScalarEvaluationLinear_norm L T k hφ μ hμ x s

/-- Actual Riesz vector constructed from the genuine singular-weight norm. -/
def nativePhiEvaluationRiesz (x : X) : NativePhiHilbertSections L T k φ hφ μ hμ :=
  (InnerProductSpace.toDual ℂ (NativePhiHilbertSections L T k φ hφ μ hμ)).symm
    (nativePhiScalarEvaluation L T k hφ μ hμ x)

theorem nativePhiEvaluationRiesz_inner (x : X)
    (s : NativePhiHilbertSections L T k φ hφ μ hμ) :
    inner ℂ (nativePhiEvaluationRiesz L T k hφ μ hμ x) s =
      nativePhiScalarEvaluation L T k hφ μ hμ x s :=
  InnerProductSpace.toDual_symm_apply

theorem nativePhiEvaluationRiesz_norm (x : X) :
    ‖nativePhiEvaluationRiesz L T k hφ μ hμ x‖ =
      ‖nativePhiScalarEvaluation L T k hφ μ hμ x‖ :=
  (InnerProductSpace.toDual ℂ (NativePhiHilbertSections L T k φ hφ μ hμ)).symm.norm_map _

/-- The ORIGINAL full-section Bergman supremum. Every global section is
quantified, and its SAME singular-phi integral determines admissibility. -/
def nativePhiOriginalBergmanDensity (x : X) : ENNReal :=
  ⨆ s : twistedSections L T k,
    ⨆ (_ : (∫⁻ y, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s y ∂μ) ≤ 1),
      ENNReal.ofReal (‖s x‖ ^ 2)

/-- Exact equality of the original ALL-section integral unit ball with the
internally produced full-Gamma Hilbert unit ball, in both directions. -/
theorem nativePhiOriginalBergmanDensity_eq_unitball (x : X) :
    nativePhiOriginalBergmanDensity L T k (φ := φ) μ x =
      ⨆ s : NativePhiHilbertSections L T k φ hφ μ hμ, ⨆ (_ : ‖s‖ ≤ 1),
        ENNReal.ofReal (‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ ^ 2) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    have hideal := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
      (twistedPower L T k).Fiber k hφ s hμ).mpr (hs.trans_lt ENNReal.one_lt_top)
    let g := (literalTwistedMultiplierSectionEquiv L T k φ).symm ⟨s, hideal⟩
    let t := (nativePhiOriginalGammaEquiv L T k hφ μ hμ).symm g
    have ht : nativePhiUnderlyingSection L T k hφ μ hμ t = s := by
      simp only [nativePhiUnderlyingSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
        t, g, LinearEquiv.apply_symm_apply, Submodule.subtype_apply]
    have htnorm : ‖t‖ ≤ 1 := by
      rw [← ENNReal.ofReal_le_one, nativePhi_ofReal_norm,
        nativePhiExtendedSectionNorm_le_one_iff, ht]
      exact hs
    apply le_iSup_of_le t
    apply le_iSup_of_le htnorm
    rw [nativePhiScalarEvaluation_norm, ht]
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    have hsint : (∫⁻ y, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k
        (nativePhiUnderlyingSection L T k hφ μ hμ s) y ∂μ) ≤ 1 := by
      rw [← nativePhiExtendedSectionNorm_le_one_iff, ← nativePhi_ofReal_norm,
        ENNReal.ofReal_le_one]
      exact hs
    apply le_iSup_of_le (nativePhiUnderlyingSection L T k hφ μ hμ s)
    apply le_iSup_of_le hsint
    rw [nativePhiScalarEvaluation_norm]

/-- The zero-space case is retained; otherwise the genuine normalized
Riesz vector attains the original evaluation norm. -/
theorem exists_nativePhi_unit_evaluation_max (x : X) :
    ∃ s : NativePhiHilbertSections L T k φ hφ μ hμ, ‖s‖ ≤ 1 ∧
      ‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ ^ 2 =
        ‖nativePhiEvaluationRiesz L T k hφ μ hμ x‖ ^ 2 := by
  let r := nativePhiEvaluationRiesz L T k hφ μ hμ x
  change ∃ s : NativePhiHilbertSections L T k φ hφ μ hμ, ‖s‖ ≤ 1 ∧
    ‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ ^ 2 = ‖r‖ ^ 2
  by_cases hr : r = 0
  · refine ⟨0, by simp, ?_⟩
    rw [map_zero, norm_zero, hr, norm_zero]
  · have hp : 0 < ‖r‖ := norm_pos_iff.mpr hr
    let c : ℂ := Complex.ofReal ‖r‖⁻¹
    let s := c • r
    have hc : ‖c‖ = ‖r‖⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    have hs : ‖s‖ = 1 := by rw [norm_smul, hc, inv_mul_cancel₀ hp.ne']
    refine ⟨s, hs.le, ?_⟩
    have hself : nativePhiScalarEvaluation L T k hφ μ hμ x r =
        Complex.ofReal (‖r‖ ^ 2) := by
      rw [← nativePhiEvaluationRiesz_inner]
      change inner ℂ r r = Complex.ofReal (‖r‖ ^ 2)
      calc
        _ = (RCLike.ofReal ‖r‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K r
        _ = _ := by norm_cast
    have hv : ‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ = ‖r‖ := by
      rw [map_smul, norm_smul, hc, hself, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
        pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    rw [hv]

theorem nativePhiOriginalBergmanDensity_eq_riesz (x : X) :
    nativePhiOriginalBergmanDensity L T k (φ := φ) μ x =
      ENNReal.ofReal (‖nativePhiEvaluationRiesz L T k hφ μ hμ x‖ ^ 2) := by
  rw [nativePhiOriginalBergmanDensity_eq_unitball L T k hφ μ hμ x]
  apply le_antisymm
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    apply ENNReal.ofReal_le_ofReal
    have hb : ‖nativePhiScalarEvaluation L T k hφ μ hμ x s‖ ≤
        ‖nativePhiEvaluationRiesz L T k hφ μ hμ x‖ := by
      calc
        _ ≤ ‖nativePhiScalarEvaluation L T k hφ μ hμ x‖ * ‖s‖ :=
          (nativePhiScalarEvaluation L T k hφ μ hμ x).le_opNorm s
        _ ≤ ‖nativePhiScalarEvaluation L T k hφ μ hμ x‖ * 1 :=
          mul_le_mul_of_nonneg_left hs (norm_nonneg _)
        _ = _ := by rw [mul_one, nativePhiEvaluationRiesz_norm]
    gcongr
  · obtain ⟨s, hs, heq⟩ := exists_nativePhi_unit_evaluation_max L T k hφ μ hμ x
    rw [← heq]
    exact le_iSup_of_le s (le_iSup_of_le hs le_rfl)

/-- Actual Riesz/Parseval equality for ANY genuine full ON basis; no
finite-family/basis-existence or evaluation certificate is assumed. -/
theorem nativePhiOriginalBergmanDensity_eq_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (NativePhiHilbertSections L T k φ hφ μ hμ)) (x : X) :
    nativePhiOriginalBergmanDensity L T k (φ := φ) μ x =
      ENNReal.ofReal (∑ i, ‖nativePhiUnderlyingSection L T k hφ μ hμ (b i) x‖ ^ 2) := by
  rw [nativePhiOriginalBergmanDensity_eq_riesz L T k hφ μ hμ x]
  congr 1
  calc
    _ = ∑ i, ‖inner ℂ (nativePhiEvaluationRiesz L T k hφ μ hμ x) (b i)‖ ^ 2 :=
      (b.sum_sq_norm_inner_left _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [nativePhiEvaluationRiesz_inner, nativePhiScalarEvaluation_norm]

end SGPT.Bergman.NativeSingularPhi

end
end ToricCanonicalFragment007
/- END SGPT.Bergman.SourceNativePhiBergmanKernel -/

/- BEGIN SGPT.Toric.ToricCompactCharacterSeparation; source SHA256 67d2c773b65cf3aabfa88bf3220aebd5ab460f595ae3964216efa33ca20e8453 -/
section ToricCanonicalFragment019

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory Complex UnitAddTorus
open scoped Topology ComplexConjugate

-- This is only the auxiliary Fourier parameter torus measure.  It never
-- replaces or normalizes the original raw Kähler volume on the variety.
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The existing actual Fourier parametrization lands in the source
compact torus; this requires no choice of a nontrivial coordinate. -/
theorem isCompactTorusElement_compactTorusPoint {n : ℕ}
    (t : UnitAddTorus (Fin n)) : IsCompactTorusElement (compactTorusPoint t) := by
  intro j
  change ‖((AddCircle.toCircle (t j) : Circle) : ℂ)‖ = 1
  exact Circle.norm_coe _

/-- Distinct original integer characters are separated by an actual
compact-torus point.  The proof uses the existing genuine Fourier family,
so the zero-dimensional endpoint is vacuous without an extra premise. -/
theorem exists_compactTorus_latticeCharacter_ne {n : ℕ} {m l : Fin n → ℤ}
    (hne : m ≠ l) :
    ∃ a : Fin n → ℂˣ, IsCompactTorusElement a ∧
      (latticeCharacter m a : ℂ) ≠ (latticeCharacter l a : ℂ) := by
  by_contra h
  push Not at h
  have hfour : mFourier m = mFourier l := by
    ext t
    rw [mFourier_eq_latticeCharacter, mFourier_eq_latticeCharacter]
    exact h (compactTorusPoint t) (isCompactTorusElement_compactTorusPoint t)
  have hlp : mFourierLp 2 m = mFourierLp 2 l :=
    congrArg (ContinuousMap.toLp 2 volume ℂ) hfour
  exact hne (orthonormal_mFourier.linearIndependent.injective hlp)

/-- Distinct eigenvalues of a genuine complex linear isometry force
orthogonality when the first eigenvalue has unit norm. -/
theorem inner_eq_zero_of_linearIsometry_eigen
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : E →ₗᵢ[ℂ] E) {s t : E} {c d : ℂ} (hc : ‖c‖ = 1) (hcd : c ≠ d)
    (hs : F s = c • s) (ht : F t = d • t) : inner ℂ s t = 0 := by
  by_contra hz
  have hi := F.inner_map_map s t
  rw [hs, ht, inner_smul_left, inner_smul_right] at hi
  have hmul : conj c * d = 1 :=
    mul_right_cancel₀ hz (by simpa only [mul_assoc, one_mul] using hi)
  have hunit : c * conj c = 1 := by rw [Complex.mul_conj', hc]; norm_num
  apply hcd
  calc
    c = c * (conj c * d) := by rw [hmul, mul_one]
    _ = (c * conj c) * d := (mul_assoc _ _ _).symm
    _ = d := by rw [hunit, one_mul]

/-- Pointwise normalization of an actual finite orthogonal algebraic
basis produces its genuine ON basis, preserving empty index sets. -/
def normalizedOrthogonalComplexBasis
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : Module.Basis ι ℂ E) (ho : Pairwise fun i j => inner ℂ (b i) (b j) = 0) :
    OrthonormalBasis ι ℂ E := by
  let w : ι → ℂ := fun i => ((‖b i‖⁻¹ : ℝ) : ℂ)
  have hw : ∀ i, IsUnit (w i) := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    change ((‖b i‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr (b.ne_zero i))
  let B := b.isUnitSMul hw
  apply B.toOrthonormalBasis
  constructor
  · intro i
    change ‖b.isUnitSMul hw i‖ = 1
    rw [Module.Basis.isUnitSMul_apply]
    change ‖((‖b i‖⁻¹ : ℝ) : ℂ) • b i‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (b.ne_zero i))]
  · intro i j hij
    change inner ℂ (b.isUnitSMul hw i) (b.isUnitSMul hw j) = 0
    rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply]
    rw [inner_smul_left, inner_smul_right, ho hij, mul_zero, mul_zero]

/-- The produced ON vectors are precisely the positive-real norm
normalizations of the original basis vectors. -/
theorem normalizedOrthogonalComplexBasis_apply
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : Module.Basis ι ℂ E) (ho : Pairwise fun i j => inner ℂ (b i) (b j) = 0) (i : ι) :
    normalizedOrthogonalComplexBasis b ho i = ((‖b i‖⁻¹ : ℝ) : ℂ) • b i := by
  simp [normalizedOrthogonalComplexBasis, Module.Basis.isUnitSMul_apply]

end SGPT.Toric

end
end ToricCanonicalFragment019
/- END SGPT.Toric.ToricCompactCharacterSeparation -/

/- BEGIN SGPT.Toric.ToricNativeDegreeIdealCoefficients; source SHA256 505a5b197d81abfec0a1bd24ada1f8125b271f6725d4f3e9737c205fe684dc4b -/
section ToricCanonicalFragment028

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine ENTIRE ideal stalk condition on ALL actual atlas frames
is detected by the actual original vertex tensor frames. The comparison
uses the already proved full-stalk frame changes, rather than a restricted
replacement ideal or a chosen coefficient certificate. -/
theorem toricNativeDegreeIdealSections_iff_vertex_coefficients
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ)
    (A : GermIdeal n (PolytopeToricVariety γ hs)) (hA : A.IsCoherent)
    (s : ToricNativeDegreeSections h q) :
    s ∈ fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber A ↔
      ∀ (v : latticePolytopeVertices γ) (p : PolytopeToricVariety γ hs),
        p ∈ (originalPolytopeNativeModelChart γ hs v).source →
          A.mem p (toricNativeDegreeSectionFrameCoeff h q v s) := by
  let V := (toricNativeDegreeBundle h q).Fiber
  constructor
  · intro hs v p hp
    have hs' : globalSectionSheafEquiv (n := n) V s ∈
        idealOpenSectionSubmodule (n := n) V A ⊤ := hs
    have hmem := toricNativeDegreeFrame_mem h v q hp
    exact (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) V A hA
      (toricNativeDegreeFrame h v q) s hmem).mp
        (hs' (toricNativeDegreeFrame h v q) ⟨p, mem_univ p⟩ hmem)
  · intro hcoeff
    change globalSectionSheafEquiv (n := n) V s ∈ idealOpenSectionSubmodule (n := n) V A ⊤
    intro e p hp
    let v := toricNativePreferredVertex γ hs p.val
    have hv : p.val ∈ (originalPolytopeNativeModelChart γ hs v).source :=
      toricNativePreferredVertex_mem p.val
    have hmem := toricNativeDegreeFrame_mem h v q hv
    have hn := (localFrameCoefficientGerm_mem_iff_originalCoefficient (n := n) V A hA
      (toricNativeDegreeFrame h v q) s hmem).mpr (hcoeff v p.val hv)
    exact (localFrameCoefficientGerm_mem_iff (n := n) V A ⊤
      (toricNativeDegreeFrame h v q) e
      (globalSectionSheafEquiv (n := n) V s) p hmem hp).mp hn

end SGPT.Toric

end
end ToricCanonicalFragment028
/- END SGPT.Toric.ToricNativeDegreeIdealCoefficients -/

/- BEGIN SGPT.Toric.ToricNativeDegreeMultiplierMembership; source SHA256 0c64dd5d0fccd4976effa17403b37c28b80adadb327b39426898e13b3d433470 -/
section ToricCanonicalFragment029

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology TopologicalSpace Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The original toric atlas quasi-PSH hypothesis gives the native
global hypothesis, including the established original local nondegeneracy.
No coherence or ideal-stalk comparison is supplied as input. -/
theorem toric_isGlobalQuasiPshPotential_of_isQPSH
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    IsGlobalQuasiPshPotential (n := n) φ :=
  ⟨IsQPSH.chartFunction hφ, SGPT.PSH.VariableComplexAtlas.IsQPSH.locallyNondegenerate hφ⟩

/-- The ACTUAL all-frame whole original ideal condition is exactly the
independent original toric multiplier coefficient condition at the SAME
unscaled phi and SAME exponent q. Coherence is internally produced from
the original quasi-PSH hypothesis. -/
theorem toricNativeDegreeIdealSections_iff_toricMultiplierCoefficient
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (s : ToricNativeDegreeSections h q) :
    s ∈ fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
        (sourceDegreeMultiplierIdeal (n := n) q φ) ↔
      IsToricMultiplierCoefficient ((q : ℤ) • D) (q : ℝ) φ
        (toricNativeDegreeSectionTorusFunction h q s) := by
  have hcoh : (multiplierIdeal (n := n) (q : ℝ) φ).IsCoherent :=
    multiplierIdeal_isCoherent_genuine (toric_isGlobalQuasiPshPotential_of_isQPSH hφ)
      (Nat.cast_pos.mpr hq)
  rw [sourceDegreeMultiplierIdeal_pos q hq,
    toricNativeDegreeIdealSections_iff_vertex_coefficients h q _ hcoh s]
  constructor
  · intro hmem v f hf hgf p hp
    have hfun : f = toricNativeDegreeSectionChartCoeff h q v s :=
      toricSectionCoeff_unique ((q : ℤ) • D) v hf
        (differentiable_toricNativeDegreeSectionChartCoeff h q v s).continuous hgf
        (toricNativeDegreeSectionTorusFunction_eq_chartCoeff h q v s)
    have hlocal : toricNativeDegreeSectionFrameCoeff h q v s =ᶠ[𝓝 p]
        (fun y => f (originalPolytopeNativeModelChart γ hs v y)) := by
      filter_upwards [(originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds hp]
        with y hy
      rw [hfun, toricNativeDegreeSectionChartCoeff_chart_apply h q v s hy]
    exact Pending.MultiplierIdealProductComparison.mem_multiplierIdeal_congr
      (hmem v p hp) hlocal
  · intro hmem v p hp
    have hm := hmem v (toricNativeDegreeSectionChartCoeff h q v s)
      (differentiable_toricNativeDegreeSectionChartCoeff h q v s).continuous
      (toricNativeDegreeSectionTorusFunction_eq_chartCoeff h q v s) p hp
    have hlocal : (fun y => toricNativeDegreeSectionChartCoeff h q v s
        (originalPolytopeNativeModelChart γ hs v y)) =ᶠ[𝓝 p]
          toricNativeDegreeSectionFrameCoeff h q v s := by
      filter_upwards [(originalPolytopeNativeModelChart γ hs v).open_source.mem_nhds hp]
        with y hy
      exact toricNativeDegreeSectionChartCoeff_chart_apply h q v s hy
    exact Pending.MultiplierIdealProductComparison.mem_multiplierIdeal_congr hm hlocal

theorem toricNativeDegreeIdealSections_iff_toricMultiplierSections
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (s : ToricNativeDegreeSections h q) :
    s ∈ fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
        (sourceDegreeMultiplierIdeal (n := n) q φ) ↔
      (toricNativeDegreeSectionRestriction h q s).val ∈
        toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ := by
  rw [mem_toricMultiplierSections]
  exact ⟨fun hm => ⟨toricNativeDegreeSectionTorusFunction_mem h q s,
    (toricNativeDegreeIdealSections_iff_toricMultiplierCoefficient h q hq hφ s).mp hm⟩,
    fun hm => (toricNativeDegreeIdealSections_iff_toricMultiplierCoefficient h q hq hφ s).mpr hm.2⟩

end SGPT.Toric

end
end ToricCanonicalFragment029
/- END SGPT.Toric.ToricNativeDegreeMultiplierMembership -/

/- BEGIN SGPT.Toric.ToricNativeLiteralMultiplierSectionEquiv; source SHA256 9ee9940754d4ca3b6d9895c927167ddf3b3e059d1d866be733da2d3caabd739c -/
section ToricCanonicalFragment030

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeDegreeMultiplierSectionMap {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    ↥(fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
      (sourceDegreeMultiplierIdeal (n := n) q φ)) →ₗ[ℂ]
        toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ where
  toFun s := ⟨(toricNativeDegreeSectionRestriction h q s.val).val,
    (toricNativeDegreeIdealSections_iff_toricMultiplierSections h q hq hφ s.val).mp s.property⟩
  map_add' s t := by
    apply Subtype.ext
    exact congrArg (fun g : toricSections ((q : ℤ) • D) => g.val)
      ((toricNativeDegreeSectionRestriction h q).map_add s.val t.val)
  map_smul' c s := by
    apply Subtype.ext
    exact congrArg (fun g : toricSections ((q : ℤ) • D) => g.val)
      ((toricNativeDegreeSectionRestriction h q).map_smul c s.val)

theorem toricNativeDegreeMultiplierSectionMap_injective {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    Function.Injective (toricNativeDegreeMultiplierSectionMap h q hq hφ) := by
  intro s t hst
  apply Subtype.ext
  apply toricNativeDegreeSectionRestriction_injective h q
  apply Subtype.ext
  exact congrArg (fun g : toricMultiplierSections ((q : ℤ) • D)
    (Nat.cast_pos.mpr hq) hφ => g.val) hst

theorem toricNativeDegreeMultiplierSectionMap_surjective {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    Function.Surjective (toricNativeDegreeMultiplierSectionMap h q hq hφ) := by
  intro g
  let f : toricSections ((q : ℤ) • D) := ⟨g.val, g.property.1⟩
  let s := (toricNativeDegreeFullSectionEquiv h q).symm f
  have hr : toricNativeDegreeSectionRestriction h q s = f :=
    (toricNativeDegreeFullSectionEquiv h q).apply_symm_apply f
  have hs' : s ∈ fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
      (sourceDegreeMultiplierIdeal (n := n) q φ) := by
    apply (toricNativeDegreeIdealSections_iff_toricMultiplierSections h q hq hφ s).mpr
    rw [hr]
    exact g.property
  refine ⟨⟨s, hs'⟩, ?_⟩
  apply Subtype.ext
  exact congrArg (fun g : toricSections ((q : ℤ) • D) => g.val) hr

/-- BOTH directions for ALL actual whole-ideal H0 sections, rather than
a chosen toric subseries or an incoming ideal section dictionary. -/
def toricNativeDegreeMultiplierSectionEquiv {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    ↥(fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
      (sourceDegreeMultiplierIdeal (n := n) q φ)) ≃ₗ[ℂ]
        toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ :=
  LinearEquiv.ofBijective (toricNativeDegreeMultiplierSectionMap h q hq hφ)
    ⟨toricNativeDegreeMultiplierSectionMap_injective h q hq hφ,
      toricNativeDegreeMultiplierSectionMap_surjective h q hq hφ⟩

/-- The actual literal original tensor-sheaf Gamma of L^q tensor I(q phi)
and the independently defined FULL original toric multiplier sections are
genuinely linearly equivalent. Original qPSH is the only analytic input;
no coherence, Gamma, H0, norm, basis or comparison certificate enters. -/
def toricNativeLiteralMultiplierSectionEquiv {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ ≃ₗ[ℂ]
        toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ :=
  (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h)
    HermitianHolomorphicLineBundle.unit q φ).trans
      (toricNativeDegreeMultiplierSectionEquiv h q hq hφ)

/-- The literal source degree zero retains its actual unit tensor and
internally proved I(0)=O_X, even on original poles. The positive-exponent
legacy toric multiplier definition is never applied at forbidden zero. -/
def toricNativeLiteralDegreeZeroSectionEquiv {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (φ : PolytopeToricVariety γ hs → EReal) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit 0 φ ≃ₗ[ℂ] toricSections ((0 : ℤ) • D) :=
  (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h)
    HermitianHolomorphicLineBundle.unit 0 φ).trans
      ((LinearEquiv.ofEq _ _ (fullHolomorphicDegreeIdealSections_zero_eq_top
        (toricNativeHermitianLineBundle h) HermitianHolomorphicLineBundle.unit φ)).trans
          (Submodule.topEquiv.trans (toricNativeDegreeFullSectionEquiv h 0)))

end SGPT.Toric

end
end ToricCanonicalFragment030
/- END SGPT.Toric.ToricNativeLiteralMultiplierSectionEquiv -/

/- BEGIN SGPT.Toric.ToricNativeSectionTorusAction; source SHA256 bc0c0bea19ecd5c78aeaa215fc6cf8950ea42b8f69e7aa2cade3eb9338b8e085 -/
section ToricCanonicalFragment033

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Genuine translation of ALL independently defined original Cartier
sections on the SAME original dense torus. -/
def toricCartierSectionTranslation (D : ToricDivisor γ hs) (t : Fin n → ℂˣ) :
    toricSections D →ₗ[ℂ] toricSections D where
  toFun g := ⟨fun a => g.val (t * a), translate_mem_toricSections g.property t⟩
  map_add' g k := by apply Subtype.ext; rfl
  map_smul' c g := by apply Subtype.ext; rfl

theorem toricCartierSectionTranslation_one (D : ToricDivisor γ hs) (g : toricSections D) :
    toricCartierSectionTranslation D 1 g = g := by
  apply Subtype.ext
  funext a
  change g.val (1 * a) = g.val a
  rw [one_mul]

theorem toricCartierSectionTranslation_mul (D : ToricDivisor γ hs)
    (t u : Fin n → ℂˣ) (g : toricSections D) :
    toricCartierSectionTranslation D t (toricCartierSectionTranslation D u g) =
      toricCartierSectionTranslation D (t * u) g := by
  apply Subtype.ext
  funext a
  change g.val (u * (t * a)) = g.val ((t * u) * a)
  exact congrArg g.val ((mul_left_comm u t a).trans (mul_assoc t u a).symm)

/-- Operators on ALL actual plain-power ContMDiffSection, constructed
through the proved independent full-H0 dictionary. The whole original
Cartier frame reading will identify this with the source linearization. -/
def toricNativePlainSectionTranslation {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (t : Fin n → ℂˣ) :
    ToricNativePlainPowerSections h q →ₗ[ℂ] ToricNativePlainPowerSections h q :=
  (toricNativePlainPowerFullSectionEquiv h q).symm.toLinearMap.comp
    ((toricCartierSectionTranslation ((q : ℤ) • D) t).comp
      (toricNativePlainPowerFullSectionEquiv h q).toLinearMap)

theorem toricNativePlainSectionTranslation_restriction {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (t : Fin n → ℂˣ)
    (s : ToricNativePlainPowerSections h q) :
    toricNativePlainPowerFullSectionEquiv h q (toricNativePlainSectionTranslation h q t s) =
      toricCartierSectionTranslation ((q : ℤ) • D) t
        (toricNativePlainPowerFullSectionEquiv h q s) :=
  (toricNativePlainPowerFullSectionEquiv h q).apply_symm_apply _

theorem toricNativePlainSectionTranslation_one {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (s : ToricNativePlainPowerSections h q) :
    toricNativePlainSectionTranslation h q 1 s = s := by
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativePlainSectionTranslation_restriction, toricCartierSectionTranslation_one]

theorem toricNativePlainSectionTranslation_mul {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (t u : Fin n → ℂˣ)
    (s : ToricNativePlainPowerSections h q) :
    toricNativePlainSectionTranslation h q t (toricNativePlainSectionTranslation h q u s) =
      toricNativePlainSectionTranslation h q (t * u) s := by
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativePlainSectionTranslation_restriction,
    toricNativePlainSectionTranslation_restriction,
    toricNativePlainSectionTranslation_restriction, toricCartierSectionTranslation_mul]

def toricNativePlainSectionTorusEquiv {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (t : Fin n → ℂˣ) :
    ToricNativePlainPowerSections h q ≃ₗ[ℂ] ToricNativePlainPowerSections h q where
  toFun := toricNativePlainSectionTranslation h q t
  invFun := toricNativePlainSectionTranslation h q t⁻¹
  left_inv s := by
    rw [toricNativePlainSectionTranslation_mul, inv_mul_cancel, toricNativePlainSectionTranslation_one]
  right_inv s := by
    rw [toricNativePlainSectionTranslation_mul, mul_inv_cancel, toricNativePlainSectionTranslation_one]
  map_add' := (toricNativePlainSectionTranslation h q t).map_add
  map_smul' := (toricNativePlainSectionTranslation h q t).map_smul

theorem toricNativePlainSectionTranslation_monomial {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (t : Fin n → ℂˣ) {m : Fin n → ℤ}
    (hm : m ∈ toricLatticePoints ((q : ℤ) • D)) :
    toricNativePlainSectionTranslation h q t (toricNativePlainPowerMonomialSection h q hm) =
      (latticeCharacter m t : ℂ) • toricNativePlainPowerMonomialSection h q hm := by
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativePlainSectionTranslation_restriction, map_smul]
  have hmono : toricNativePlainPowerFullSectionEquiv h q
      (toricNativePlainPowerMonomialSection h q hm) =
        ⟨fun a => (latticeCharacter m a : ℂ), latticeCharacter_mem_toricSections _ hm⟩ :=
    (toricNativePlainPowerFullSectionEquiv h q).apply_symm_apply _
  rw [hmono]
  apply Subtype.ext
  funext a
  change (latticeCharacter m (t * a) : ℂ) =
    (latticeCharacter m t : ℂ) * (latticeCharacter m a : ℂ)
  rw [map_mul, Units.val_mul]

end SGPT.Toric

end
end ToricCanonicalFragment033
/- END SGPT.Toric.ToricNativeSectionTorusAction -/

/- BEGIN SGPT.Toric.ToricNativePlainFrames; source SHA256 1c4501c4eeba44c7cc2249c50858cef37d22be5f10c05b42660d4b7947cc5769 -/
section ToricCanonicalFragment034

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.NativeRightUnit
open HermitianHolomorphicLineBundle
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual ORIGINAL plain unit/positive-power frames, not a new
coefficient or section carrier. -/
def toricNativePlainPowerFrame {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) :
    ∀ q : ℕ, AtlasFrame (toricNativePlainPowerBundle h q)
  | 0 => unitAtlasFrame
  | k + 1 => positivePowerAtlasFrame (toricNativeLineAtlasFrame h v) k


/-- The PROVED actual right-unit map preserves ORIGINAL frame
coefficients at every original boundary point and every degree. -/
theorem toricNativePlainPowerFrame_rightUnit_coefficient {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (v : latticePolytopeVertices γ) (q : ℕ)
    (s : ToricNativeDegreeSections h q) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativePlainPowerFrame h v q).val
        ⟨p, toricNativePlainPowerRightUnitEquiv h q s p⟩).2 =
      ((toricNativeDegreeFrame h v q).val ⟨p, s p⟩).2 := by
  cases q with
  | zero => exact (nativeRightUnit_coordinate unitAtlasFrame (mem_univ p) (s p)).symm
  | succ k =>
    exact (nativeRightUnit_coordinate
      (positivePowerAtlasFrame (toricNativeLineAtlasFrame h v) k)
      (positivePowerAtlasFrame_mem (toricNativeLineAtlasFrame h v) hp k) (s p)).symm

theorem toricNativePlainPowerFullSectionEquiv_symm_actual_coefficient
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ)
    (g : toricSections ((q : ℤ) • D)) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativePlainPowerFrame h v q).val
      ⟨p, (toricNativePlainPowerFullSectionEquiv h q).symm g p⟩).2 =
      toricOriginalSectionCoeff g v (originalPolytopeNativeModelChart γ hs v p) := by
  exact (toricNativePlainPowerFrame_rightUnit_coefficient h v q
    ((toricNativeDegreeFullSectionEquiv h q).symm g) hp).trans
      (toricNativeDegreeFullSectionEquiv_symm_coefficient h q g v hp)

/-- Every actual ORIGINAL plain frame reads the independently given
entire Cartier coefficient of EVERY actual H0 section. -/
theorem toricNativePlainPowerFullSectionEquiv_actual_coefficient
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativePlainPowerFrame h v q).val ⟨p, s p⟩).2 =
      toricOriginalSectionCoeff (toricNativePlainPowerFullSectionEquiv h q s) v
        (originalPolytopeNativeModelChart γ hs v p) := by
  have hc := toricNativePlainPowerFullSectionEquiv_symm_actual_coefficient h q
    (toricNativePlainPowerFullSectionEquiv h q s) v hp
  simpa only [LinearEquiv.symm_apply_apply] using hc

/-- The SAME physical metric of EVERY actual plain-power H0 section in
EVERY original frame, including q0, zeros and all boundary strata. -/
theorem toricNativePlainPowerSection_norm_sq_actual_frame
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ)
    (s : ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ‖s p‖ ^ 2 = ‖((toricNativePlainPowerFrame h v q).val ⟨p, s p⟩).2‖ ^ 2 *
      Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
  have hn := toricNativePlainPowerFullSectionEquiv_symm_norm_sq h q
    (toricNativePlainPowerFullSectionEquiv h q s) v hp
  have hn' : ‖s p‖ ^ 2 =
      ‖toricOriginalSectionCoeff (toricNativePlainPowerFullSectionEquiv h q s) v
        (originalPolytopeNativeModelChart γ hs v p)‖ ^ 2 *
          Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
    simpa only [LinearEquiv.symm_apply_apply] using hn
  exact hn'.trans (congrArg
    (fun z : ℂ => ‖z‖ ^ 2 *
      Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)))
    (toricNativePlainPowerFullSectionEquiv_actual_coefficient h q s v hp).symm)

end SGPT.Toric

end
end ToricCanonicalFragment034
/- END SGPT.Toric.ToricNativePlainFrames -/

/- BEGIN SGPT.Toric.ToricNativeTorusFrameReading; source SHA256 de3adba7ba6797ce3120c3d941ec9e54a66fcc0d219611ae8ad28be2ada87b4c -/
section ToricCanonicalFragment035

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Original translated Cartier coefficients on the WHOLE C^n model,
proved by original entire-coefficient uniqueness, including all boundary. -/
theorem toricOriginalSectionCoeff_translation (D : ToricDivisor γ hs)
    (t : Fin n → ℂˣ) (g : toricSections D) (v : latticePolytopeVertices γ) :
    toricOriginalSectionCoeff (toricCartierSectionTranslation D t g) v =
      fun z => (latticeCharacter (toricCartierDatum D v) t : ℂ) *
        toricOriginalSectionCoeff g v (originalPolytopeNativeModelActionLinear γ hs v t z) := by
  apply toricSectionCoeff_unique D v
    (differentiable_toricOriginalSectionCoeff (toricCartierSectionTranslation D t g) v).continuous
    (((differentiable_const (latticeCharacter (toricCartierDatum D v) t : ℂ)).mul
      ((differentiable_toricOriginalSectionCoeff g v).comp
        (originalPolytopeNativeModelActionLinear γ hs v t).differentiable)).continuous)
    (toricOriginalSectionCoeff_torus (toricCartierSectionTranslation D t g) v)
  intro a
  change g.val (t * a) = _
  rw [toricOriginalSectionCoeff_torus g v (t * a), vertexChart_embedding_mul,
    map_mul, Units.val_mul]
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

theorem toricNativeAction_mem_modelChartSource (v : latticePolytopeVertices γ)
    (t : Fin n → ℂˣ) {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    originalPolytopeNativeAction γ t p ∈ (originalPolytopeNativeModelChart γ hs v).source := by
  rw [originalPolytopeNativeModelChart_source]
  apply (originalPolytopeNativeAction_mem_chart_source_iff γ hs v t p).mpr
  rw [← originalPolytopeNativeModelChart_source]
  exact hp

/-- The transported operator IS the original Cartier toric action:
EVERY actual ORIGINAL plain frame has the correct rational-frame reader
at EVERY original point, including every boundary stratum. There is no
incoming bundle-action or frame-equivariance certificate. -/
theorem toricNativePlainSectionTranslation_actual_frame
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (q : ℕ) (t : Fin n → ℂˣ)
    (s : ToricNativePlainPowerSections h q) (v : latticePolytopeVertices γ)
    {p : PolytopeToricVariety γ hs}
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    ((toricNativePlainPowerFrame h v q).val
      ⟨p, toricNativePlainSectionTranslation h q t s p⟩).2 =
      (latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) t : ℂ) *
        ((toricNativePlainPowerFrame h v q).val
          ⟨originalPolytopeNativeAction γ t p, s (originalPolytopeNativeAction γ t p)⟩).2 := by
  have ht := toricNativeAction_mem_modelChartSource v t hp
  rw [toricNativePlainPowerFullSectionEquiv_actual_coefficient h q
      (toricNativePlainSectionTranslation h q t s) v hp,
    toricNativePlainPowerFullSectionEquiv_actual_coefficient h q s v ht,
    toricNativePlainSectionTranslation_restriction,
    toricOriginalSectionCoeff_translation,
    originalPolytopeNativeModelChart_action γ hs v t p hp]

end SGPT.Toric

end
end ToricCanonicalFragment035
/- END SGPT.Toric.ToricNativeTorusFrameReading -/

/- BEGIN SGPT.Toric.ToricNativeTorusPhysicalNorm; source SHA256 b9e80757460189539168bacb7ae5bc409a05c0e35cffeaec50fd64b32d62f1e2 -/
section ToricCanonicalFragment036

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original action preserves physical squared norms for
EVERY full plain-power section over its actual moved original point. -/
theorem toricNativePlainSectionTranslation_norm_sq {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t)
    (s : ToricNativePlainPowerSections h q) (p : PolytopeToricVariety γ hs) :
    ‖toricNativePlainSectionTranslation h q t s p‖ ^ 2 =
      ‖s (originalPolytopeNativeAction γ t p)‖ ^ 2 := by
  let v := toricNativePreferredVertex γ hs p
  have hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source := toricNativePreferredVertex_mem p
  have htp := toricNativeAction_mem_modelChartSource v t hp
  have hchar : ‖(latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) t : ℂ)‖ ^ 2 = 1 := by
    rw [norm_latticeCharacter_of_compact _ ht, one_pow]
  have hw : h.weight v (originalPolytopeNativeModelChart γ hs v
      (originalPolytopeNativeAction γ t p)) =
        h.weight v (originalPolytopeNativeModelChart γ hs v p) := by
    rw [originalPolytopeNativeModelChart_action γ hs v t p hp]
    exact h.invariant v t ht _
  calc
    _ = ‖((toricNativePlainPowerFrame h v q).val
        ⟨p, toricNativePlainSectionTranslation h q t s p⟩).2‖ ^ 2 *
          Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) :=
      toricNativePlainPowerSection_norm_sq_actual_frame h q _ v hp
    _ = ‖(latticeCharacter (toricCartierDatum ((q : ℤ) • D) v) t : ℂ) *
        ((toricNativePlainPowerFrame h v q).val
          ⟨originalPolytopeNativeAction γ t p, s (originalPolytopeNativeAction γ t p)⟩).2‖ ^ 2 *
            Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
      rw [toricNativePlainSectionTranslation_actual_frame h q t s v hp]
    _ = ‖((toricNativePlainPowerFrame h v q).val
          ⟨originalPolytopeNativeAction γ t p, s (originalPolytopeNativeAction γ t p)⟩).2‖ ^ 2 *
            Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v p)) := by
      rw [norm_mul, mul_pow, hchar, one_mul]
    _ = ‖((toricNativePlainPowerFrame h v q).val
          ⟨originalPolytopeNativeAction γ t p, s (originalPolytopeNativeAction γ t p)⟩).2‖ ^ 2 *
            Real.exp (-(q : ℝ) * h.weight v (originalPolytopeNativeModelChart γ hs v
              (originalPolytopeNativeAction γ t p))) := by rw [hw]
    _ = _ := (toricNativePlainPowerSection_norm_sq_actual_frame h q s v htp).symm


/-- SAME original singular density, including EVERY pole/zero and actual
degree0 convention. No measure or Hilbert invariance certificate enters. -/
theorem toricNativePlainSectionTranslation_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t)
    {φ : PolytopeToricVariety γ hs → EReal} (hinv : PolytopeToricInvariant γ hs φ)
    (s : ToricNativePlainPowerSections h q) (p : PolytopeToricVariety γ hs) :
    originalSectionDensity (n := n) (toricNativePlainPowerBundle h q).Fiber φ q
        (toricNativePlainSectionTranslation h q t s) p =
      originalSectionDensity (n := n) (toricNativePlainPowerBundle h q).Fiber φ q
        s (originalPolytopeNativeAction γ t p) := by
  have hphi : φ (originalPolytopeNativeAction γ t p) = φ p := hinv t ht p
  change ENNReal.ofReal (‖toricNativePlainSectionTranslation h q t s p‖ ^ 2) *
      multiplierWeight (q : ℝ) (φ p) =
    ENNReal.ofReal (‖s (originalPolytopeNativeAction γ t p)‖ ^ 2) *
      multiplierWeight (q : ℝ) (φ (originalPolytopeNativeAction γ t p))
  exact congrArg₂ (fun a b : ENNReal => a * b)
    (congrArg ENNReal.ofReal (toricNativePlainSectionTranslation_norm_sq h q ht s p))
    (congrArg (multiplierWeight (q : ℝ)) hphi.symm)

end SGPT.Toric

end
end ToricCanonicalFragment036
/- END SGPT.Toric.ToricNativeTorusPhysicalNorm -/

/- BEGIN SGPT.Toric.ToricNativeMultiplierTorusAction; source SHA256 d20f43ebf34f79fde878eb31f15626515f1132d3aa1c866db81bf6882ad161e4 -/
section ToricCanonicalFragment037

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine FULL independent original toric multiplier carrier is
preserved, rather than a selected finite character subseries. -/
def toricMultiplierSectionTranslation (D : ToricDivisor γ hs) {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t) :
    toricMultiplierSections D hc hφ →ₗ[ℂ] toricMultiplierSections D hc hφ where
  toFun g := ⟨fun a => g.val (t * a),
    translate_mem_toricMultiplierSections hc hφ hinv g.property ht⟩
  map_add' g k := by apply Subtype.ext; rfl
  map_smul' a g := by apply Subtype.ext; rfl

/-- Actual original tensor-sheaf Gamma action, manufactured from its
proved BOTH-direction full multiplier dictionary and original translation. -/
def toricNativeLiteralMultiplierTranslation {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ →ₗ[ℂ]
        LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
          HermitianHolomorphicLineBundle.unit q φ :=
  (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).symm.toLinearMap.comp
    ((toricMultiplierSectionTranslation ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ hinv ht).comp
      (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).toLinearMap)

theorem toricNativeLiteralMultiplierTranslation_restriction {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t)
    (s : LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ) :
    toricNativeLiteralMultiplierSectionEquiv h q hq hφ
        (toricNativeLiteralMultiplierTranslation h q hq hφ hinv ht s) =
      toricMultiplierSectionTranslation ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ hinv ht
        (toricNativeLiteralMultiplierSectionEquiv h q hq hφ s) :=
  (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).apply_symm_apply _

/-- The ACTUAL sheaf-tensor Gamma forgetful map followed by the actual
physical right-unit section map. This does not reconstruct a section from
an assigned function or a chosen toric subseries. -/
def toricNativeLiteralMultiplierToPlain {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (φ : PolytopeToricVariety γ hs → EReal) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ →ₗ[ℂ] ToricNativePlainPowerSections h q :=
  (toricNativePlainPowerRightUnitEquiv h q).toLinearMap.comp
    ((fullHolomorphicIdealSections (n := n) (toricNativeDegreeBundle h q).Fiber
      (sourceDegreeMultiplierIdeal (n := n) q φ)).subtype.comp
        (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h)
          HermitianHolomorphicLineBundle.unit q φ).toLinearMap)


/-- BOTH independently produced original dictionaries commute with the
actual Gamma forgetful map and original physical right-unit map. -/
theorem toricNativeLiteralMultiplierToPlain_restriction {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (s : LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ) :
    toricNativePlainPowerFullSectionEquiv h q (toricNativeLiteralMultiplierToPlain h q φ s) =
      ⟨(toricNativeLiteralMultiplierSectionEquiv h q hq hφ s).val,
        (toricNativeLiteralMultiplierSectionEquiv h q hq hφ s).property.1⟩ := by
  change toricNativeDegreeFullSectionEquiv h q
    ((toricNativePlainPowerRightUnitEquiv h q).symm
      (toricNativePlainPowerRightUnitEquiv h q
        (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h)
          HermitianHolomorphicLineBundle.unit q φ s).val)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The ACTUAL original Gamma action and ACTUAL plain-power H0 action
commute through the original sheaf maps at every section, not just basis vectors. -/
theorem toricNativeLiteralMultiplierTranslation_toPlain {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t)
    (s : LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ) :
    toricNativeLiteralMultiplierToPlain h q φ
        (toricNativeLiteralMultiplierTranslation h q hq hφ hinv ht s) =
      toricNativePlainSectionTranslation h q t (toricNativeLiteralMultiplierToPlain h q φ s) := by
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativeLiteralMultiplierToPlain_restriction h q hq hφ,
    toricNativePlainSectionTranslation_restriction,
    toricNativeLiteralMultiplierToPlain_restriction h q hq hφ,
    toricNativeLiteralMultiplierTranslation_restriction]
  apply Subtype.ext
  rfl

end SGPT.Toric

end
end ToricCanonicalFragment037
/- END SGPT.Toric.ToricNativeMultiplierTorusAction -/

/- BEGIN SGPT.Toric.ToricNativeMultiplierCharacters; source SHA256 36a826230cc7dbd64cbdb31153dcd73e86de2a0e729939098844cebd889f3a22 -/
section ToricCanonicalFragment038

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeMultiplierExponentSet (D : ToricDivisor γ hs) {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) : Set (Fin n → ℤ) :=
  {m | (fun a => (latticeCharacter m a : ℂ)) ∈ toricMultiplierSections D hc hφ}

theorem finite_toricNativeMultiplierExponentSet (D : ToricDivisor γ hs) {c : ℝ} (hc : 0 < c)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    (toricNativeMultiplierExponentSet D hc hφ).Finite :=
  (finite_toricLatticePoints D).subset (setOf_latticeCharacter_mem_subset hc hφ)

abbrev ToricNativeMultiplierCharacterIndex {D : ToricDivisor γ hs}
    (_h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :=
  ↥(toricNativeMultiplierExponentSet ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ)

instance toricNativeMultiplierIndexFintype {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    Fintype (ToricNativeMultiplierCharacterIndex h q hq hφ) :=
  (finite_toricNativeMultiplierExponentSet ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ).fintype

/-- An actual section of the LITERAL whole source tensor-sheaf Gamma,
manufactured from the genuine contained original character. -/
def toricNativeLiteralMultiplierCharacter {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ :=
  (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).symm
    ⟨fun a => (latticeCharacter m.val a : ℂ), m.property⟩

theorem toricNativeLiteralMultiplierCharacter_restriction {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativeLiteralMultiplierSectionEquiv h q hq hφ
      (toricNativeLiteralMultiplierCharacter h q hq hφ m) =
        ⟨fun a => (latticeCharacter m.val a : ℂ), m.property⟩ :=
  (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).apply_symm_apply _


theorem toricNativeMultiplierCharacterIndex_mem_lattice {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    m.val ∈ toricLatticePoints ((q : ℤ) • D) := by
  have hm : (fun a => (latticeCharacter m.val a : ℂ)) ∈
      toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ := m.property
  exact mem_toricLatticePoints_of_latticeCharacter_mem hm.1

/-- The actual source Gamma character really maps to the actual ordinary
PLAIN original L^q monomial section through the original sheaf/right-unit maps. -/
theorem toricNativeLiteralMultiplierCharacter_toPlain {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativeLiteralMultiplierToPlain h q φ (toricNativeLiteralMultiplierCharacter h q hq hφ m) =
      toricNativePlainPowerMonomialSection h q (toricNativeMultiplierCharacterIndex_mem_lattice h q hq hφ m) := by
  apply (toricNativePlainPowerFullSectionEquiv h q).injective
  rw [toricNativeLiteralMultiplierToPlain_restriction h q hq hφ,
    toricNativeLiteralMultiplierCharacter_restriction]
  exact (toricNativePlainPowerFullSectionEquiv h q).apply_symm_apply _ |>.symm

/-- Actual ORIGINAL Gamma characters are genuine eigen-sections for the
actual original compact-torus action; eigenvectors are produced internally. -/
theorem toricNativeLiteralMultiplierCharacter_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {t : Fin n → ℂˣ} (ht : IsCompactTorusElement t)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativeLiteralMultiplierTranslation h q hq hφ hinv ht
        (toricNativeLiteralMultiplierCharacter h q hq hφ m) =
      (latticeCharacter m.val t : ℂ) • toricNativeLiteralMultiplierCharacter h q hq hφ m := by
  apply (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).injective
  rw [toricNativeLiteralMultiplierTranslation_restriction, map_smul]
  simp only [toricNativeLiteralMultiplierCharacter_restriction]
  apply Subtype.ext
  funext a
  change (latticeCharacter m.val (t * a) : ℂ) =
    (latticeCharacter m.val t : ℂ) * (latticeCharacter m.val a : ℂ)
  rw [map_mul, Units.val_mul]

end SGPT.Toric

end
end ToricCanonicalFragment038
/- END SGPT.Toric.ToricNativeMultiplierCharacters -/

/- BEGIN SGPT.Toric.ToricNativeMultiplierCharacterBasis; source SHA256 ca299cb72d1b64e489a4b95e75c4e18ba20cb8f70ecd83d834c56a3c88803731 -/
section ToricCanonicalFragment039

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open scoped Topology BigOperators Classical ContDiff Manifold
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

def toricNativeLiteralMultiplierFunctionLinearMap {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
      HermitianHolomorphicLineBundle.unit q φ →ₗ[ℂ] ((Fin n → ℂˣ) → ℂ) :=
  (toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ).subtype.comp
    (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).toLinearMap

theorem toricNativeLiteralMultiplierFunctionLinearMap_injective {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    Function.Injective (toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ) := by
  intro s t hst
  apply (toricNativeLiteralMultiplierSectionEquiv h q hq hφ).injective
  apply Subtype.ext
  exact hst

theorem toricNativeLiteralMultiplierFunctionLinearMap_character {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ
      (toricNativeLiteralMultiplierCharacter h q hq hφ m) =
        fun a => (latticeCharacter m.val a : ℂ) :=
  congrArg (fun g : toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ => g.val)
    (toricNativeLiteralMultiplierCharacter_restriction h q hq hφ m)

theorem toricNativeLiteralMultiplierFunctionLinearMap_range {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    LinearMap.range (toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ) =
      toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ := by
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact (toricNativeLiteralMultiplierSectionEquiv h q hq hφ s).property
  · intro hg
    refine ⟨(toricNativeLiteralMultiplierSectionEquiv h q hq hφ).symm ⟨g, hg⟩, ?_⟩
    exact congrArg
      (fun f : toricMultiplierSections ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ => f.val)
      ((toricNativeLiteralMultiplierSectionEquiv h q hq hφ).apply_symm_apply ⟨g, hg⟩)

/-- Actual literal Gamma character sections are independent in the
ORIGINAL sheaf Gamma, not only as abstract supplied eigenvectors. -/
theorem linearIndependent_toricNativeLiteralMultiplierCharacter {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ) :
    LinearIndependent ℂ (toricNativeLiteralMultiplierCharacter h q hq hφ) := by
  apply LinearIndependent.of_comp (toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ)
  have heq : (toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ) ∘
      (toricNativeLiteralMultiplierCharacter h q hq hφ) =
        fun m => fun a => (latticeCharacter m.val a : ℂ) := by
    funext m
    exact toricNativeLiteralMultiplierFunctionLinearMap_character h q hq hφ m
  rw [heq]
  exact linearIndependent_latticeCharacter.comp
    (Subtype.val : ToricNativeMultiplierCharacterIndex h q hq hφ → Fin n → ℤ) Subtype.val_injective

/-- The manufactured actual eigen-sections span the ENTIRE original
literal multiplier Gamma. No chosen toric subseries replaces the carrier. -/
theorem span_toricNativeLiteralMultiplierCharacter {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Submodule.span ℂ (Set.range (toricNativeLiteralMultiplierCharacter h q hq hφ)) = ⊤ := by
  let F := toricNativeLiteralMultiplierFunctionLinearMap h q hq hφ
  apply Submodule.map_injective_of_injective (f := F)
    (toricNativeLiteralMultiplierFunctionLinearMap_injective h q hq hφ)
  rw [Submodule.map_span, Submodule.map_top]
  have himage : F '' Set.range (toricNativeLiteralMultiplierCharacter h q hq hφ) =
      (fun m : Fin n → ℤ => fun a => (latticeCharacter m a : ℂ)) ''
        toricNativeMultiplierExponentSet ((q : ℤ) • D) (Nat.cast_pos.mpr hq) hφ := by
    ext g
    constructor
    · rintro ⟨s, ⟨m, rfl⟩, rfl⟩
      exact ⟨m.val, m.property,
        (toricNativeLiteralMultiplierFunctionLinearMap_character h q hq hφ m).symm⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨toricNativeLiteralMultiplierCharacter h q hq hφ ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, ?_⟩
      exact toricNativeLiteralMultiplierFunctionLinearMap_character h q hq hφ ⟨m, hm⟩
  rw [himage]
  exact (toricMultiplierSections_eq_span (D := (q : ℤ) • D)
    (Nat.cast_pos.mpr hq) hφ hinv).symm.trans
      (toricNativeLiteralMultiplierFunctionLinearMap_range h q hq hφ).symm

/-- A finite algebraic eigenbasis of the FULL ACTUAL original multiplier
Gamma, produced from original invariance; zero/empty Gamma is retained.
Physical singular-weight orthonormal normalization is a separate next step. -/
def toricNativeLiteralMultiplierCharacterBasis {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Module.Basis (ToricNativeMultiplierCharacterIndex h q hq hφ) ℂ
      (LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h)
        HermitianHolomorphicLineBundle.unit q φ) :=
  Module.Basis.mk (linearIndependent_toricNativeLiteralMultiplierCharacter h q hq hφ)
    (span_toricNativeLiteralMultiplierCharacter h q hq hφ hinv).ge

theorem toricNativeLiteralMultiplierCharacterBasis_apply {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n
      (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativeLiteralMultiplierCharacterBasis h q hq hφ hinv m =
      toricNativeLiteralMultiplierCharacter h q hq hφ m := Module.Basis.mk_apply _ _ m

end SGPT.Toric

end
end ToricCanonicalFragment039
/- END SGPT.Toric.ToricNativeMultiplierCharacterBasis -/

/- BEGIN SGPT.Toric.ToricNativePhiUnitary; source SHA256 28ad65f95f83dc84d861a576cda9797fc2f94992c6966ebde02a8ad92d020792 -/
section ToricCanonicalFragment042

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The original source QPSH predicate yields the native potential needed
by the frozen actual singular-weight Hilbert construction. -/
theorem toricNativePhi_globalQpsh {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    IsGlobalQuasiPshPotential (n := n) φ := by
  obtain ⟨θ, hθ⟩ := hφ
  exact ((isThetaPSH_iff_nativeThetaPotential θ φ).mp hθ).quasiPshPotential

/-- The ENTIRE original multiplier Gamma with its true singular-phi norm,
using the same actual raw Guillemin volume throughout. -/
abbrev ToricNativePhiHilbertSections {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :=
  NativePhiKahlerSections (toricNativeHermitianLineBundle h) unit q
    (toricNativePhi_globalQpsh hφ) (polytopeToricKahlerBackground γ hs)

/-- Exact full-Gamma map in both directions; no finite character subspace
replaces the original multiplier sections. -/
def toricNativePhiGammaEquiv {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ) :
    ToricNativePhiHilbertSections h q hφ ≃ₗ[ℂ]
      LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h) unit q φ :=
  nativePhiOriginalGammaEquiv (toricNativeHermitianLineBundle h) unit q
    (toricNativePhi_globalQpsh hφ) _ _

/-- Actual original sheaf action transported to the genuine singular-phi
norm model.  Isometry is proved below, rather than supplied. -/
def toricNativePhiTranslation {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    ToricNativePhiHilbertSections h q hφ →ₗ[ℂ] ToricNativePhiHilbertSections h q hφ :=
  (toricNativePhiGammaEquiv h q hφ).symm.toLinearMap.comp
    ((toricNativeLiteralMultiplierTranslation h q hq hφ hinv ha).comp
      (toricNativePhiGammaEquiv h q hφ).toLinearMap)

/-- The physical right-unit map preserves the SAME original singular
section density, including all poles and the actual degree-zero convention. -/
theorem toricNativeLiteralMultiplierToPlain_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (φ : PolytopeToricVariety γ hs → EReal)
    (s : LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h) unit q φ)
    (p : PolytopeToricVariety γ hs) :
    originalSectionDensity (n := n) (toricNativePlainPowerBundle h q).Fiber φ q
        (toricNativeLiteralMultiplierToPlain h q φ s) p =
      originalSectionDensity (n := n) (toricNativeDegreeBundle h q).Fiber φ q
        (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h) unit q φ s).val p := by
  change ENNReal.ofReal (‖toricNativePlainPowerRightUnitEquiv h q _ p‖ ^ 2) * _ = _
  rw [toricNativePlainPowerRightUnitEquiv_norm]
  rfl

/-- Original Gamma action covariance for the literal physical singular
density.  This is on every point of the native compact variety. -/
theorem toricNativeLiteralMultiplierTranslation_density {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (s : LiteralTwistedMultiplierSections (toricNativeHermitianLineBundle h) unit q φ)
    (p : PolytopeToricVariety γ hs) :
    originalSectionDensity (n := n) (toricNativeDegreeBundle h q).Fiber φ q
        (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h) unit q φ
          (toricNativeLiteralMultiplierTranslation h q hq hφ hinv ha s)).val p =
      originalSectionDensity (n := n) (toricNativeDegreeBundle h q).Fiber φ q
        (literalTwistedMultiplierSectionEquiv (toricNativeHermitianLineBundle h) unit q φ s).val
          (polytopeToricAction γ hs a p) := by
  rw [← toricNativeLiteralMultiplierToPlain_density,
    toricNativeLiteralMultiplierTranslation_toPlain,
    toricNativePlainSectionTranslation_density h q ha hinv,
    toricNativeLiteralMultiplierToPlain_density]
  rfl


/-- Integrating the actual density covariance against the internally
proved invariant RAW Guillemin measure preserves the literal singular norm. -/
theorem toricNativePhiTranslation_norm {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (s : ToricNativePhiHilbertSections h q hφ) :
    ‖toricNativePhiTranslation h q hq hφ hinv ha s‖ = ‖s‖ := by
  let L := toricNativeHermitianLineBundle h
  let μ := kahlerVolume (polytopeToricKahlerBackground γ hs)
  let hμ := isSmoothPositiveVolume_kahlerVolume (polytopeToricKahlerBackground γ hs)
  let hp := toricNativePhi_globalQpsh hφ
  change (nativePhiExtendedSectionNorm (twistedPower L unit q) φ q μ
      (nativePhiUnderlyingSection L unit q hp μ hμ
        (toricNativePhiTranslation h q hq hφ hinv ha s))).toReal =
    (nativePhiExtendedSectionNorm (twistedPower L unit q) φ q μ
      (nativePhiUnderlyingSection L unit q hp μ hμ s)).toReal
  congr 1
  unfold nativePhiExtendedSectionNorm
  congr 1
  have hd : ∀ p,
      originalSectionDensity (n := n) (twistedPower L unit q).Fiber φ q
        (nativePhiUnderlyingSection L unit q hp μ hμ
          (toricNativePhiTranslation h q hq hφ hinv ha s)) p =
      originalSectionDensity (n := n) (twistedPower L unit q).Fiber φ q
        (nativePhiUnderlyingSection L unit q hp μ hμ s) (polytopeToricAction γ hs a p) :=
    toricNativeLiteralMultiplierTranslation_density h q hq hφ hinv ha
      (toricNativePhiGammaEquiv h q hφ s)
  simp_rw [hd]
  exact (toricNativeRawKahlerVolume_measurePreserving ha).lintegral_comp
    (measurable_originalSectionDensity _ hp.1.upperSemicontinuous.measurable _ _)

/-- A genuine complex linear isometry on the ENTIRE original singular-phi
Hilbert space, manufactured from raw-volume invariance and physical density. -/
def toricNativePhiTranslationIsometry {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a) :
    ToricNativePhiHilbertSections h q hφ →ₗᵢ[ℂ] ToricNativePhiHilbertSections h q hφ where
  toLinearMap := toricNativePhiTranslation h q hq hφ hinv ha
  norm_map' := toricNativePhiTranslation_norm h q hq hφ hinv ha


end SGPT.Toric

end
end ToricCanonicalFragment042
/- END SGPT.Toric.ToricNativePhiUnitary -/

/- BEGIN SGPT.Toric.ToricNativePhiEigenbasis; source SHA256 4d23da543d037a23822d06e5a3e5e1c6575a2654deae0896b624289538680520 -/
section ToricCanonicalFragment043

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The genuine produced full original monomial basis, transported to the
ENTIRE actual singular-phi Hilbert space by its original Gamma equivalence. -/
def toricNativePhiCharacterBasis {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Module.Basis (ToricNativeMultiplierCharacterIndex h q hq hφ) ℂ
      (ToricNativePhiHilbertSections h q hφ) :=
  (toricNativeLiteralMultiplierCharacterBasis h q hq hφ hinv).map
    (toricNativePhiGammaEquiv h q hφ).symm

theorem toricNativePhiCharacterBasis_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativePhiTranslation h q hq hφ hinv ha
        (toricNativePhiCharacterBasis h q hq hφ hinv m) =
      (latticeCharacter m.val a : ℂ) • toricNativePhiCharacterBasis h q hq hφ hinv m := by
  simp only [toricNativePhiCharacterBasis, Module.Basis.map_apply,
    toricNativeLiteralMultiplierCharacterBasis_apply]
  change (toricNativePhiGammaEquiv h q hφ).symm
      (toricNativeLiteralMultiplierTranslation h q hq hφ hinv ha
        ((toricNativePhiGammaEquiv h q hφ)
          ((toricNativePhiGammaEquiv h q hφ).symm
            (toricNativeLiteralMultiplierCharacter h q hq hφ m)))) = _
  rw [LinearEquiv.apply_symm_apply, toricNativeLiteralMultiplierCharacter_eigen, map_smul]

/-- Distinct monomial vectors are orthogonal for the ORIGINAL singular-phi
integral inner product, using the actual proved raw-volume unitary action. -/
theorem toricNativePhiCharacterBasis_pairwise_orthogonal {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    Pairwise fun m l => inner ℂ (toricNativePhiCharacterBasis h q hq hφ hinv m)
      (toricNativePhiCharacterBasis h q hq hφ hinv l) = 0 := by
  intro m l hml
  have hne : m.val ≠ l.val := fun h => hml (Subtype.ext h)
  obtain ⟨a, ha, hchars⟩ := exists_compactTorus_latticeCharacter_ne hne
  exact inner_eq_zero_of_linearIsometry_eigen
    (toricNativePhiTranslationIsometry h q hq hφ hinv ha)
    (norm_latticeCharacter_of_compact _ ha) hchars
    (toricNativePhiCharacterBasis_eigen h q hq hφ hinv ha m)
    (toricNativePhiCharacterBasis_eigen h q hq hφ hinv ha l)

/-- Full actual ON EIGENbasis, obtained by positive-real normalization of
the produced monomials in the genuine SINGULAR-PHI Hilbert norm.  Empty
Gamma/character sets are preserved. No ON/eigenbasis premise is supplied. -/
def toricNativePhiOrthonormalEigenbasis {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    OrthonormalBasis (ToricNativeMultiplierCharacterIndex h q hq hφ) ℂ
      (ToricNativePhiHilbertSections h q hφ) :=
  normalizedOrthogonalComplexBasis (toricNativePhiCharacterBasis h q hq hφ hinv)
    (toricNativePhiCharacterBasis_pairwise_orthogonal h q hq hφ hinv)

/-- Every produced ON vector remains an actual original character
eigensection for EVERY compact torus element. -/
theorem toricNativePhiOrthonormalEigenbasis_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativePhiTranslation h q hq hφ hinv ha
        (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m) =
      (latticeCharacter m.val a : ℂ) •
        toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m := by
  simp only [toricNativePhiOrthonormalEigenbasis, normalizedOrthogonalComplexBasis_apply,
    map_smul, toricNativePhiCharacterBasis_eigen]
  exact smul_comm _ _ _

/-- Physical ordinary original L^q sections from the actual normalized
Gamma vectors, using the proved sheaf forgetful and right-unit maps. -/
def toricNativePhiOrthonormalPlainSection {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) : ToricNativePlainPowerSections h q :=
  toricNativeLiteralMultiplierToPlain h q φ
    (toricNativePhiGammaEquiv h q hφ (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m))

/-- The genuine plain L^q readback is an actual toric eigensection, not
merely a vector of an abstract finite-dimensional representation. -/
theorem toricNativePhiOrthonormalPlainSection_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativePlainSectionTranslation h q a
        (toricNativePhiOrthonormalPlainSection h q hq hφ hinv m) =
      (latticeCharacter m.val a : ℂ) •
        toricNativePhiOrthonormalPlainSection h q hq hφ hinv m := by
  unfold toricNativePhiOrthonormalPlainSection
  rw [← toricNativeLiteralMultiplierTranslation_toPlain h q hq hφ hinv ha]
  have he := congrArg (toricNativePhiGammaEquiv h q hφ)
    (toricNativePhiOrthonormalEigenbasis_eigen h q hq hφ hinv ha m)
  change toricNativeLiteralMultiplierTranslation h q hq hφ hinv ha
      ((toricNativePhiGammaEquiv h q hφ)
        (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m)) = _ at he
  rw [map_smul] at he
  rw [he, map_smul]

/-- The ordinary physical ON vectors are exactly positive-real singular
norm normalizations of the genuine original monomial L^q sections. -/
theorem toricNativePhiOrthonormalPlainSection_eq_normalizedMonomial {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativePhiOrthonormalPlainSection h q hq hφ hinv m =
      ((‖toricNativePhiCharacterBasis h q hq hφ hinv m‖⁻¹ : ℝ) : ℂ) •
        toricNativePlainPowerMonomialSection h q
          (toricNativeMultiplierCharacterIndex_mem_lattice h q hq hφ m) := by
  simp only [toricNativePhiOrthonormalPlainSection, toricNativePhiOrthonormalEigenbasis,
    normalizedOrthogonalComplexBasis_apply, map_smul]
  congr 1
  rw [toricNativePhiCharacterBasis, Module.Basis.map_apply,
    toricNativeLiteralMultiplierCharacterBasis_apply,
    LinearEquiv.apply_symm_apply, toricNativeLiteralMultiplierCharacter_toPlain]

/-- Genuine toric eigensections for the ENTIRE original complex algebraic
torus, as required by the source displayed formula, not only its compact part. -/
theorem toricNativePhiOrthonormalPlainSection_complexTorus_eigen {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (a : Fin n → ℂˣ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    toricNativePlainSectionTranslation h q a
        (toricNativePhiOrthonormalPlainSection h q hq hφ hinv m) =
      (latticeCharacter m.val a : ℂ) •
        toricNativePhiOrthonormalPlainSection h q hq hφ hinv m := by
  rw [toricNativePhiOrthonormalPlainSection_eq_normalizedMonomial, map_smul,
    toricNativePlainSectionTranslation_monomial]
  exact smul_comm _ _ _

end SGPT.Toric

end
end ToricCanonicalFragment043
/- END SGPT.Toric.ToricNativePhiEigenbasis -/

/- BEGIN SGPT.Toric.ToricNativePhiBergmanReadback; source SHA256 c19a3dbf8033d184461c38754e09879c99c8f2fbf00d4ef6815bacab76f025c9 -/
section ToricCanonicalFragment044

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every original Gamma vector has the SAME actual singular norm after
the physical plain-power right-unit readback.  This holds also at q=0. -/
theorem toricNativePhi_ofReal_norm_eq_plain {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (s : ToricNativePhiHilbertSections h q hφ) :
    ENNReal.ofReal ‖s‖ = nativePhiExtendedSectionNorm (toricNativePlainPowerBundle h q) φ q
      (kahlerVolume (polytopeToricKahlerBackground γ hs))
      (toricNativeLiteralMultiplierToPlain h q φ (toricNativePhiGammaEquiv h q hφ s)) := by
  rw [nativePhi_ofReal_norm (toricNativeHermitianLineBundle h) unit q
    (toricNativePhi_globalQpsh hφ) _ _]
  unfold nativePhiExtendedSectionNorm
  congr 1
  apply lintegral_congr
  intro p
  exact (toricNativeLiteralMultiplierToPlain_density h q φ
    (toricNativePhiGammaEquiv h q hφ s) p).symm

/-- Every produced ordinary L^q eigensection has the literal source
singular-phi weighted norm one for the SAME original raw Guillemin measure. -/
theorem toricNativePhiOrthonormalPlainSection_original_norm {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ)
    (m : ToricNativeMultiplierCharacterIndex h q hq hφ) :
    nativePhiExtendedSectionNorm (toricNativePlainPowerBundle h q) φ q
      (kahlerVolume (polytopeToricKahlerBackground γ hs))
      (toricNativePhiOrthonormalPlainSection h q hq hφ hinv m) = 1 := by
  rw [toricNativePhiOrthonormalPlainSection, ← toricNativePhi_ofReal_norm_eq_plain,
    (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv).norm_eq_one, ENNReal.ofReal_one]

/-- The literal physical finite sum of squared norms of the ACTUAL full
singular-phi ON eigensections, with no prescribed Bergman-density output. -/
def toricNativePhiBergmanDensity {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) : ENNReal :=
  ∑ m, ENNReal.ofReal (‖toricNativePhiOrthonormalPlainSection h q hq hφ hinv m p‖ ^ 2)

/-- The entire finite Bergman sum is pointwise compact-torus invariant,
including its base locus and the empty/zero-dimensional Hilbert space. -/
theorem toricNativePhiBergmanDensity_invariant {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (p : PolytopeToricVariety γ hs) :
    toricNativePhiBergmanDensity h q hq hφ hinv (polytopeToricAction γ hs a p) =
      toricNativePhiBergmanDensity h q hq hφ hinv p := by
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  let s := toricNativePhiOrthonormalPlainSection h q hq hφ hinv m
  calc
    ‖s (polytopeToricAction γ hs a p)‖ ^ 2 =
        ‖toricNativePlainSectionTranslation h q a s p‖ ^ 2 :=
      (toricNativePlainSectionTranslation_norm_sq h q ha s p).symm
    _ = ‖(latticeCharacter m.val a : ℂ) • s p‖ ^ 2 := by
      rw [toricNativePhiOrthonormalPlainSection_eigen h q hq hφ hinv ha m]
      rfl
    _ = ‖s p‖ ^ 2 := by
      rw [norm_smul, norm_latticeCharacter_of_compact _ ha, one_mul]

/-- The exact displayed source finite Bergman potential; logarithm at
zero is genuine negative infinity, with no clipping or empty-basis exception. -/
def toricNativePhiBergmanPotential {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) : EReal :=
  ((q : ℝ)⁻¹ : EReal) * ENNReal.log (toricNativePhiBergmanDensity h q hq hφ hinv p)

/-- Pointwise invariance of the actual displayed Bergman expression,
derived from the original singular-phi ON eigensections. -/
theorem toricNativePhiBergmanPotential_invariant {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) :
    PolytopeToricInvariant γ hs (toricNativePhiBergmanPotential h q hq hφ hinv) := by
  intro a ha p
  unfold toricNativePhiBergmanPotential
  rw [toricNativePhiBergmanDensity_invariant h q hq hφ hinv ha p]

end SGPT.Toric

end
end ToricCanonicalFragment044
/- END SGPT.Toric.ToricNativePhiBergmanReadback -/

/- BEGIN SGPT.Toric.ToricNativePhiGlobalBergman; source SHA256 8c1f7404abcd7ca710f96a460cb8a93a96bfc870806ac9b1a8433ccfa4bcd9e9 -/
section ToricCanonicalFragment045

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Bundle MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.NativeSingularPhi
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff Manifold ENNReal BigOperators
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual ALL-section, singular-phi integral-unit-ball supremum is
EXACTLY the produced original physical full ON eigensection finite sum. -/
theorem toricNativePhiOriginalBergmanDensity_eq_eigenbasis {D : ToricDivisor γ hs}
    (h : BigToricMetric D) (q : ℕ) (hq : 0 < q)
    {φ : PolytopeToricVariety γ hs → EReal}
    (hφ : (ofFixedModel n (PolytopeToricVariety γ hs)).IsQPSH φ)
    (hinv : PolytopeToricInvariant γ hs φ) (p : PolytopeToricVariety γ hs) :
    nativePhiOriginalBergmanDensity (toricNativeHermitianLineBundle h) unit q
        (φ := φ) (kahlerVolume (polytopeToricKahlerBackground γ hs)) p =
      toricNativePhiBergmanDensity h q hq hφ hinv p := by
  rw [nativePhiOriginalBergmanDensity_eq_basis (toricNativeHermitianLineBundle h) unit q
    (toricNativePhi_globalQpsh hφ) _
    (isSmoothPositiveVolume_kahlerVolume (polytopeToricKahlerBackground γ hs))
    (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv) p,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro m _
  change ENNReal.ofReal (‖nativePhiUnderlyingSection (toricNativeHermitianLineBundle h) unit q
      (toricNativePhi_globalQpsh hφ) _ _
      (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m) p‖ ^ 2) =
    ENNReal.ofReal (‖toricNativePlainPowerRightUnitEquiv h q
      (nativePhiUnderlyingSection (toricNativeHermitianLineBundle h) unit q
        (toricNativePhi_globalQpsh hφ) _ _
        (toricNativePhiOrthonormalEigenbasis h q hq hφ hinv m)) p‖ ^ 2)
  rw [toricNativePlainPowerRightUnitEquiv_norm]



end SGPT.Toric

end
end ToricCanonicalFragment045
/- END SGPT.Toric.ToricNativePhiGlobalBergman -/
