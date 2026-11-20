import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import SGPT.Bergman.Quant2SharpSpectral
import SGPT.Bergman.SourceBergmanFiniteMeasures
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import SGPT.Okounkov.TranscendentalWNRegStatement
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

/-!
# Quant2SharpKahlerDensity

Identification of the Monge-Ampere density of the smooth weight with the Kahler density, and the measure-level upper bound for weak limits of Bergman measures.

Support for source `prop:smooth_weak_conv` (sharp upper bound `τ ≤ θ^n_{P_{θ,X}[φ]_I(v)}` for every
weak cluster point `τ` of the Bergman measures). Ported verbatim (modulo module names) from the
previous team's drafts under `wip/RESUME-20261109/KODAIRA-TRANSPORT/` and re-checked.
-/

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpChartDensityUniqueness.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set MeasureTheory
open SGPT.Foundations.Analysis.FirstPass
/-- The SAME actual chart measure has a unique continuous nonnegative
density at every chart point. This identifies the density returned by the
original sharp-upper producer with the native Kahler top density; no density
identity is added as a new original-endpoint hypothesis. -/
theorem sourceSharp_actual_chart_density_unique {n : ℕ}
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    {ρ σ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ U) (hσ : ContinuousOn σ U)
    (hmap : (volume.restrict U).withDensity (fun z => ENNReal.ofReal (ρ z)) =
      (volume.restrict U).withDensity (fun z => ENNReal.ofReal (σ z)))
    {a : ComplexModel n} (ha : a ∈ U) (hρa : 0 ≤ ρ a) (hσa : 0 ≤ σ a) :
    ρ a = σ a := by
  have hρe : ContinuousOn (fun z => ENNReal.ofReal (ρ z)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn hρ
  have hσe : ContinuousOn (fun z => ENNReal.ofReal (σ z)) U :=
    ENNReal.continuous_ofReal.comp_continuousOn hσ
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (hρe.aemeasurable hU.measurableSet) (hσe.aemeasurable hU.measurableSet)).mp hmap
  have heq := Measure.eqOn_open_of_ae_eq hae hU hρe hσe
  exact (ENNReal.ofReal_eq_ofReal_iff hρa hσa).mp (heq ha)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpKahlerDensityIdentity.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open GlobalNonPluripolar DiagonalMass IntegrationCurrent SmoothMixedMeasureDensity
  ProductTestForms TopDegreeDensity ChartwiseGlobalL1
open scoped Topology ContDiff
variable {n : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
/-- Readback of the canonical chart density of the SAME native Kahler
volume, from its actual zero-potential smooth mixed-measure authority.
The measure, top power and density are existing native objects. -/
theorem sourceSharp_kahlerVolume_chart_map (omega : KahlerBackground n X)
    (e : ComplexChart n X) :
    Measure.map e.val ((kahlerVolume omega).restrict e.val.source) =
      (volume.restrict e.val.target).withDensity
        (fun z => ENNReal.ofReal (topDensity ((formPow omega.form.val n).coeff e z))) := by
  have hdensity : chartDensity (fun _ => omega.form) e =
      fun z => ENNReal.ofReal (topDensity ((formPow omega.form.val n).coeff e z)) := by
    funext z
    simp only [chartDensity, formPow_coeff, formPower_eq_wedgeProd, topDensity_wedgeProd]
  have h0 : IsThetaPshPotential omega.form.val (fun _ => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x,e.val.map_source hx,e.val.left_inv hx⟩
  let ν := (volume.restrict e.val.target).withDensity (chartDensity (fun _ => omega.form) e)
  have hac : ν ≪ volume.restrict e.val.target := withDensity_absolutelyContinuous _ _
  have hν : (kahlerVolume omega).restrict e.val.source = Measure.map e.val.symm ν := by
    rw [← himage,kahlerVolume,diagonalPotentialMeasure]
    exact restrict_image_eq_map (fun _ => h0.1) e e.val.open_target.measurableSet (Subset.refl _)
  have hinv : AEMeasurable e.val.symm ν :=
    (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac hac
  have hforward : AEMeasurable e.val (Measure.map e.val.symm ν) := by
    rw [← hν]
    exact e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  rw [hν,hforward.map_map_of_aemeasurable hinv]
  have hid : (e.val ∘ e.val.symm) =ᵐ[ν] id :=
    hac.ae_le ((ae_restrict_mem e.val.open_target.measurableSet).mono fun z hz => e.val.right_inv hz)
  rw [Measure.map_congr hid,Measure.map_id]
  change (volume.restrict e.val.target).withDensity (chartDensity (fun _ => omega.form) e) = _
  rw [hdensity]

/-- The actual smooth chart density returned by the original local upper is
necessarily the native Kahler top density, at the SAME original chart point. -/
theorem sourceSharp_kahler_chart_density_eq (omega : KahlerBackground n X)
    (e : ComplexChart n X) {ρ : ComplexModel n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ e.val.target)
    (hmap : Measure.map e.val ((kahlerVolume omega).restrict e.val.source) =
      (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {a : ComplexModel n} (ha : a ∈ e.val.target) (hρa : 0 ≤ ρ a) :
    ρ a = topDensity ((formPow omega.form.val n).coeff e a) := by
  have hsm : ContDiffOn ℝ ∞
      (fun z => topDensity ((formPow omega.form.val n).coeff e z)) e.val.target :=
    (ContinuousAlternatingMap.apply ℝ (ComplexModel n) ℝ (topBasis n)).contDiff.comp_contDiffOn
      ((formPow omega.form.val n).smooth e)
  exact sourceSharp_actual_chart_density_unique e.val.open_target
    hρ.continuousOn hsm.continuousOn
    (hmap.symm.trans (sourceSharp_kahlerVolume_chart_map omega e)) ha hρa
    (topDensity_formPow_pos omega.isKahler.1 ha).le
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalKahlerUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open IntegrationCurrent ProductTestForms TopDegreeDensity ManifoldTubePositivity
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
/-- The actual normalized original beta density has the genuine global
smooth top-form ratio as its upper limsup. The chart density is identified
internally with the native raw omega^n density, and the physical curvature
is the original global c1(L)+ddc(v). No probability or projectivity premise,
chart/frame/spectral choice, or density-identification certificate remains. -/
theorem sourceSharp_original_beta_kahler_pointwise_upper
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (φ : X → EReal) (x : X) :
    limsup (fun (k : ℕ) => sourceBergmanNormalization (n := n) k *
      sourcePartialBergmanDensity L T (wholeWeightedSubset v)
        ((kahlerVolume omega).comap
          (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
        ⟨x,Set.mem_univ x⟩) atTop ≤
      ENNReal.ofReal (topRatio omega.form.val
        (formPow (sourceNativeFirstChernForm L hL + ddcClosedForm v hv).val n) x) := by
  let c := complexChartAt (n := n) x
  let a := c.val x
  obtain ⟨ρ,d,S,hρsm,hmap,hρ,_hS,_hwedge,hupper,_hbad⟩ :=
    sourceSharp_original_beta_pointwise_upper L T hL hT v hv (kahlerVolume omega)
      (KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega) x φ
  have hρeq := sourceSharp_kahler_chart_density_eq omega c hρsm hmap
    (c.val.map_source (mem_complexChartAt_source x)) hρ.le
  have hcoeff : (sourceNativeFirstChernForm L hL + ddcClosedForm v hv).val.coeff c a =
      sourcePhysicalCurvature L hL v c a := rfl
  have hratio : topRatio omega.form.val
      (formPow (sourceNativeFirstChernForm L hL + ddcClosedForm v hv).val n) x =
      actualTopPowerDensity (sourcePhysicalCurvature L hL v c a) / ρ a := by
    change topDensity ((formPow (sourceNativeFirstChernForm L hL + ddcClosedForm v hv).val n).coeff c a) /
      topDensity ((formPow omega.form.val n).coeff c a) = _
    rw [formPow_coeff,topDensity_formPower,hcoeff,← hρeq]
  rw [hratio]
  exact hupper
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalBetaDensity.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open ChartwiseGlobalL1 IntegrationCurrent
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.ContactConcentration
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
/-- The original unit-volume choice of omega manufactures BM on the SAME raw
measure; actual beta is its original normalized measurable density and has
ONE common bound before every positive degree, phi and point. No replacement
probability measure or incoming norm/density/bound certificate is used. -/
theorem sourceSharp_original_beta_density_data
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) :
    let b := fun (k : ℕ) (φ : X → EReal) (x : X) => sourceBergmanNormalization (n := n) k *
      sourcePartialBergmanDensity L T (wholeWeightedSubset v)
        ((kahlerVolume omega).comap
          (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
        ⟨x,Set.mem_univ x⟩
    ∃ D : ℝ, 0 < D ∧ ∀ (k : ℕ) (hk : 0 < k) (φ : X → EReal),
      (sourceBergmanFiniteMeasure omega L T hL hT v hv k hk φ : Measure X) =
        (kahlerVolume omega).withDensity (b k φ) ∧
      Measurable (b k φ) ∧ ∀ x, b k φ x ≤ ENNReal.ofReal D := by
  intro b
  let μ := kahlerVolume omega
  let W := wholeWeightedSubset (n := n) v
  let μK := μ.comap (Subtype.val : W.carrier → X)
  let : IsProbabilityMeasure μ := ⟨hvol⟩
  have hμ : IsSmoothPositiveVolume (n := n) μ :=
    KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  have hBM := smoothPositiveProbabilityVolume_general_BM L T v μ hμ
  obtain ⟨C,hC,hbound⟩ := exists_source_smooth_weighted_Bergman_bound L T hL hT v hv μ hμ
  refine ⟨(n.factorial : ℝ) * C,
    mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) hC,fun k hk φ => ?_⟩
  have hext : sourcePartialBergmanDensityOnX L T W μK k φ =
      fun x => sourcePartialBergmanDensity L T W μK k φ ⟨x,Set.mem_univ x⟩ := by
    funext x
    exact sourcePartialBergmanDensityOnX_in L T W μK k φ ⟨x,Set.mem_univ x⟩
  have hm : Measurable (fun x => sourcePartialBergmanDensity L T W μK k φ ⟨x,Set.mem_univ x⟩) := by
    rw [← hext]
    exact sourcePartialBergmanDensityOnX_measurable L T W μK hBM k hk φ
  have hmap : Measure.map (Subtype.val : W.carrier → X) μK = μ := by
    dsimp only [μK,W,wholeWeightedSubset]
    rw [map_comap_subtype_coe MeasurableSet.univ,Measure.restrict_univ]
  have hread := sourcePartialBergmanMeasure_eq_global_density L T W μK hBM k hk φ
  have hfactor : sourceBergmanNormalization (n := n) k *
      ENNReal.ofReal (C * (k : ℝ) ^ n) = ENNReal.ofReal ((n.factorial : ℝ) * C) := by
    have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    rw [sourceBergmanNormalization,← ENNReal.ofReal_mul
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))]
    congr 1
    field_simp
  refine ⟨?_,measurable_const.mul hm,fun x => ?_⟩
  · change sourcePartialBergmanMeasure L T W μK k φ = μ.withDensity (b k φ)
    rw [hread,hmap,hext]
    rw [← withDensity_smul _ hm]
    rfl
  · change sourceBergmanNormalization (n := n) k *
      sourcePartialBergmanDensity L T W μK k φ ⟨x,Set.mem_univ x⟩ ≤ _
    exact (mul_le_mul_right (hbound k hk φ ⟨x,Set.mem_univ x⟩) _).trans_eq hfactor
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpWeakDensityFilterUpper.lean`.
section
set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
/-- The bounded test step used by the original beta cluster consumer.
The weak limit may be on any nontrivial subfilter of integer atTop. Its
scalar test limit is bounded by the ORIGINAL integer-sequence limsup, so
Fatou is used only for that sequence, never for an arbitrary net. This retains
actual finite measures, their actual density readback and the
pointwise sharp upper; it never normalizes them to probabilities. -/
theorem sourceSharp_weak_density_filter_test_upper
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {ν : ℕ → FiniteMeasure X} {τ : FiniteMeasure X}
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (hweak : Tendsto ν l (𝓝 τ)) {f : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞}
    (hν : ∀ j, (ν j : Measure X) = μ.withDensity (f j))
    (hf : ∀ j, Measurable (f j)) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ j x, f j x ≤ C)
    (hpoint : ∀ x, limsup (fun j => f j x) atTop ≤ F x)
    (g : BoundedContinuousFunction X ℝ≥0) (hg : ∀ x, g x ≤ 1) :
    (∫⁻ x, (g x : ℝ≥0∞) ∂(τ : Measure X)) ≤
      ∫⁻ x, (g x : ℝ≥0∞) ∂μ.withDensity F := by
  have hgm : Measurable (fun x => (g x : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.comp g.continuous).measurable
  have hgb (x : X) : (g x : ℝ≥0∞) ≤ 1 := by exact_mod_cast hg x
  have hprod : ∀ j, Measurable (fun x => f j x * (g x : ℝ≥0∞)) := fun j => (hf j).mul hgm
  have hdom : ∀ j, (fun x => f j x * (g x : ℝ≥0∞)) ≤ᵐ[μ] fun _ => C := by
    intro j
    apply Filter.Eventually.of_forall
    intro x
    calc
      _ ≤ C * 1 := mul_le_mul (hbound j x) (hgb x) zero_le zero_le
      _ = C := mul_one C
  have hfin : (∫⁻ _ : X, C ∂μ) ≠ ∞ := by
    simpa only [lintegral_const] using ENNReal.mul_ne_top hC (measure_ne_top μ univ)
  have hFatou := limsup_lintegral_le (fun _ : X => C) hprod hdom hfin
  have hw := FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hweak g
  have heq (j : ℕ) : (∫⁻ x, (g x : ℝ≥0∞) ∂(ν j : Measure X)) =
      ∫⁻ x, f j x * (g x : ℝ≥0∞) ∂μ := by
    rw [hν j]
    exact lintegral_withDensity_eq_lintegral_mul μ (hf j) hgm
  have hw' := hw.congr' (Filter.Eventually.of_forall heq)
  calc
    _ = limsup (fun j => ∫⁻ x, f j x * (g x : ℝ≥0∞) ∂μ) l := hw'.limsup_eq.symm
    _ ≤ limsup (fun j => ∫⁻ x, f j x * (g x : ℝ≥0∞) ∂μ) atTop :=
      limsup_le_limsup_of_le hl
    _ ≤ ∫⁻ x, limsup (fun j => f j x * (g x : ℝ≥0∞)) atTop ∂μ := hFatou
    _ ≤ ∫⁻ x, F x * (g x : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ENNReal.limsup_mul_const_of_ne_top ENNReal.coe_ne_top]
      simpa only [mul_comm] using mul_le_mul_left (hpoint x) (g x : ℝ≥0∞)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul μ hF hgm).symm

/-- Closed-set approximation and actual weakly regular finite measures turn
the original bounded beta test inequalities into the full measure order. -/
theorem sourceSharp_weak_density_filter_measure_upper
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {μ : Measure X} [IsFiniteMeasure μ]
    {ν : ℕ → FiniteMeasure X} {τ : FiniteMeasure X}
    [Measure.WeaklyRegular (τ : Measure X)]
    {f : ℕ → X → ℝ≥0∞} {F : X → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity F)]
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (hweak : Tendsto ν l (𝓝 τ))
    (hν : ∀ j, (ν j : Measure X) = μ.withDensity (f j))
    (hf : ∀ j, Measurable (f j)) (hF : Measurable F)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hbound : ∀ j x, f j x ≤ C)
    (hpoint : ∀ x, limsup (fun j => f j x) atTop ≤ F x) :
    (τ : Measure X) ≤ μ.withDensity F := by
  have hclosed : ∀ K : Set X, IsClosed K → (τ : Measure X) K ≤ (μ.withDensity F) K := by
    intro K hK
    apply ge_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK (μ.withDensity F))
    apply Filter.Eventually.of_forall
    intro m
    exact (HasOuterApproxClosed.measure_le_lintegral hK (τ : Measure X) m).trans
      (sourceSharp_weak_density_filter_test_upper l hl hweak hν hf hF hC hbound hpoint
        (hK.apprSeq m) (HasOuterApproxClosed.apprSeq_apply_le_one hK m))
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top (τ : Measure X) A)]
  exact iSup_le fun K => iSup_le fun hKA => iSup_le fun hK =>
    (hclosed K hK).trans (measure_mono hKA)
end SGPT.Bergman.SharpLocalUpper
end
end

-- Ported from `wip/RESUME-20261109/KODAIRA-TRANSPORT/ORIGINAL-SMOOTH-WEAK-CONV01/sources/SourceSharpOriginalFilterClusterUpper.lean`.
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SharpLocalUpper
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open IntegrationCurrent ProductTestForms ManifoldTubePositivity
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.NativeHermitianMetric
open SGPT.Bergman.ContactConcentration SGPT.Okounkov.TranscendentalWNReg
open HermitianHolomorphicLineBundle
open scoped Topology ContDiff ENNReal
variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
/-- Every actual weak limit on a nontrivial subfilter of integer atTop of the original beta is dominated
by the native positive top measure of c1(L)+ddc(v). All local sharp estimates,
actual density/volume identification, common bounds and weak test transport
are manufactured; no Berman upper, probability replacement, projectivity,
contact-null, mass limit or desired measure inequality is a caller premise. -/
theorem sourceSharp_original_filter_cluster_le_positiveTopMeasure
    (omega : KahlerBackground n X) (hvol : (kahlerVolume omega) univ = 1)
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v) (φ : X → EReal)
    (σ : ℕ → ℕ) (hpos : ∀ j, 0 < σ j) (hσ : Tendsto σ atTop atTop)
    (l : Filter ℕ) [NeBot l] (hl : l ≤ atTop) (τ : FiniteMeasure X)
    (hweak : Tendsto (fun j => sourceBergmanFiniteMeasure omega L T hL hT v hv
      (σ j) (hpos j) φ) l (𝓝 τ)) :
    (τ : Measure X) ≤ positiveTopMeasure omega (sourceNativeFirstChernForm L hL + ddcClosedForm v hv) := by
  let μ := kahlerVolume omega
  let α := sourceNativeFirstChernForm L hL + ddcClosedForm v hv
  let F : X → ℝ≥0∞ := fun x => ENNReal.ofReal (topRatio omega.form.val (formPow α.val n) x)
  let b := fun (k : ℕ) (φ : X → EReal) (x : X) => sourceBergmanNormalization (n := n) k *
    sourcePartialBergmanDensity L T (wholeWeightedSubset v)
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ
      ⟨x,Set.mem_univ x⟩
  let f := fun j x => b (σ j) φ x
  have hc : Continuous (topRatio omega.form.val (formPow α.val n)) :=
    continuous_topRatio omega.isKahler.1 _
  have hF : Measurable F := (ENNReal.continuous_ofReal.comp hc).measurable
  let : IsFiniteMeasure (μ.withDensity F) := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
    obtain ⟨x₀,_,hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
    calc
      _ ≤ ∫⁻ _ : X, ENNReal.ofReal (topRatio omega.form.val (formPow α.val n) x₀) ∂μ :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hx₀ (mem_univ x)))
      _ < (∞ : ℝ≥0∞) := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)⟩
  let : TopologicalSpace.PseudoMetrizableSpace X :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n X
  obtain ⟨D,_hD,hdata⟩ := sourceSharp_original_beta_density_data omega hvol L T hL hT v hv
  have hpoint (x : X) : limsup (fun j => f j x) atTop ≤ F x := by
    have hs := hσ.limsup_comp_le_limsup (u := fun k : ℕ => b k φ x)
    exact hs.trans (sourceSharp_original_beta_kahler_pointwise_upper omega L T hL hT v hv φ x)
  change (τ : Measure X) ≤ μ.withDensity F
  apply sourceSharp_weak_density_filter_measure_upper l hl hweak
    (f := f) (F := F) (C := ENNReal.ofReal D)
  · intro j
    exact (hdata (σ j) (hpos j) φ).1
  · intro j
    exact (hdata (σ j) (hpos j) φ).2.1
  · exact hF
  · exact ENNReal.ofReal_ne_top
  · intro j x
    exact (hdata (σ j) (hpos j) φ).2.2 x
  · exact hpoint
end SGPT.Bergman.SharpLocalUpper
end
end
