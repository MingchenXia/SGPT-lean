import SGPT.IGood.DXLowPointwise
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.OpenPos
import SGPT.Bergman.SourceMultiplierSectionGlobalMass
import SGPT.Bergman.SourceTwistedMultiplierSections

/-!
# The dimension of `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` dominates the integral of the Bergman density

Blueprint `claude-dx-low`, node `claude-dx-low:trace`. For the weighted `L²` norm
`‖s‖² = ∫_X |s|² e^{-kφ} dμ` on the finite-dimensional space
`H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` (the holomorphic sections of finite norm,
`fullHolomorphicThetaDegreeIdealSections_iff_finite_integral`), an orthonormal basis `(sᵢ)`
gives a measurable function `D_k = ∑ᵢ |sᵢ|² e^{-kφ}` with `∫ D_k dμ = h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` and
`B_k ≤ D_k` (Cauchy–Schwarz), where `B_k` is the weighted Bergman density
(`bergmanDensity`). This is `exists_bergman_majorant`; the inner product is produced from the
parallelogram law (`InnerProductSpace.ofNorm`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
  SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.QuantizationDraft
  SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

namespace SGPT.IGood.DXLow

/-- A smooth positive volume charges every nonempty open set. -/
theorem isOpenPosMeasure_of_isSmoothPositiveVolume {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) : μ.IsOpenPosMeasure := by
  refine ⟨fun O hO hne => ?_⟩
  obtain ⟨y, hy⟩ := hne
  set e := complexChartAt (n := n) y with he
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  have hys : y ∈ e.val.source := mem_complexChartAt_source y
  set A : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' O with hA
  have hAo : IsOpen A := e.val.isOpen_inter_preimage_symm hO
  have hzA : e.val y ∈ A := ⟨e.val.map_source hys, by
    rw [mem_preimage, e.val.left_inv hys]; exact hy⟩
  obtain ⟨r, hr, hrA⟩ := Metric.isOpen_iff.mp hAo _ hzA
  have hρc : ContinuousOn ρ e.val.target := hρs.continuousOn
  -- `ρ` is bounded below by a positive constant near `e y`
  have hρy : 0 < ρ (e.val y) := hρpos _ hzA.1
  obtain ⟨r', hr', hr'ball⟩ := Metric.mem_nhds_iff.mp ((hρc.continuousAt
    (e.val.open_target.mem_nhds hzA.1)).eventually (lt_mem_nhds (half_lt_self hρy)))
  set r₀ := min r r' with hr₀
  have hr₀ : 0 < r₀ := lt_min hr hr'
  have hball : ball (e.val y) r₀ ⊆ A := (ball_subset_ball (min_le_left _ _)).trans hrA
  have hpre : e.val.source ∩ e.val ⁻¹' ball (e.val y) r₀ ⊆ O := by
    intro x hx
    have h1 := (hball hx.2).2
    rwa [mem_preimage, e.val.left_inv hx.1] at h1
  have hmeas : MeasurableSet (ball (e.val y) r₀) := measurableSet_ball
  have h1 : (Measure.map e.val (μ.restrict e.val.source)) (ball (e.val y) r₀) ≤ μ O := by
    rw [Measure.map_apply_of_aemeasurable
      (e.val.continuousOn.aemeasurable e.val.open_source.measurableSet) hmeas,
      Measure.restrict_apply' e.val.open_source.measurableSet]
    exact measure_mono (by rw [inter_comm]; exact hpre)
  have h2 : 0 < (Measure.map e.val (μ.restrict e.val.source)) (ball (e.val y) r₀) := by
    rw [hmap, withDensity_apply _ hmeas, Measure.restrict_restrict hmeas]
    have hsub : ball (e.val y) r₀ ⊆ e.val.target := fun z hz => (hball hz).1
    rw [inter_eq_left.mpr hsub]
    calc (0 : ℝ≥0∞) < ∫⁻ _z in ball (e.val y) r₀, ENNReal.ofReal (ρ (e.val y) / 2) := by
          rw [setLIntegral_const]
          exact ENNReal.mul_pos (by simpa using half_pos hρy)
            (measure_ball_pos volume _ hr₀).ne'
      _ ≤ ∫⁻ z in ball (e.val y) r₀, ENNReal.ofReal (ρ z) := by
          refine setLIntegral_mono' hmeas fun z hz => ENNReal.ofReal_le_ofReal ?_
          exact (hr'ball (ball_subset_ball (min_le_right _ _) hz)).le
  exact (h2.trans_le h1).ne'

section Hilbert

variable [CompactSpace X] {μ : Measure X} (L T : HermitianHolomorphicLineBundle.{0, 0} n X)
  (k : ℕ) {φ : X → EReal}

/-- The weighted `L²` mass `∫_X |s|² e^{-kφ} dμ` of a section. -/
abbrev sectionMass (μ : Measure X) (φ : X → EReal) (s : twistedSections L T k) : ℝ≥0∞ :=
  ∫⁻ y, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k s y ∂μ

theorem sectionMass_eq (μ : Measure X) (φ : X → EReal) (s : twistedSections L T k) :
    sectionMass L T k μ φ s =
      ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y) ∂μ := rfl

variable {L T k}

/-- Minkowski's inequality for the weighted mass. -/
theorem sectionMass_add_rpow_le (hφm : Measurable φ) (s t : twistedSections L T k) :
    sectionMass L T k μ φ (s + t) ^ (1 / 2 : ℝ) ≤
      sectionMass L T k μ φ s ^ (1 / 2 : ℝ) + sectionMass L T k μ φ t ^ (1 / 2 : ℝ) := by
  set w : X → ℝ≥0∞ := fun y => multiplierWeight (k : ℝ) (φ y) with hw
  have hwm : Measurable w := measurable_originalMultiplierWeight hφm k
  set F : twistedSections L T k → X → ℝ≥0∞ :=
    fun u y => ENNReal.ofReal ‖u y‖ * w y ^ (1 / 2 : ℝ) with hF
  have hFm : ∀ u : twistedSections L T k, AEMeasurable (F u) μ := fun u =>
    ((ENNReal.continuous_ofReal.comp (sectionNormMap _ u).continuous).measurable.mul
      (hwm.pow_const _)).aemeasurable
  have hsq : ∀ u : twistedSections L T k, ∀ y,
      F u y ^ (2 : ℝ) = originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k u y := by
    intro u y
    simp only [hF, originalSectionDensity]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_cast
  have hmass : ∀ u, sectionMass L T k μ φ u = ∫⁻ y, F u y ^ (2 : ℝ) ∂μ := by
    intro u
    exact lintegral_congr fun y => (hsq u y).symm
  have hle : ∀ y, F (s + t) y ^ (2 : ℝ) ≤ (F s + F t) y ^ (2 : ℝ) := by
    intro y
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    simp only [hF, Pi.add_apply]
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ zero_le
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ContMDiffSection.coe_add]
    exact norm_add_le _ _
  have hmink := ENNReal.lintegral_Lp_add_le (hFm s) (hFm t) (p := 2) (by norm_num)
  rw [hmass, hmass, hmass]
  refine le_trans ?_ (by simpa only [one_div] using hmink)
  simp only [one_div]
  exact ENNReal.rpow_le_rpow (lintegral_mono hle) (by norm_num)

theorem sectionMass_smul (c : ℂ) (s : twistedSections L T k) :
    sectionMass L T k μ φ (c • s) = ENNReal.ofReal (‖c‖ ^ 2) * sectionMass L T k μ φ s := by
  rw [sectionMass, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun y => ?_
  simp only [originalSectionDensity, ContMDiffSection.coe_smul, Pi.smul_apply, norm_smul,
    mul_pow]
  rw [ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]

theorem sectionMass_neg (s : twistedSections L T k) :
    sectionMass L T k μ φ (-s) = sectionMass L T k μ φ s := by
  simp only [sectionMass, originalSectionDensity, ContMDiffSection.coe_neg, Pi.neg_apply,
    norm_neg]

theorem sectionMass_zero : sectionMass L T k μ φ 0 = 0 := by
  simp [sectionMass, originalSectionDensity, ContMDiffSection.coe_zero]

theorem sectionMass_parallelogram (hφm : Measurable φ) (s t : twistedSections L T k) :
    sectionMass L T k μ φ (s + t) + sectionMass L T k μ φ (s - t) =
      2 * sectionMass L T k μ φ s + 2 * sectionMass L T k μ φ t := by
  have hm : ∀ u : twistedSections L T k,
      Measurable (originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k u) :=
    fun u => measurable_originalSectionDensity _ hφm k u
  rw [sectionMass, sectionMass, sectionMass, sectionMass, ← lintegral_add_left (hm _),
    ← lintegral_const_mul _ (hm _), ← lintegral_const_mul _ (hm _), ← lintegral_add_left
      ((hm s).const_mul _)]
  refine lintegral_congr fun y => ?_
  simp only [originalSectionDensity, ContMDiffSection.coe_add, ContMDiffSection.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  have hp := parallelogram_law_with_norm ℂ (s y) (t y)
  have e : ‖s y + t y‖ ^ 2 + ‖s y - t y‖ ^ 2 = 2 * ‖s y‖ ^ 2 + 2 * ‖t y‖ ^ 2 := by
    simp only [sq]; linarith
  rw [← add_mul, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), e,
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  ring

/-- A section of zero weighted mass vanishes. -/
theorem eq_zero_of_sectionMass_eq_zero (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hφm : Measurable φ) (hφtop : ∀ y, φ y ≠ ⊤) {s : twistedSections L T k}
    (hs : sectionMass L T k μ φ s = 0) : s = 0 := by
  have : μ.IsOpenPosMeasure := isOpenPosMeasure_of_isSmoothPositiveVolume hμ
  have h0 := (lintegral_eq_zero_iff (measurable_originalSectionDensity _ hφm k s)).mp hs
  have hzero : ∀ᵐ y ∂μ, ‖s y‖ = 0 := by
    filter_upwards [h0] with y hy
    simp only [originalSectionDensity, Pi.zero_apply, mul_eq_zero,
      ENNReal.ofReal_eq_zero] at hy
    rcases hy with hy | hy
    · exact le_antisymm (by nlinarith [norm_nonneg (s y)]) (norm_nonneg _)
    · exfalso
      revert hy
      induction h : φ y using EReal.rec with
      | bot =>
          intro hy0
          rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk; simp [multiplierWeight] at hy0
          · have hk' : (0 : ℝ) < k := by exact_mod_cast hk
            rw [multiplierWeight_bot hk'] at hy0
            exact ENNReal.top_ne_zero hy0
      | coe r => simp [multiplierWeight_coe, Real.exp_pos]
      | top => exact absurd h (hφtop y)
  have hc : Continuous fun y => ‖s y‖ := (sectionNormMap _ s).continuous
  have hall : ∀ y, ‖s y‖ = 0 := by
    have hae : (fun y => ‖s y‖) =ᵐ[μ] fun _ => (0 : ℝ) := hzero
    have := (Continuous.ae_eq_iff_eq μ hc continuous_const).mp hae
    intro y
    exact congrFun this y
  ext y
  · simp [norm_eq_zero.mp (hall y)]

end Hilbert

section Majorant

variable [CompactSpace X] (L T : HermitianHolomorphicLineBundle.{0, 0} n X) (k : ℕ)
  (φ : X → EReal)

/-- `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` as a subspace of the holomorphic sections. -/
abbrev multiplierSubspace : Submodule ℂ (twistedSections L T k) :=
  fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)

/-- A copy of `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`, to carry the weighted `L²` structure. -/
def WeightedSections : Type := ↥(multiplierSubspace L T k φ)

instance : AddCommGroup (WeightedSections L T k φ) :=
  inferInstanceAs (AddCommGroup ↥(multiplierSubspace L T k φ))

instance : Module ℂ (WeightedSections L T k φ) :=
  inferInstanceAs (Module ℂ ↥(multiplierSubspace L T k φ))

/-- The underlying section. -/
def WeightedSections.sec {L T : HermitianHolomorphicLineBundle.{0, 0} n X} {k : ℕ} {φ : X → EReal}
    (e : WeightedSections L T k φ) : twistedSections L T k :=
  (show ↥(multiplierSubspace L T k φ) from e).1

/-- The underlying section, as a linear map. -/
def WeightedSections.secₗ : WeightedSections L T k φ →ₗ[ℂ] twistedSections L T k :=
  (multiplierSubspace L T k φ).subtype

theorem WeightedSections.secₗ_apply (e : WeightedSections L T k φ) :
    WeightedSections.secₗ L T k φ e = e.sec := rfl

variable {μ : Measure X} {θ : SmoothRealForm n X 2} {L T k φ}

/-- Sections of `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` have finite weighted mass. -/
theorem sectionMass_ne_top (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hφ : IsThetaPshPotential θ φ) (e : WeightedSections L T k φ) :
    sectionMass L T k μ φ e.sec ≠ ⊤ :=
  ((fullHolomorphicThetaDegreeIdealSections_iff_finite_integral _ k hφ e.sec hμ).mp
    (show ↥(multiplierSubspace L T k φ) from e).2).ne

/-- The weighted `L²` norm `(∫ |s|² e^{-kφ} dμ)^{1/2}` on `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))`. -/
def weightedAddGroupNorm (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hφ : IsThetaPshPotential θ φ) : AddGroupNorm (WeightedSections L T k φ) where
  toFun e := (sectionMass L T k μ φ e.sec ^ (1 / 2 : ℝ)).toReal
  map_zero' := by
    change (sectionMass L T k μ φ 0 ^ (1 / 2 : ℝ)).toReal = 0
    rw [sectionMass_zero, ENNReal.zero_rpow_of_pos (by norm_num), ENNReal.toReal_zero]
  add_le' e f := by
    have hφm : Measurable φ := hφ.quasiPshPotential.1.upperSemicontinuous.measurable
    have h := sectionMass_add_rpow_le (μ := μ) hφm e.sec f.sec
    have he := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (sectionMass_ne_top hμ hφ e)
    have hf := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (sectionMass_ne_top hμ hφ f)
    rw [← ENNReal.toReal_add he hf]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨he, hf⟩) h
  neg' e := by
    change (sectionMass L T k μ φ (-e.sec) ^ (1 / 2 : ℝ)).toReal = _
    rw [sectionMass_neg]
  eq_zero_of_map_eq_zero' e he := by
    have hφm : Measurable φ := hφ.quasiPshPotential.1.upperSemicontinuous.measurable
    have hne := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (sectionMass_ne_top hμ hφ e)
    have h0 : sectionMass L T k μ φ e.sec ^ (1 / 2 : ℝ) = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp he |>.resolve_right hne
    have h1 : sectionMass L T k μ φ e.sec = 0 := by
      rcases ENNReal.rpow_eq_zero_iff.mp h0 with h | h
      · exact h.1
      · exact absurd h.1 (sectionMass_ne_top hμ hφ e)
    have h2 := eq_zero_of_sectionMass_eq_zero hμ hφm
      (fun y => hφ.1.quasiPlurisubharmonic.ne_top y) h1
    exact Subtype.ext h2

theorem weightedAddGroupNorm_sq (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hφ : IsThetaPshPotential θ φ) (e : WeightedSections L T k φ) :
    weightedAddGroupNorm hμ hφ e ^ 2 = (sectionMass L T k μ φ e.sec).toReal := by
  change ((sectionMass L T k μ φ e.sec ^ (1 / 2 : ℝ)).toReal) ^ 2 = _
  rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **The Bergman majorant** (blueprint `claude-dx-low:trace`): there is a measurable `D_k` with
`B_k ≤ D_k` and `∫_X D_k dμ = h⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` (`D_k = ∑ |sᵢ|² e^{-kφ}` for an orthonormal
basis of `H⁰(X, L^k ⊗ T ⊗ 𝓘(kφ))` with the weighted `L²` product). -/
theorem exists_bergman_majorant (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hφ : IsThetaPshPotential θ φ) :
    ∃ Dk : X → ℝ≥0∞, Measurable Dk ∧ (∀ x, bergmanDensity μ L T φ k x ≤ Dk x) ∧
      ∫⁻ x, Dk x ∂μ = Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) := by
  classical
  have hφm : Measurable φ := hφ.quasiPshPotential.1.upperSemicontinuous.measurable
  set N := weightedAddGroupNorm (L := L) (T := T) (k := k) hμ hφ with hN
  let : NormedAddCommGroup (WeightedSections L T k φ) := N.toNormedAddCommGroup
  have hnorm : ∀ e : WeightedSections L T k φ, ‖e‖ = N e := fun e => rfl
  have hsq : ∀ e : WeightedSections L T k φ,
      ‖e‖ ^ 2 = (sectionMass L T k μ φ e.sec).toReal := fun e =>
    weightedAddGroupNorm_sq hμ hφ e
  have hnn : ∀ e : WeightedSections L T k φ, 0 ≤ ‖e‖ := fun e => norm_nonneg e
  let _ : NormedSpace ℂ (WeightedSections L T k φ) :=
    { norm_smul_le := fun c e => by
        refine le_of_eq ?_
        have h1 : ‖c • e‖ ^ 2 = (‖c‖ * ‖e‖) ^ 2 := by
          rw [hsq, mul_pow, hsq]
          change (sectionMass L T k μ φ (c • e.sec)).toReal = _
          rw [sectionMass_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
        exact (pow_left_inj₀ (hnn _) (mul_nonneg (norm_nonneg c) (hnn e))
          (by norm_num : (2 : ℕ) ≠ 0)).mp h1 }
  let _ : InnerProductSpace ℂ (WeightedSections L T k φ) := InnerProductSpace.ofNorm ℂ
    (fun e f => by
      have h := sectionMass_parallelogram (μ := μ) hφm e.sec f.sec
      have hfin : ∀ g : WeightedSections L T k φ, sectionMass L T k μ φ g.sec ≠ ⊤ :=
        sectionMass_ne_top hμ hφ
      have h' := congrArg ENNReal.toReal h
      rw [ENNReal.toReal_add (show sectionMass L T k μ φ (e.sec + f.sec) ≠ ⊤ from hfin (e + f))
        (show sectionMass L T k μ φ (e.sec - f.sec) ≠ ⊤ from hfin (e - f)), ENNReal.toReal_add
        (ENNReal.mul_ne_top (by norm_num) (hfin e)) (ENNReal.mul_ne_top (by norm_num) (hfin f)),
        ENNReal.toReal_mul, ENNReal.toReal_mul] at h'
      simp only [← pow_two, hsq]
      change (sectionMass L T k μ φ (e.sec + f.sec)).toReal +
        (sectionMass L T k μ φ (e.sec - f.sec)).toReal = _
      rw [h']
      norm_num
      ring)
  have : FiniteDimensional ℂ (WeightedSections L T k φ) :=
    fullTwistedMultiplierSections_finiteDimensional L T k φ
  set b := stdOrthonormalBasis ℂ (WeightedSections L T k φ) with hb
  set d := Module.finrank ℂ (WeightedSections L T k φ) with hd
  refine ⟨fun x => ∑ i, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k
    (b i).sec x, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ => measurable_originalSectionDensity _ hφm k _
  · intro x
    refine iSup_le fun s => iSup_le fun hs => ?_
    have hsW : s ∈ multiplierSubspace L T k φ :=
      (fullHolomorphicThetaDegreeIdealSections_iff_finite_integral _ k hφ s hμ).mpr
        (lt_of_le_of_lt hs ENNReal.one_lt_top)
    set e : WeightedSections L T k φ := (⟨s, hsW⟩ : ↥(multiplierSubspace L T k φ)) with he
    have hes : e.sec = s := rfl
    have he1 : ‖e‖ ^ 2 ≤ 1 := by
      rw [hsq, hes]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact hs)
    -- expansion in the orthonormal basis
    have hexp : s x = ∑ i, b.repr e i • (b i).sec x := by
      let ev : twistedSections L T k →ₗ[ℂ] (twistedPower L T k).Fiber x :=
        { toFun := fun s => s x
          map_add' := fun s t => by rw [ContMDiffSection.coe_add]; rfl
          map_smul' := fun c s => by rw [ContMDiffSection.coe_smul]; rfl }
      have h1 := congrArg (fun f : WeightedSections L T k φ =>
        ev (WeightedSections.secₗ L T k φ f)) (b.sum_repr e)
      simp only [map_sum, map_smul] at h1
      rw [← hes]
      exact h1.symm
    have hrepr : ∑ i, ‖b.repr e i‖ ^ 2 = ‖e‖ ^ 2 := by
      rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    have hcs : ‖s x‖ ^ 2 ≤ ∑ i, ‖(b i).sec x‖ ^ 2 := by
      have h1 : ‖s x‖ ≤ ∑ i, ‖b.repr e i‖ * ‖(b i).sec x‖ := by
        rw [hexp]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => norm_smul _ _
      have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖b.repr e i‖)
        (fun i => ‖(b i).sec x‖)
      have h3 : ‖s x‖ ^ 2 ≤ (∑ i, ‖b.repr e i‖ * ‖(b i).sec x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [hrepr] at h2
      have h4 : 0 ≤ ∑ i, ‖(b i).sec x‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    calc ENNReal.ofReal (‖s x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x)
        ≤ ENNReal.ofReal (∑ i, ‖(b i).sec x‖ ^ 2) * multiplierWeight (k : ℝ) (φ x) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hcs) zero_le
      _ = ∑ i, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k (b i).sec x := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _), Finset.sum_mul]
          rfl
  · rw [lintegral_finsetSum _ fun i _ => measurable_originalSectionDensity _ hφm k _]
    have hone : ∀ i, ∫⁻ y, originalSectionDensity (n := n) (twistedPower L T k).Fiber φ k
        (b i).sec y ∂μ = 1 := by
      intro i
      have h1 : ‖b i‖ ^ 2 = 1 := by rw [b.orthonormal.1 i, one_pow]
      rw [hsq] at h1
      change sectionMass L T k μ φ (b i).sec = 1
      rw [← ENNReal.ofReal_toReal (sectionMass_ne_top hμ hφ (b i)), h1, ENNReal.ofReal_one]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [hd]
    exact_mod_cast (LinearEquiv.finrank_eq (literalTwistedMultiplierSectionEquiv L T k φ)).symm

end Majorant

end SGPT.IGood.DXLow
