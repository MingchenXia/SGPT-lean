import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalComparison
import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.GlobalMixedMassMonotone

set_option autoImplicit false

/-!
# Actual mixed full mass and mixed E1 gap integrability

Xia SGPT PDF0124--0126, the actual mixed integrability underlying (3.39)--(3.41).
Every binary measure below is the actual global mixed non-pluripolar measure.
Its mass and domination by the actual midpoint measure are produced internally.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedGap

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses RelativeEnergyIntegrability DiagonalMass GlobalNonPluripolar
  GlobalDiagonalScaling GlobalMultilinearExpansion MixedMassProductCalculus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- The actual original-background mixed measure with the selected endpoints. -/
def binaryMixedMeasure (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential θ.val v) (σ : Fin n → Bool) : Measure M :=
  globalMixedMeasure (fun _ => θ) (fun i => if σ i then u else v)
    (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hv.1 | exact hu.1)

/-- Every actual binary mixed measure is dominated by the actual midpoint
diagonal measure, by the positive actual multilinear expansion. -/
theorem binaryMixedMeasure_le_pow_smul_midpoint (omega : KahlerBackground n M)
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential θ.val v)
    (σ : Fin n → Bool) :
    binaryMixedMeasure hu hv σ ≤ ENNReal.ofReal ((2 : ℝ) ^ n) •
      diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v)
        (ThetaPshConvexCombination.isThetaPshPotential_convexComb hu hv (by norm_num) (by norm_num)) := by
  classical
  let coeff : Bool → ℝ := fun _ => 1 / 2
  let pots : Bool → M → EReal := fun e => if e then u else v
  have hc (_ : Fin n) (e : Bool) : 0 ≤ coeff e := by norm_num [coeff]
  have hpots (e : Bool) : IsThetaPshPotential θ.val (pots e) := by
    cases e
    · exact hv
    · exact hu
  have hexp := globalMixedMeasure_sumPot_expand omega hc hpots
  have hforms : (fun _ : Fin n => sumForm Finset.univ coeff (fun _ : Bool => θ)) =
      fun _ => θ := by
    funext i
    simp only [sumForm, Fintype.sum_bool, coeff]
    rw [← add_smul]
    norm_num
  have hpot : (fun _ : Fin n => sumPot Finset.univ coeff pots) =
      fun _ => ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v := by
    funext i x
    simp only [ThetaPshConvexCombination.convexComb]
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    simp [sumPot, coeff, pots]
  rw [globalMixedMeasure_congr hforms hpot _
    (fun _ => (ThetaPshConvexCombination.isThetaPshPotential_convexComb hu hv
      (by norm_num) (by norm_num)).1)] at hexp
  apply Measure.le_iff.mpr
  intro s _
  have he := congrArg (fun μ : Measure M => μ s) hexp
  rw [Measure.coe_finsetSum, Finset.sum_apply] at he
  have hterm := Finset.single_le_sum (fun (g : Fin n → Bool) _ =>
    bot_le (a := (ENNReal.ofReal (∏ i, coeff (g i)) •
      globalMixedMeasure (fun _ => θ) (fun i => pots (g i))
        (fun i => (hpots (g i)).1)) s)) (Finset.mem_univ σ)
  rw [← he] at hterm
  have hweight : (∏ i : Fin n, coeff (σ i)) = (1 / 2 : ℝ) ^ n := by simp [coeff]
  change (ENNReal.ofReal (∏ i, coeff (σ i)) • binaryMixedMeasure hu hv σ) s ≤
    diagonalPotentialMeasure θ (ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v)
      (ThetaPshConvexCombination.isThetaPshPotential_convexComb hu hv (by norm_num) (by norm_num)) s at hterm
  rw [hweight, Measure.smul_apply, smul_eq_mul] at hterm
  rw [Measure.smul_apply, smul_eq_mul]
  have hinv : ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    norm_num
  calc binaryMixedMeasure hu hv σ s = ENNReal.ofReal ((2 : ℝ) ^ n) *
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ n) * binaryMixedMeasure hu hv σ s) := by
          rw [← mul_assoc, hinv, one_mul]
    _ ≤ _ := mul_le_mul_right hterm _

/-- Actual E1 rooftop mass and actual mixed-mass monotonicity produce the
full actual mixed mass, with no mixed-mass certificate as a premise. -/
theorem binaryMixedMeasure_univ [ConnectedSpace M] (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (σ : Fin n → Bool) :
    binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ univ =
      diagonalPotentialMass θ φ hφ.plurisubharmonic := by
  have hr := relativeFiniteEnergy_rooftop omega hu hv
  have hslots (i : Fin n) : IsThetaPshPotential θ.val (if σ i then u else v) := by
    cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hv.1.plurisubharmonic | exact hu.1.plurisubharmonic
  have hlow := GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
    (fun _ : Fin n => hr.1.plurisubharmonic) hslots (fun i => MoreSingularOn.of_le fun x _ => by
      cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact rooftop_le_right hu.1.plurisubharmonic hv.1.plurisubharmonic x
              | exact rooftop_le_left hu.1.plurisubharmonic hv.1.plurisubharmonic x)
  have hhigh := GlobalMixedMassMonotone.globalMixedMass_mono_of_isThetaPshPotential omega
    hslots (fun _ : Fin n => hφ.plurisubharmonic) (fun i => MoreSingularOn.of_le fun x _ => by
      cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hv.1.le_reference x | exact hu.1.le_reference x)
  have hrmass : diagonalPotentialMass θ (rooftop θ u v) hr.1.plurisubharmonic =
      diagonalPotentialMass θ φ hφ.plurisubharmonic := hr.1.2.2
  change diagonalPotentialMass θ (rooftop θ u v) hr.1.plurisubharmonic ≤
    binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ univ at hlow
  change binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ univ ≤
    diagonalPotentialMass θ φ hφ.plurisubharmonic at hhigh
  rw [hrmass] at hlow
  exact le_antisymm hhigh hlow

omit [BorelSpace M] in
private theorem reference_relativeFiniteEnergy : RelativeFiniteEnergy θ φ φ hφ := by
  refine ⟨⟨hφ.plurisubharmonic, le_rfl, rfl⟩, hφ.plurisubharmonic, ?_⟩
  have hz (x : M) : canonicalERealAbsDiff (φ x) (φ x) = 0 :=
    canonicalERealAbsDiff_self_of_ne_top (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
  simp only [relativeFiniteEnergyIntegral, hz, lintegral_zero]
  exact bot_lt_top

/-- Genuine E1 reference gaps are integrable against every actual binary
mixed measure; neither mixed integrability nor a measure bound is assumed. -/
theorem integrable_referenceGaps_binaryMixedMeasure [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (σ : Fin n → Bool) :
    Integrable (fun x => canonicalERealDiffToReal (φ x) (u x))
      (binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ) ∧
    Integrable (fun x => canonicalERealDiffToReal (φ x) (v x))
      (binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ) := by
  let h := ThetaPshConvexCombination.convexComb (1 / 2 : ℝ) u v
  have hh : RelativeFiniteEnergyPreceq θ φ h hφ :=
    SingularModelDarvasDiagonalComparison.relativeFiniteEnergyPreceq_convexComb omega
      (preceq_of_relativeFiniteEnergy hu) (preceq_of_relativeFiniteEnergy hv)
      (by norm_num) (by norm_num)
  let μ := binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ
  let f := fun x => canonicalERealDiffToReal (φ x) (h x)
  have hfDiag : Integrable f (diagonalPotentialMeasure θ h hh.1.plurisubharmonic) :=
    (SingularModelFiniteEnergyGapMax.integrable_canonicalDiff_diagonal_add omega
      (preceq_of_relativeFiniteEnergy reference_relativeFiniteEnergy) hh).right_of_add_measure
  have hf : Integrable f μ := Integrable.of_measure_le_smul ENNReal.ofReal_ne_top
    (binaryMixedMeasure_le_pow_smul_midpoint omega hu.1.plurisubharmonic hv.1.plurisubharmonic σ) hfDiag
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μ, w x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, μ, binaryMixedMeasure] using globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin n => θ) (u := fun i => if σ i then u else v)
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hv.1.plurisubharmonic.1 | exact hu.1.plurisubharmonic.1) hw
  have hbounds : ∀ᵐ x ∂μ,
      ‖canonicalERealDiffToReal (φ x) (u x)‖ ≤ 2 * f x ∧
      ‖canonicalERealDiffToReal (φ x) (v x)‖ ≤ 2 * f x := by
    filter_upwards [hpole φ hφ.plurisubharmonic, hpole u hu.1.plurisubharmonic,
      hpole v hv.1.plurisubharmonic] with x hpb hub hvb
    have hcp := EReal.coe_toReal (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpb
    have hcu := EReal.coe_toReal (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hub
    have hcv := EReal.coe_toReal (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hvb
    have hum : (u x).toReal ≤ (φ x).toReal := EReal.toReal_le_toReal (hu.1.le_reference x)
      hub (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
    have hvm : (v x).toReal ≤ (φ x).toReal := EReal.toReal_le_toReal (hv.1.le_reference x)
      hvb (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x)
    have hch : h x = (((u x).toReal + (v x).toReal) / 2 : ℝ) := by
      change (1 / 2 : ℝ) * u x + (((1 - 1 / 2 : ℝ) : EReal) * v x) = _
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← hcu, ← hcv]
      simp only [EReal.toReal_coe]
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring
    have hef : f x = (φ x).toReal - ((u x).toReal + (v x).toReal) / 2 := by
      change canonicalERealDiffToReal (φ x) (h x) = _
      rw [← hcp, hch, canonicalERealDiffToReal_coe_coe]
      simp only [EReal.toReal_coe]
    rw [← hcp, ← hcu, ← hcv, canonicalERealDiffToReal_coe_coe,
      canonicalERealDiffToReal_coe_coe, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hum), abs_of_nonneg (sub_nonneg.mpr hvm), hef]
    constructor <;> linarith
  have hmeas (w : M → EReal) (hw : IsThetaPshPotential θ.val w) :
      AEStronglyMeasurable (fun x => canonicalERealDiffToReal (φ x) (w x)) μ :=
    (measurable_canonicalERealDiffToReal.comp
      ((GlobalSlotComparison.ThetaPlurisubharmonic.measurable hφ.plurisubharmonic.1).prodMk
        (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hw.1))).aestronglyMeasurable
  exact ⟨(hf.const_mul 2).mono' (hmeas u hu.1.plurisubharmonic) (hbounds.mono fun _ => And.left),
    (hf.const_mul 2).mono' (hmeas v hv.1.plurisubharmonic) (hbounds.mono fun _ => And.right)⟩

/-- The actual canonical signed E1 difference is integrable against every
actual binary mixed product, from the produced two reference-gap integrals. -/
theorem integrable_canonicalDiff_binaryMixedMeasure [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergy θ φ u hφ) (hv : RelativeFiniteEnergy θ φ v hφ)
    (σ : Fin n → Bool) :
    Integrable (fun x => canonicalERealDiffToReal (u x) (v x))
      (binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ) := by
  let μ := binaryMixedMeasure hu.1.plurisubharmonic hv.1.plurisubharmonic σ
  have hi := integrable_referenceGaps_binaryMixedMeasure omega hu hv σ
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μ, w x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, μ, binaryMixedMeasure] using globalMixedMeasure_pole_null_of_nondegenerate
      (θ := fun _ : Fin n => θ) (u := fun i => if σ i then u else v)
      (fun i => by cases σ i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        first | exact hv.1.plurisubharmonic.1 | exact hu.1.plurisubharmonic.1) hw
  apply (hi.2.sub hi.1).congr
  filter_upwards [hpole φ hφ.plurisubharmonic, hpole u hu.1.plurisubharmonic,
    hpole v hv.1.plurisubharmonic] with x hpb hub hvb
  change canonicalERealDiffToReal (φ x) (v x) - canonicalERealDiffToReal (φ x) (u x) =
    canonicalERealDiffToReal (u x) (v x)
  rw [← EReal.coe_toReal (hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpb,
    ← EReal.coe_toReal (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hub,
    ← EReal.coe_toReal (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hvb]
  simp only [canonicalERealDiffToReal_coe_coe]
  ring

end

end SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedGap
