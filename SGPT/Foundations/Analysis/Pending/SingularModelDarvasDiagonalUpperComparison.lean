import SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalComparison

set_option autoImplicit false

/-!
# Actual upper Darvas--diagonal comparison with Xia's dimension constant

Xia SGPT PDF0162--0163, Theorem 4.3.1, Step 2. Genuine midpoint/rooftop
producers, actual diagonal midpoint domination, actual ordered endpoint
bounds, and nullity of genuine poles control both strict comparison sets.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses DiagonalMass SingularModelFiniteEnergyDiagonalGap
  SingularModelDarvasDiagonalComparison ThetaPshConvexCombination

noncomputable section

private theorem midpoint_gap_bounds {a b c : EReal}
    (hat : a ≠ ⊤) (hab : a ≠ ⊥) (hbt : b ≠ ⊤) (hbb : b ≠ ⊥)
    (hct : c ≠ ⊤) (hcb : c ≠ ⊥) (hca : c ≤ a)
    (hcm : c ≤ (1 / 2 : ℝ) * a + ((1 - 1 / 2 : ℝ) : EReal) * b) :
    (b ≤ a → canonicalERealAbsDiff a b ≤ ENNReal.ofReal 2 * canonicalERealAbsDiff a c) ∧
    (a ≤ b → canonicalERealAbsDiff a b ≤ ENNReal.ofReal 2 *
      canonicalERealAbsDiff ((1 / 2 : ℝ) * a + ((1 - 1 / 2 : ℝ) : EReal) * b) c) := by
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hct hcb] at hca
  rw [← EReal.coe_toReal hat hab, ← EReal.coe_toReal hbt hbb, ← EReal.coe_toReal hct hcb] at hcm ⊢
  simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff,
    canonicalERealAbsDiff_coe_coe] at hca hcm ⊢
  constructor
  · intro hba
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonneg (sub_nonneg.mpr hba), abs_of_nonneg (sub_nonneg.mpr hca)]
    linarith
  · intro hab
    rw [← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonneg (by linarith)]
    linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

variable {θ : ClosedRealOneOneForm n M} {φ u v : M → EReal} {hφ : IsModelPotential θ φ}

/-- Both actual strict comparison regions are controlled by the actual
midpoint distance; the midpoint measure domination is produced internally. -/
theorem lintegral_gap_le_mul_midpoint_distance (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
      ENNReal.ofReal (((2 : ℝ) ^ (n + 2)) * relativeD1 θ φ hφ u (convexComb (1 / 2 : ℝ) u v)) := by
  classical
  let h := convexComb (1 / 2 : ℝ) u v
  let p := rooftop θ u h
  have hh : RelativeFiniteEnergyPreceq θ φ h hφ :=
    relativeFiniteEnergyPreceq_convexComb omega hu hv (by norm_num) (by norm_num)
  have hp : RelativeFiniteEnergyPreceq θ φ p hφ := relativeFiniteEnergyPreceq_rooftop omega hu hh
  have hpu : p ≤ u := rooftop_le_left hu.1.plurisubharmonic hh.1.plurisubharmonic
  have hph : p ≤ h := rooftop_le_right hu.1.plurisubharmonic hh.1.plurisubharmonic
  let μu := diagonalPotentialMeasure θ u hu.1.plurisubharmonic
  let μh := diagonalPotentialMeasure θ h hh.1.plurisubharmonic
  let f := fun x => canonicalERealAbsDiff (u x) (v x)
  let gu := fun x => canonicalERealAbsDiff (u x) (p x)
  let gh := fun x => canonicalERealAbsDiff (h x) (p x)
  let S := {x | u x < v x}
  let D := relativeD1 θ φ hφ u h
  have hSm : MeasurableSet S := measurableSet_lt
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hu.1.plurisubharmonic.1)
    (GlobalSlotComparison.ThetaPlurisubharmonic.measurable hv.1.plurisubharmonic.1)
  have hpole (w : M → EReal) (hw : IsThetaPshPotential θ.val w) : ∀ᵐ x ∂μu, w x ≠ ⊥ := by
    have hz : μu {x | w x = ⊥} = 0 :=
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (fun _ : Fin n => hu.1.plurisubharmonic.1) hw
    exact ae_iff.mpr (by simpa only [not_not] using hz)
  have hpoint : ∀ᵐ x ∂μu,
      (v x ≤ u x → f x ≤ ENNReal.ofReal 2 * gu x) ∧
      (u x ≤ v x → f x ≤ ENNReal.ofReal 2 * gh x) := by
    filter_upwards [hpole u hu.1.plurisubharmonic, hpole v hv.1.plurisubharmonic,
      hpole p hp.1.plurisubharmonic] with x hub hvb hpb
    exact midpoint_gap_bounds
      (hu.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hub
      (hv.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hvb
      (hp.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpb (hpu x) (hph x)
  have heD : D = ((energy θ φ hφ u).toReal - (energy θ φ hφ p).toReal) +
      ((energy θ φ hφ h).toReal - (energy θ φ hφ p).toReal) := by
    change relativeD1 θ φ hφ u h = _
    rw [relativeD1]
    ring
  have hu0 : 0 ≤ (energy θ φ hφ u).toReal - (energy θ φ hφ p).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hp hu hpu)
  have hh0 : 0 ≤ (energy θ φ hφ h).toReal - (energy θ φ hφ p).toReal :=
    sub_nonneg.mpr (SingularModelFiniteRealEnergy.toReal_energy_mono omega hp hh hph)
  have hD0 : 0 ≤ D := by rw [heD]; exact add_nonneg hu0 hh0
  have hJu : (∫⁻ x, gu x ∂μu) ≤ ENNReal.ofReal D :=
    (diagonalGap_endpoint_bounds_of_preceq omega hu hp hpu).1.trans
      (ENNReal.ofReal_le_ofReal (by rw [heD]; linarith))
  have hJh : (∫⁻ x, gh x ∂μh) ≤ ENNReal.ofReal D :=
    (diagonalGap_endpoint_bounds_of_preceq omega hh hp hph).1.trans
      (ENNReal.ofReal_le_ofReal (by rw [heD]; linarith))
  have hmeasure : μu ≤ ENNReal.ofReal ((2 : ℝ) ^ n) • μh :=
    diagonalPotentialMeasure_le_pow_smul_midpoint hu.1.plurisubharmonic hv.1.plurisubharmonic
  have hmove : (∫⁻ x, gh x ∂μu) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal D := by
    calc (∫⁻ x, gh x ∂μu) ≤ ∫⁻ x, gh x ∂(ENNReal.ofReal ((2 : ℝ) ^ n) • μh) :=
        lintegral_mono' hmeasure le_rfl
      _ = ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ x, gh x ∂μh := by
        rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ _ := mul_le_mul_right hJh _
  have hS : (∫⁻ x in S, f x ∂μu) ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal D) := by
    calc
      (∫⁻ x in S, f x ∂μu) ≤ ∫⁻ x in S, ENNReal.ofReal 2 * gh x ∂μu := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hpoint, ae_restrict_mem hSm] with x hx hxS
        exact hx.2 (le_of_lt hxS)
      _ ≤ ∫⁻ x, ENNReal.ofReal 2 * gh x ∂μu := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal 2 * ∫⁻ x, gh x ∂μu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_right hmove _
  have hSc : (∫⁻ x in Sᶜ, f x ∂μu) ≤ ENNReal.ofReal 2 * ENNReal.ofReal D := by
    calc
      (∫⁻ x in Sᶜ, f x ∂μu) ≤ ∫⁻ x in Sᶜ, ENNReal.ofReal 2 * gu x ∂μu := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hpoint, ae_restrict_mem hSm.compl] with x hx hxS
        exact hx.1 (not_lt.mp hxS)
      _ ≤ ∫⁻ x, ENNReal.ofReal 2 * gu x ∂μu := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal 2 * ∫⁻ x, gu x ∂μu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_right hJu _
  have hcoeff : (2 : ℝ) * 2 ^ n + 2 ≤ 2 ^ (n + 2) := by
    have hp1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ, pow_succ]
    nlinarith
  change (∫⁻ x, f x ∂μu) ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 2)) * D)
  calc (∫⁻ x, f x ∂μu) = (∫⁻ x in S, f x ∂μu) + ∫⁻ x in Sᶜ, f x ∂μu :=
      (lintegral_add_compl f hSm).symm
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal ((2 : ℝ) ^ n) * ENNReal.ofReal D) +
        ENNReal.ofReal 2 * ENNReal.ofReal D := add_le_add hS hSc
    _ = ENNReal.ofReal (((2 : ℝ) * 2 ^ n + 2) * D) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcoeff hD0)

/-- One actual endpoint diagonal gap has Xia's constant
3·2^(n+1)·(n+1) times the actual Darvas distance. -/
theorem lintegral_gap_le_mul_relativeD1 (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
      ENNReal.ofReal ((3 * (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v) := by
  calc (∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 2)) * relativeD1 θ φ hφ u (convexComb (1 / 2 : ℝ) u v)) :=
        lintegral_gap_le_mul_midpoint_distance omega hu hv
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (n + 2)) *
        ((3 * ((n : ℝ) + 1) / 2) * relativeD1 θ φ hφ u v)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (relativeD1_midpoint_le omega hu hv) (by positivity))
    _ = _ := by
      congr 1
      rw [pow_succ]
      ring

private theorem canonicalAbs_symm (a b : EReal) :
    canonicalERealAbsDiff a b = canonicalERealAbsDiff b a := by
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff, ← EReal.coe_sub,
      EReal.abs_def, abs_sub_comm]

/-- The actual upper Darvas--diagonal comparison has precisely Xia's
dimension constant C_n=3·2^(n+2)·(n+1), with all analytic inputs produced. -/
theorem diagonalGapIntegral_le_mul_relativeD1 (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ≤
      ENNReal.ofReal ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v) := by
  have ha := lintegral_gap_le_mul_relativeD1 omega hu hv
  have hb := lintegral_gap_le_mul_relativeD1 omega hv hu
  rw [relativeD1_comm θ φ hφ v u] at hb
  simp only [canonicalAbs_symm] at hb
  have h := add_le_add ha hb
  have hnonneg : 0 ≤ (3 * (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v :=
    mul_nonneg (by positivity) (SingularModelDarvasBasic.relativeD1_nonneg omega hu hv)
  rw [← ENNReal.ofReal_add hnonneg hnonneg] at h
  have he : (3 * (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v +
      (3 * (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v =
        (3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v := by
    rw [pow_succ]
    ring
  rw [he] at h
  simpa only [diagonalGapIntegral, lintegral_add_measure] using h

/-- Xia's actual two-sided Darvas--diagonal comparison for arbitrary
singular-model E1 endpoints on connected compact Kähler manifolds. -/
theorem ofReal_relativeD1_le_diagonalGapIntegral_le_mul (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hv : RelativeFiniteEnergyPreceq θ φ v hφ) :
    ENNReal.ofReal (relativeD1 θ φ hφ u v) ≤
      diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ∧
    diagonalGapIntegral θ u v hu.1.plurisubharmonic hv.1.plurisubharmonic ≤
      ENNReal.ofReal ((3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)) * relativeD1 θ φ hφ u v) :=
  ⟨ofReal_relativeD1_le_diagonalGapIntegral omega hu hv,
    diagonalGapIntegral_le_mul_relativeD1 omega hu hv⟩

end

end SGPT.Foundations.Analysis.Pending.SingularModelDarvasDiagonalUpperComparison
