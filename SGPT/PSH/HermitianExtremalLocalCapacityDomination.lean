import SGPT.PSH.HermitianExtremalSublevelCapacity
import SGPT.PSH.HermitianLocalCorrection

/-!
# One actual local correction for all Hermitian capacity competitors

A smooth local majorant is chosen from the supplied Hermitian form on
a compact coordinate closure, before any potential. The actual corrected
representative of every `0 ≤ v ≤ 1` Hermitian PSH potential is locally
bounded PSH, with one common bound. Its genuine ordinary Bedford--Taylor
measure is therefore dominated by one multiple of ordinary relative
capacity. Comparison with the nonclosed-background product is separate.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianExtremal

open Set Metric MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.BedfordTaylor
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open Hermitian
open scoped Topology ContDiff

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The real representative of the actual locally corrected potential;
the membership theorem below uses original global bounds to exclude poles. -/
def localCorrectedRealPotential (u : M → EReal) (e : ComplexChart (m + 1) M)
    (q : ComplexModel (m + 1) → ℝ) (z : ComplexModel (m + 1)) : ℝ :=
  (chartFunction u e z).toReal + q z

/-- A genuine smooth form majorant corrects every actual bounded
Hermitian PSH competitor to an original locally bounded PSH function. -/
theorem isLocallyBoundedPshOn_localCorrectedRealPotential
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    {Ω : Opens (ComplexModel (m + 1))} (hΩ : Ω ≤ chartTarget e)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q Ω)
    (hdom : ∀ z ∈ Ω, ∀ w : ComplexModel (m + 1),
      omega.form.coeff e z ![w, Complex.I • w] ≤ smoothDDC q z ![w, Complex.I • w])
    {B : ℝ} (_hB : 0 ≤ B) (hqbound : ∀ z ∈ Ω, |q z| ≤ B)
    {v : M → EReal} (hv : IsHermitianPSH omega v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 1) :
    IsLocallyBoundedPshOn Ω (localCorrectedRealPotential v e q) := by
  have hreal (z : ComplexModel (m + 1)) :
      ((chartFunction v e z).toReal : EReal) = chartFunction v e z := by
    apply EReal.coe_toReal
    · exact hv.ne_top _
    · exact ne_of_gt ((EReal.bot_lt_coe 0).trans_le (hvb _).1)
  have hpsh : PlurisubharmonicOn
      (fun z => (localCorrectedRealPotential v e q z : EReal)) Ω := by
    have h := chart_add_smooth_plurisubharmonicOn omega.isTypeOneOne hv e hΩ hq hdom
    intro z hz
    apply (h z hz).congr
    exact Filter.Eventually.of_forall fun y => by
      simp only [localCorrectedRealPotential, EReal.coe_add, hreal]
  apply isLocallyBoundedPshOn_of_abs_le hpsh (C := B + 1)
  intro z hz
  have hvreal : 0 ≤ (chartFunction v e z).toReal ∧ (chartFunction v e z).toReal ≤ 1 := by
    constructor
    · apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_zero, hreal z]
      exact (hvb (e.val.symm z)).1
    · apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_one, hreal z]
      exact (hvb (e.val.symm z)).2
  have hqb := abs_le.mp (hqbound z hz)
  change |(chartFunction v e z).toReal + q z| ≤ B + 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The same actual correction has one fixed relative-capacity bound
for every genuine `0 ≤ v ≤ 1` competitor. -/
theorem correctedBedfordTaylorMeasure_le_relCapacity
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    {Ω : Opens (ComplexModel (m + 1))} (hΩ : Ω ≤ chartTarget e)
    {q : ComplexModel (m + 1) → ℝ} (hq : ContDiffOn ℝ ∞ q Ω)
    (hdom : ∀ z ∈ Ω, ∀ w : ComplexModel (m + 1),
      omega.form.coeff e z ![w, Complex.I • w] ≤ smoothDDC q z ![w, Complex.I • w])
    {B : ℝ} (hB : 0 ≤ B) (hqbound : ∀ z ∈ Ω, |q z| ≤ B)
    {v : M → EReal} (hv : IsHermitianPSH omega v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 1)
    (E : Set (ComplexModel (m + 1))) :
    SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω
      (localCorrectedRealPotential v e q)
      (isLocallyBoundedPshOn_localCorrectedRealPotential omega e hΩ hq hdom hB hqbound hv hvb) E ≤
      ENNReal.ofReal ((2 * B + 3) ^ (m + 1)) * relCapacity Ω E := by
  have hcorr := isLocallyBoundedPshOn_localCorrectedRealPotential omega e hΩ hq hdom hB hqbound hv hvb
  have hbound (z : ComplexModel (m + 1)) (hz : z ∈ Ω) :
      -(B + 1) ≤ localCorrectedRealPotential v e q z ∧
      localCorrectedRealPotential v e q z ≤ B + 2 := by
    have hv0 : 0 ≤ (chartFunction v e z).toReal := EReal.toReal_nonneg (hvb _).1
    have hv1 : (chartFunction v e z).toReal ≤ 1 := by
      exact EReal.toReal_le_toReal (hvb _).2
        (ne_of_gt ((EReal.bot_lt_coe 0).trans_le (hvb _).1))
        (by simpa only [EReal.coe_one] using EReal.coe_ne_top (1 : ℝ))
    have hqb := abs_le.mp (hqbound z hz)
    dsimp only [localCorrectedRealPotential]
    constructor <;> linarith
  simpa only [show B + 2 - -(B + 1) = 2 * B + 3 by ring] using
    canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds hcorr
      (by linarith : -(B + 1) < B + 2) hbound E

/-- A single actual quadratic and a finite bound on the compact closure
are selected before the entire Hermitian competitor family. -/
theorem exists_uniform_localCorrectedRealPotential_capacity_bound
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (Ω : Opens (ComplexModel (m + 1)))
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))))
    (htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target)
    (a : ComplexModel (m + 1)) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
      (∀ z ∈ Ω, |ballPot A a 0 z| ≤ B) ∧
      (∀ z ∈ Ω, ∀ w : ComplexModel (m + 1),
        omega.form.coeff e z ![w, Complex.I • w] ≤ smoothDDC (ballPot A a 0) z ![w, Complex.I • w]) ∧
      ∀ (v : M → EReal) (_hv : IsHermitianPSH omega v) (_hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 1),
        ∃ hcorr : IsLocallyBoundedPshOn Ω (localCorrectedRealPotential v e (ballPot A a 0)),
          ∀ E : Set (ComplexModel (m + 1)),
            SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω
              (localCorrectedRealPotential v e (ballPot A a 0)) hcorr E ≤
              ENNReal.ofReal ((2 * B + 3) ^ (m + 1)) * relCapacity Ω E := by
  obtain ⟨A, hA, hdom⟩ := HermitianQuadratic.exists_compact_quadratic_domination
    (omega.form.coeff e) hcompact ((omega.form.smooth e).continuousOn.mono htarget) a
  obtain ⟨B₀, hB₀⟩ := hcompact.exists_bound_of_continuousOn
    (contDiff_ballPot A a 0).continuous.continuousOn
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hqbound : ∀ z ∈ Ω, |ballPot A a 0 z| ≤ B :=
    fun z hz => (hB₀ z (subset_closure hz)).trans (le_max_left _ _)
  have hdom' := fun z (hz : z ∈ Ω) w => hdom z (subset_closure hz) w
  have hΩ : Ω ≤ chartTarget e := subset_closure.trans htarget
  refine ⟨A, B, hA, hB, hqbound, hdom', fun v hv hvb => ?_⟩
  exact ⟨isLocallyBoundedPshOn_localCorrectedRealPotential omega e hΩ
      (contDiff_ballPot A a 0).contDiffOn hdom' hB hqbound hv hvb,
    correctedBedfordTaylorMeasure_le_relCapacity omega e hΩ
      (contDiff_ballPot A a 0).contDiffOn hdom' hB hqbound hv hvb⟩

/-- The corrected ordinary measures of all actual Hermitian competitors
have one `D/(N+1)` budget on every actual radial compact sublevel. The
quadratic, its genuine form inequality and the budget are all produced
before the competitor and before either sequence index. -/
theorem exists_uniform_corrected_measure_radial_sublevel_bound
    (omega : Background (m + 1) M) (e : ComplexChart (m + 1) M)
    (Ω : Opens (ComplexModel (m + 1)))
    (hcompact : IsCompact (closure (Ω : Set (ComplexModel (m + 1)))))
    (htarget : closure (Ω : Set (ComplexModel (m + 1))) ⊆ e.val.target)
    (a : ComplexModel (m + 1)) {r R T : ℝ}
    (hR : 0 < R) (hr : r < R / 2) (hRT : 3 * R < T)
    (hΩ : closedBall a (5 * R) ⊆ Ω)
    {u : ComplexModel (m + 1) → EReal} (hu : PlurisubharmonicOn u (ball a T))
    (hne : ∃ z ∈ ball a T, u z ≠ ⊥) (hnonpos : ∀ z ∈ ball a T, u z ≤ 0) :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧
      (∀ z ∈ Ω, ∀ w : ComplexModel (m + 1),
        omega.form.coeff e z ![w, Complex.I • w] ≤
          smoothDDC (ballPot A a 0) z ![w, Complex.I • w]) ∧
      ∀ (v : M → EReal) (_hv : IsHermitianPSH omega v) (_hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 1),
        ∃ hcorr : IsLocallyBoundedPshOn Ω (localCorrectedRealPotential v e (ballPot A a 0)),
          ∀ j N, SGPT.Foundations.Analysis.Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω
            (localCorrectedRealPotential v e (ballPot A a 0)) hcorr
            (compactSublevel (closedBall a r)
              (radialApproximation ((T - r) / 2) u) j (N + 1)) ≤
            ENNReal.ofReal (D / ((N : ℝ) + 1)) := by
  obtain ⟨A, B, hA, hB, _, hdom, hcorrected⟩ :=
    exists_uniform_localCorrectedRealPotential_capacity_bound omega e Ω hcompact htarget a
  obtain ⟨C, hC, hcapacity⟩ :=
    exists_relCapacity_radial_compactSublevel_le a hR hr hRT hΩ hu hne hnonpos
  have hP : 0 ≤ (2 * B + 3) ^ (m + 1) := pow_nonneg (by linarith) _
  refine ⟨A, (2 * B + 3) ^ (m + 1) * C, hA, mul_nonneg hP hC, hdom, fun v hv hvb => ?_⟩
  obtain ⟨hcorr, hmeasure⟩ := hcorrected v hv hvb
  refine ⟨hcorr, fun j N => ?_⟩
  refine (hmeasure _).trans ?_
  calc ENNReal.ofReal ((2 * B + 3) ^ (m + 1)) *
        relCapacity Ω (compactSublevel (closedBall a r)
          (radialApproximation ((T - r) / 2) u) j (N + 1)) ≤
      ENNReal.ofReal ((2 * B + 3) ^ (m + 1)) * ENNReal.ofReal (C / ((N : ℝ) + 1)) := by
        gcongr
        exact hcapacity j N
    _ = ENNReal.ofReal ((2 * B + 3) ^ (m + 1) * C / ((N : ℝ) + 1)) := by
      rw [← ENNReal.ofReal_mul hP]
      congr 1
      ring

end SGPT.PSH.HermitianExtremal
