import SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero
import SGPT.Foundations.Analysis.Pending.FullSpacePatchMeasure
import SGPT.Foundations.Analysis.Pending.SemiconcaveDegenerateHessian
import SGPT.Foundations.Analysis.Pending.BedfordTaylorInduction

set_option autoImplicit false

/-!
# A Kähler manifold has positive volume (step V0 of I-0510)

On a nonempty compact Kähler manifold `(M, ω)` the non-pluripolar mass of the potential `0`,
i.e. the volume `∫_M ω^n`, is positive (`diagonalPotentialMass_zero_pos`).

*Proof.*  Take a point `x`, its chart `e` and one smooth local potential `ρ` of `ω` near `e x`
(`ddᶜρ = ω`).  The patch whose `n` corrections all equal `ρ` identifies the global diagonal
measure of `0` on inverse-chart images of a small ball `W` with the smooth Monge--Ampère measure
of `ρ` (`FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal`).
Since `ω` is strictly positive, the complex Hessian of `ρ` is positive definite
(`complexHessian_posDef_of_isStrictlyPositive`: the complex diagonal of `ddᶜρ` is the Levi form
divided by `π`), so the density `n!/πⁿ det(∂∂̄ρ)` is positive on `W`, and `W` has positive
Lebesgue measure.

As a consequence the volume hypothesis `hvol` of step C1
(`PluripolarCapacityZero.exists_isThetaPshPotential_poles_of_outerCapacityZero`,
`PluripolarCapacityZero.manifoldLocallyPluripolar_of_outerCapacityZero`) is discharged:
`exists_isThetaPshPotential_poles_of_outerCapacityZero'` and
`manifoldLocallyPluripolar_of_outerCapacityZero'` are the same statements without it.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere FirstPass.GlobalPotentialPatches
  FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.GlobalNonPluripolar
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy
open SGPT.Foundations.Analysis.Pending.PluripolarCapacityZero

variable {n : ℕ}

/-- A nonzero coefficient tuple gives a nonzero vector. -/
theorem coordCombination_ne_zero {y : Fin n → ℂ} (hy : y ≠ 0) :
    SemiconcaveHessian.coordCombination y ≠ 0 := by
  intro h0
  apply hy
  set v : ComplexModel n := WithLp.toLp 2 (fun i => star (y i)) with hv
  have hstar : (fun i => star (v i)) = y := by
    funext i
    simp [hv]
  have := SemiconcaveHessian.coordCombination_star v
  rw [hstar, h0] at this
  funext i
  have hi := congrArg (fun w : ComplexModel n => star (w i)) this
  simpa [hv] using hi.symm

/-- **Strict positivity of `ddᶜu` gives a positive definite complex Hessian.** -/
theorem complexHessian_posDef_of_isStrictlyPositive {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) (h : IsStrictlyPositive (smoothDDC u z)) :
    (complexHessian u z).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (complexHessian_isHermitian hu) fun y hy => ?_
  rw [SemiconcaveHessian.dotProduct_mulVec_complexHessian_eq_leviForm hu y]
  have hpos := h _ (coordCombination_ne_zero hy)
  rw [smoothDDC_complexDiagonal_eq_leviForm hu] at hpos
  have hlevi : 0 < leviForm u z (SemiconcaveHessian.coordCombination y) :=
    (div_pos_iff_of_pos_right Real.pi_pos).mp hpos
  exact_mod_cast hlevi

/-- Under the same hypothesis the smooth Monge--Ampère density is positive. -/
theorem smoothDensity_pos_of_isStrictlyPositive {u : ComplexModel n → ℝ}
    {z : ComplexModel n} (hu : ContDiffAt ℝ 2 u z) (h : IsStrictlyPositive (smoothDDC u z)) :
    0 < smoothDensity u z := by
  classical
  have hdet : 0 < (complexHessian u z).det :=
    (complexHessian_posDef_of_isStrictlyPositive hu h).det_pos
  unfold smoothDensity
  exact mul_pos (by positivity) (Complex.pos_iff.mp hdet).1

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- **Step V0 of I-0510: a nonempty compact Kähler manifold has positive volume**,
`0 < ∫_M ω^n`, the non-pluripolar mass of the potential `0`. -/
theorem diagonalPotentialMass_zero_pos [Nonempty M] (omega : KahlerBackground n M) :
    0 < diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega) := by
  classical
  set θ : ClosedRealOneOneForm n M := omega.form with hθ
  have h0 := isThetaPshPotential_zero omega
  obtain ⟨x⟩ := ‹Nonempty M›
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  -- one smooth local potential of `ω` near `e x`
  obtain ⟨V, ρ, hzV, hρ, hpsh⟩ := h0.1 e (e.val x) hz
  set D : TopologicalSpace.Opens (ComplexModel n) :=
    ⟨e.val.target ∩ V, e.val.open_target.inter hρ.1⟩ with hD
  have hDV : (D : Set (ComplexModel n)) ⊆ V := inter_subset_right
  have hzD : e.val x ∈ D := ⟨hz, hzV⟩
  let Q : Patch (fun _ : Fin n => θ) (fun _ => (fun _ : M => (0 : EReal))) :=
    { chart := e
      domain := D
      domain_le_target := inter_subset_left
      potential := fun _ => ρ
      localPotential := fun _ => hρ.mono D.isOpen hDV
      plurisubharmonic := fun _ => hpsh.mono hDV }
  have hcorr : ∀ i y, Q.corrected i y = ((ρ y : ℝ) : EReal) := fun i y => by
    simp [Patch.corrected, Q, chartFunction]
  -- a small ball around `e x` on which `ρ > ρ(e x) - 1`
  have hρcont : ContinuousAt ρ (e.val x) :=
    (hρ.2.2.1.continuousOn.mono hDV).continuousAt (D.isOpen.mem_nhds hzD)
  have hnhds : (D : Set (ComplexModel n)) ∩ {y | ρ (e.val x) - 1 < ρ y} ∈ 𝓝 (e.val x) :=
    Filter.inter_mem (D.isOpen.mem_nhds hzD)
      (hρcont.eventually (lt_mem_nhds (by linarith : ρ (e.val x) - 1 < ρ (e.val x))))
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  set W : TopologicalSpace.Opens (ComplexModel n) := ⟨ball (e.val x) r, isOpen_ball⟩ with hW
  have hWD : W ≤ Q.domain := fun y hy => (hball (ball_subset_closedBall hy)).1
  have hWrel : RelativelyCompactIn W Q.domain := by
    refine ⟨(isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
      (closure_ball_subset_closedBall), fun y hy => ?_⟩
    exact (hball (closure_ball_subset_closedBall hy)).1
  obtain ⟨k, hk⟩ := exists_nat_gt (1 - ρ (e.val x))
  have hWk : (W : Set (ComplexModel n)) ⊆ commonStrictLocus Q.domain Q.corrected k := by
    intro y hy
    refine ⟨hWD hy, fun i => ?_⟩
    rw [hcorr]
    have h1 : ρ (e.val x) - 1 < ρ y := (hball (ball_subset_closedBall hy)).2
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  -- `ρ` is smooth and strictly psh on `W`
  have hρW : ContDiffOn ℝ ∞ ρ W := hρ.2.2.1.mono fun y hy => hDV (hWD hy)
  have hρ2 : ∀ y ∈ W, ContDiffAt ℝ 2 ρ y := fun y hy =>
    ((hρW y hy).contDiffAt (W.isOpen.mem_nhds hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hstrict : ∀ y ∈ W, IsStrictlyPositive (smoothDDC ρ y) := by
    intro y hy
    have hyD := hWD hy
    rw [hρ.2.2.2 (hDV hyD)]
    exact (omega.isKahler.1 e y hyD.1).2
  have hf : IsSmoothPshOn W ρ := by
    refine ⟨hρW, ?_, fun y hy =>
      (complexHessian_posDef_of_isStrictlyPositive (hρ2 y hy) (hstrict y hy)).posSemidef⟩
    have := hpsh.mono fun y hy => hDV (hWD hy)
    simpa [chartFunction] using this
  have hcorrected : ∀ i, EqOn (fun z => (Q.corrected i z).toReal) ρ W := fun i y _ => by
    simp only [hcorr, EReal.toReal_coe]
  have heq := FullSpacePatchMeasure.globalMixedMeasure_coordinate_inverse_image_eq_smoothMeasure_of_diagonal
    h0.1 Q W hWD k hWrel hWk hf hcorrected (subset_refl _)
  -- the smooth measure of `W` is positive
  have hcH : ContinuousOn (fun z => complexHessian ρ z) W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      BedfordTaylor.IsSmoothPsdOn.continuousOn_complexHessian hρW j k
  have hdens : ContinuousOn (fun z => ENNReal.ofReal (smoothDensity ρ z)) W :=
    ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      (Complex.continuous_re.comp_continuousOn
        ((Continuous.matrix_det continuous_id).comp_continuousOn hcH)))
  have hpos : 0 < smoothMeasure W ρ hf W := by
    rw [smoothMeasure, pos_iff_ne_zero, Ne,
      withDensity_apply_eq_zero' (hdens.aemeasurable W.isOpen.measurableSet)]
    rw [Measure.restrict_apply' W.isOpen.measurableSet]
    have hsub : (W : Set (ComplexModel n)) ⊆
        {y | ENNReal.ofReal (smoothDensity ρ y) ≠ 0} ∩ W ∩ W := fun y hy =>
      ⟨⟨by simpa using smoothDensity_pos_of_isStrictlyPositive (hρ2 y hy) (hstrict y hy),
        hy⟩, hy⟩
    intro h0'
    have : volume (W : Set (ComplexModel n)) = 0 := measure_mono_null hsub h0'
    exact (isOpen_ball.measure_ne_zero volume (nonempty_ball.mpr hr)) this
  calc (0 : ℝ≥0∞) < smoothMeasure W ρ hf W := hpos
    _ = globalMixedMeasure (fun _ : Fin n => θ) (fun _ => fun _ : M => (0 : EReal))
          (fun _ => h0.1) (Q.chart.val.symm '' W) := heq.symm
    _ ≤ globalMixedMeasure (fun _ : Fin n => θ) (fun _ => fun _ : M => (0 : EReal))
          (fun _ => h0.1) univ := measure_mono (subset_univ _)
    _ = diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega) := rfl

/-- **Step C1 of I-0510 without the volume hypothesis**: on a compact connected Kähler manifold
of positive dimension, a set of outer capacity zero lies in the pole set of one `ω`-PSH
potential. -/
theorem exists_isThetaPshPotential_poles_of_outerCapacityZero' (hn : 0 < n) [ConnectedSpace M]
    (omega : KahlerBackground n M) {E : Set M} (hE : OuterCapacityZero omega E) :
    ∃ φ : M → EReal, IsThetaPshPotential omega.form.val φ ∧ ∀ x ∈ E, φ x = ⊥ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨fun _ => 0, isThetaPshPotential_zero omega, fun x _ => (IsEmpty.false x).elim⟩
  · exact exists_isThetaPshPotential_poles_of_outerCapacityZero hn omega
      (diagonalPotentialMass_zero_pos omega) hE

/-- **Sets of outer capacity zero are `ManifoldLocallyPluripolar`** (compact connected Kähler,
positive dimension; no volume hypothesis). -/
theorem manifoldLocallyPluripolar_of_outerCapacityZero' (hn : 0 < n) [ConnectedSpace M]
    (omega : KahlerBackground n M) {E : Set M} (hE : OuterCapacityZero omega E) :
    ManifoldLocallyPluripolar (n := n) E := by
  obtain ⟨φ, hφ, hpoles⟩ := exists_isThetaPshPotential_poles_of_outerCapacityZero' hn omega hE
  exact ManifoldLocallyPluripolar.mono (quasiPsh_poles_manifoldLocallyPluripolar
    hφ.quasiPshPotential) fun x hx => hpoles x hx

end

end SGPT.Foundations.Analysis.Pending.KahlerVolumePositive
