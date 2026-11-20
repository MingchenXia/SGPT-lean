import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalFoundation
import SGPT.Foundations.Analysis.Pending.ActualContinuousObstacleDiscreteEnergyVariation
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

set_option autoImplicit false

/-! # Actual Euler equation of natural smooth-volume variational optimality

The original actual functional's natural optimality implies the original
whole Euler measure equation via internally produced genuine roofs,
finite energy, pole-null real inequalities and discrete variation.
This does not construct a variational maximum or prescribed MA solution.
Full mathematical statements and proofs preceded SOURCE.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalEuler

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass RelativeEnergy
  RelativeDarvasDistance RelativePreceqClasses IntegrationCurrent
  ActualSmoothVolumeVariationalFoundation ActualContinuousObstacleDiscreteEnergyVariation
  ActualContinuousSingularObstacleContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]
  {θ : ClosedRealOneOneForm n M} {φ u : M → EReal} {hφ : IsModelPotential θ φ}

/-- Natural original functional optimality and actual discrete variation
produce every negative continuous-direction Euler inequality internally. -/
theorem integral_le_of_nonpositive_of_functional_max (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hu0 : ∀ x, u x ≤ 0)
    (hmax : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      smoothVolumeFunctional omega θ φ hφ a ≤ smoothVolumeFunctional omega θ φ hφ u)
    {h : M → ℝ} (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    (∫ x, h x ∂diagonalPotentialMeasure θ u hu.1.plurisubharmonic) ≤
      smoothVolumeCoefficient omega θ φ hφ * (∫ x, h x ∂kahlerVolume omega) := by
  have huP := hu.1.plurisubharmonic
  have hUi := (integrable_and_integral_toReal_add_const omega huP 0).1
  have hHi : Integrable h (kahlerVolume omega) := by
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hh.continuousOn
  have hω0 : IsThetaPshPotential omega.form.val (fun _ : M => (0 : EReal)) :=
    (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
  have hpole : ∀ᵐ x ∂kahlerVolume omega, u x ≠ ⊥ := by
    apply ae_iff.mpr
    simpa only [not_not, kahlerVolume, diagonalPotentialMeasure] using
      GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
        (θ := fun _ : Fin n => omega.form) (u := fun _ => fun _ : M => (0 : EReal))
        (fun _ : Fin n => hω0.1) huP
  have hc : 0 ≤ smoothVolumeCoefficient omega θ φ hφ :=
    div_nonneg measureReal_nonneg measureReal_nonneg
  have hbound : ∀ t : ℝ, 0 < t →
      ((energy θ φ hφ (perturbedRooftop θ u h t)).toReal -
        (energy θ φ hφ u).toReal) / t ≤
      smoothVolumeCoefficient omega θ φ hφ * (∫ x, h x ∂kahlerVolume omega) := by
    intro t ht
    let p : M → EReal := perturbedRooftop θ u h t
    have hpF := relativeFiniteEnergyPreceq_perturbedRooftop omega hn hbig hu hu0 hh hh0 ht.le
    have hPi := (integrable_and_integral_toReal_add_const omega hpF.1.plurisubharmonic 0).1
    have hth : Continuous (fun x => t * h x) := continuous_const.mul hh
    have hth0 : ∀ x, t * h x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos ht.le (hh0 x)
    obtain ⟨L, _hL0, _hL, hp, hlo, hbelow, _hhigh⟩ :=
      exists_genuine_rooftop_sandwich hn hbig huP hu0 hth hth0
    have hreal : ∀ᵐ x ∂kahlerVolume omega, (p x).toReal ≤ (u x).toReal + t * h x := by
      filter_upwards [hpole] with x hx
      have hux : u x = ((u x).toReal : EReal) :=
        (EReal.coe_toReal (huP.1.quasiPlurisubharmonic.ne_top x) hx).symm
      have hlowbot : u x + ((-L : ℝ) : EReal) ≠ ⊥ := by
        rw [hux, ← EReal.coe_add]
        simp
      have hpxbot : p x ≠ ⊥ := ne_bot_of_le_ne_bot hlowbot (hlo x)
      have hpx : p x = ((p x).toReal : EReal) :=
        (EReal.coe_toReal (hp.1.quasiPlurisubharmonic.ne_top x) hpxbot).symm
      have hbd := hbelow x
      change p x ≤ u x + ((t * h x : ℝ) : EReal) at hbd
      rw [hpx, hux, ← EReal.coe_add] at hbd
      exact EReal.coe_le_coe_iff.mp hbd
    have hIp := integral_mono_ae hPi (hUi.add (hHi.const_mul t)) hreal
    change (∫ x, (p x).toReal ∂kahlerVolume omega) ≤
      (∫ x, (u x).toReal + t * h x ∂kahlerVolume omega) at hIp
    rw [integral_add hUi (hHi.const_mul t), integral_const_mul] at hIp
    have hF := hmax p hpF
    unfold smoothVolumeFunctional at hF
    have hcm := mul_le_mul_of_nonneg_left hIp hc
    apply (div_le_iff₀ ht).mpr
    change (energy θ φ hφ p).toReal - (energy θ φ hφ u).toReal ≤
      smoothVolumeCoefficient omega θ φ hφ * (∫ x, h x ∂kahlerVolume omega) * t
    nlinarith
  exact le_of_tendsto (energy_quotient_tendsto omega hn hbig hu hu0 hh hh0)
    (Eventually.of_forall fun j => hbound (1 / ((j : ℝ) + 1)) (by positivity))


/-- Natural original functional optimality produces the whole original
Euler measure equation; optimizer and prescribed-MA existence are separate. -/
theorem diagonalPotentialMeasure_eq_smul_kahlerVolume_of_functional_max
    (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (hu0 : ∀ x, u x ≤ 0)
    (hmax : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      smoothVolumeFunctional omega θ φ hφ a ≤ smoothVolumeFunctional omega θ φ hφ u) :
    diagonalPotentialMeasure θ u hu.1.plurisubharmonic =
      ENNReal.ofReal (smoothVolumeCoefficient omega θ φ hφ) • kahlerVolume omega := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n M
  let μ := diagonalPotentialMeasure θ u hu.1.plurisubharmonic
  let vol := kahlerVolume omega
  let c := smoothVolumeCoefficient omega θ φ hφ
  let ν := ENNReal.ofReal c • vol
  let : IsFiniteMeasure μ :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hu.1.plurisubharmonic
  let : IsFiniteMeasure ν := by
    constructor
    change ENNReal.ofReal c * vol univ < ⊤
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top vol univ)
  have hc : 0 ≤ c := div_nonneg measureReal_nonneg measureReal_nonneg
  have hvolpos : 0 < vol.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos
      (KahlerLaplacianStokes.kahlerVolume_pos_of_isOpen omega isOpen_univ univ_nonempty).ne'
      (measure_ne_top _ _)
  have hmassModel : μ.real univ = modelVolume θ φ hφ :=
    congrArg ENNReal.toReal (hu.1.mass_eq hu.1.plurisubharmonic)
  have hcoef : c * vol.real univ = modelVolume θ φ hφ :=
    div_mul_cancel₀ _ hvolpos.ne'
  have hmass : μ.real univ = c * vol.real univ := hmassModel.trans hcoef.symm
  change μ = ν
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro q
  have hqμ : Integrable (fun x => q x) μ := BoundedContinuousFunction.integrable μ q
  have hqvol : Integrable (fun x => q x) vol := BoundedContinuousFunction.integrable vol q
  obtain ⟨B, hB⟩ := (isCompact_range q.continuous.abs).bddAbove
  let K : ℝ := max B 0
  have hqK : ∀ x, |q x| ≤ K := fun x =>
    (hB ⟨x, rfl⟩).trans (le_max_left _ _)
  have h1 := integral_le_of_nonpositive_of_functional_max omega hn hbig hu hu0 hmax
    (h := fun x => q x - K) (q.continuous.sub continuous_const)
    (fun x => sub_nonpos.mpr ((le_abs_self _).trans (hqK x)))
  have h2 := integral_le_of_nonpositive_of_functional_max omega hn hbig hu hu0 hmax
    (h := fun x => -(q x) - K) (q.continuous.neg.sub continuous_const)
    (fun x => sub_nonpos.mpr ((neg_le_abs _).trans (hqK x)))
  change (∫ x, q x - K ∂μ) ≤ c * (∫ x, q x - K ∂vol) at h1
  change (∫ x, -(q x) - K ∂μ) ≤ c * (∫ x, -(q x) - K ∂vol) at h2
  rw [integral_sub hqμ (integrable_const K), integral_sub hqvol (integrable_const K),
    integral_const, integral_const] at h1
  have hnqμ : Integrable (fun x => -(q x)) μ := by
    convert hqμ.neg using 1
    funext x
    rfl
  have hnqvol : Integrable (fun x => -(q x)) vol := by
    convert hqvol.neg using 1
    funext x
    rfl
  rw [integral_sub hnqμ (integrable_const K), integral_sub hnqvol (integrable_const K),
    integral_neg, integral_neg, integral_const, integral_const] at h2
  simp only [smul_eq_mul] at h1 h2
  rw [hmass] at h1 h2
  have hread : (∫ x, q x ∂μ) = c * (∫ x, q x ∂vol) :=
    le_antisymm (by nlinarith [h1]) (by nlinarith [h2])
  calc (∫ x, q x ∂μ) = c * (∫ x, q x ∂vol) := hread
    _ = ∫ x, q x ∂ν := by
      change c * (∫ x, q x ∂vol) = ∫ x, q x ∂(ENNReal.ofReal c • vol)
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_ofReal hc, smul_eq_mul]

end

end SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalEuler
