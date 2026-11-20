import SGPT.Envelopes.RelativeMAExpLsc
import SGPT.Foundations.Analysis.Pending.ActualSmoothVolumeVariationalEuler
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedTranslation
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity

/-!
# Euler–Lagrange equation of the exponential functional

For a model potential `φ` with positive mass, a finite measure `ν` charging no
pluripolar set, `λ > 0` and `κ ≥ 0`, consider on `E¹(X, θ; φ)` the functional
`G(v) = E(v) - κ ∫ e^{λ v} dν`.
If a nonpositive `b ∈ E¹(X, θ; φ)` maximizes `G`, then `θ_b^n = κ λ e^{λ b} ν`
(Xia, *Foundations of pluripotential theory*,
`lem:relative-exponential-maximizer-equation`).

The proof perturbs `b` by the envelopes `P_θ(b + t h)` of continuous
`h ≤ 0` and uses the one-sided derivative of the energy along these envelopes
(TN `ActualContinuousObstacleDiscreteEnergyVariation.energy_quotient_tendsto`).
Translations `b + s` give the mass identity `∫ θ_b^n = κ λ ∫ e^{λ b} dν`, which
turns the one-sided inequalities into an equality of measures.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Envelopes.RelativeMA

open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass SGPT.Foundations.Analysis.Pending.RelativePreceqClasses
open SGPT.Foundations.Analysis.Pending.RelativeDarvasDistance
open SGPT.Foundations.Analysis.Pending.ActualContinuousObstacleDiscreteEnergyVariation

theorem exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have hx := Real.exp_pos x
  have e : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- The exponential functional `G(v) = E(v) - κ ∫ e^{λ v} dν`. -/
def expFunctional (θ : ClosedRealOneOneForm n M) (φ : M → EReal) (hφ : IsModelPotential θ φ)
    (ν : Measure M) (lam κ : ℝ) (u : M → EReal) : ℝ :=
  (energy θ φ hφ u).toReal - κ * ∫ x, expWeight lam u x ∂ν

variable {θ : ClosedRealOneOneForm n M} {φ : M → EReal} {hφ : IsModelPotential θ φ}

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- Translation of the exponential weight off the pole set. -/
theorem expWeight_add_const {lam : ℝ} {u : M → EReal} (hu : ∀ x, u x ≠ ⊤) (s : ℝ) {x : M}
    (hx : u x ≠ ⊥) :
    expWeight lam (fun y => u y + (s : EReal)) x = Real.exp (lam * s) * expWeight lam u x := by
  unfold expWeight
  rw [EReal.toReal_add (hu x) hx (EReal.coe_ne_top s) (EReal.coe_ne_bot s), EReal.toReal_coe,
    ← Real.exp_add]
  ring_nf

omit [CompactSpace M] [BorelSpace M] in
theorem integral_expWeight_add_const {ν : Measure M}
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {lam : ℝ} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (s : ℝ) :
    ∫ x, expWeight lam (fun y => u y + (s : EReal)) x ∂ν =
      Real.exp (lam * s) * ∫ x, expWeight lam u x ∂ν := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_ne_bot_of_doesNotCharge hν hu] with x hx
  exact expWeight_add_const hu.1.quasiPlurisubharmonic.ne_top s hx

/-- Energy translation in real form on `E¹`. -/
theorem toReal_energy_add_const (omega : KahlerBackground n M)
    {u : M → EReal} (hu : RelativeFiniteEnergyPreceq θ φ u hφ) (s : ℝ) :
    (energy θ φ hφ (fun x => u x + (s : EReal))).toReal =
      (energy θ φ hφ u).toReal + s * modelVolume θ φ hφ := by
  rw [SingularModelEnergyExtendedTranslation.energy_add_const omega u s,
    ← SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu, ← EReal.coe_add]
  simp only [EReal.toReal_coe]

/-- **Mass identity** of a maximizer of the exponential functional:
`∫ θ_b^n = κ λ ∫ e^{λ b} dν`. -/
theorem modelVolume_eq_of_expFunctional_max (omega : KahlerBackground n M) {ν : Measure M}
    [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {lam κ : ℝ}
    (hκ : 0 ≤ κ) {b : M → EReal} (hb : RelativeFiniteEnergyPreceq θ φ b hφ)
    (hmax : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      expFunctional θ φ hφ ν lam κ a ≤ expFunctional θ φ hφ ν lam κ b) :
    modelVolume θ φ hφ = κ * lam * ∫ x, expWeight lam b x ∂ν := by
  set m := modelVolume θ φ hφ
  set I := ∫ x, expWeight lam b x ∂ν
  have hI : 0 ≤ I := integral_nonneg fun x => expWeight_nonneg lam b x
  have hkey : ∀ s : ℝ, s * m ≤ κ * I * (Real.exp (lam * s) - 1) := by
    intro s
    have h := hmax _ (RelativeFiniteEnergyPreceq.add_const omega hb s)
    unfold expFunctional at h
    rw [toReal_energy_add_const omega hb s,
      integral_expWeight_add_const hν hb.1.plurisubharmonic s] at h
    nlinarith
  have hbound : ∀ s : ℝ, s * m ≤ s * (κ * I * lam * Real.exp (lam * s)) := by
    intro s
    have h1 := exp_sub_one_le_mul_exp (lam * s)
    have hκI : 0 ≤ κ * I := mul_nonneg hκ hI
    calc s * m ≤ κ * I * (Real.exp (lam * s) - 1) := hkey s
      _ ≤ κ * I * (lam * s * Real.exp (lam * s)) := mul_le_mul_of_nonneg_left h1 hκI
      _ = s * (κ * I * lam * Real.exp (lam * s)) := by ring
  have hlim : Tendsto (fun s : ℝ => κ * I * lam * Real.exp (lam * s)) (𝓝 0)
      (𝓝 (κ * I * lam * Real.exp (lam * 0))) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0).const_mul _
  rw [mul_zero, Real.exp_zero, mul_one] at hlim
  have hpos : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hneg : Tendsto (fun k : ℕ => -(1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [neg_zero] using hpos.neg
  have hup : m ≤ κ * I * lam := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.comp hpos) fun k => ?_
    have hs : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact le_of_mul_le_mul_left (hbound _) hs
  have hlow : κ * I * lam ≤ m := by
    refine le_of_tendsto_of_tendsto' (hlim.comp hneg) tendsto_const_nhds fun k => ?_
    have hs : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have h := hbound (-(1 / ((k : ℝ) + 1)))
    simp only [Function.comp_apply]
    nlinarith
  linarith

/-- The difference quotients of the exponential term converge to `λ ∫ h e^{λ b} dν`. -/
theorem tendsto_expWeight_quotient {ν : Measure M} [IsFiniteMeasure ν] {lam : ℝ}
    (hlam : 0 < lam) {b : M → EReal} (hbP : IsThetaPshPotential θ.val b) (hb0 : ∀ x, b x ≤ 0)
    {h : M → ℝ} (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    Tendsto (fun j : ℕ => ∫ x, expWeight lam b x *
        ((Real.exp (lam * (1 / ((j : ℝ) + 1) * h x)) - 1) / (1 / ((j : ℝ) + 1))) ∂ν)
      atTop (𝓝 (lam * ∫ x, h x * expWeight lam b x ∂ν)) := by
  obtain ⟨K, hK⟩ := (isCompact_range hh.abs).bddAbove
  have hK' : ∀ x, |h x| ≤ K := fun x => hK ⟨x, rfl⟩
  have hbm := measurable_expWeight hbP lam
  rw [← integral_const_mul]
  refine tendsto_integral_of_dominated_convergence (fun _ => lam * K) ?_ (integrable_const _) ?_ ?_
  · intro j
    exact (hbm.mul ((((Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.mul hh))).sub continuous_const).div_const _).measurable)).aestronglyMeasurable
  · intro j
    refine Eventually.of_forall fun x => ?_
    set t : ℝ := 1 / ((j : ℝ) + 1)
    have ht : 0 < t := by positivity
    set y : ℝ := lam * h x
    have hy : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le (hh0 x)
    have e1 : lam * (t * h x) = t * y := by ring
    rw [e1]
    have h1 : t * y ≤ Real.exp (t * y) - 1 := by linarith [Real.add_one_le_exp (t * y)]
    have h2 : Real.exp (t * y) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le hy)
    have hq1 : y ≤ (Real.exp (t * y) - 1) / t := by
      rw [le_div_iff₀ ht]; linarith
    have hq2 : (Real.exp (t * y) - 1) / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ht.le
    have he0 := expWeight_nonneg lam b x
    have he1 := expWeight_le_one hlam.le hb0 x
    have hyK : -(lam * K) ≤ y := by
      have := (abs_le.mp (hK' x)).1
      simp only [y]
      nlinarith
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith
  · refine Eventually.of_forall fun x => ?_
    set y : ℝ := lam * h x
    have hy : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le (hh0 x)
    have hpos : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hupper : Tendsto (fun j : ℕ => y * Real.exp (1 / ((j : ℝ) + 1) * y)) atTop (𝓝 y) := by
      have hc : Continuous (fun t : ℝ => Real.exp (t * y)) :=
        Real.continuous_exp.comp (continuous_id.mul continuous_const)
      have := (hc.tendsto 0).comp hpos
      simp only [zero_mul, Real.exp_zero] at this
      have h2 := this.const_mul y
      rw [mul_one] at h2
      exact h2
    have hq : Tendsto (fun j : ℕ => (Real.exp (1 / ((j : ℝ) + 1) * y) - 1) / (1 / ((j : ℝ) + 1)))
        atTop (𝓝 y) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun j => ?_) (fun j => ?_)
      · have ht : 0 < 1 / ((j : ℝ) + 1) := by positivity
        rw [le_div_iff₀ ht]
        linarith [Real.add_one_le_exp (1 / ((j : ℝ) + 1) * y)]
      · have ht : 0 < 1 / ((j : ℝ) + 1) := by positivity
        rw [div_le_iff₀ ht]
        have := exp_sub_one_le_mul_exp (1 / ((j : ℝ) + 1) * y)
        nlinarith
    have e : ∀ j : ℕ, lam * (1 / ((j : ℝ) + 1) * h x) = 1 / ((j : ℝ) + 1) * y := fun j => by ring
    simp only [e]
    have := hq.const_mul (expWeight lam b x)
    convert this using 2
    simp only [y]
    ring

variable [ConnectedSpace M]

/-- The one-sided Euler inequality for a nonpositive maximizer of `G`. -/
theorem integral_le_of_expFunctional_max (omega : KahlerBackground n M) (hn : 0 < n)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ν : Measure M} [IsFiniteMeasure ν]
    (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {lam κ : ℝ} (hlam : 0 < lam) (hκ : 0 ≤ κ)
    {b : M → EReal} (hb : RelativeFiniteEnergyPreceq θ φ b hφ) (hb0 : ∀ x, b x ≤ 0)
    (hmax : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      expFunctional θ φ hφ ν lam κ a ≤ expFunctional θ φ hφ ν lam κ b)
    {h : M → ℝ} (hh : Continuous h) (hh0 : ∀ x, h x ≤ 0) :
    (∫ x, h x ∂diagonalPotentialMeasure θ b hb.1.plurisubharmonic) ≤
      κ * (lam * ∫ x, h x * expWeight lam b x ∂ν) := by
  have hbP := hb.1.plurisubharmonic
  have hpole := ae_ne_bot_of_doesNotCharge hν hbP
  have hIb := integrable_expWeight (ν := ν) hlam.le hbP hb0
  let τ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hτ : ∀ j, 0 < τ j := fun j => by positivity
  have hbound : ∀ j : ℕ,
      ((energy θ φ hφ (perturbedRooftop θ b h (τ j))).toReal - (energy θ φ hφ b).toReal) / τ j ≤
      κ * ∫ x, expWeight lam b x * ((Real.exp (lam * (τ j * h x)) - 1) / τ j) ∂ν := by
    intro j
    set t := τ j
    have ht := hτ j
    let p : M → EReal := perturbedRooftop θ b h t
    have hpF := relativeFiniteEnergyPreceq_perturbedRooftop omega hn hbig hb hb0 hh hh0 ht.le
    have hth : Continuous (fun x => t * h x) := continuous_const.mul hh
    have hth0 : ∀ x, t * h x ≤ 0 := fun x => mul_nonpos_of_nonneg_of_nonpos ht.le (hh0 x)
    obtain ⟨L, _hL0, _hL, _hp, hlo, hbelow, _hhigh⟩ :=
      ActualContinuousSingularObstacleContact.exists_genuine_rooftop_sandwich hn hbig hbP hb0 hth
        hth0
    have hp0 : ∀ x, p x ≤ 0 := fun x => (hbelow x).trans (_hhigh x) |>.trans (hb0 x)
    have hIp := integrable_expWeight (ν := ν) hlam.le hpF.1.plurisubharmonic hp0
    have hmul : Continuous fun x => Real.exp (lam * (t * h x)) :=
      Real.continuous_exp.comp (continuous_const.mul (continuous_const.mul hh))
    have hIprod : Integrable (fun x => expWeight lam b x * Real.exp (lam * (t * h x))) ν := by
      refine hIb.mul_of_top_left ?_
      refine memLp_top_of_bound hmul.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos hlam.le (hth0 x)
    have hcmp : ∫ x, expWeight lam p x ∂ν ≤
        ∫ x, expWeight lam b x * Real.exp (lam * (t * h x)) ∂ν := by
      apply integral_mono_ae hIp hIprod
      filter_upwards [hpole] with x hx
      have hbfin : ((b x).toReal : EReal) = b x :=
        EReal.coe_toReal (hbP.1.quasiPlurisubharmonic.ne_top x) hx
      have hpbot : p x ≠ ⊥ := by
        apply ne_bot_of_le_ne_bot _ (hlo x)
        rw [← hbfin, ← EReal.coe_add]
        exact EReal.coe_ne_bot _
      have hpfin : ((p x).toReal : EReal) = p x :=
        EReal.coe_toReal (hpF.1.plurisubharmonic.1.quasiPlurisubharmonic.ne_top x) hpbot
      have hle : (p x).toReal ≤ (b x).toReal + t * h x := by
        have h1 := hbelow x
        change p x ≤ b x + ((t * h x : ℝ) : EReal) at h1
        rw [← hpfin, ← hbfin, ← EReal.coe_add] at h1
        exact EReal.coe_le_coe_iff.mp h1
      unfold expWeight
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hF := hmax p hpF
    unfold expFunctional at hF
    have hκI := mul_le_mul_of_nonneg_left hcmp hκ
    have hsplit : ∫ x, expWeight lam b x * ((Real.exp (lam * (t * h x)) - 1) / t) ∂ν =
        ((∫ x, expWeight lam b x * Real.exp (lam * (t * h x)) ∂ν) -
          ∫ x, expWeight lam b x ∂ν) / t := by
      rw [← integral_sub hIprod hIb, ← integral_div]
      congr 1
      funext x
      ring
    rw [hsplit, ← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right ht).mpr (by linarith)
  exact le_of_tendsto_of_tendsto (energy_quotient_tendsto omega hn hbig hb hb0 hh hh0)
    ((tendsto_expWeight_quotient hlam hbP hb0 hh hh0).const_mul κ) (Eventually.of_forall hbound)

/-- **Euler–Lagrange equation.** A nonpositive maximizer `b` of
`G(v) = E(v) - κ ∫ e^{λ v} dν` on `E¹(X, θ; φ)` satisfies `θ_b^n = κ λ e^{λ b} ν`. -/
theorem diagonalPotentialMeasure_eq_of_expFunctional_max (omega : KahlerBackground n M)
    (hn : 0 < n) (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {ν : Measure M}
    [IsFiniteMeasure ν] (hν : DoesNotChargeManifoldPluripolar (n := n) ν) {lam κ : ℝ}
    (hlam : 0 < lam) (hκ : 0 ≤ κ)
    {b : M → EReal} (hb : RelativeFiniteEnergyPreceq θ φ b hφ) (hb0 : ∀ x, b x ≤ 0)
    (hmax : ∀ a : M → EReal, RelativeFiniteEnergyPreceq θ φ a hφ →
      expFunctional θ φ hφ ν lam κ a ≤ expFunctional θ φ hφ ν lam κ b) :
    diagonalPotentialMeasure θ b hb.1.plurisubharmonic =
      ν.withDensity (fun x => ENNReal.ofReal (κ * lam * expWeight lam b x)) := by
  let : Nonempty M := ModelRaySupremum.nonempty_of_modelPotential hφ
  let : TopologicalSpace.PseudoMetrizableSpace M :=
    DiagonalMeasureRegularity.pseudoMetrizableSpace_of_isComplexManifold n M
  have hbP := hb.1.plurisubharmonic
  let μ := diagonalPotentialMeasure θ b hbP
  let dens : M → ℝ := fun x => κ * lam * expWeight lam b x
  have hdens0 : ∀ x, 0 ≤ dens x := fun x =>
    mul_nonneg (mul_nonneg hκ hlam.le) (expWeight_nonneg lam b x)
  have hdm : Measurable dens := measurable_const.mul (measurable_expWeight hbP lam)
  let ρ := ν.withDensity (fun x => ENNReal.ofReal (dens x))
  let : IsFiniteMeasure μ :=
    DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure omega θ hbP
  have hIb := integrable_expWeight (ν := ν) hlam.le hbP hb0
  let : IsFiniteMeasure ρ := by
    refine isFiniteMeasure_withDensity_ofReal ?_
    exact ((hIb.const_mul (κ * lam)).hasFiniteIntegral)
  have hρint : ∀ g : M → ℝ, ∫ x, g x ∂ρ = ∫ x, dens x * g x ∂ν := by
    intro g
    change ∫ x, g x ∂(ν.withDensity (fun x => ENNReal.ofReal (dens x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (hdens0 x), smul_eq_mul]
  have hmassModel : μ.real univ = modelVolume θ φ hφ :=
    congrArg ENNReal.toReal (hb.1.mass_eq hbP)
  have hmass : modelVolume θ φ hφ = κ * lam * ∫ x, expWeight lam b x ∂ν :=
    modelVolume_eq_of_expFunctional_max omega hν hκ hb hmax
  change μ = ρ
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro q
  have hqμ : Integrable (fun x => q x) μ := BoundedContinuousFunction.integrable μ q
  obtain ⟨B, hB⟩ := (isCompact_range q.continuous.abs).bddAbove
  let K : ℝ := max B 0
  have hqK : ∀ x, |q x| ≤ K := fun x => (hB ⟨x, rfl⟩).trans (le_max_left _ _)
  have hqe : Integrable (fun x => q x * expWeight lam b x) ν := by
    refine hIb.bdd_mul q.continuous.aestronglyMeasurable (c := K) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]; exact hqK x
  have h1 := integral_le_of_expFunctional_max omega hn hbig hν hlam hκ hb hb0 hmax
    (h := fun x => q x - K) (q.continuous.sub continuous_const)
    (fun x => sub_nonpos.mpr ((le_abs_self _).trans (hqK x)))
  have h2 := integral_le_of_expFunctional_max omega hn hbig hν hlam hκ hb hb0 hmax
    (h := fun x => -(q x) - K) (q.continuous.neg.sub continuous_const)
    (fun x => sub_nonpos.mpr ((neg_le_abs _).trans (hqK x)))
  change (∫ x, q x - K ∂μ) ≤ κ * (lam * ∫ x, (q x - K) * expWeight lam b x ∂ν) at h1
  change (∫ x, -(q x) - K ∂μ) ≤ κ * (lam * ∫ x, (-(q x) - K) * expWeight lam b x ∂ν) at h2
  have e1 : ∫ x, (q x - K) * expWeight lam b x ∂ν =
      ∫ x, q x * expWeight lam b x ∂ν - K * ∫ x, expWeight lam b x ∂ν := by
    rw [show (fun x => (q x - K) * expWeight lam b x) =
        fun x => q x * expWeight lam b x - K * expWeight lam b x by funext x; ring,
      integral_sub hqe (hIb.const_mul K), integral_const_mul]
  have e2 : ∫ x, (-(q x) - K) * expWeight lam b x ∂ν =
      -∫ x, q x * expWeight lam b x ∂ν - K * ∫ x, expWeight lam b x ∂ν := by
    rw [show (fun x => (-(q x) - K) * expWeight lam b x) =
        fun x => -(q x * expWeight lam b x + K * expWeight lam b x) by funext x; ring,
      integral_neg, integral_add hqe (hIb.const_mul K), integral_const_mul]
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [integral_sub hqμ (integrable_const K), integral_const] at h1
  have hnqμ : Integrable (fun x => -(q x)) μ := hqμ.neg
  rw [integral_sub hnqμ (integrable_const K), integral_neg, integral_const] at h2
  simp only [smul_eq_mul] at h1 h2
  rw [hmassModel, hmass] at h1 h2
  rw [hρint]
  have hread : (∫ x, q x ∂μ) = κ * lam * ∫ x, q x * expWeight lam b x ∂ν := by
    apply le_antisymm <;> nlinarith
  rw [hread, ← integral_const_mul]
  congr 1
  funext x
  simp only [dens]
  ring

end SGPT.Envelopes.RelativeMA
