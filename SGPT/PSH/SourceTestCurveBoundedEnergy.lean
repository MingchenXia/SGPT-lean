import SGPT.PSH.SourceTestCurvePrefixIncrement
import SGPT.PSH.SourceTestCurveDyadicEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedTranslation

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

omit [ConnectedSpace M] in
private theorem model_energy_zero (omega : KahlerBackground n M) :
    sourceRelativeEnergy θ φ φ hφ = 0 := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyCocycle.energy_eq_of_relativeEInfinity omega _ hφ.toNative
      ⟨hφ.toNative.plurisubharmonic, SameSingularityTypeOn.refl φ univ⟩,
    RelativeEnergy.relativeEnergyOfMinimalType_self, EReal.coe_zero]

omit [ConnectedSpace M] in
private theorem model_translate_energy (omega : KahlerBackground n M) (c : ℝ) :
    sourceRelativeEnergy θ φ (fun x => φ x + (c : EReal)) hφ =
      ((c * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  rw [sourceRelativeEnergy_eq_native,
    SingularModelEnergyExtendedTranslation.energy_add_const omega φ c]
  have hz := model_energy_zero (θ := θ) (hφ := hφ) omega
  rw [sourceRelativeEnergy_eq_native] at hz
  rw [hz, zero_add]
  rfl

omit [BorelSpace M] [ConnectedSpace M] in
/-- Every included earlier parameter is the ACTUAL model slice, so the
literal anchored prefix equals that model plus its final finite coefficient. -/
theorem SourceTestCurve.integerPrefix_anchor
    (Γ : SourceTestCurve θ) {L : ℕ} (hL : 0 < L)
    (hanchor : ∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata (1 / (2 : ℝ)^N) t
      (-(L : ℤ) * (2 : ℤ)^N) = fun x => φ x + ((-(t * (L : ℝ)) : ℝ) : EReal) := by
  have hδ : 0 < 1 / (2 : ℝ)^N := by positivity
  have ha : ((-(L : ℤ) * (2 : ℤ)^N : ℤ) : ℝ) * (1 / (2 : ℝ)^N) = -(L : ℝ) := by
    push_cast
    field_simp
  funext x
  apply le_antisymm
  · apply iSup_le
    intro k
    have hk : (k.1 : ℝ) * (1 / (2 : ℝ)^N) ≤ -(L : ℝ) := by
      rw [← ha]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show k.1 ≤ -(L : ℤ) * (2 : ℤ)^N from k.2)) hδ.le
    rw [hanchor _ hk]
    apply add_le_add le_rfl
    apply EReal.coe_le_coe
    nlinarith [mul_le_mul_of_nonneg_left hk ht.le]
  · have hh := le_iSup (fun k : Iic (-(L : ℤ) * (2 : ℤ)^N) =>
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) * (1 / (2 : ℝ)^N)) x +
        ((t * (k.1 : ℝ) * (1 / (2 : ℝ)^N) : ℝ) : EReal))
      ⟨-(L : ℤ) * (2 : ℤ)^N, by change -(L : ℤ) * (2 : ℤ)^N ≤ -(L : ℤ) * (2 : ℤ)^N; exact le_rfl⟩
    have hcoef : t * ((-(L : ℤ) * (2 : ℤ)^N : ℤ) : ℝ) * (1 / (2 : ℝ)^N) =
        -(t * (L : ℝ)) := by nlinarith [congrArg (fun z : ℝ => t * z) ha]
    rw [ha, hanchor _ le_rfl, hcoef] at hh
    exact hh

omit [ConnectedSpace M] in
/-- Genuine arbitrary-model energy translation computes the SAME actual
anchored prefix energy; no boundedness of the model or energy certificate. -/
theorem SourceTestCurve.integerPrefix_anchor_energy (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) {L : ℕ} (hL : 0 < L)
    (hanchor : ∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    sourceRelativeEnergy θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata (1 / (2 : ℝ)^N) t
        (-(L : ℤ) * (2 : ℤ)^N)) hφ =
      ((-(t * (L : ℝ)) *
        (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  rw [Γ.integerPrefix_anchor hL hanchor ht N]
  exact model_translate_energy omega _

omit [ConnectedSpace M] [BorelSpace M] in
private theorem mass_readback_congr {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (heq : u = v) :
    (sourcePotentialNonPluripolarMeasure θ u hu univ).toReal =
      (sourcePotentialNonPluripolarMeasure θ v hv univ).toReal := by
  cases heq
  rfl

private theorem deficit_eq_of_anchor (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0)
    {L : ℕ} (hL : 0 < L)
    (hanchor : ∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ) :
    let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
    let f := sourceTestCurveClosedRealMassAt omega Γ
    (∫⁻ r : ℝ in Iio (0 : ℝ), ENNReal.ofReal (V - sourceTestCurveRealMassAt omega Γ r)) =
      ENNReal.ofReal ((L : ℝ) * V - ∫ r in (-(L : ℝ))..0, f r) ∧
    0 ≤ (L : ℝ) * V - ∫ r in (-(L : ℝ))..0, f r := by
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  let f := sourceTestCurveClosedRealMassAt omega Γ
  let q := fun r : ℝ => V - sourceTestCurveRealMassAt omega Γ r
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hleft : -(L : ℝ) ≤ 0 := by linarith
  have hb : ∀ r : ℝ, 0 ≤ f r ∧ f r ≤ V :=
    sourceTestCurveClosedRealMassAt_nonneg_le_model omega hφ Γ hΓ.1
  have hf : IntervalIntegrable f volume (-(L : ℝ)) 0 :=
    (sourceTestCurveClosedRealMassAt_antitone omega Γ).intervalIntegrable
  have hqi : IntervalIntegrable (fun r => V - f r) volume (-(L : ℝ)) 0 :=
    intervalIntegrable_const.sub hf
  have hqset : IntegrableOn (fun r => V - f r) (Ioc (-(L : ℝ)) 0) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hleft).mp hqi
  have hcalc : (∫ r in (-(L : ℝ))..0, V - f r) =
      (L : ℝ) * V - ∫ r in (-(L : ℝ))..0, f r := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf, intervalIntegral.integral_const]
    simp only [zero_sub, neg_neg, smul_eq_mul]
  have hnonneg : 0 ≤ (L : ℝ) * V - ∫ r in (-(L : ℝ))..0, f r := by
    rw [← hcalc, intervalIntegral.integral_of_le hleft]
    exact integral_nonneg (fun r => sub_nonneg.mpr (hb r).2)
  have hmodel (r : ℝ) (hr : r ≤ -(L : ℝ)) :
      sourceTestCurveRealMassAt omega Γ r = V := by
    have hrmax : r < Γ.max := by rw [hmax]; linarith
    rw [← sourceTestCurveClosedRealMassAt_eq_realMassAt_of_lt omega Γ hrmax,
      sourceTestCurveClosedRealMassAt_of_le omega Γ hrmax.le]
    exact mass_readback_congr _ _ (hanchor r hr)
  have htail : (∫⁻ r : ℝ in Iio (-(L : ℝ)), ENNReal.ofReal (q r)) = 0 := by
    calc
      _ = ∫⁻ _r : ℝ in Iio (-(L : ℝ)), (0 : ENNReal) :=
        setLIntegral_congr_fun measurableSet_Iio fun r hr => by
          dsimp [q]
          rw [hmodel r hr.le, sub_self, ENNReal.ofReal_zero]
      _ = 0 := by simp
  have hdisj : Disjoint (Iio (-(L : ℝ))) (Ico (-(L : ℝ)) 0) := by
    apply Set.disjoint_left.mpr
    intro r hr hs
    exact not_lt_of_ge hs.1 hr
  have hfinite : (∫⁻ r : ℝ in Ico (-(L : ℝ)) 0, ENNReal.ofReal (q r)) =
      ENNReal.ofReal ((L : ℝ) * V - ∫ r in (-(L : ℝ))..0, f r) := by
    calc
      _ = ∫⁻ r : ℝ in Ico (-(L : ℝ)) 0, ENNReal.ofReal (V - f r) := by
        apply setLIntegral_congr_fun measurableSet_Ico
        intro r hr
        have hh := sourceTestCurveClosedRealMassAt_eq_realMassAt_of_lt omega Γ
          (show r < Γ.max by rw [hmax]; exact hr.2)
        dsimp [q, f]
        rw [hh]
      _ = ∫⁻ r : ℝ in Ioc (-(L : ℝ)) 0, ENNReal.ofReal (V - f r) := by
        rw [MeasureTheory.restrict_Ico_eq_restrict_Ioc]
      _ = ENNReal.ofReal (∫ r : ℝ in Ioc (-(L : ℝ)) 0, V - f r) :=
        (ofReal_integral_eq_lintegral_ofReal hqset
          (Filter.Eventually.of_forall fun r => sub_nonneg.mpr (hb r).2)).symm
      _ = _ := by rw [← intervalIntegral.integral_of_le hleft, hcalc]
  refine ⟨?_, hnonneg⟩
  change (∫⁻ r : ℝ in Iio (0 : ℝ), ENNReal.ofReal (q r)) = _
  rw [← Iio_union_Ico_eq_Iio hleft, lintegral_union measurableSet_Ico hdisj, htail, zero_add]
  exact hfinite

/-- The ACTUAL defining TC energy equals the finite closed-mass interval
formula; its infinite tail is genuinely zero, and cutoff endpoints only AE. -/
theorem SourceTestCurve.boundedEnergy_eq_interval_of_anchor (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0)
    {L : ℕ} (hL : 0 < L)
    (hanchor : ∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ) :
    sourceTestCurveEnergy omega hφ Γ hΓ.1 =
      ((∫ r in (-(L : ℝ))..0, sourceTestCurveClosedRealMassAt omega Γ r) -
        (L : ℝ) * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) := by
  have hh := deficit_eq_of_anchor omega Γ hΓ hmax hL hanchor
  unfold sourceTestCurveEnergy
  rw [hmax, hh.1, EReal.coe_ennreal_ofReal,
    max_eq_left hh.2]
  simp only [zero_mul, EReal.coe_zero, zero_sub]
  rw [← EReal.coe_neg]
  congr 1
  ring

/-- Original boundedness manufactures the finite formula and genuine
finite-energy membership without any assumed energy certificate. -/
theorem SourceTestCurve.boundedEnergy_finite (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0) :
    Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ ∧
    ∃ L : ℕ, 0 < L ∧
      (∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ) ∧
      sourceTestCurveEnergy omega hφ Γ hΓ.1 =
        ((∫ r in (-(L : ℝ))..0, sourceTestCurveClosedRealMassAt omega Γ r) -
          (L : ℝ) * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) := by
  obtain ⟨L, hL, ha, _⟩ := Γ.exists_integer_model_anchor omega hφ hΓ hmax
  have he := Γ.boundedEnergy_eq_interval_of_anchor omega hΓ hmax hL ha
  refine ⟨⟨hΓ.1, ?_⟩, L, hL, ha, he⟩
  rw [he]
  exact EReal.bot_lt_coe _

private theorem prefix_energy_readback_step (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (((j + 1 : ℤ) : ℝ) * d) ≤ Γ.max) :
    let e := fun k : ℤ => (sourceRelativeEnergy θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t k) hφ).toReal
    t * d * sourceTestCurveClosedRealMassAt omega Γ (((j + 1 : ℤ) : ℝ) * d) ≤
        e (j + 1) - e j ∧
      e (j + 1) - e j ≤ t * d * sourceTestCurveClosedRealMassAt omega Γ ((j : ℝ) * d) := by
  have hjold : (j : ℝ) * d ≤ Γ.max := by
    have hjcast : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
    rw [hjcast] at hj
    nlinarith
  have hh := Γ.integerPrefix_energy_bounds omega hΓ hd ht j hj
  dsimp only at hh ⊢
  rw [Γ.integerPrefix_energy_finite omega hΓ hd ht (j + 1) hj,
    Γ.integerPrefix_energy_finite omega hΓ hd ht j hjold,
    sourceTestCurveClosedRealMassAt_of_le omega Γ hj,
    sourceTestCurveClosedRealMassAt_of_le omega Γ hjold]
  simpa only [EReal.toReal_coe] using hh

/-- The genuine actual analytic increment, summed over the internally
anchored original grid, bounds the SAME defining dyadic energy readback. -/
theorem SourceTestCurve.dyadicEnergy_darboux_bounds (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0)
    {L : ℕ} (hL : 0 < L)
    (hanchor : ∀ r : ℝ, r ≤ -(L : ℝ) → sourceTestCurveAt Γ.toSourceTestCurvePredata r = φ)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
    let f := sourceTestCurveClosedRealMassAt omega Γ
    t * dyadicMassRightSum f L N ≤
      (sourceRelativeEnergy θ φ
        (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal +
        t * (L : ℝ) * V ∧
    (sourceRelativeEnergy θ φ
        (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal +
        t * (L : ℝ) * V ≤ t * dyadicMassLeftSum f L N := by
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  let f := sourceTestCurveClosedRealMassAt omega Γ
  let δ : ℝ := 1 / (2 : ℝ)^N
  let J : ℕ := L * 2^N
  let a : ℤ := -(J : ℤ)
  let e := fun k : ℤ => (sourceRelativeEnergy θ φ
    (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata δ t k) hφ).toReal
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgrid (i : ℕ) : ((a + (i : ℤ) : ℤ) : ℝ) * δ =
      -(L : ℝ) + δ * (i : ℝ) := by
    dsimp [a, J, δ]
    push_cast
    field_simp
  have hstep (i : ℕ) (hi : i < J) :
      t * δ * f (-(L : ℝ) + δ * ((i + 1 : ℕ) : ℝ)) ≤
        e (a + ((i + 1 : ℕ) : ℤ)) - e (a + (i : ℤ)) ∧
      e (a + ((i + 1 : ℕ) : ℤ)) - e (a + (i : ℤ)) ≤
        t * δ * f (-(L : ℝ) + δ * (i : ℝ)) := by
    have hcast : a + (i : ℤ) + 1 = a + ((i + 1 : ℕ) : ℤ) := by omega
    have hjInt : a + (i : ℤ) + 1 ≤ 0 := by dsimp [a]; omega
    have hj : (((a + (i : ℤ) + 1 : ℤ) : ℝ) * δ) ≤ Γ.max := by
      rw [hmax]
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hjInt) hδ.le
    have hh := prefix_energy_readback_step omega Γ hΓ hδ ht (a + (i : ℤ)) hj
    dsimp only at hh
    simpa only [hcast, hgrid, e, f] using hh
  have hlo := Finset.sum_le_sum (s := Finset.range J)
    (fun i hi => (hstep i (Finset.mem_range.mp hi)).1)
  have hup := Finset.sum_le_sum (s := Finset.range J)
    (fun i hi => (hstep i (Finset.mem_range.mp hi)).2)
  have htel : (∑ i ∈ Finset.range J,
      (e (a + ((i + 1 : ℕ) : ℤ)) - e (a + (i : ℤ)))) = e 0 - e a := by
    rw [Finset.sum_range_sub (fun i : ℕ => e (a + (i : ℤ)))]
    have heq : a + (J : ℤ) = 0 := by dsimp [a]; omega
    rw [heq]
    simp only [Nat.cast_zero, add_zero]
  rw [htel] at hlo hup
  have haE : e a = -(t * (L : ℝ)) * V := by
    dsimp [e, a, J, δ, V]
    rw [← neg_mul,
      Γ.integerPrefix_anchor_energy omega hL hanchor ht N, EReal.toReal_coe]
  have hzero : e 0 = (sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal := by
    rw [Γ.toSourceTestCurvePredata.dyadicLegendre_eq_integerPrefix]
  rw [haE, hzero] at hlo hup
  have hslo : (∑ i ∈ Finset.range J,
      t * δ * f (-(L : ℝ) + δ * ((i + 1 : ℕ) : ℝ))) =
      t * dyadicMassRightSum f L N := by
    simp only [dyadicMassRightSum, ← Finset.mul_sum, J, δ]
    ring
  have hsup : (∑ i ∈ Finset.range J,
      t * δ * f (-(L : ℝ) + δ * (i : ℝ))) =
      t * dyadicMassLeftSum f L N := by
    simp only [dyadicMassLeftSum, ← Finset.mul_sum, J, δ]
    ring
  rw [hslo] at hlo
  rw [hsup] at hup
  constructor <;> nlinarith

/-- The normalized bounded instance of the original energy identity,
for the SAME defining source energies, with finiteness produced internally. -/
theorem SourceTestCurve.boundedLegendre_energy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0)
    {t : ℝ} (ht : 0 < t) :
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
        (t : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ.1 ∧
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
        ((t * (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) := by
  obtain ⟨_, L, hL, ha, hTC⟩ := Γ.boundedEnergy_finite omega hΓ hmax
  let V := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  let f := sourceTestCurveClosedRealMassAt omega Γ
  let I := ∫ r in (-(L : ℝ))..0, f r
  let E := (sourceRelativeEnergy θ φ
    (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ).toReal
  have hf : Antitone f := sourceTestCurveClosedRealMassAt_antitone omega Γ
  have hb : ∀ r : ℝ, 0 ≤ f r ∧ f r ≤ V :=
    sourceTestCurveClosedRealMassAt_nonneg_le_model omega hφ Γ hΓ.1
  have hmass := dyadicMassSums_tendsto f hf V hb L
  have hElim := (Γ.dyadicLegendre_realEnergy_tendsto omega hΓ hmax ht).1
  have hmid : Tendsto (fun N : ℕ => (sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal +
      t * (L : ℝ) * V) atTop (𝓝 (E + t * (L : ℝ) * V)) := hElim.add_const _
  have hlo : t * I ≤ E + t * (L : ℝ) * V :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hmass.2) hmid
      (Filter.Eventually.of_forall fun N => (Γ.dyadicEnergy_darboux_bounds omega hΓ hmax hL ha ht N).1)
  have hup : E + t * (L : ℝ) * V ≤ t * I :=
    le_of_tendsto_of_tendsto hmid (tendsto_const_nhds.mul hmass.1)
      (Filter.Eventually.of_forall fun N => (Γ.dyadicEnergy_darboux_bounds omega hΓ hmax hL ha ht N).2)
  have hreal : E = t * (I - (L : ℝ) * V) := by nlinarith
  have hTC' : sourceTestCurveEnergy omega hφ Γ hΓ.1 = ((I - (L : ℝ) * V : ℝ) : EReal) := hTC
  have hfinite := (Γ.dyadicLegendre_energy_finite omega hΓ hmax ht).2
  have hcoe : ((E : ℝ) : EReal) =
      sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ := by
    dsimp [E]
    rw [hfinite, EReal.toReal_coe]
  have hext : sourceRelativeEnergy θ φ
      (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
      ((t * (I - (L : ℝ) * V) : ℝ) : EReal) := by rw [← hcoe, hreal]
  constructor
  · rw [hTC', ← EReal.coe_mul]
    exact hext
  · rw [hTC', EReal.toReal_coe]
    exact hext

/-- EVERY actual nonnegative assigned-ray time, including its unchanged
model initial value, satisfies the normalized bounded energy identity. -/
theorem SourceTestCurve.boundedLegendre_assigned_energy_identity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ) (hmax : Γ.max = 0)
    (t : Ici (0 : ℝ)) :
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
        ((t.1 * (sourceTestCurveEnergy omega hφ Γ hΓ.1).toReal : ℝ) : EReal) ∧
    sourceRelativeEnergy θ φ (sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t) hφ =
        (t.1 : EReal) * sourceTestCurveEnergy omega hφ Γ hΓ.1 := by
  by_cases ht : t.1 = 0
  · have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ.1
    have hzero : sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t = φ := by
      simp [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, ht, hbase]
    rw [hzero, model_energy_zero omega, ht]
    simp
  · have htpos : 0 < t.1 := lt_of_le_of_ne t.2 (Ne.symm ht)
    have hh := Γ.boundedLegendre_energy_identity omega hΓ hmax htpos
    simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial, if_neg ht] using
      And.intro hh.2 hh.1

end SGPT.PSH.VariableComplexAtlas
