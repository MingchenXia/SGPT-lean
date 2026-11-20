import SGPT.PSH.SourceTestCurvePrefixWinning
import SGPT.PSH.SourceTestCurvePrefixLocality
import SGPT.PSH.SourceTestCurvePrefixDifference
import SGPT.PSH.SourceTestCurveDyadicApproximation

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

omit [ConnectedSpace M] in
private theorem translated_measure {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) (c : ℝ)
    (hc : (ofFixedModel n M).IsThetaPSH θ (fun x ↦ u x + (c : EReal))) :
    sourcePotentialNonPluripolarMeasure θ (fun x ↦ u x + (c : EReal)) hc =
      sourcePotentialNonPluripolarMeasure θ u hu :=
  DiagonalMeasureRegularity.diagonalPotentialMeasure_add_const
    (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu) c
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hc)

/-- On the actual strict winning set the new prefix has exactly the
actual adjacent-slice measure, including the genuine cutoff slice. -/
theorem SourceTestCurve.prefixWinning_measure_new {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (((j + 1 : ℤ) : ℝ) * d) ≤ Γ.max) :
    (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1))
      (Γ.integerPrefix_thetaPSH hΓ hd ht (j + 1) hj)).restrict
        {x | sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x <
          sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x} =
    (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveAt Γ.toSourceTestCurvePredata (((j + 1 : ℤ) : ℝ) * d))
      (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hj)).restrict
        {x | sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x <
          sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x} := by
  let P := Γ.toSourceTestCurvePredata
  let G := sourceTestCurveIntegerPrefix P d t
  let f := fun x ↦ sourceTestCurveAt P (((j + 1 : ℤ) : ℝ) * d) x +
    ((t * ((j + 1 : ℤ) : ℝ) * d : ℝ) : EReal)
  have hjold : (j : ℝ) * d ≤ Γ.max := by
    have heq : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
    rw [heq] at hj
    nlinarith
  have hγ := P.at_thetaPSH_of_le hj
  have hf : (ofFixedModel n M).IsThetaPSH θ f :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (((isThetaPSH_iff_nativeThetaPotential θ _).mp hγ).add_const _)
  have hg := Γ.integerPrefix_thetaPSH hΓ hd ht j hjold
  have hm := sourceThetaMaximum_genuine hf hg
  have heq : (fun x ↦ max (f x) (G j x)) = G (j + 1) := by
    funext x
    rw [show G (j + 1) x = max (G j x) (f x) from congrFun (P.integerPrefix_succ d t j) x]
    exact max_comm _ _
  have hA : {x | G j x < G (j + 1) x} ⊆ {x | G j x < f x} := by
    intro x hx
    change G j x < G (j + 1) x at hx
    rw [show G (j + 1) x = max (G j x) (f x) from congrFun (P.integerPrefix_succ d t j) x] at hx
    exact (lt_max_iff.mp hx).resolve_left (lt_irrefl _)
  have hloc := sourceDiagonalMeasure_restrict_max_eq_on hf hg hm hA
  have hshift := translated_measure hγ (t * ((j + 1 : ℤ) : ℝ) * d) hf
  rw [hshift] at hloc
  have heq' : (fun x ↦ max (f x)
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x)) =
      sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) := heq
  simpa only [heq'] using hloc

/-- The actual old prefix restricts to the actual old slice measure on
its strict winning region, using the genuinely strict previous prefix. -/
theorem SourceTestCurve.prefixWinning_measure_old {φ : M → EReal}
    {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (j : ℝ) * d ≤ Γ.max) :
    (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j)
      (Γ.integerPrefix_thetaPSH hΓ hd ht j hj)).restrict
        {x | sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x <
          sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x} =
    (sourcePotentialNonPluripolarMeasure θ
      (sourceTestCurveAt Γ.toSourceTestCurvePredata ((j : ℝ) * d))
      (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hj)).restrict
        {x | sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x <
          sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x} := by
  let P := Γ.toSourceTestCurvePredata
  let G := sourceTestCurveIntegerPrefix P d t
  let f := fun x ↦ sourceTestCurveAt P ((j : ℝ) * d) x +
    ((t * (j : ℝ) * d : ℝ) : EReal)
  have hjprev : ((j - 1 : ℤ) : ℝ) * d ≤ Γ.max := by
    have heq : ((j - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; rfl
    rw [heq]
    nlinarith
  have hγ := P.at_thetaPSH_of_le hj
  have hf : (ofFixedModel n M).IsThetaPSH θ f :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (((isThetaPSH_iff_nativeThetaPotential θ _).mp hγ).add_const _)
  have hg := Γ.integerPrefix_thetaPSH hΓ hd ht (j - 1) hjprev
  have hm := sourceThetaMaximum_genuine hf hg
  have heq : (fun x ↦ max (f x) (G (j - 1) x)) = G j := by
    funext x
    have hs := congrFun (P.integerPrefix_succ d t (j - 1)) x
    have hjj : j - 1 + 1 = j := by omega
    simp only [hjj] at hs
    exact (max_comm _ _).trans hs.symm
  have hA : {x | G j x < G (j + 1) x} ⊆ {x | G (j - 1) x < f x} := by
    intro x hx
    exact Γ.prefixWinning_strict_previous hΓ hd ht j x hx
  have hloc := sourceDiagonalMeasure_restrict_max_eq_on hf hg hm hA
  have hshift := translated_measure hγ (t * (j : ℝ) * d) hf
  rw [hshift] at hloc
  have heq' : (fun x ↦ max (f x)
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j - 1) x)) =
      sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j := heq
  simpa only [heq'] using hloc

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem prefix_eq_coe_at_zero_contact (P : SourceTestCurvePredata θ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ) (x : M)
    (hz : sourceTestCurveAt P ((j : ℝ) * d) x = 0) :
    sourceTestCurveIntegerPrefix P d t j x = ((t * (j : ℝ) * d : ℝ) : EReal) := by
  have hs (k : ℤ) (hk : k ≤ j) : sourceTestCurveAt P ((k : ℝ) * d) x = 0 := by
    apply le_antisymm (P.at_le_zero _ x)
    change (0 : EReal) ≤ _
    rw [← hz]
    exact P.at_antitone x (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hd.le)
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [hs k.1 k.2, zero_add]
    apply EReal.coe_le_coe
    have hk : (k.1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show k.1 ≤ j from k.2)
    nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg ht.le hd.le)]
  · have h := le_iSup (fun k : Iic j ↦ sourceTestCurveAt P ((k.1 : ℝ) * d) x +
      ((t * (k.1 : ℝ) * d : ℝ) : EReal)) ⟨j, by change j ≤ j; exact le_rfl⟩
    simpa only [hz, zero_add, sourceTestCurveIntegerPrefix] using h

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- At the actual new zero-contact points the gain is exactly td and the
point belongs to the actual strict winning region. -/
theorem SourceTestCurvePredata.prefixWinning_contact_gain
    (P : SourceTestCurvePredata θ) {d t : ℝ} (hd : 0 < d) (ht : 0 < t)
    (j : ℤ) (x : M)
    (hz : sourceTestCurveAt P (((j + 1 : ℤ) : ℝ) * d) x = 0) :
    sourceTestCurveIntegerPrefix P d t j x < sourceTestCurveIntegerPrefix P d t (j + 1) x ∧
    canonicalERealDiffToReal (sourceTestCurveIntegerPrefix P d t (j + 1) x)
      (sourceTestCurveIntegerPrefix P d t j x) = t * d := by
  have hzero : sourceTestCurveAt P ((j : ℝ) * d) x = 0 := by
    apply le_antisymm (P.at_le_zero _ x)
    change (0 : EReal) ≤ _
    rw [← hz]
    apply P.at_antitone x
    have hj : (j : ℝ) ≤ ((j + 1 : ℤ) : ℝ) := by exact_mod_cast (show j ≤ j + 1 by omega)
    exact mul_le_mul_of_nonneg_right hj hd.le
  rw [prefix_eq_coe_at_zero_contact P hd ht j x hzero,
    prefix_eq_coe_at_zero_contact P hd ht (j + 1) x hz]
  constructor
  · apply EReal.coe_lt_coe
    push_cast
    nlinarith [mul_pos ht hd]
  · rw [canonicalERealDiffToReal_coe_coe]
    push_cast
    ring

omit [MeasurableSpace M] [BorelSpace M] in
private theorem at_fixedPoint_of_le (P : SourceTestCurvePredata θ)
    {τ : ℝ} (hτ : τ ≤ P.max) :
    sourceSingularityEnvelope θ (sourceTestCurveAt P τ) = sourceTestCurveAt P τ := by
  rcases hτ.eq_or_lt with heq | hlt
  · rw [heq, sourceTestCurveAt_eq_max]
    exact P.cutoff_fixedPoint
  · rw [sourceTestCurveAt_of_lt P hlt]
    exact P.fixedPoint ⟨τ, hlt⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem prefix_difference_zero_off_winning (P : SourceTestCurvePredata θ)
    {d : ℝ} (hd : 0 < d) (t : ℝ) (j : ℤ) (x : M)
    (hx : ¬ sourceTestCurveIntegerPrefix P d t j x <
      sourceTestCurveIntegerPrefix P d t (j + 1) x) :
    canonicalERealDiffToReal (sourceTestCurveIntegerPrefix P d t (j + 1) x)
      (sourceTestCurveIntegerPrefix P d t j x) = 0 := by
  have heq := le_antisymm (le_of_not_gt hx) ((P.integerPrefix_bounds hd t j).1 x)
  rw [heq, canonicalERealDiffToReal_self]

/-- The lower endpoint integral is EXACTLY td times the ACTUAL adjacent
slice mass, including a zero-mass genuine cutoff. -/
theorem SourceTestCurve.prefixWinning_integral_new (omega : KahlerBackground n M)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (((j + 1 : ℤ) : ℝ) * d) ≤ Γ.max) :
    (∫ x, canonicalERealDiffToReal
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x)
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x)
      ∂sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1))
        (Γ.integerPrefix_thetaPSH hΓ hd ht (j + 1) hj)) =
      t * d * (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveAt Γ.toSourceTestCurvePredata (((j + 1 : ℤ) : ℝ) * d))
        (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hj) univ).toReal := by
  let P := Γ.toSourceTestCurvePredata
  let G := sourceTestCurveIntegerPrefix P d t
  let D := fun x ↦ canonicalERealDiffToReal (G (j + 1) x) (G j x)
  let A := {x | G j x < G (j + 1) x}
  let γ := sourceTestCurveAt P (((j + 1 : ℤ) : ℝ) * d)
  have hγ := P.at_thetaPSH_of_le hj
  let μ := sourcePotentialNonPluripolarMeasure θ γ hγ
  have hzero : ∀ x, x ∉ A → D x = 0 := fun x hx ↦
    prefix_difference_zero_off_winning P hd t j x hx
  have hcontact : ∀ᵐ x ∂μ, γ x = 0 := by
    rw [ae_iff]
    exact sourceOrdinaryFixedPoint_contact_zero omega hγ (at_fixedPoint_of_le P hj)
  have hgain : ∀ᵐ x ∂μ, D x = t * d := hcontact.mono fun x hx ↦
    (P.prefixWinning_contact_gain hd ht j x hx).2
  have hloc := Γ.prefixWinning_measure_new hΓ hd ht j hj
  calc
    _ = ∫ x in A, D x ∂sourcePotentialNonPluripolarMeasure θ (G (j + 1))
        (Γ.integerPrefix_thetaPSH hΓ hd ht (j + 1) hj) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in A, D x ∂μ := by rw [hloc]
    _ = ∫ x, D x ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = ∫ _ : M, t * d ∂μ := integral_congr_ae hgain
    _ = t * d * (μ univ).toReal := by
      rw [integral_const]
      simp only [measureReal_def, smul_eq_mul, mul_comm]

/-- The upper endpoint integral is bounded by td times the ACTUAL old
slice mass; integrability is produced from genuine relative minimal type. -/
theorem SourceTestCurve.prefixWinning_integral_old_le (omega : KahlerBackground n M)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (((j + 1 : ℤ) : ℝ) * d) ≤ Γ.max) :
    let hjold : (j : ℝ) * d ≤ Γ.max := by
      have hh : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
      rw [hh] at hj
      nlinarith
    (∫ x, canonicalERealDiffToReal
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1) x)
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j x)
      ∂sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j)
        (Γ.integerPrefix_thetaPSH hΓ hd ht j hjold)) ≤
      t * d * (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveAt Γ.toSourceTestCurvePredata ((j : ℝ) * d))
        (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hjold) univ).toReal := by
  dsimp only
  let P := Γ.toSourceTestCurvePredata
  let G := sourceTestCurveIntegerPrefix P d t
  let D := fun x ↦ canonicalERealDiffToReal (G (j + 1) x) (G j x)
  let A := {x | G j x < G (j + 1) x}
  have hjold : (j : ℝ) * d ≤ Γ.max := by
    have hh : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
    rw [hh] at hj
    nlinarith
  let γ := sourceTestCurveAt P ((j : ℝ) * d)
  have hγ := P.at_thetaPSH_of_le hjold
  let μ := sourcePotentialNonPluripolarMeasure θ γ hγ
  let : IsFiniteMeasure μ := DiagonalMeasureRegularity.isFiniteMeasure_diagonalPotentialMeasure
    omega (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ _).mp hγ)
  have hu := Γ.integerPrefix_eInfinity hΓ hd ht (j + 1) hj
  have hv := Γ.integerPrefix_eInfinity hΓ hd ht j hjold
  have htype : SameSingularityTypeOn (G (j + 1)) (G j) univ :=
    SameSingularityTypeOn.trans hu.2 (SameSingularityTypeOn.symm hv.2)
  have hint : Integrable D μ :=
    RelativeEnergyIntegrability.integrable_canonicalDiff_globalMixedMeasure omega
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu.1).1
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp hv.1).1 htype
      (fun _ : Fin n ↦ ((isThetaPSH_iff_nativeThetaPotential θ _).mp hγ).1)
  have hzero : ∀ x, x ∉ A → D x = 0 := fun x hx ↦
    prefix_difference_zero_off_winning P hd t j x hx
  have hloc := Γ.prefixWinning_measure_old hΓ hd ht j hjold
  calc
    _ = ∫ x in A, D x ∂sourcePotentialNonPluripolarMeasure θ (G j)
        (Γ.integerPrefix_thetaPSH hΓ hd ht j hjold) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in A, D x ∂μ := by rw [hloc]
    _ = ∫ x, D x ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ ≤ ∫ _ : M, t * d ∂μ := integral_mono hint (integrable_const _)
      (fun x ↦ (P.integerPrefix_canonicalDifference_bounds hd ht j x).2)
    _ = t * d * (μ univ).toReal := by
      rw [integral_const]
      simp only [measureReal_def, smul_eq_mul, mul_comm]

/-- The WHOLE original adjacent-prefix energy estimate, for every
positive real mesh and time and every genuine adjacent slice through the
actual cutoff. All PSH, same-type, locality, contact and integrability
outputs are manufactured from the original bounded test curve. -/
theorem SourceTestCurve.integerPrefix_energy_bounds (omega : KahlerBackground n M)
    {φ : M → EReal} {hφ : SourceModelPotential θ φ} (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (j : ℤ)
    (hj : (((j + 1 : ℤ) : ℝ) * d) ≤ Γ.max) :
    let hjold : (j : ℝ) * d ≤ Γ.max := by
      have hh : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
      rw [hh] at hj
      nlinarith
    let enew := sourceRelativeEnergyOfMinimalType θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t (j + 1)) hφ.thetaPSH
      (Γ.integerPrefix_thetaPSH hΓ hd ht (j + 1) hj)
    let eold := sourceRelativeEnergyOfMinimalType θ φ
      (sourceTestCurveIntegerPrefix Γ.toSourceTestCurvePredata d t j) hφ.thetaPSH
      (Γ.integerPrefix_thetaPSH hΓ hd ht j hjold)
    t * d * (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveAt Γ.toSourceTestCurvePredata (((j + 1 : ℤ) : ℝ) * d))
        (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hj) univ).toReal ≤ enew - eold ∧
      enew - eold ≤ t * d * (sourcePotentialNonPluripolarMeasure θ
        (sourceTestCurveAt Γ.toSourceTestCurvePredata ((j : ℝ) * d))
        (Γ.toSourceTestCurvePredata.at_thetaPSH_of_le hjold) univ).toReal := by
  dsimp only
  have hjold : (j : ℝ) * d ≤ Γ.max := by
    have hh : ((j + 1 : ℤ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
    rw [hh] at hj
    nlinarith
  have he := sourceRelativeEnergy_endpoint_bounds omega hφ
    (Γ.integerPrefix_eInfinity hΓ hd ht (j + 1) hj)
    (Γ.integerPrefix_eInfinity hΓ hd ht j hjold)
  constructor
  · have h := he.1
    rw [Γ.prefixWinning_integral_new omega hΓ hd ht j hj] at h
    exact h
  · exact he.2.trans (Γ.prefixWinning_integral_old_le omega hΓ hd ht j hj)

end SGPT.PSH.VariableComplexAtlas
