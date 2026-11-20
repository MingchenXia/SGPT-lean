import SGPT.PSH.SourceTestCurveDyadicApproximation
import SGPT.PSH.SourceTestCurvePrefixEnergy
import SGPT.Envelopes.SourceRelativeEnergyClosure

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas

open Set Filter Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
  {φ : M → EReal} {hφ : SourceModelPotential θ φ}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- The SAME literal integer-grid supremum at mesh 2^-N, without replacement. -/
theorem SourceTestCurvePredata.dyadicLegendre_eq_integerPrefix
    (Γ : SourceTestCurvePredata θ) (N : ℕ) (t : ℝ) :
    sourceTestCurveDyadicLegendre Γ N t =
      sourceTestCurveIntegerPrefix Γ (1 / (2 : ℝ)^N) t 0 := by
  funext x
  unfold sourceTestCurveDyadicLegendre sourceTestCurveIntegerPrefix
  simp only [div_eq_mul_inv, one_mul, mul_assoc]

/-- Original boundedness internally produces a uniform finite lower barrier
for EVERY actual dyadic approximant, with the original raw upper barrier. -/
theorem SourceTestCurve.dyadicLegendre_uniform_bounds (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ,
      (fun x => φ x + ((-(t * (L : ℝ)) : ℝ) : EReal)) ≤
        sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t ∧
      sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t ≤
        sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t ∧
      sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t ≤ φ := by
  obtain ⟨L, hL, hanchor, _⟩ := Γ.exists_integer_model_anchor omega hφ hΓ hmax
  refine ⟨L, hL, fun N => ⟨?_, ?_, ?_⟩⟩
  · let k : Iic (0 : ℤ) := ⟨-(L : ℤ) * (2 : ℤ)^N, by
      change -(L : ℤ) * (2 : ℤ)^N ≤ 0
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Int.natCast_nonneg L))
        (pow_nonneg (by norm_num) _)⟩
    have hk : (k.1 : ℝ) / (2 : ℝ)^N = -(L : ℝ) := by
      dsimp [k]
      push_cast
      field_simp
    intro x
    have hh := le_iSup (fun k : Iic (0 : ℤ) =>
      sourceTestCurveAt Γ.toSourceTestCurvePredata ((k.1 : ℝ) / (2 : ℝ)^N) x +
        ((t * ((k.1 : ℝ) / (2 : ℝ)^N) : ℝ) : EReal)) k
    rw [hk, hanchor (-(L : ℝ)) le_rfl] at hh
    simpa only [sourceTestCurveDyadicLegendre, mul_neg] using hh
  · intro x
    rw [← Γ.toSourceTestCurvePredata.dyadicLegendre_iSup_eq_raw hmax t ht x]
    exact le_iSup (fun N => sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t x) N
  · have hh := Γ.toSourceTestCurvePredata.rawLegendre_le_limit_add ht.le
    have hbase : sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ := hΓ.1
    rw [hbase] at hh
    simpa only [hmax, mul_zero, EReal.coe_zero, add_zero] using hh

omit [BorelSpace M] in
/-- Genuine PSH comes from the already established actual finite-prefix producer. -/
theorem SourceTestCurve.dyadicLegendre_thetaPSH
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (ofFixedModel n M).IsThetaPSH θ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) := by
  rw [Γ.toSourceTestCurvePredata.dyadicLegendre_eq_integerPrefix]
  exact Γ.integerPrefix_thetaPSH hΓ (by positivity) ht 0 (by simp [hmax])

omit [BorelSpace M] in
/-- The original bounded curve produces genuine minimal type at every dyadic stage. -/
theorem SourceTestCurve.dyadicLegendre_eInfinity
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    SourceRelativeEInfinity θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) := by
  rw [Γ.toSourceTestCurvePredata.dyadicLegendre_eq_integerPrefix]
  exact Γ.integerPrefix_eInfinity hΓ (by positivity) ht 0 (by simp [hmax])

/-- The actual raw Legendre transform has the same relative minimal type,
with its finite comparisons manufactured by the uniform original barriers. -/
theorem SourceTestCurve.rawLegendre_eInfinity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    SourceRelativeEInfinity θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) := by
  obtain ⟨L, _, hbounds⟩ := Γ.dyadicLegendre_uniform_bounds omega hΓ hmax ht
  have h := hbounds 0
  refine ⟨Γ.toSourceTestCurvePredata.rawLegendre_thetaPSH omega ht, ?_⟩
  refine ⟨⟨0, fun x _ => ?_⟩, ⟨t * (L : ℝ), fun x _ => ?_⟩⟩
  · simpa using h.2.2 x
  · have hh := (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot (-(t * (L : ℝ)))))
      (Or.inl (EReal.coe_ne_top (-(t * (L : ℝ)))))).mpr ((h.1 x).trans (h.2.1 x))
    simpa only [sub_eq_add_neg, ← EReal.coe_neg, neg_neg] using hh

/-- Both actual defining extended energies equal their finite real formulas.
This excludes both infinite endpoints before any energy real readback. -/
theorem SourceTestCurve.dyadicLegendre_energy_finite (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    (∀ N : ℕ, sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ =
      (sourceRelativeEnergyOfMinimalType θ φ
        (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t)
        hφ.thetaPSH (Γ.dyadicLegendre_thetaPSH hΓ hmax ht N) : EReal)) ∧
    sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ =
      (sourceRelativeEnergyOfMinimalType θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t)
        hφ.thetaPSH (Γ.rawLegendre_eInfinity omega hΓ hmax ht).1 : EReal) := by
  exact ⟨fun N => sourceRelativeEnergy_eq_of_eInfinity omega
    (Γ.dyadicLegendre_eInfinity hΓ hmax ht N),
    sourceRelativeEnergy_eq_of_eInfinity omega (Γ.rawLegendre_eInfinity omega hΓ hmax ht)⟩

omit [ConnectedSpace M] in
private theorem actualFiniteEnergy_of_minimal (omega : KahlerBackground n M)
    {u : M → EReal} (hu : SourceRelativeEInfinity θ φ u) :
    SourceRelativeFiniteEnergy θ φ u hφ := by
  apply (sourceRelativeFiniteEnergy_iff_native θ φ u hφ).mpr
  exact RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
    ((sourceRelativeEInfinity_iff_native θ φ u).mp hu)

private theorem actualDyadicEnergy_continuity (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ)) ∧
    Tendsto (fun N : ℕ => (sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal) atTop
      (𝓝 (sourceRelativeEnergy θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ).toReal) := by
  apply sourceRelativeFiniteEnergy_increasing_ae_net omega
    (fun N => actualFiniteEnergy_of_minimal omega (Γ.dyadicLegendre_eInfinity hΓ hmax ht N))
    (actualFiniteEnergy_of_minimal omega (Γ.rawLegendre_eInfinity omega hΓ hmax ht))
    (fun x N P hNP => Γ.toSourceTestCurvePredata.dyadicLegendre_monotone t hNP x)
  exact Filter.Eventually.of_forall (Γ.toSourceTestCurvePredata.dyadicLegendre_tendsto hmax t ht)

/-- Existing arbitrary-model monotone continuity for the SAME defining
extended energies of the actual original dyadic approximants. -/
theorem SourceTestCurve.dyadicLegendre_energy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ) atTop
      (𝓝 (sourceRelativeEnergy θ φ (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ)) :=
  (actualDyadicEnergy_continuity omega Γ hΓ hmax ht).1

/-- BOTH actual energy readback and actual finite-formula convergence,
using finite identities only after their genuine memberships are produced. -/
theorem SourceTestCurve.dyadicLegendre_realEnergy_tendsto (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (hΓ : Γ ∈ SourceBoundedTestCurves θ φ hφ)
    (hmax : Γ.max = 0) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => (sourceRelativeEnergy θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t) hφ).toReal) atTop
      (𝓝 (sourceRelativeEnergy θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t) hφ).toReal) ∧
    Tendsto (fun N : ℕ => sourceRelativeEnergyOfMinimalType θ φ
      (sourceTestCurveDyadicLegendre Γ.toSourceTestCurvePredata N t)
      hφ.thetaPSH (Γ.dyadicLegendre_thetaPSH hΓ hmax ht N)) atTop
      (𝓝 (sourceRelativeEnergyOfMinimalType θ φ
        (sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t)
        hφ.thetaPSH (Γ.rawLegendre_eInfinity omega hΓ hmax ht).1)) := by
  have he := (actualDyadicEnergy_continuity omega Γ hΓ hmax ht).2
  refine ⟨he, ?_⟩
  have hf := Γ.dyadicLegendre_energy_finite omega hΓ hmax ht
  simpa only [hf.1, hf.2, EReal.toReal_coe] using he

end SGPT.PSH.VariableComplexAtlas
