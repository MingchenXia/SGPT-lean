import SGPT.PSH.SourceTestCurveEnergy
import SGPT.PSH.SourceTestCurveLegendrePSH
import Mathlib.MeasureTheory.Group.LIntegral

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The ORIGINAL family at the translated genuine open parameter, with
cutoff m-a and no quotient, representative or output analytic certificate. -/
def SourceTestCurvePredata.shift (Γ : SourceTestCurvePredata θ) (a : ℝ) :
    SourceTestCurvePredata θ where
  max := Γ.max - a
  potential := fun τ ↦ Γ.potential ⟨τ.1 + a, by change τ.1 + a < Γ.max; have ht : τ.1 < Γ.max - a := τ.2; linarith⟩
  thetaPSH := fun τ ↦ Γ.thetaPSH _
  antitone := by
    intro x r s hrs
    apply Γ.antitone x
    change r.1 + a ≤ s.1 + a
    linarith [show r.1 ≤ s.1 from hrs]
  concave := by
    intro x
    let T : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
      { toFun := fun p ↦ (p.1 + a, p.2)
        linear := LinearMap.id
        map_vadd' := by intro p v; ext <;> simp [add_assoc] }
    have hc := Convex.affine_preimage T (Γ.concave x)
    change Convex ℝ (SGPT.Convex.epigraph _)
    have hset : SGPT.Convex.epigraph (sourceTestCurveNegativeTrace (Γ.max - a)
        (fun τ : Iio (Γ.max - a) ↦ Γ.potential ⟨τ.1 + a, by
          change τ.1 + a < Γ.max; have ht : τ.1 < Γ.max - a := τ.2; linarith⟩) x) =
        T ⁻¹' SGPT.Convex.epigraph (sourceTestCurveNegativeTrace Γ.max Γ.potential x) := by
      ext p
      have hiff : p.1 < Γ.max - a ↔ p.1 + a < Γ.max := by constructor <;> intro hp <;> linarith
      by_cases hp : p.1 < Γ.max - a
      · simp [SGPT.Convex.epigraph, T, sourceTestCurveNegativeTrace, hp, hiff.mp hp]
      · simp [SGPT.Convex.epigraph, T, sourceTestCurveNegativeTrace, hp,
          (not_congr hiff).mp hp]
    rw [hset]
    exact hc
  fixedPoint := fun τ ↦ Γ.fixedPoint _

/-- The ACTUAL translated real cutoff. -/
theorem SourceTestCurvePredata.shift_max (Γ : SourceTestCurvePredata θ) (a : ℝ) :
    (Γ.shift a).max = Γ.max - a := rfl

/-- The LITERAL original translated potential at every original parameter. -/
theorem SourceTestCurvePredata.shift_potential (Γ : SourceTestCurvePredata θ) (a : ℝ)
    (τ : Iio (Γ.max - a)) :
    (Γ.shift a).potential τ =
      Γ.potential ⟨τ.1 + a, by change τ.1 + a < Γ.max; have ht : τ.1 < Γ.max - a := τ.2; linarith⟩ := rfl

/-- The exact open-interval translation bijection preserves the ACTUAL
pointwise supremum, hence the SAME spatial usc-regularized limit. -/
theorem SourceTestCurvePredata.shift_limit (Γ : SourceTestCurvePredata θ) (a : ℝ) :
    sourceTestCurveLimit (Γ.shift a) = sourceTestCurveLimit Γ := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro τ
    exact le_iSup (fun σ : Iio Γ.max ↦ Γ.potential σ x)
      ⟨τ.1 + a, by change τ.1 + a < Γ.max; have ht : τ.1 < Γ.max - a := τ.2; linarith⟩
  · apply iSup_le
    intro σ
    let τ : Iio (Γ.max - a) := ⟨σ.1 - a, by change σ.1 - a < Γ.max - a; have hs : σ.1 < Γ.max := σ.2; linarith⟩
    have heq : τ.1 + a = σ.1 := by dsimp [τ]; ring
    simpa only [SourceTestCurvePredata.shift, heq] using
      (le_iSup (fun q : Iio (Γ.max - a) ↦ (Γ.shift a).potential q x) τ)


/-- Literal raw Legendre translation at EVERY real time. Only finite
coefficient arithmetic and the existing arbitrary-supremum order isomorphism
are used; every original EReal pole is retained. -/
theorem SourceTestCurvePredata.shift_rawLegendre (Γ : SourceTestCurvePredata θ)
    (a t : ℝ) : sourceTestCurveRawLegendre (Γ.shift a) t =
      fun x ↦ sourceTestCurveRawLegendre Γ t x - ((t * a : ℝ) : EReal) := by
  funext x
  rw [(Γ.shift a).rawLegendre_eq_iSup_open, Γ.rawLegendre_eq_iSup_open,
    sub_eq_add_neg, ← EReal.coe_neg, ← SGPT.Foundations.Analysis.FirstPass.iSup_add_coe]
  have hterm (r : ℝ) (u : EReal) : ((t * r : ℝ) : EReal) + u =
      (((t * (r + a) : ℝ) : EReal) + u) + ((-(t * a) : ℝ) : EReal) := by
    calc
      _ = u + ((t * r : ℝ) : EReal) := add_comm _ _
      _ = u + ((t * (r + a) - t * a : ℝ) : EReal) := by congr 2; ring
      _ = _ := by rw [EReal.coe_sub, sub_eq_add_neg, ← EReal.coe_neg]; ac_rfl
  apply le_antisymm
  · apply iSup_le
    intro τ
    change ((t * τ.1 : ℝ) : EReal) + Γ.potential _ x ≤ _
    rw [hterm]
    exact le_iSup (fun σ : Iio Γ.max ↦
      (((t * σ.1 : ℝ) : EReal) + Γ.potential σ x) + ((-(t * a) : ℝ) : EReal))
      ⟨τ.1 + a, by change τ.1 + a < Γ.max; have ht : τ.1 < Γ.max - a := τ.2; linarith⟩
  · apply iSup_le
    intro σ
    let τ : Iio (Γ.max - a) := ⟨σ.1 - a, by
      change σ.1 - a < Γ.max - a; have hs : σ.1 < Γ.max := σ.2; linarith⟩
    have heq : τ.1 + a = σ.1 := by dsimp [τ]; ring
    have hh := le_iSup (fun q : Iio (Γ.max - a) ↦
      ((t * q.1 : ℝ) : EReal) + (Γ.shift a).potential q x) τ
    change ((t * τ.1 : ℝ) : EReal) + Γ.potential _ x ≤ _ at hh
    rw [hterm] at hh
    simpa only [SourceTestCurvePredata.shift, heq] using hh

/-- The SAME assigned ray translation at EVERY nonnegative time. The
zero case uses equality of ACTUAL limits, independently of raw time zero. -/
theorem SourceTestCurvePredata.shift_legendreRay (Γ : SourceTestCurvePredata θ)
    (a : ℝ) (t : Ici (0 : ℝ)) :
    sourceTestCurveLegendreRay (Γ.shift a) t =
      fun x ↦ sourceTestCurveLegendreRay Γ t x - ((t.1 * a : ℝ) : EReal) := by
  by_cases ht : t.1 = 0
  · simp only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      ht, if_true, Γ.shift_limit a, zero_mul, EReal.coe_zero, sub_zero]
  · simpa only [sourceTestCurveLegendreRay, sourceTestCurveLegendreWithInitial,
      if_neg ht] using Γ.shift_rawLegendre a t.1


private theorem shift_eventually_model_iff (Γ : SourceTestCurvePredata θ) (a : ℝ)
    (φ : M → EReal) :
    (∀ᶠ τ : Iio (Γ.shift a).max in atBot, (Γ.shift a).potential τ = φ) ↔
      ∀ᶠ τ : Iio Γ.max in atBot, Γ.potential τ = φ := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := eventually_atBot.mp h
    let σ : Iio Γ.max := ⟨r.1 + a, by
      change r.1 + a < Γ.max; have ht : r.1 < Γ.max - a := r.2; linarith⟩
    apply eventually_atBot.mpr
    refine ⟨σ, ?_⟩
    intro q hq
    let τ : Iio (Γ.shift a).max := ⟨q.1 - a, by
      change q.1 - a < Γ.max - a; have ht : q.1 < Γ.max := q.2; linarith⟩
    have hτ : τ ≤ r := by
      change q.1 - a ≤ r.1
      have hreal : q.1 ≤ r.1 + a := hq
      linarith
    have heq := hr τ hτ
    have ht : τ.1 + a = q.1 := by dsimp [τ]; ring
    simpa only [SourceTestCurvePredata.shift, ht] using heq
  · intro h
    obtain ⟨r, hr⟩ := eventually_atBot.mp h
    let σ : Iio (Γ.shift a).max := ⟨r.1 - a, by
      change r.1 - a < Γ.max - a; have ht : r.1 < Γ.max := r.2; linarith⟩
    apply eventually_atBot.mpr
    refine ⟨σ, ?_⟩
    intro q hq
    let τ : Iio Γ.max := ⟨q.1 + a, by
      change q.1 + a < Γ.max; have ht : q.1 < Γ.max - a := q.2; linarith⟩
    apply hr τ
    change q.1 + a ≤ r.1
    have hreal : q.1 ≤ r.1 - a := hq
    linarith

variable [MeasurableSpace M] [CompactSpace M]

private theorem shift_same_measure {u v : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u)
    (hv : (ofFixedModel n M).IsThetaPSH θ v) (heq : u = v) :
    sourcePotentialNonPluripolarMeasure θ u hu = sourcePotentialNonPluripolarMeasure θ v hv := by
  cases heq
  rfl

/-- The same ACTUAL positive mass supplies the genuine translated original
test curve, after equality of its ACTUAL source limit has been proved. -/
def SourceTestCurve.shift (Γ : SourceTestCurve θ) (a : ℝ) : SourceTestCurve θ where
  toSourceTestCurvePredata := Γ.toSourceTestCurvePredata.shift a
  positiveLimitMass := by
    have hm := shift_same_measure (Γ.toSourceTestCurvePredata.shift a).limit_thetaPSH
      Γ.toSourceTestCurvePredata.limit_thetaPSH (Γ.toSourceTestCurvePredata.shift_limit a)
    rw [hm]
    exact Γ.positiveLimitMass

/-- The actual translated original test curve has the SAME literal limit. -/
theorem SourceTestCurve.shift_limit (Γ : SourceTestCurve θ) (a : ℝ) :
    sourceTestCurveLimit (Γ.shift a).toSourceTestCurvePredata =
      sourceTestCurveLimit Γ.toSourceTestCurvePredata := Γ.toSourceTestCurvePredata.shift_limit a

/-- Original based membership is equivalent by equality of ACTUAL limits. -/
theorem SourceTestCurve.shift_based_iff {φ : M → EReal} (hφ : SourceModelPotential θ φ)
    (Γ : SourceTestCurve θ) (a : ℝ) :
    Γ.shift a ∈ SourceTestCurvesBased θ φ hφ ↔ Γ ∈ SourceTestCurvesBased θ φ hφ := by
  change sourceTestCurveLimit (Γ.shift a).toSourceTestCurvePredata = φ ↔
    sourceTestCurveLimit Γ.toSourceTestCurvePredata = φ
  rw [Γ.shift_limit a]


/-- SAME actual mass at the translated parameter, including BOTH dummy
outside-domain zero branches, with no replacement by a cutoff mass. -/
theorem SourceTestCurve.shift_realMassAt (omega : KahlerBackground n M)
    (Γ : SourceTestCurve θ) (a τ : ℝ) :
    sourceTestCurveRealMassAt omega (Γ.shift a) τ = sourceTestCurveRealMassAt omega Γ (τ + a) := by
  by_cases ht : τ < Γ.max - a
  · have ht' : τ + a < Γ.max := by linarith
    rw [sourceTestCurveRealMassAt_of_lt omega (Γ.shift a) ht,
      sourceTestCurveRealMassAt_of_lt omega Γ ht']
    rfl
  · have ht' : ¬ τ + a < Γ.max := by linarith
    simp only [sourceTestCurveRealMassAt,
      dif_neg (show ¬ τ < (Γ.shift a).max from ht), dif_neg ht']

/-- GENUINE Lebesgue translation of the ACTUAL nonnegative deficit on
its original infinite interval. No integrability/finite-measure premise;
the equality retains a possibly infinite ENNReal integral. -/
theorem SourceTestCurve.shift_deficitIntegral (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) (a : ℝ) :
    (∫⁻ τ : ℝ in Iio (Γ.shift a).max, ENNReal.ofReal
      ((sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal -
        sourceTestCurveRealMassAt omega (Γ.shift a) τ)) =
      ∫⁻ τ : ℝ in Iio Γ.max, ENNReal.ofReal
        ((sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal -
          sourceTestCurveRealMassAt omega Γ τ) := by
  let f : ℝ → ENNReal := fun τ ↦ ENNReal.ofReal
    ((sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal -
      sourceTestCurveRealMassAt omega Γ τ)
  have htrans := (measurePreserving_add_right (volume : Measure ℝ) a).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding f (Iio Γ.max)
  have hpre : (fun τ : ℝ ↦ τ + a) ⁻¹' Iio Γ.max = Iio (Γ.max - a) := by
    ext τ
    change τ + a < Γ.max ↔ τ < Γ.max - a
    constructor <;> intro ht <;> linarith
  rw [hpre] at htrans
  change (∫⁻ τ : ℝ in Iio (Γ.max - a), ENNReal.ofReal
    ((sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal -
      sourceTestCurveRealMassAt omega (Γ.shift a) τ)) = _
  calc
    _ = ∫⁻ τ : ℝ in Iio (Γ.max - a), f (τ + a) := by
      apply lintegral_congr
      intro τ
      rw [Γ.shift_realMassAt omega a τ]
    _ = _ := htrans

/-- The genuine ACTUAL extended test-curve energy translates by the finite
model-mass coefficient, INCLUDING its possible negative-infinite branch.
No finite-energy or bounded-model premise occurs. -/
theorem SourceTestCurve.shift_energy (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) (a : ℝ) :
    sourceTestCurveEnergy omega hφ (Γ.shift a) ((Γ.shift_based_iff hφ a).mpr hΓ) =
      sourceTestCurveEnergy omega hφ Γ hΓ -
        ((a * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) := by
  unfold sourceTestCurveEnergy
  rw [Γ.shift_deficitIntegral omega hφ a]
  let V : ℝ := (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal
  have hc : (((Γ.max - a) * V : ℝ) : EReal) =
      ((Γ.max * V : ℝ) : EReal) + ((-(a * V) : ℝ) : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  change (((Γ.max - a) * V : ℝ) : EReal) - _ = _
  rw [hc]
  simp only [sub_eq_add_neg, ← EReal.coe_neg]
  ac_rfl

/-- Exact ORIGINAL atBot eventual function equality and based membership
are equivalent under either real parameter translation. -/
theorem SourceTestCurve.shift_bounded_iff {φ : M → EReal} (hφ : SourceModelPotential θ φ)
    (Γ : SourceTestCurve θ) (a : ℝ) :
    Γ.shift a ∈ SourceBoundedTestCurves θ φ hφ ↔ Γ ∈ SourceBoundedTestCurves θ φ hφ := by
  change (Γ.shift a ∈ SourceTestCurvesBased θ φ hφ ∧
    (∀ᶠ τ : Iio (Γ.shift a).max in atBot, (Γ.shift a).potential τ = φ)) ↔
      (Γ ∈ SourceTestCurvesBased θ φ hφ ∧
        (∀ᶠ τ : Iio Γ.max in atBot, Γ.potential τ = φ))
  rw [Γ.shift_based_iff hφ a]
  exact and_congr_right fun _ ↦ shift_eventually_model_iff Γ.toSourceTestCurvePredata a φ

/-- The ACTUAL original extended finite-energy class is unchanged by a
finite parameter shift. Its possible bottom energy is retained until the
strict-bottom membership comparison itself excludes it. -/
theorem SourceTestCurve.shift_finiteEnergy_iff (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ) (a : ℝ) :
    Γ.shift a ∈ SourceFiniteEnergyTestCurves omega θ φ hφ ↔
      Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ := by
  constructor
  · rintro ⟨hb, hpos⟩
    have hb0 := (Γ.shift_based_iff hφ a).mp hb
    refine ⟨hb0, ?_⟩
    have hE := Γ.shift_energy omega hφ hb0 a
    rw [hE, sub_eq_add_neg, ← EReal.coe_neg, EReal.bot_lt_add_iff] at hpos
    exact hpos.1
  · rintro ⟨hb, hpos⟩
    refine ⟨(Γ.shift_based_iff hφ a).mpr hb, ?_⟩
    rw [Γ.shift_energy omega hφ hb a, sub_eq_add_neg, ← EReal.coe_neg, EReal.bot_lt_add_iff]
    exact ⟨hpos, EReal.bot_lt_coe _⟩

/-- The genuine original zero-cutoff normalization needed in Step 3.1:
SAME based model, actual limits/classes, literal Legendre rays, and ACTUAL
extended TC energy including negative infinity. No radial-energy claim. -/
theorem source_test_curve_zero_cutoff_normalization (omega : KahlerBackground n M)
    {φ : M → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    (Γ.shift Γ.max).max = 0 ∧
    Γ.shift Γ.max ∈ SourceTestCurvesBased θ φ hφ ∧
    sourceTestCurveLimit (Γ.shift Γ.max).toSourceTestCurvePredata = φ ∧
    (∀ t : ℝ, sourceTestCurveRawLegendre (Γ.shift Γ.max).toSourceTestCurvePredata t =
      fun x ↦ sourceTestCurveRawLegendre Γ.toSourceTestCurvePredata t x - ((t * Γ.max : ℝ) : EReal)) ∧
    (∀ t : Ici (0 : ℝ), sourceTestCurveLegendreRay (Γ.shift Γ.max).toSourceTestCurvePredata t =
      fun x ↦ sourceTestCurveLegendreRay Γ.toSourceTestCurvePredata t x -
        ((t.1 * Γ.max : ℝ) : EReal)) ∧
    sourceTestCurveEnergy omega hφ (Γ.shift Γ.max) ((Γ.shift_based_iff hφ Γ.max).mpr hΓ) =
      sourceTestCurveEnergy omega hφ Γ hΓ -
        ((Γ.max * (sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ).toReal : ℝ) : EReal) ∧
    (Γ.shift Γ.max ∈ SourceBoundedTestCurves θ φ hφ ↔ Γ ∈ SourceBoundedTestCurves θ φ hφ) ∧
    (Γ.shift Γ.max ∈ SourceFiniteEnergyTestCurves omega θ φ hφ ↔
      Γ ∈ SourceFiniteEnergyTestCurves omega θ φ hφ) := by
  refine ⟨?_, (Γ.shift_based_iff hφ Γ.max).mpr hΓ, ?_,
    fun t ↦ Γ.toSourceTestCurvePredata.shift_rawLegendre Γ.max t,
    fun t ↦ Γ.toSourceTestCurvePredata.shift_legendreRay Γ.max t,
    Γ.shift_energy omega hφ hΓ Γ.max, Γ.shift_bounded_iff hφ Γ.max,
    Γ.shift_finiteEnergy_iff omega hφ Γ.max⟩
  · change Γ.max - Γ.max = 0
    exact sub_self _
  · exact (Γ.shift_limit Γ.max).trans hΓ

end SGPT.PSH.VariableComplexAtlas
