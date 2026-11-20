import SGPT.Okounkov.ZeroSourcePartialBody
import SGPT.AlmostSemigroup.BrunnMinkowski

/-!
# The actual source Okounkov test curve in dimension zero

Source: revised SGPT 69360cfd, `thm:Okountescurvex`, in dimension zero.
Every family member and the limit are the genuine source general bodies
constructed through resolution, approximation and perturbation intersections
in `ZeroSourcePartialBody`. The original cutoff and potentials are retained.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Okounkov.ZeroSource

open Set Filter MeasureTheory
open scoped Topology ENNReal Pointwise
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ThetaPshL1Topology
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable (F : OriginalFlagGeometry.{u} 0) [MeasurableSpace F.carrier]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel 0 F.carrier)}

/-- The genuine original limit with its genuine native theta-psh proof. -/
def nativeLimit (Γ : SourceTestCurve θ) :
    ThetaPshL1 (atlasClosedFormToNative θ).val :=
  ⟨sourceTestCurveLimit Γ.toSourceTestCurvePredata,
    (isThetaPSH_iff_nativeThetaPotential θ _).mp Γ.limit_thetaPSH⟩

/-- The exact source family, using the original general-body carrier at
every actual source parameter and the actual original source limit. -/
def okounkovTestCurve (Γ : SourceTestCurve θ) :
    TestCurve (partialConvexBody F (atlasClosedFormToNative θ)
      (nativeLimit F Γ).val (nativeLimit F Γ).property) where
  max := Γ.max
  body τ := partialConvexBody F (atlasClosedFormToNative θ)
    (Γ.potential τ) (Γ.native_thetaPSH τ)
  antitone s t _ := by
    rw [partialConvexBody_eq F (atlasClosedFormToNative θ) (atlasClosedFormToNative θ)
      (Γ.potential t) (Γ.potential s) (Γ.native_thetaPSH t) (Γ.native_thetaPSH s)]
  concave s t a ha ha1 := by
    intro x _
    change x ∈ TranscendentalMain.euclideanImage (generalBody F
      (atlasClosedFormToNative θ) _ _)
    rw [euclidean_generalBody_eq_singleton_zero]
    exact Subsingleton.elim _ _
  limit := by
    have heq : (fun τ : Iio Γ.max => partialConvexBody F (atlasClosedFormToNative θ)
        (Γ.potential τ) (Γ.native_thetaPSH τ)) =
        fun _ : Iio Γ.max => partialConvexBody F (atlasClosedFormToNative θ)
          (nativeLimit F Γ).val (nativeLimit F Γ).property := by
      funext τ
      exact partialConvexBody_eq F _ _ _ _ _ _
    rw [heq]
    exact tendsto_const_nhds

/-- Exact original cutoff readback. -/
@[simp] theorem okounkovTestCurve_max (Γ : SourceTestCurve θ) :
    (okounkovTestCurve F Γ).max = Γ.max := rfl

/-- Exact source carrier readback, after genuine geometric body construction. -/
theorem coe_okounkovTestCurve_body (Γ : SourceTestCurve θ) (τ : Iio Γ.max) :
    ((okounkovTestCurve F Γ).body τ : Set (EuclideanSpace ℝ (Fin 0))) =
      TranscendentalMain.euclideanImage (generalBody F (atlasClosedFormToNative θ)
        (Γ.potential τ) (Γ.native_thetaPSH τ)) := rfl

/-- The actual source family equals its original limit at every actual
parameter, so its boundedness needs no assumption on the source curve. -/
theorem okounkovTestCurve_isBounded (Γ : SourceTestCurve θ) :
    (okounkovTestCurve F Γ).IsBounded := by
  apply Filter.Eventually.of_forall
  intro τ
  exact partialConvexBody_eq F _ _ _ _ _ _

/-- Actual convex energy in dimension zero, with the original signed
integral and infinite original parameter domain. -/
theorem TestCurve_energy_eq_max {Δ : ConvexBody (EuclideanSpace ℝ (Fin 0))}
    (K : TestCurve Δ) : K.energy = (K.max : EReal) := by
  rw [TestCurve.energy_eq_deficit]
  simp only [Nat.factorial_zero, Nat.cast_one,
    SGPT.AlmostSemigroup.BrunnMinkowski.volume_zero_dimensional, one_mul, mul_one,
    sub_self, ENNReal.ofReal_zero, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

/-- Energy of the actual source family in dimension zero. -/
theorem okounkovTestCurve_energy_eq_max (Γ : SourceTestCurve θ) :
    (okounkovTestCurve F Γ).energy = (Γ.max : EReal) :=
  TestCurve_energy_eq_max _

variable [BorelSpace F.carrier]

/-- Original ordinary masses on the entire original integration domain
are produced equal to one by the genuine zero-dimensional NP measure. -/
theorem sourceTestCurveRealMassAt_eq_one (ω : KahlerBackground 0 F.carrier)
    (Γ : SourceTestCurve θ) {τ : ℝ} (hτ : τ < Γ.max) :
    sourceTestCurveRealMassAt ω Γ τ = 1 := by
  rw [sourceTestCurveRealMassAt_of_lt ω Γ hτ,
    SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero, ENNReal.toReal_one]

/-- Energy of the exact original based curve in dimension zero, with its
original base and genuine original nonnegative deficit integral. -/
theorem sourceTestCurveEnergy_eq_max (ω : KahlerBackground 0 F.carrier)
    {φ : F.carrier → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    sourceTestCurveEnergy ω hφ Γ hΓ = (Γ.max : EReal) := by
  have hmass : sourcePotentialNonPluripolarMeasure θ φ hφ.thetaPSH univ = 1 :=
    SGPT.NPP.sourcePotentialNonPluripolarMass_eq_one_of_dim_zero θ φ hφ.thetaPSH
  have hzero : (∫⁻ τ : ℝ in Iio Γ.max,
      ENNReal.ofReal (1 - sourceTestCurveRealMassAt ω Γ τ)) = 0 := by
    calc
      _ = ∫⁻ _τ : ℝ in Iio Γ.max, (0 : ENNReal) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Iio] with τ hτ
        rw [sourceTestCurveRealMassAt_eq_one F ω Γ hτ, sub_self, ENNReal.ofReal_zero]
      _ = 0 := lintegral_zero
  rw [sourceTestCurveEnergy, hmass, ENNReal.toReal_one, mul_one, hzero,
    EReal.coe_ennreal_zero, sub_zero]

/-- Revised source energy equality, even without I-model assumptions, in
the actual zero-dimensional branch of `thm:Okountescurvex`. -/
theorem okounkovTestCurve_energy_eq (ω : KahlerBackground 0 F.carrier)
    {φ : F.carrier → EReal} (hφ : SourceModelPotential θ φ) (Γ : SourceTestCurve θ)
    (hΓ : Γ ∈ SourceTestCurvesBased θ φ hφ) :
    (okounkovTestCurve F Γ).energy = sourceTestCurveEnergy ω hφ Γ hΓ := by
  rw [okounkovTestCurve_energy_eq_max, sourceTestCurveEnergy_eq_max F ω hφ Γ hΓ]

omit [BorelSpace F.carrier] in
/-- Every exact original source family in dimension zero has finite energy. -/
theorem okounkovTestCurve_hasFiniteEnergy (Γ : SourceTestCurve θ) :
    (okounkovTestCurve F Γ).HasFiniteEnergy := by
  change (⊥ : EReal) < (okounkovTestCurve F Γ).energy
  rw [okounkovTestCurve_energy_eq_max]
  exact EReal.bot_lt_coe _

end SGPT.Okounkov.ZeroSource
