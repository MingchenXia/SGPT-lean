import SGPT.Foundations.Analysis.Pending.SignedSmoothCoefficientTensorLaw
import SGPT.Foundations.Analysis.Pending.OpenSmoothFormDistributionReflection
import SGPT.Foundations.Analysis.FirstPass.BottChern

set_option autoImplicit false

/-! Actual smooth closed real (1,1) representatives and original native ddC
differences, built internally from arbitrary compact signed closed currents.
Full mathematical statements and ENTIRE proofs precede this source. -/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions ContDiff Topology
namespace SGPT.Foundations.Analysis.Pending.ClosedCurrentSmoothBottChernRepresentative


open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor
  LocalSmoothFormDensityGluing SignedSmoothCoefficientTensorLaw
  OpenSmoothFormDistributionReflection FiniteGlobalCurrentSmoothLocalDensity
  FiniteGlobalScalarDdc FiniteGlobalScalarCurrent FiniteScalarDistributionGluing
  DistributionFullChartCutoffTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

private theorem coefficients_smoothGlobalCurrent
    (A : SmoothRealForm n M 2) (e : ComplexChart n M) :
    (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) A).coefficients b e =
      smoothFormDistribution b A e := by
  change fromLocalCurrent b (degreeTwo hn)
    (toLocalCurrent b (degreeTwo hn) (smoothFormDistribution b A e)) = _
  exact CurrentPairing.fromLocalCurrent_toLocalCurrent b (degreeTwo hn) _

/-- Actual local full smooth readings, original closedness and type internally
produce a genuine compatible smooth closed real (1,1) form and full equality. -/
theorem exists_closed_smooth_form_of_local_readings
    (K : GlobalCurrent n M (degreeTwo hn)) (hclosed : K.IsClosed b)
    (h11 : K.IsTypeOneOne b hn)
    (hloc : ∀ (e : ComplexChart n M) (x : ComplexModel n), x ∈ e.val.target →
      ∃ (V : Opens (ComplexModel n)) (hVe : V ≤ chartTarget e)
        (β : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ),
        x ∈ V ∧ ContDiffOn ℝ ∞ β V ∧ ∃ hβ : LocallyIntegrableOn β V b.addHaar,
          restrictForm (K.coefficients b e) hVe = regularFormDistribution b.addHaar β hβ) :
    ∃ σ : ClosedRealOneOneForm n M,
      K = GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val ∧
      ∀ e, K.coefficients b e = smoothFormDistribution b σ.val e := by
  classical
  have hp : ∀ e : ComplexChart n M,
      ∃ a : ComplexModel n → (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ,
        ContDiffOn ℝ ∞ a (chartTarget e) ∧
        ∃ hL : LocallyIntegrableOn a (chartTarget e) b.addHaar,
          K.coefficients b e = regularFormDistribution b.addHaar a hL := by
    intro e
    exact exists_smooth_density b.addHaar (K.coefficients b e) (hloc e)
  choose a ha hL heq using hp
  have hread : ∀ e, K.coefficients b e = regularFormDistribution b.addHaar (a e)
      ((ha e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet) := heq
  let A : SmoothRealForm n M 2 := {
    coeff := a
    smooth := ha
    compatible := fun e f z hz v =>
      tensor_law_of_smooth_coefficient_readings b K a ha hread e f z hz v }
  have hAclosed : A.IsClosed := by
    intro e z hz
    have hc : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed
        (regularFormDistribution b.addHaar (a e)
          ((ha e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)) := by
      rw [← hread e]
      exact hclosed e
    exact (isClosed_regularForm_iff b.addHaar (a e) (ha e)).mp hc z hz
  have hA11 : A.IsTypeOneOne := by
    intro e z hz
    have ht : _root_.SGPT.Foundations.Analysis.LocalCurrents.IsOneOne
        (regularFormDistribution b.addHaar (a e)
          ((ha e).continuousOn.locallyIntegrableOn (chartTarget e).isOpen.measurableSet)) := by
      rw [← hread e]
      exact h11 e
    exact isOneOne_of_regularForm_isOneOne b.addHaar (a e) (ha e) ht z hz
  let σ : ClosedRealOneOneForm n M := ⟨A, hAclosed, hA11⟩
  have hcoeff : ∀ e, K.coefficients b e = smoothFormDistribution b σ.val e := heq
  refine ⟨σ, ?_, hcoeff⟩
  apply globalCurrent_ext b
  intro e
  rw [coefficients_smoothGlobalCurrent]
  exact hcoeff e

/-- Every original compact signed closed type-(1,1) current internally yields
its own actual global scalar partition and a genuine smooth closed form,
with a literal native ddC difference in the original full current spaces. -/
theorem exists_smooth_native_bott_chern_representative [CompactSpace M]
    (T : GlobalCurrent n M (degreeTwo hn)) (hclosed : T.IsClosed b)
    (h11 : T.IsTypeOneOne b hn) :
    ∃ (m : ℕ) (g : Fin m → ComplexChart n M) (P : Fin m → Opens (ComplexModel n))
      (hP : ∀ j, P j ≤ chartTarget (g j)) (R : ∀ j, 𝓓'(chartTarget (g j), ℝ))
      (χ : Fin m → M → ℝ) (hχ : ∀ j, ChartSmooth (n := n) (χ j))
      (hc : ∀ j, IsCompact (tsupport (χ j)))
      (hs : ∀ j, tsupport (χ j) ⊆ (g j).val.source)
      (Q : GlobalCurrent n M (0 : CurrentDegree n)) (σ : ClosedRealOneOneForm n M),
      (∀ j y, 0 ≤ χ j y) ∧
      (∀ j, tsupport (χ j) ⊆ {y | y ∈ (g j).val.source ∧ (g j).val y ∈ P j}) ∧
      (∀ y, ∑ j, χ j y = 1) ∧
      (∀ j, ddC (restrictDistribution (R j) (hP j)) =
        restrictForm (T.coefficients b (g j)) (hP j)) ∧
      T = GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val +
        finiteGlobalDdc b hn g χ hχ hc hs R ∧
      (∀ e, T.coefficients b e = smoothFormDistribution b σ.val e +
        ddC (finiteScalarFamily g χ hχ hc hs R e)) ∧
      ∀ e (η : TestForm (chartTarget e) (Module.finrank ℝ (ComplexModel n))),
        Q.inChart e η = ∑ j, R j (fullChartTestCLM e (g j) (χ j) (hχ j) (hc j) (hs j)
          (testCoefficientCLM b η)) := by
  obtain ⟨m, g, P, hP, R, χ, hχ, hc, hs, K, hK, hnon, hsP, hsum, hR,
      hKclosed, hK11, hloc⟩ :=
    exists_global_remainder_with_smooth_local_densities b hn T hclosed h11
  obtain ⟨σ, hσ, hσcoeff⟩ :=
    exists_closed_smooth_form_of_local_readings b hn K hKclosed hK11 hloc
  have hT : T = GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val +
      finiteGlobalDdc b hn g χ hχ hc hs R := by
    rw [hK] at hσ
    apply GlobalCurrent.ext
    intro e η
    have hlocal := congrArg (fun Z : GlobalCurrent n M (degreeTwo hn) => Z.inChart e η) hσ
    change T.inChart e η - (finiteGlobalDdc b hn g χ hχ hc hs R).inChart e η =
      (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val).inChart e η at hlocal
    change T.inChart e η =
      (GlobalCurrents.smoothGlobalCurrent b (k := degreeTwo hn) σ.val).inChart e η +
        (finiteGlobalDdc b hn g χ hχ hc hs R).inChart e η
    linarith
  refine ⟨m, g, P, hP, R, χ, hχ, hc, hs,
    finiteGlobalScalarCurrent b g χ hχ hc hs R, σ,
    hnon, hsP, hsum, hR, hT, ?_, ?_⟩
  · intro e
    rw [hT, GlobalCurrent.coefficients_add, coefficients_smoothGlobalCurrent,
      finiteGlobalDdc_coefficients]
  · exact fun e η => finiteGlobalScalarCurrent_apply b g χ hχ hc hs R e η

end SGPT.Foundations.Analysis.Pending.ClosedCurrentSmoothBottChernRepresentative
