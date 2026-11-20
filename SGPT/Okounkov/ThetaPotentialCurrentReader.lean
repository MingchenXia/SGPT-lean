import SGPT.Okounkov.OriginalCurrentLelong
import SGPT.Okounkov.LocalThetaReader
import SGPT.Foundations.Analysis.Pending.ThetaPotentialPrescribedChartReader
import SGPT.Foundations.Analysis.Pending.SourceTraceRepresentativeDefinition

set_option autoImplicit false

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions Manifold ENNReal

namespace SGPT.Okounkov

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending CanonicalCurrentFrame GlobalPositiveCurrentACRestriction
open ActualQuasiPshPotentialSmoothCompatibility NaturalThetaPshGeometricCurrent
open SquaredLogLelongSourceNormalization SourceTraceRepresentativeDefinition
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The exact whole-current local reading property produced for arbitrary
original fully positive currents. -/
def IsOriginalCurrentSourceReader
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))) (μ : M → ℝ≥0∞) : Prop :=
  ∀ (e : ComplexChart (m + 1) M) (U : Opens (ComplexModel (m + 1)))
    (_hU : U ≤ chartTarget e) (u : ComplexModel (m + 1) → EReal)
    (hu : LocalQuasiPshPotentialOn u U),
    (∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ) →
    ∀ p ∈ e.val.source, e.val p ∈ U →
      μ p = squaredLogLelongNumber (n := m + 1) u (e.val p)

/-- Genuine original theta data give the whole-current reader equality,
without an analytic or current-to-potential equality premise. -/
theorem original_current_source_reader_eq_theta_potential
    {θ : SmoothRealForm (m + 1) M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) {μ : M → ℝ≥0∞}
    (hμ : IsOriginalCurrentSourceReader (thetaPotentialCurrent θ u hu) μ) :
    μ = fun p => squaredLogLelongNumber (n := m + 1) u p := by
  funext p
  let e := complexChartAt (n := m + 1) p
  have hp : p ∈ e.val.source := mem_complexChartAt_source p
  obtain ⟨W, ρ, hpW, hpot, _hpsh, hν⟩ := exists_psh_local_theta_reader hu e p hp
  let U : Opens (ComplexModel (m + 1)) := ⟨W, hpot.1⟩
  let F : ComplexModel (m + 1) → EReal :=
    fun z => chartFunction u e z + (ρ z : EReal)
  obtain ⟨hFpsh, hFfin, hL, hcurr, _hscalar, _hpositive⟩ :=
    ThetaPotentialPrescribedChartReader.exists_corrected_original_chart_reader
      θ hu e (W := U) ρ hpot
  have hF : LocalQuasiPshPotentialOn F U := by
    refine ⟨U.isOpen, fun x hx => (hFpsh x hx).quasiPlurisubharmonicAt, ?_⟩
    intro x hx V hV hxV
    have hpos : volume ((U : Set (ComplexModel (m + 1))) ∩ V) ≠ 0 :=
      ((U.isOpen.inter hV).measure_pos volume ⟨x, hx, hxV⟩).ne'
    obtain ⟨y, hy, hfy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left hFfin)
    exact ⟨y, hy, hfy.2⟩
  have hread : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(U, ℝ)),
      (thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e w
        (TestFunction.monoCLM ℝ φ) = ddC (regularLocalQuasiPsh hF) w φ := by
    intro w φ
    have hcoeff : LelongPoincareDivisor.restrictForm
        ((thetaPotentialCurrent θ u hu).coefficients (canonicalBasis (m + 1)) e)
        (hpot.2.1 : U ≤ chartTarget e) = ddC (regularLocalQuasiPsh hF) := hcurr
    exact congrArg (fun A => A w φ) hcoeff
  rw [hμ e U hpot.2.1 F hF hread p hp hpW]
  apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
  rw [← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m),
    ← lelongNumber_eq_two_mul_squaredLog (Nat.succ_ne_zero m)]
  simpa only [e.val.left_inv hp] using hν (e.val p) hpW

/-- The actual canonical source reader agrees with every global theta
representation of the same original current. -/
theorem exists_original_full_positive_current_theta_invariant_source_reader
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hclosed : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hT : IsFullPositive T) :
    ∃ μ : M → ℝ≥0∞, IsOriginalCurrentSourceReader T μ ∧
      ∀ (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal)
        (hu : IsThetaPshPotential θ u), T = thetaPotentialCurrent θ u hu →
          μ = fun p => squaredLogLelongNumber (n := m + 1) u p := by
  obtain ⟨μ, hμ, _huniq⟩ :=
    exists_unique_original_full_positive_current_source_reader T hclosed h11 hT
  refine ⟨μ, hμ, ?_⟩
  intro θ u hu heq
  exact original_current_source_reader_eq_theta_potential hu (heq ▸ hμ)

/-- Equality of the actual whole currents forces equality of their original
source point readers, even for different smooth backgrounds. -/
theorem squaredLogLelongNumber_eq_of_thetaPotentialCurrent_eq
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv) :
    (fun p => squaredLogLelongNumber (n := m + 1) u p) =
      fun p => squaredLogLelongNumber (n := m + 1) v p := by
  obtain ⟨hc, h11, hT⟩ :=
    NaturalThetaPshClosedCurrent.thetaPotentialCurrent_closed_type_positive θ u hu
  obtain ⟨μ, _hμ, hinv⟩ :=
    exists_original_full_positive_current_theta_invariant_source_reader
      (thetaPotentialCurrent θ u hu) hc h11 hT
  exact (hinv θ u hu rfl).symm.trans (hinv σ v hv heq)

/-- The actual whole-set generic coefficient is independent of the global
theta-potential representation; empty carriers and infinite values are retained. -/
theorem sourceGeneric_eq_of_thetaPotentialCurrent_eq
    {θ σ : SmoothRealForm (m + 1) M 2} {u v : M → EReal}
    (hu : IsThetaPshPotential θ u) (hv : IsThetaPshPotential σ v)
    (heq : thetaPotentialCurrent θ u hu = thetaPotentialCurrent σ v hv)
    {V : Type*} (ι : V → M) :
    sourceGenericLelongNumber (n := m + 1) ι u =
      sourceGenericLelongNumber (n := m + 1) ι v := by
  have hpoint := squaredLogLelongNumber_eq_of_thetaPotentialCurrent_eq hu hv heq
  exact iInf_congr fun x => congrFun hpoint (ι x)

end SGPT.Okounkov
