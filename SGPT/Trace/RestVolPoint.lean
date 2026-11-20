import SGPT.Trace.RestVolTrace
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalGlobalMixedMass

/-!
# Restricted volumes along a point (`dim Y = 0`)

Lane TRACE-RV, blueprint `claude-rest-vol.tex`, node `claude-rest-vol:point`.  The case
`dim Y = 0` of `thm:rest_volume` and `thm:rest_volume_2` (`chapter_trace.tex`): `Y` is a point,
`m!/k^m = 1`, every `h⁰` is at most the rank `1` of the line bundle, and the mass of the trace
(when defined) is the number of points of `Y`, i.e. `1`.

* `finrank_twistedSections_le_one_of_dim_zero`: on a compact connected manifold of dimension
  `0`, `h⁰(V, L^k ⊗ T) ≤ 1`;
* `sourceTraceMass_eq_one_of_dim_zero`: `∫_Y (θ|_Y + dd^c Tr^θ_Y(φ))^0 = 1` when the trace is
  defined.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.RestVol

open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle

section Point

variable {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel 0) V]
  [IsComplexManifold 0 V] [CompactSpace V] [ConnectedSpace V]

/-- A compact connected manifold of dimension `0` is a point. -/
theorem subsingleton_of_dim_zero : Subsingleton V := by
  have := (ZeroDimensionalGlobalMixedMass.compact_zero_dim_finite_discrete (M := V)).1
  exact subsingleton_of_preconnected_totallyDisconnected

theorem natCard_eq_one_of_dim_zero : Nat.card V = 1 := by
  have := subsingleton_of_dim_zero (V := V)
  exact Nat.card_unique

/-- `h⁰(V, E) ≤ 1` for a holomorphic line bundle `E` on a point. -/
theorem finrank_holomorphicSections_le_one_of_dim_zero
    (E : HermitianHolomorphicLineBundle.{0, 0} 0 V) :
    Module.finrank ℂ (HolomorphicSections (n := 0) E.Fiber) ≤ 1 := by
  have hsub := subsingleton_of_dim_zero (V := V)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty V)
  let ev : HolomorphicSections (n := 0) E.Fiber →ₗ[ℂ] E.Fiber x₀ :=
    { toFun := fun s => s x₀
      map_add' := fun s t => rfl
      map_smul' := fun c s => rfl }
  have hinj : Function.Injective ev := by
    intro s t hst
    ext y
    rw [Subsingleton.elim y x₀]
    exact hst
  have hx₀ : x₀ ∈ (trivializationAt ℂ E.Fiber x₀).baseSet :=
    mem_baseSet_trivializationAt ℂ E.Fiber x₀
  have hfib : Module.finrank ℂ (E.Fiber x₀) = 1 := by
    rw [((trivializationAt ℂ E.Fiber x₀).linearEquivAt ℂ x₀ hx₀).finrank_eq,
      Module.finrank_self]
  have := twistedSections_finiteDimensional (n := 0) E unit 0
  have : FiniteDimensional ℂ (E.Fiber x₀) :=
    LinearEquiv.finiteDimensional
      ((trivializationAt ℂ E.Fiber x₀).linearEquivAt ℂ x₀ hx₀).symm
  rw [← hfib]
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_twistedSections_le_one_of_dim_zero
    (L T : HermitianHolomorphicLineBundle.{0, 0} 0 V) (k : ℕ) :
    Module.finrank ℂ (twistedSections L T k) ≤ 1 :=
  finrank_holomorphicSections_le_one_of_dim_zero (twistedPower L T k)

variable [MeasurableSpace V] [BorelSpace V]

/-- The mass of a potential on a point is `1`. -/
theorem diagonalPotentialMass_eq_one_of_dim_zero (η : ClosedRealOneOneForm 0 V) {u : V → EReal}
    (hu : IsThetaPshPotential η.val u) : diagonalPotentialMass η u hu = 1 := by
  have hcount := (ZeroDimensionalGlobalMixedMass.global_empty_mixed_measure_eq_count
    (M := V) (fun _ => η) (fun _ => u) (fun _ => hu.1)).2.1
  have hmass : diagonalPotentialMass η u hu = (Nat.card V : ℝ≥0∞) := hcount
  rw [hmass, natCard_eq_one_of_dim_zero, Nat.cast_one]

/-- **The mass of the trace along a point is `1`** (when the trace is defined). -/
theorem sourceTraceMass_eq_one_of_dim_zero {n : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X]
    (ωb : KahlerBackground n X) (ωV : KahlerBackground 0 V) {ι : V → X}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (θ : ClosedRealOneOneForm n X) (u : X → EReal)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong ωb ωV hι θ u) :
    SGPT.Trace.sourceTraceMass ωb ωV hι θ u = 1 := by
  unfold SGPT.Trace.sourceTraceMass
  rw [dif_pos hdefined]
  exact diagonalPotentialMass_eq_one_of_dim_zero _ _

end Point

end SGPT.Trace.RestVol
