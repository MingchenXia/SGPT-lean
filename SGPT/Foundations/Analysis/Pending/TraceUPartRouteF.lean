import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.DominationBigRestriction

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Route F: `TraceUPart` from a positive lower bound on the restricted approximant masses

Human decision I-0796 (D0 = route F).  For a quasi-equisingular approximation `Φ_j` of `V_θ` as in
`PositiveCurrentAssembly.TraceUPart` (global type `(2^{-j}, 𝓘(2^jV_θ))`, errors `ε_j > 0`), with
restrictions `φ_j = Φ_j|_V ∈ PSH(V, γ + ε_jω_V)`, the trace-free limit
`u = ⨅_j P_{γ+ε_jω_V}[φ_j]` (`TraceFreeLimit`) satisfies

* (T2) `u ≤ P_{γ+ε_jω_V}[φ_j]` for every `j` (by construction, `C_j = 0`);
* (T3) `∫(γ + ε_jω_V)_{φ_j}^k → ∫γ_u^k` (DX24 Prop. 2.1, `tendsto_diagonalPotentialMass_traceFreeLimit`);
* (T1) `∫γ_u^k > 0` as soon as the masses `b_j = ∫(γ + ε_jω_V)_{φ_j}^k` are bounded below by a
  positive constant — the content of DX24 Thm 3.15 / plan §5.2 `F-b` (`b_j ≥ h`), recorded here as
  the hypothesis `RestrictedApproximantMassBound` (not an interface).

Hence `traceUPart_of_restrictedApproximantMassBound`, and, with `DominationBigRestriction`,
`positiveCurrentInput_of_restrictedApproximantMassBound`: the positive-current root needs exactly
`F-b` (plus the existing Boucksom root).  Sorry-free.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal

universe u

namespace SGPT.Foundations.Analysis.Pending.TraceUPartRouteF

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.HolomorphicIdealSheaves
  FirstPass.GlobalAnalyticSingularities FirstPass.QuasiEquisingularApproximation FirstPass.BlowupSequences
  SubmanifoldChartedSpace SubmanifoldMassCalculus Copy4TraceInputReduction
  PositiveCurrentAssembly DiagonalMass TraceFreeLimit

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Route F, `F-b`, as a statement**: for every quasi-equisingular approximation `Φ_j` of `V_θ` as in
`TraceUPart`, the masses `∫_V (γ + ε_jω_V)_{Φ_j|_V}^k` of the restrictions are bounded below by one
positive constant.  (Plan §5.2: `b_q ≥ h = ⟨α^k⟩_{X|V}`; any positive constant suffices.) -/
def RestrictedApproximantMassBound [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  letI := chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  haveI := isComplexManifold_chartedSpace (le_of_isClosedConnectedSubmanifold hV) hV.2.2
  letI : MeasurableSpace V.carrier := borel _
  haveI : BorelSpace V.carrier := ⟨rfl⟩
  haveI : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  ∀ (ε : ℕ → ℝ) (Φ : ℕ → X → EReal),
    IsQuasiEquisingularApproximation omega θ (thetaPshSupremum θ.val) ε Φ → (∀ j, 0 < ε j) →
    (∀ j, HasAnalyticSingularitiesOfType (n := n) (Φ j) (((2 ^ j : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := n) ((2 ^ j : ℕ) : ℝ) (thetaPshSupremum θ.val))) →
    ∀ hφ : ∀ j, IsThetaPshPotential
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form).val
        (fun x : V.carrier => Φ j x.1),
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ j, c ≤ diagonalPotentialMass
        (ClosedRealOneOneForm.pullback
            (contMDiff_val (le_of_isClosedConnectedSubmanifold hV) hV.2.2) θ +
          ε j • (SubmanifoldKahlerRestriction.kahlerBackground
            (le_of_isClosedConnectedSubmanifold hV) hV.2.2 omega).form)
        (fun x : V.carrier => Φ j x.1) (hφ j)

/-- **`TraceUPart` along route F**: the trace-free limit `u = ⨅_j P_{γ+ε_jω_V}[Φ_j|_V]` has
(T2) by construction, (T3) by DX24 Prop. 2.1, and (T1) from the lower bound `F-b`. -/
theorem traceUPart_of_restrictedApproximantMassBound [CompactSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hB : RestrictedApproximantMassBound omega θ V hV) : TraceUPart omega θ V hV := by
  set hk := le_of_isClosedConnectedSubmanifold hV
  let := chartedSpace hk hV.2.2
  have := isComplexManifold_chartedSpace hk hV.2.2
  let : MeasurableSpace V.carrier := borel _
  have : BorelSpace V.carrier := ⟨rfl⟩
  have : CompactSpace V.carrier := compactSpace_of_isClosed hV.1
  have : ConnectedSpace V.carrier := connectedSpace_of_isClosedConnectedSubmanifold hV
  have : Nonempty V.carrier := hV.2.1.nonempty.to_subtype
  intro ε Φ hqea hεpos htype hφ
  obtain ⟨c, hc, hcle⟩ := hB ε Φ hqea hεpos htype hφ
  set ωV := SubmanifoldKahlerRestriction.kahlerBackground hk hV.2.2 omega
  set γ := ClosedRealOneOneForm.pullback (contMDiff_val hk hV.2.2) θ
  have hφanti : ∀ x : V.carrier, Antitone fun j => Φ j x.1 := fun x =>
    hqea.decreasesPointwise.1 x.1
  have hu := isThetaPshPotential_traceFreeLimit ωV hqea.error_antitone hqea.error_tendsto hφ
    hφanti
  have hT3 := tendsto_diagonalPotentialMass_traceFreeLimit hdim_pos ωV hεpos hqea.error_antitone
    hqea.error_tendsto hφ hφanti
  refine ⟨traceFreeLimit γ ωV.form ε (fun j (x : V.carrier) => Φ j x.1), hu, ?_, hT3,
    Eventually.of_forall fun j => ⟨0, fun x => ?_⟩⟩
  · exact lt_of_lt_of_le hc (ge_of_tendsto' hT3 hcle)
  · rw [EReal.coe_zero, add_zero]
    exact traceFreeLimit_le γ ωV.form ε (fun j (x : V.carrier) => Φ j x.1) j x

/-- **The positive-current root needs exactly `F-b`.**  Under the standing hypotheses of
`PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput` (`{θ}` big, `0 < dim V < n`,
`V ⊄ E_nn(α)`), the lower bound `RestrictedApproximantMassBound` gives `PositiveCurrentInput`
(route F for `TraceUPart`; `lem:domination` through the existing Boucksom root,
`DominationBigRestriction`). -/
theorem positiveCurrentInput_of_restrictedApproximantMassBound [CompactSpace X]
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hB : RestrictedApproximantMassBound omega θ V hV) :
    PositiveCurrentInput omega θ V hV :=
  DominationBigRestriction.positiveCurrentInput_of_traceUPart' omega θ hbig V hV hdim_pos hdim_lt
    hnonNef (traceUPart_of_restrictedApproximantMassBound omega θ V hV hdim_pos hB)

end

end SGPT.Foundations.Analysis.Pending.TraceUPartRouteF
