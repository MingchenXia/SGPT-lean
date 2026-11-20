import SGPT.Trace.SmoothTarget
import SGPT.Foundations.Analysis.Pending.ActualTraceMultiplierInclusion
import SGPT.Foundations.Analysis.Pending.ZeroDimensionalQuasiPshMultiplierIdeals
import SGPT.Foundations.Analysis.Pending.HolomorphicGermAlgebra

/-!
# Multiplier ideals of the trace operator

Source `prop:OT2` (`chapter_trace.tex`): let `φ ∈ QPSH(X)` with `ν(φ, Y) = 0` and
assume that `Y` is smooth. Then for every `λ > 0`,
`𝓘(λ Tr_Y(φ)) ⊆ Res_Y 𝓘(λ φ)`.

A smooth irreducible analytic subset of the connected compact Kähler manifold `X` is
a closed connected complex submanifold `W` (`IsClosedConnectedSubmanifold n W k`); it
is its own normalization, so the trace is the natural trace predicate
`IsNaturalSourceTraceRepresentative` with the induced complex and Kähler structure.
`Res_Y 𝓘` is `SubmanifoldIdealRestriction.restrictIdeal`, the ideal of `𝒪_Y` generated
by the restrictions of the germs of `𝓘` (the image of `𝓘` in `𝒪_Y = 𝒪_X/𝓘_Y`, i.e.
`𝓘/(𝓘 ∩ 𝓘_Y)`, source `def:restidealsheaf`), and the inclusion is the stalkwise
inclusion `GermIdeal.Le`.

The positive-dimensional case is the Ohsawa–Takegoshi/strong-openness argument of the
source proof, formalized in `ActualTraceMultiplierInclusion`; the zero-dimensional
ambient case (where `X` and `Y` are points) is checked directly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ENNReal ContDiff

namespace SGPT.Trace

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
  SGPT.Foundations.Analysis.Pending
  SourceTraceRepresentativeDefinition NaturalSubmanifoldSourceTraceDefinition
  SubmanifoldChartedSpace SubmanifoldIdealRestriction

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Source `prop:OT2`: for a closed connected complex submanifold `W` (the smooth
irreducible analytic subset `Y`) of the compact Kähler manifold `X`, every trace
operator `τ` of `u` along `W` satisfies `𝓘(c τ) ⊆ Res_W 𝓘(c u)` for every real `c > 0`.
The hypothesis `ν(u, W) = 0` is part of the trace predicate. -/
theorem multiplierIdeal_trace_le_restrictIdeal (omega : KahlerBackground n M)
    {W : Set M} (hW : IsClosedConnectedSubmanifold n W k) {u : M → EReal} {τ : W → EReal}
    (htrace : IsNaturalSourceTraceRepresentative omega hW u τ) {c : ℝ} (hc : 0 < c) :
    letI := chartedSpace (le_of_isClosedConnectedSubmanifold hW) hW.2.2
    (multiplierIdeal (n := k) c τ).Le
      (restrictIdeal (k := k) (W := W) (multiplierIdeal (n := n) c u)) := by
  let hk := le_of_isClosedConnectedSubmanifold hW
  let : ChartedSpace (ComplexModel k) W := chartedSpace hk hW.2.2
  have : IsComplexManifold k W := isComplexManifold_chartedSpace hk hW.2.2
  let : ConnectedSpace W := isConnected_iff_connectedSpace.mp hW.2.1
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  let omegaW := SubmanifoldKahlerRestriction.kahlerBackground hk hW.2.2 omega
  let hι := contMDiff_val hk hW.2.2
  have hT : IsSourceTraceRepresentativeAlong omega omegaW hι u τ := htrace
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    obtain ⟨_hg, θ, _ε, _U, happ, β, _hadm, hτ, _hterms, _hlim⟩ := hT
    have hu : IsGlobalQuasiPshPotential (n := 0) u := happ.target.quasiPshPotential
    have hτq : IsGlobalQuasiPshPotential (n := 0) τ := hτ.quasiPshPotential
    intro p F hF
    have hFhol : HolomorphicAt 0 F p :=
      (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
        hτq hc p F).mp hF
    have hone : (multiplierIdeal (n := 0) c u).mem p.1 (fun _ => (1 : ℂ)) :=
      (ZeroDimensionalQuasiPshMultiplierIdeals.mem_multiplierIdeal_iff_holomorphicAt
        hu hc p.1 _).mpr (holomorphicAt_const 1)
    refine ⟨hFhol, 1, fun _ _ => 1, fun _ => F, fun _ => ⟨fun _ => 1, hone, rfl⟩,
      fun _ => hFhol, Eventually.of_forall fun y => ?_⟩
    simp
  have hnat := (isSourceTraceRepresentativeAlong_iff_native hn omega omegaW hι u τ).mp hT
  exact ActualTraceMultiplierInclusion.multiplierIdeal_le_restrictIdeal_of_isTraceRepresentativeAlong
    hW omega omegaW hnat hc

end SGPT.Trace
