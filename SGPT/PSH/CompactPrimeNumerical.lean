import SGPT.PSH.CompactPrimeOver
import SGPT.PSH.SourceIdealOrderPointCriteria
import SGPT.PSH.SourceGenericLelongModificationConvergence

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.CompactPrimeNumerical

open Set Filter
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open BlowupTowers
open AnalyticModificationLocalDiscrepancy VariableComplexAtlas
  SquaredLogLelongSourceNormalization SGPT.PSH.CompactPrimeOver

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [ConnectedSpace X] [CompactSpace X]

omit [ConnectedSpace X] [CompactSpace X] in
private theorem genuine_of_sourceQPSH {u : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) : IsGlobalQuasiPshPotential (n := n) u := by
  obtain ⟨θ, hθ⟩ := hu
  exact ((isThetaPSH_iff_nativeThetaPotential θ u).mp hθ).quasiPshPotential

/-- The actual original QPSH reader on the actual DIRECT prime quotient. -/
def directSourceQPSHReader (u : X → EReal) (hu : (ofFixedModel n X).IsQPSH u) :
    DirectPrimeOver n X → ℝ≥0∞ := directReader u (genuine_of_sourceQPSH hu).1

theorem directSourceQPSHReader_mk (u : X → EReal)
    (hu : (ofFixedModel n X).IsQPSH u) (p : PrimePresentation n X) :
    directSourceQPSHReader u hu (Quot.mk commonResolutionRelation p) = presentationReader u p := rfl

omit [ConnectedSpace X] [CompactSpace X] in
/-- Actual every-proper-model point comparison yields whole-prime comparison;
the converse uses the genuinely included finite prime tests. Dimension zero
is explicit, with no nonexistent hypersurface presentation supplied. -/
theorem sourceIOrder_iff_presentationComparison {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIOrder (ofFixedModel n X) u v ↔
      ∀ p : PrimePresentation n X, presentationReader v p ≤ presentationReader u p := by
  cases n with
  | zero =>
      constructor
      · intro _hI p
        have hp : 0 < 0 := p.dimension_pos
        omega
      · intro _horder
        apply (sourceIOrder_iff_native hu hv).mpr
        exact ZeroDimensionalQuasiPshMultiplierIdeals.iOrderOnManifold_of_genuine_right
          u (genuine_of_sourceQPSH hv)
  | succ m =>
      constructor
      · intro hI p
        change (⨅ y ∈ p.divisor,
          (ofFixedModel (m + 1) p.model).sourceLelong (v ∘ p.projection) y) ≤
          ⨅ y ∈ p.divisor,
            (ofFixedModel (m + 1) p.model).sourceLelong (u ∘ p.projection) y
        exact iInf_mono fun y => iInf_mono fun _hy =>
          sourcePointComparison_of_sourceIOrder_on_analyticModification hu hv hI p.modification y
      · intro horder
        apply (sourceIOrder_iff_native hu hv).mpr
        apply (FiniteConnectedSmoothPrimeIdealOrder.iOrder_iff_all_finite_connected_smooth_prime_orders_of_genuine_right
          (genuine_of_sourceQPSH hu).1 (genuine_of_sourceQPSH hv)).mpr
        intro Y _ _ _ π hπ _hseq E hclosed hconn hhyper
        obtain ⟨k, hk, hreg⟩ := hhyper
        let p : PrimePresentation (m + 1) X :=
          { model := CMfd.of (n := m + 1) Y
            projection := π
            modification := hπ
            divisor := E
            divisorDimension := k
            smooth := ⟨hclosed, hconn, hreg⟩
            codimension_one := hk }
        apply (iInf_lelongNumber_le_iff_squaredLog (by omega : m + 1 ≠ 0)
          (fun y => u (π y)) (fun y => v (π y)) E).mpr
        simpa only [presentationReader, sourceGenericLelong, sourceLelong_ofFixedModel_eq,
          p, Function.comp_def] using horder p

/-- The original fifth clause now quantifies over the actual direct classes,
with the exact reader binding at EVERY representative. -/
theorem sourceIOrder_iff_directPrimeComparison {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIOrder (ofFixedModel n X) u v ↔
      ∀ q : DirectPrimeOver n X, directSourceQPSHReader v hv q ≤ directSourceQPSHReader u hu q := by
  constructor
  · intro hI q
    refine Quot.inductionOn q ?_
    intro p
    change presentationReader v p ≤ presentationReader u p
    exact (sourceIOrder_iff_presentationComparison hu hv).mp hI p
  · intro horder
    apply (sourceIOrder_iff_presentationComparison hu hv).mpr
    intro p
    exact horder (Quot.mk commonResolutionRelation p)

theorem sourceIEquivalent_iff_directPrimeEquality {u v : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) (hv : (ofFixedModel n X).IsQPSH v) :
    sourceIEquivalent (ofFixedModel n X) u v ↔
      ∀ q : DirectPrimeOver n X, directSourceQPSHReader u hu q = directSourceQPSHReader v hv q := by
  constructor
  · intro h q
    exact le_antisymm ((sourceIOrder_iff_directPrimeComparison hv hu).mp h.2 q)
      ((sourceIOrder_iff_directPrimeComparison hu hv).mp h.1 q)
  · intro h
    exact ⟨(sourceIOrder_iff_directPrimeComparison hu hv).mpr (fun q => (h q).ge),
      (sourceIOrder_iff_directPrimeComparison hv hu).mpr (fun q => (h q).le)⟩

/-- All five ORIGINAL comparison clauses, with clause5 on the actual direct
prime classes. Original compact Kahler base and genuine QPSH domain retained. -/
theorem source_five_way_criterion_on_direct_primes (omega : KahlerBackground n X)
    {u v : X → EReal} (hu : (ofFixedModel n X).IsQPSH u)
    (hv : (ofFixedModel n X).IsQPSH v) :
    (sourcePositiveIntegerOrder (n := n) u v ↔ sourceIOrder (ofFixedModel n X) u v) ∧
    (sourceIOrder (ofFixedModel n X) u v ↔ finiteModificationPointComparison (n := n) u v) ∧
    (sourceIOrder (ofFixedModel n X) u v ↔ kahlerModificationPointComparison (n := n) u v) ∧
    (sourceIOrder (ofFixedModel n X) u v ↔
      ∀ q : DirectPrimeOver n X, directSourceQPSHReader v hv q ≤ directSourceQPSHReader u hu q) := by
  exact ⟨sourcePositiveIntegerOrder_iff_sourceIOrder hu hv,
    sourceIOrder_iff_finiteModificationPointComparison hu hv,
    sourceIOrder_iff_kahlerModificationPointComparison omega hu hv,
    sourceIOrder_iff_directPrimeComparison hu hv⟩

section ThetaReader

variable [MeasurableSpace X] [BorelSpace X]

/-- The SAME actual direct reader on original theta-potentials, using their
internally supplied genuine quasi-PSH regularity. -/
def directThetaReader (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (a : SourceThetaPotentialL1 θ) : DirectPrimeOver n X → ℝ≥0∞ :=
  directReader a.val
    (((isThetaPSH_iff_nativeThetaPotential θ a.val).mp a.property).quasiPshPotential.1)

omit [MeasurableSpace X] [BorelSpace X] in
theorem directThetaReader_mk (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (a : SourceThetaPotentialL1 θ) (p : PrimePresentation n X) :
    directThetaReader θ a (Quot.mk commonResolutionRelation p) =
      (ofFixedModel n p.model).sourceGenericLelong (a.val ∘ p.projection) p.divisor := rfl

/-- Original thm:Lelongcont on actual DIRECT prime classes. All filters,
infinite values and n=0 are retained; theta's big-class premise is original. -/
theorem tendsto_directThetaReader_of_sourceSingularityTopology
    (omega : KahlerBackground n X) (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hlim : Tendsto w F (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology omega θ hbig) v)) (q : DirectPrimeOver n X) :
    Tendsto (fun i => directThetaReader θ (w i) q) F (𝓝 (directThetaReader θ v q)) := by
  refine Quot.inductionOn q ?_
  intro p
  change Tendsto (fun i => (ofFixedModel n p.model).sourceGenericLelong
      (fun y => (w i).val (p.projection y)) p.divisor) F
    (𝓝 ((ofFixedModel n p.model).sourceGenericLelong
      (fun y => v.val (p.projection y)) p.divisor))
  exact tendsto_sourceGenericLelong_comp_of_sourceSingularityTopology omega θ hbig
    p.modification F w v hlim p.divisor

end ThetaReader
end SGPT.PSH.CompactPrimeNumerical
