import SGPT.TestCurve.TCOriginalBookDH

/-! Complete original source/BHJ comparison with a strictly positive ACTUAL geometric weight
measure in EVERY cofinal-tail original degree. No zero-mass normalization fallback is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.OriginalBookDH
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov SGPT.TestCurve.GeomLin SGPT.TestCurve.TCEnc
open scoped Topology ENNReal NNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  [IsIntegral X] {n : ℕ} [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance positiveDHTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance positiveDHCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance positiveDHManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance positiveDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance positiveDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- Entire original rmk:NApotential:L862 with genuine BHJ probabilities N_k^-1 W_k on EVERY
sufficiently large original integer degree. Actual original ampleness produces N_k>0 internally. -/
theorem geomLinearized_book_DH_positive_tail (H : SchemeLineBundleMetric f n E L)
    (T : GeomLinearizedTestConfiguration f a) (hA : T.IsAmple) (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let F := T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)
  ∃ (μ : FiniteMeasure ℝ) (ν : ProbabilityMeasure ℝ) (B : ℕ) (W : ℕ → FiniteMeasure ℝ),
    (∀ j, (W j : Measure ℝ) = CentralFiber.geometricCentralWeightMeasure
      T.toTestConfiguration T.linearization (B+j+1)) ∧
    (∀ j, (W j).mass = (h0 f L (B+j+1) : ℝ≥0)) ∧
    (∀ j, 0 < (W j).mass) ∧
    (∀ j, ((W j).normalize : Measure ℝ) =
      (h0 f L (B+j+1) : ℝ≥0∞)⁻¹ • CentralFiber.geometricCentralWeightMeasure
        T.toTestConfiguration T.linearization (B+j+1)) ∧
    Tendsto (fun j => (W j).normalize) atTop (𝓝 ν) ∧
    (μ.mass : ℝ) = P.selfIntersection n ∧
    μ = (P.selfIntersection n).toNNReal • ν.toFiniteMeasure ∧
    ∀ (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      (μ : Measure ℝ) = originalFiltrationDH E F H P Y hY := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  obtain ⟨μ, ν, B₀, W₀, hW₀, hm₀, hlim, hm, hscale, hall⟩ := geomLinearized_book_DH E H T hA P
  obtain ⟨C, hC⟩ := eventually_atTop.mp (P.eventually_h0_pos a)
  let B := B₀+C
  let W (j : ℕ) := W₀ (C+j)
  have hW (j : ℕ) : (W j : Measure ℝ) = CentralFiber.geometricCentralWeightMeasure
      T.toTestConfiguration T.linearization (B+j+1) := by
    simpa only [W, B, Nat.add_assoc] using hW₀ (C+j)
  have hmass (j : ℕ) : (W j).mass = (h0 f L (B+j+1) : ℝ≥0) := by
    simpa only [W, B, Nat.add_assoc] using hm₀ (C+j)
  have hpos (j : ℕ) : 0 < (W j).mass := by
    rw [hmass]
    exact_mod_cast hC (B+j+1) (by dsimp only [B]; omega)
  have hprob (j : ℕ) : ((W j).normalize : Measure ℝ) =
      (h0 f L (B+j+1) : ℝ≥0∞)⁻¹ • CentralFiber.geometricCentralWeightMeasure
        T.toTestConfiguration T.linearization (B+j+1) := by
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _
      ((FiniteMeasure.mass_nonzero_iff _).mp (hpos j).ne')]
    rw [hW j]
    change ((↑((W j).mass⁻¹) : ℝ≥0∞)) •
      CentralFiber.geometricCentralWeightMeasure T.toTestConfiguration T.linearization (B+j+1) = _
    rw [ENNReal.coe_inv (hpos j).ne', hmass j, ENNReal.coe_natCast]
  refine ⟨μ, ν, B, W, hW, hmass, hpos, hprob, ?_, hm, hscale, hall⟩
  have ht := hlim.comp (tendsto_add_atTop_nat C)
  apply ht.congr
  intro j
  simp only [Function.comp_apply, W, Nat.add_comm]

end SGPT.TestCurve.OriginalBookDH
