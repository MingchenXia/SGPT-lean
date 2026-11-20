import SGPT.Trace.TwistedL2SingularDiagonal
import SGPT.Trace.TwistedL2SingularCauchyLimit

/-!
# Simultaneous holomorphic limits in actual local frames

The original weighted estimates supply a single subsequence whose coefficients in
all members of a countable chart-frame cover converge locally uniformly to genuine
holomorphic functions. No local limit data are assumed.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- One common subsequence has holomorphic locally uniform limits in every
frame of an actual countable cover. -/
theorem exists_frame_locally_uniform_subsequence
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    (hAn : IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {V : ℕ → Set X} (hVo : ∀ j, IsOpen (V j)) (hVm : Monotone V)
    (hcover : ∀ x : X, ∃ j, x ∈ V j)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) (V j))
    (hbound : ∀ j, (∫⁻ x in V j \ {x | ψ x = ⊥}, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ (D : Set X) (σ : ℕ → ℕ)
      (F : D → ComplexModel n → ℂ),
      (∀ x : X, ∃ y ∈ D, x ∈ preferredChartFrameDomain L y) ∧ StrictMono σ ∧
      ∀ y : D,
        DifferentiableOn ℂ (F y)
          (chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val)) ∧
        TendstoLocallyUniformlyOn
          (fun j => chartCoeff L (complexChartAt (n := n) y.val)
            (preferredAtlasFrame L y.val) (T (σ j))) (F y) atTop
          (chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val)) ∧
        ∀ z ∈ chartFrameDomain L (complexChartAt (n := n) y.val)
            (preferredAtlasFrame L y.val),
          Tendsto (fun j => chartCoeff L (complexChartAt (n := n) y.val)
            (preferredAtlasFrame L y.val) (T (σ j)) z) atTop (𝓝 (F y z)) := by
  classical
  obtain ⟨D, hD, Q, σ, hcoverD, hQ, hσ, hlim⟩ :=
    exists_frame_dense_diagonal_subsequence hμ L hqpsh htop hcl hAn ha0 hb0 hM
      hG hVo hVm hcover hI T hT hbound
  let F : D → ComplexModel n → ℂ := fun y z => limUnder atTop fun j =>
    chartCoeff L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val) (T (σ j)) z
  refine ⟨D, σ, F, hcoverD, hσ, ?_⟩
  intro y
  let c : ComplexChart n X := complexChartAt (n := n) y.val
  let e : AtlasFrame L := preferredAtlasFrame L y.val
  have hdom : IsOpen (chartFrameDomain L c e) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  have hf : ∀ z ∈ chartFrameDomain L c e, ∃ r > 0, ∃ A : ℝ, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (chartCoeff L c e (T (σ j))) (ball z r) ∧
        ∀ w ∈ ball z r, ‖chartCoeff L c e (T (σ j)) w‖ ≤ A := by
    intro z hz
    obtain ⟨r, hr, A, hA⟩ := exists_eventually_locally_bounded_frame_family
      hμ L hqpsh htop hcl hAn ha0 hb0 hM hG hVo hVm hcover hI T hT hbound c e hz
    exact ⟨r, hr, A, hσ.tendsto_atTop.eventually hA⟩
  have hQdense : chartFrameDomain L c e ⊆ closure (Q y) := (hQ y).2.2
  have hQlim : ∀ q ∈ Q y, CauchySeq (fun j => chartCoeff L c e (T (σ j)) q) := by
    intro q hq
    obtain ⟨a, ha⟩ := hlim y ⟨q, hq⟩
    exact ha.cauchySeq
  exact holomorphic_limit_of_eventually_bounded_of_cauchy_dense hdom
    (fun j => chartCoeff L c e (T (σ j))) hf hQdense hQlim

end SGPT.Trace.TwistedL2
