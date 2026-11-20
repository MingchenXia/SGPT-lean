import SGPT.Trace.TwistedL2SingularCountable
import SGPT.Foundations.Analysis.Pending.HolomorphicNormalFamilies

/-!
# One common subsequence of actual local frame values

From the original exhaustion sections and their weighted `L²` bounds, choose
countably many actual charts and frames, dense sets in their coordinate domains,
and one strict subsequence on which all those frame coefficients converge.
No convergence or local boundedness certificate is an input.
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

/-- A single strict subsequence converges at every point of a countable dense
set in each of countably many genuine chart-frame domains covering `X`. -/
theorem exists_frame_dense_diagonal_subsequence
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
    ∃ (D : Set X) (_hD : D.Countable) (Q : D → Set (ComplexModel n)) (σ : ℕ → ℕ),
      (∀ x : X, ∃ y ∈ D, x ∈ preferredChartFrameDomain L y) ∧
      (∀ y : D, Q y ⊆ chartFrameDomain L (complexChartAt (n := n) y.val)
          (preferredAtlasFrame L y.val) ∧ (Q y).Countable ∧
        chartFrameDomain L (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val) ⊆
          closure (Q y)) ∧ StrictMono σ ∧
      ∀ (y : D) (q : Q y), ∃ a : ℂ,
        Tendsto (fun j => chartCoeff L (complexChartAt (n := n) y.val)
          (preferredAtlasFrame L y.val) (T (σ j)) q.val) atTop (𝓝 a) := by
  classical
  obtain ⟨D, hD, hDc, Q, hQ⟩ := exists_countable_frame_dense_sets L
  let : Countable D := hD.to_subtype
  let (y : D) : Countable (Q y) := (hQ y).2.1.to_subtype
  let J := Σ y : D, Q y
  let f : ℕ → J → ℂ := fun j p =>
    chartCoeff L (complexChartAt (n := n) p.1.val) (preferredAtlasFrame L p.1.val) (T j) p.2.val
  have hUo : ∀ j, IsOpen (V j \ {x | ψ x = ⊥}) := fun j => (hVo j).sdiff hcl
  have hUm : Monotone (fun j => V j \ {x | ψ x = ⊥}) := fun i j hij x hx =>
    ⟨hVm hij hx.1, hx.2⟩
  have hf : ∀ p ∈ (univ : Set J), ∃ A : ℝ, ∀ᶠ j in atTop, ‖f j p‖ ≤ A := by
    rintro ⟨y, q⟩ _
    let c : ComplexChart n X := complexChartAt (n := n) y.val
    let e : AtlasFrame L := preferredAtlasFrame L y.val
    have hdomain : IsOpen (chartFrameDomain L c e) :=
      c.val.isOpen_inter_preimage_symm e.val.open_baseSet
    have hq : q.val ∈ chartFrameDomain L c e := (hQ y).1 q.property
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hdomain q.val hq
    have hhalf : 0 < R / 2 := half_pos hR
    have hchart : closedBall q.val (R / 2) ⊆ chartFrameDomain L c e :=
      (closedBall_subset_ball (half_lt_self hR)).trans hRsub
    have hKt : closedBall q.val (R / 2) ⊆ c.val.target := fun w hw => (hchart hw).1
    have hK : IsCompact (c.val.symm '' closedBall q.val (R / 2)) :=
      (isCompact_closedBall _ _).image_of_continuousOn (c.val.continuousOn_symm.mono hKt)
    have hKU : c.val.symm '' closedBall q.val (R / 2) ⊆ ⋃ j, V j := by
      intro x _
      obtain ⟨j, hj⟩ := hcover x
      exact mem_iUnion.mpr ⟨j, hj⟩
    obtain ⟨j₀, hj₀⟩ := hK.elim_directed_cover V hVo hKU (Monotone.directed_le hVm)
    have hpole : (c.val.symm '' closedBall q.val (R / 2)) \ {x | ψ x = ⊥} ⊆
        V j₀ \ {x | ψ x = ⊥} := fun x hx => ⟨hj₀ hx.1, hx.2⟩
    obtain ⟨A, hA⟩ := exists_eventually_uniform_frame_bound hμ L hqpsh htop hcl hAn
      ha0 hb0 hM hG hUo hUm hVo hVm c e q.val hhalf hchart ⟨j₀, hpole⟩
      ⟨j₀, hj₀⟩ hI T hT hbound
    refine ⟨A, hA.mono fun j hj => ?_⟩
    exact hj q.val (mem_ball_self (half_pos hhalf))
  obtain ⟨σ, hσ, hlim⟩ := exists_strictMono_tendsto_of_eventually_norm_le
    (Set.to_countable (univ : Set J)) f hf
  refine ⟨D, hD, Q, σ, hDc, hQ, hσ, ?_⟩
  intro y q
  simpa only [f] using hlim ⟨y, q⟩ (mem_univ _)

end SGPT.Trace.TwistedL2
