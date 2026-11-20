import SGPT.Trace.TwistedL2SingularFrameBound

/-!
# Local uniform frame bounds for the actual exhaustion sections

This connects the actual singular weighted error estimate to the Euclidean
mean-value estimate in a fixed chart and frame. The uniform bound is an output,
not an assumption.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]

/-- Actual weighted error estimates along an exhaustion produce an eventual
uniform bound on a smaller ball in the chosen genuine chart and frame. -/
theorem exists_eventually_uniform_frame_bound
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (L : HermitianHolomorphicLineBundle.{0, 0} n X)
    {ψ : X → EReal} (hqpsh : ManifoldQuasiPlurisubharmonic (n := n) ψ)
    (htop : ∀ x, ψ x ≠ ⊤) (hcl : IsClosed {x | ψ x = ⊥})
    (hAn : IsLocallyAnalyticNull (n := n) {x | ψ x = ⊥})
    {a b : X → ℝ} (ha0 : ∀ x, 0 < a x) (hb0 : ∀ x, 0 < b x)
    {M : ℝ} (hM : ∀ x, a x + b x ≤ M)
    {G : (x : X) → L.Fiber x} (hG : IsSmoothSectionOn L G univ)
    {U V : ℕ → Set X} (hUo : ∀ j, IsOpen (U j)) (hUm : Monotone U)
    (hVo : ∀ j, IsOpen (V j)) (hVm : Monotone V)
    (c : ComplexChart n X) (e : AtlasFrame L) (z : ComplexModel n) {R : ℝ} (hR : 0 < R)
    (hchart : closedBall z R ⊆ chartFrameDomain L c e)
    (hKU : ∃ j₀, (c.val.symm '' closedBall z R) \ {x | ψ x = ⊥} ⊆ U j₀)
    (hKV : ∃ j₀, c.val.symm '' closedBall z R ⊆ V j₀)
    {I : ℝ≥0∞} (hI : I < ⊤) (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) (V j))
    (hbound : ∀ j, (∫⁻ x in U j, ENNReal.ofReal
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I) :
    ∃ A : ℝ, ∀ᶠ j in atTop, ∀ w ∈ ball z (R / 2), ‖chartCoeff L c e (T j) w‖ ≤ A := by
  classical
  let := e.property
  set K : Set X := c.val.symm '' closedBall z R
  have hKt : closedBall z R ⊆ c.val.target := fun w hw => (hchart hw).1
  have hK : IsCompact K := (isCompact_closedBall z R).image_of_continuousOn
    (c.val.continuousOn_symm.mono hKt)
  obtain ⟨B, hB, hboundK⟩ := exists_eventually_uniform_local_sq_bound_including_poles
    hμ L hqpsh htop hcl hAn ha0 hb0 hM hG hUo hUm hK hKU hI T hbound
  obtain ⟨C, hC, hframe⟩ := exists_frame_coefficient_l2_bound hμ L c e z hR hchart
  obtain ⟨j₀, hj₀⟩ := hKV
  have hF : ∀ᶠ j in atTop, DifferentiableOn ℂ (chartCoeff L c e (T j)) (ball z R) ∧
      (∫⁻ w in ball z R, ENNReal.ofReal (‖chartCoeff L c e (T j) w‖ ^ 2)) ≤ C * B := by
    filter_upwards [hboundK, eventually_ge_atTop j₀] with j hj hj0
    have hKj : K ⊆ V j := hj₀.trans (hVm hj0)
    constructor
    · have hd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn
        e.val c (hVo j) (hT j)
      refine (hd.mono fun w hw => ?_).congr fun w hw => ?_
      · have hwK := ball_subset_closedBall hw
        exact ⟨(hchart hwK).1, hKj ⟨w, hwK, rfl⟩, (hchart hwK).2⟩
      · have hwK := ball_subset_closedBall hw
        exact (Trivialization.continuousLinearMapAt_apply_of_mem
          (R := ℂ) e.val (hchart hwK).2 _).symm
    · exact (hframe (V j) (hVo j) hKj (T j) (hT j)).trans (by gcongr)
  exact exists_eventually_uniform_norm_bound_of_ball_l2 hR
    (fun j => chartCoeff L c e (T j)) (ENNReal.mul_lt_top hC hB) hF


/-- At every point of every actual chart-frame domain, the original
exhaustion bounds manufacture an eventually holomorphic and uniformly bounded
family on one fixed Euclidean ball. -/
theorem exists_eventually_locally_bounded_frame_family
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
      (‖G x - T j x‖ ^ 2 * Real.exp (-(ψ x).toReal) / (a x + b x)) ∂μ) ≤ I)
    (c : ComplexChart n X) (e : AtlasFrame L) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) :
    ∃ r > 0, ∃ A : ℝ, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (chartCoeff L c e (T j)) (ball z r) ∧
        ∀ w ∈ ball z r, ‖chartCoeff L c e (T j) w‖ ≤ A := by
  classical
  let := e.property
  have hdomain : IsOpen (chartFrameDomain L c e) :=
    c.val.isOpen_inter_preimage_symm e.val.open_baseSet
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hdomain z hz
  have hhalf : 0 < R / 2 := half_pos hR
  have hchart : closedBall z (R / 2) ⊆ chartFrameDomain L c e :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRsub
  have hKt : closedBall z (R / 2) ⊆ c.val.target := fun w hw => (hchart hw).1
  have hK : IsCompact (c.val.symm '' closedBall z (R / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (c.val.continuousOn_symm.mono hKt)
  have hKU : c.val.symm '' closedBall z (R / 2) ⊆ ⋃ j, V j := by
    intro x _
    obtain ⟨j, hj⟩ := hcover x
    exact mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j₀, hj₀⟩ := hK.elim_directed_cover V hVo hKU (Monotone.directed_le hVm)
  have hUo : ∀ j, IsOpen (V j \ {x | ψ x = ⊥}) := fun j => (hVo j).sdiff hcl
  have hUm : Monotone (fun j => V j \ {x | ψ x = ⊥}) := fun i j hij x hx =>
    ⟨hVm hij hx.1, hx.2⟩
  have hpole : (c.val.symm '' closedBall z (R / 2)) \ {x | ψ x = ⊥} ⊆
      V j₀ \ {x | ψ x = ⊥} := fun x hx => ⟨hj₀ hx.1, hx.2⟩
  obtain ⟨A, hA⟩ := exists_eventually_uniform_frame_bound hμ L hqpsh htop hcl hAn
    ha0 hb0 hM hG hUo hUm hVo hVm c e z hhalf hchart ⟨j₀, hpole⟩
    ⟨j₀, hj₀⟩ hI T hT hbound
  refine ⟨(R / 2) / 2, half_pos hhalf, A, ?_⟩
  filter_upwards [hA, eventually_ge_atTop j₀] with j hj hj0
  refine ⟨?_, hj⟩
  have hd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn
    e.val c (hVo j) (hT j)
  refine (hd.mono fun w hw => ?_).congr fun w hw => ?_
  · have hwK : w ∈ closedBall z (R / 2) :=
      ball_subset_closedBall ((ball_subset_ball (half_le_self hhalf.le)) hw)
    exact ⟨(hchart hwK).1, hVm hj0 (hj₀ ⟨w, hwK, rfl⟩), (hchart hwK).2⟩
  · have hwK : w ∈ closedBall z (R / 2) :=
      ball_subset_closedBall ((ball_subset_ball (half_le_self hhalf.le)) hw)
    exact (Trivialization.continuousLinearMapAt_apply_of_mem
      (R := ℂ) e.val (hchart hwK).2 _).symm

end SGPT.Trace.TwistedL2
