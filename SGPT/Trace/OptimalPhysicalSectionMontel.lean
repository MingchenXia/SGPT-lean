import SGPT.Trace.TwistedL2SingularGlue

/-!
# Actual global physical section compactness from original local L2 bounds

The original physical bound produces all frame bounds, subsequence, local
limits and global holomorphic gluing; these are never supplied as outcomes.
Blueprint: work/sgpt-resume-20261114/bert-e2-physical-montel/blueprint/bert-e2-physical-montel.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalPhysicalSectionMontel
open Set Filter MeasureTheory Bundle Metric
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle SGPT.Trace.TwistedL2

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)
  (T : ℕ → (x : X) → L.Fiber x)
  (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) univ)
  (hL2 : ∀ K : Set X, IsCompact K → ∃ B : ℝ≥0∞, B < ⊤ ∧
    ∀ j, (∫⁻ x in K, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) ≤ B)

include hμ hT hL2

theorem exists_locally_bounded_original_frames
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
  obtain ⟨B, hB, hbound⟩ := hL2 _ hK
  obtain ⟨C, hC, hframe⟩ := exists_frame_coefficient_l2_bound hμ L c e z hhalf hchart
  have hcoeff : ∀ j, DifferentiableOn ℂ (chartCoeff L c e (T j)) (ball z (R / 2)) := by
    intro j
    have hd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn
      e.val c isOpen_univ (hT j)
    refine (hd.mono fun w hw => ?_).congr fun w hw => ?_
    · exact ⟨(hchart (ball_subset_closedBall hw)).1, mem_univ _,
        (hchart (ball_subset_closedBall hw)).2⟩
    · exact (Trivialization.continuousLinearMapAt_apply_of_mem
        (R := ℂ) e.val (hchart (ball_subset_closedBall hw)).2 _).symm
  have hbound' : ∀ᶠ j in atTop,
      DifferentiableOn ℂ (chartCoeff L c e (T j)) (ball z (R / 2)) ∧
      (∫⁻ w in ball z (R / 2), ENNReal.ofReal (‖chartCoeff L c e (T j) w‖ ^ 2)) ≤ C * B :=
    Filter.Eventually.of_forall fun j => ⟨hcoeff j,
      (hframe univ isOpen_univ (subset_univ _) (T j) (hT j)).trans
        (mul_le_mul_of_nonneg_left (hbound j) zero_le)⟩
  obtain ⟨A, hA⟩ := exists_eventually_uniform_norm_bound_of_ball_l2 hhalf
    (fun j => chartCoeff L c e (T j)) (ENNReal.mul_lt_top hC hB) hbound'
  refine ⟨(R / 2) / 2, half_pos hhalf, A, hA.mono fun j hj => ⟨?_, hj⟩⟩
  exact (hcoeff j).mono (ball_subset_ball (half_le_self hhalf.le))

theorem exists_original_frame_dense_diagonal :
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
  have hf : ∀ p ∈ (univ : Set J), ∃ A : ℝ, ∀ᶠ j in atTop, ‖f j p‖ ≤ A := by
    rintro ⟨y, q⟩ _
    obtain ⟨r, hr, A, hA⟩ := exists_locally_bounded_original_frames hμ L T hT hL2
      (complexChartAt (n := n) y.val) (preferredAtlasFrame L y.val) ((hQ y).1 q.property)
    exact ⟨A, hA.mono fun j hj => hj.2 q.val (mem_ball_self hr)⟩
  obtain ⟨σ, hσ, hlim⟩ := exists_strictMono_tendsto_of_eventually_norm_le
    (Set.to_countable (univ : Set J)) f hf
  refine ⟨D, hD, Q, σ, hDc, hQ, hσ, ?_⟩
  intro y q
  simpa only [f] using hlim ⟨y, q⟩ (mem_univ _)

theorem exists_original_locally_uniform_frames :
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
    exists_original_frame_dense_diagonal hμ L T hT hL2
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
    obtain ⟨r, hr, A, hA⟩ := exists_locally_bounded_original_frames hμ L T hT hL2 c e hz
    exact ⟨r, hr, A, hσ.tendsto_atTop.eventually hA⟩
  have hQdense : chartFrameDomain L c e ⊆ closure (Q y) := (hQ y).2.2
  have hQlim : ∀ q ∈ Q y, CauchySeq (fun j => chartCoeff L c e (T (σ j)) q) := by
    intro q hq
    obtain ⟨a, ha⟩ := hlim y ⟨q, hq⟩
    exact ha.cauchySeq
  exact holomorphic_limit_of_eventually_bounded_of_cauchy_dense hdom
    (fun j => chartCoeff L c e (T (σ j))) hf hQdense hQlim

theorem exists_original_global_holomorphic_limit
    (A : Set X) (F : (x : X) → L.Fiber x) (htrace : ∀ j x, x ∈ A → T j x = F x) :
    ∃ (σ : ℕ → ℕ) (S : (x : X) → L.Fiber x), StrictMono σ ∧
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∀ G : (x : X) → L.Fiber x, ∀ x,
        Tendsto (fun j => ‖G x - T (σ j) x‖) atTop (𝓝 ‖G x - S x‖)) ∧
      ∀ x ∈ A, S x = F x := by
  obtain ⟨D, σ, G, hcov, hσ, hG⟩ := exists_original_locally_uniform_frames hμ L T hT hL2
  obtain ⟨S, hS, _, hnorm⟩ := exists_holomorphic_section_of_frame_limits L D hcov
    (fun j => T (σ j)) G (fun y => ⟨(hG y).1, (hG y).2.2⟩)
  refine ⟨σ, S, hσ, hS, hnorm, ?_⟩
  intro x hx
  have hc : Tendsto (fun j => ‖F x - T (σ j) x‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [htrace _ x hx, sub_self, norm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hzero : ‖F x - S x‖ = 0 := tendsto_nhds_unique (hnorm F x) hc
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

end SGPT.Trace.OptimalPhysicalSectionMontel
