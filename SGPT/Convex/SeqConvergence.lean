import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.UniformConvergence

noncomputable section
namespace SGPT.Convex
open Set Filter Metric
open scoped Topology
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine finite subset already surrounds every actual interior point of a convex hull. -/
theorem exists_finite_hull_neighborhood {D : Set E} {x : E}
    (hx : x ∈ interior (convexHull ℝ D)) :
    ∃ T : Finset E, (↑T : Set E) ⊆ D ∧ x ∈ interior (convexHull ℝ (↑T : Set E)) := by
  classical
  obtain ⟨b, hxb, hb⟩ := exists_mem_interior_convexHull_affineBasis
    (isOpen_interior.mem_nhds hx)
  have hchoose : ∀ i, ∃ T : Finset E, (↑T : Set E) ⊆ D ∧
      b i ∈ convexHull ℝ (↑T : Set E) := by
    intro i
    have hi := hb (subset_convexHull ℝ _ (mem_range_self i))
    have hi' : b i ∈ convexHull ℝ D := interior_subset hi
    rw [convexHull_eq_union_convexHull_finite_subsets] at hi'
    simpa only [mem_iUnion, exists_prop] using hi'
  choose T hTD hbT using hchoose
  let U := Finset.univ.biUnion T
  have hU : (↑U : Set E) ⊆ D := by
    intro y hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hy
    exact hTD i hi
  have hTU (i) : (↑(T i) : Set E) ⊆ U := by
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hy⟩
  have hbU : range b ⊆ convexHull ℝ (↑U : Set E) := by
    rintro _ ⟨i, rfl⟩
    exact convexHull_mono (hTU i) (hbT i)
  exact ⟨U, hU, interior_mono
    (convexHull_min hbU (convex_convexHull ℝ _)) hxb⟩

/-- Actual dense points in an original open set supply a genuine finite convex-hull neighborhood of every original point. -/
theorem exists_finite_dense_hull_neighborhood {C D : Set E} (hC : IsOpen C)
    (hdense : C ⊆ closure D) {x : E} (hx : x ∈ C) :
    ∃ T : Finset E, (↑T : Set E) ⊆ D ∧ x ∈ interior (convexHull ℝ (↑T : Set E)) := by
  have hCD : C ⊆ (affineSpan ℝ D : Set E) := hdense.trans
    ((affineSpan ℝ D).closed_of_finiteDimensional.closure_subset_iff.mpr
      (subset_affineSpan ℝ D))
  have hspan : affineSpan ℝ D = ⊤ := by
    apply top_unique
    have h := affineSpan_le.mpr hCD
    rwa [hC.affineSpan_eq_top ⟨x, hx⟩] at h
  have hne : (interior (convexHull ℝ D)).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hCC : C ⊆ closure (convexHull ℝ D) :=
    hdense.trans (closure_mono (subset_convexHull ℝ D))
  have hx' : x ∈ interior (closure (convexHull ℝ D)) :=
    interior_mono hCC (by simpa only [hC.interior_eq] using hx)
  rw [(convex_convexHull ℝ D).interior_closure_eq_interior_of_nonempty_interior hne] at hx'
  exact exists_finite_hull_neighborhood hx'

/-- Actual upper bounds at the genuine dense vertices produce one shared upper bound on an actual original neighborhood. -/
theorem exists_local_uniform_upper_bound_of_dense_bounds {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hbound : ∀ d ∈ D, BddAbove (range (fun k ↦ f k d))) {x : E} (hx : x ∈ C) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ C ∧
      ∃ M : ℝ, ∀ k, ∀ y ∈ ball x r, f k y ≤ M := by
  classical
  obtain ⟨T, hTD, hxT⟩ := exists_finite_dense_hull_neighborhood hC hdense hx
  let M : ℝ := ∑ d ∈ T, max 0 (sSup (range (fun k ↦ f k d)))
  have hvertex (k : ℕ) {d : E} (hd : d ∈ T) : f k d ≤ M := by
    have hval := le_csSup (hbound d (hTD hd)) (mem_range_self k)
    have hsum : max 0 (sSup (range (fun k ↦ f k d))) ≤ M :=
      Finset.single_le_sum
        (f := fun y ↦ max (0 : ℝ) (sSup (range (fun k ↦ f k y))))
        (fun y _ ↦ le_max_left (0 : ℝ) _) hd
    exact hval.trans ((le_max_right 0 _).trans hsum)
  have hhull (k : ℕ) {y : E} (hy : y ∈ convexHull ℝ (↑T : Set E)) :
      y ∈ C ∧ f k y ≤ M := by
    apply convexHull_min (t := {z | z ∈ C ∧ f k z ≤ M}) _ ((hf k).convex_le M) hy
    intro d hd
    exact ⟨hDC (hTD hd), hvertex k hd⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxT)
  exact ⟨r, hr, (fun y hy ↦ (hhull 0 (hball hy)).1), M,
    fun k y hy ↦ (hhull k (hball hy)).2⟩

/-- One actual nearby dense anchor and its genuine reflected secants turn the true shared upper bound into a shared absolute-value bound. -/
theorem exists_local_uniform_abs_bound_of_dense_bounds {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hupper : ∀ d ∈ D, BddAbove (range (fun k ↦ f k d)))
    (hlower : ∀ d ∈ D, BddBelow (range (fun k ↦ f k d))) {x : E} (hx : x ∈ C) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ C ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k, ∀ y ∈ ball x r, |f k y| ≤ M := by
  obtain ⟨r, hr, hballC, M, hM⟩ :=
    exists_local_uniform_upper_bound_of_dense_bounds hC hDC hdense hf hupper hx
  obtain ⟨d, hdD, hxd⟩ := Metric.mem_closure_iff.mp (hdense hx) (r / 4) (by positivity)
  obtain ⟨L, hL⟩ := hlower d hdD
  let N : ℝ := |M| + |2 * L - M|
  have hsmall : ball x (r / 4) ⊆ ball x r := ball_subset_ball (by linarith)
  refine ⟨r / 4, by positivity, hsmall.trans hballC, N,
    add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro k y hy
  let z := (2 : ℝ) • d - y
  have hdist : dist z x ≤ 2 * dist d x + dist y x := by
    calc
      dist z x = dist (d + (d - y)) (x + 0) := by
        simp only [z, two_smul, sub_eq_add_neg, add_zero, add_assoc]
      _ ≤ dist d x + dist (d - y) 0 := dist_add_add_le _ _ _ _
      _ = dist d x + dist d y := by simp only [dist_eq_norm, sub_zero]
      _ ≤ dist d x + (dist d x + dist x y) :=
        add_le_add le_rfl (dist_triangle d x y)
      _ = 2 * dist d x + dist y x := by rw [dist_comm x y]; ring
  have hz : z ∈ ball x r := by
    rw [mem_ball]
    have hy' : dist y x < r / 4 := hy
    rw [dist_comm x d] at hxd
    linarith
  have heq : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • z = d := by
    dsimp [z]
    rw [smul_sub, smul_smul]
    norm_num
  have hmid := (hf k).2 (hballC (hsmall hy)) (hballC hz)
    (by positivity : (0 : ℝ) ≤ 1 / 2) (by positivity : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [heq] at hmid
  simp only [smul_eq_mul] at hmid
  have hlow : 2 * L - M ≤ f k y := by
    have hLd := hL (mem_range_self k)
    have hMz := hM k z hz
    linarith
  apply abs_le.mpr
  constructor
  · have habs := neg_abs_le (2 * L - M)
    have hnonneg := abs_nonneg M
    dsimp [N]
    linarith
  · have habs := le_abs_self M
    have hnonneg := abs_nonneg (2 * L - M)
    have hMy := hM k y (hsmall hy)
    dsimp [N]
    linarith

/-- Genuine finite dense-point convergence constructs a shared local Lipschitz constant for the entire original convex sequence. -/
theorem exists_local_uniform_lipschitz_of_dense_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l))
    {x : E} (hx : x ∈ C) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ C ∧
      ∃ K : NNReal, ∀ k, LipschitzOnWith K (f k) (ball x r) := by
  have hupper (d : E) (hd : d ∈ D) : BddAbove (range (fun k ↦ f k d)) := by
    obtain ⟨l, hl⟩ := hconv d hd
    exact hl.cauchySeq.isBounded_range.bddAbove
  have hlower (d : E) (hd : d ∈ D) : BddBelow (range (fun k ↦ f k d)) := by
    obtain ⟨l, hl⟩ := hconv d hd
    exact hl.cauchySeq.isBounded_range.bddBelow
  obtain ⟨r, hr, hballC, M, _, hM⟩ :=
    exists_local_uniform_abs_bound_of_dense_bounds hC hDC hdense hf hupper hlower hx
  refine ⟨r / 2, by positivity, (ball_subset_ball (by linarith)).trans hballC,
    (2 * M / (r / 2)).toNNReal, ?_⟩
  intro k
  have h := ((hf k).subset hballC (convex_ball x r)).lipschitzOnWith_of_abs_le
    (by positivity : 0 < r / 2) (fun y hy ↦ hM k y hy)
  simpa only [show r - r / 2 = r / 2 by ring] using h

/-- Genuine local Lipschitz control and actual dense-point limits make every original point's values Cauchy. -/
theorem cauchySeq_of_dense_convex_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l))
    {x : E} (hx : x ∈ C) : CauchySeq (fun k ↦ f k x) := by
  obtain ⟨r, hr, _, K, hK⟩ :=
    exists_local_uniform_lipschitz_of_dense_convergence hC hDC hdense hf hconv hx
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ : ℝ := min (r / 2) (ε / (4 * ((K : ℝ) + 1)))
  have hden : 0 < 4 * ((K : ℝ) + 1) := by positivity
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ ≤ r / 2 := min_le_left _ _
  have hKδ : (K : ℝ) * δ < ε / 4 := by
    have hδbound : δ ≤ ε / (4 * ((K : ℝ) + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ hden).mp hδbound
    nlinarith
  obtain ⟨d, hdD, hxd⟩ := Metric.mem_closure_iff.mp (hdense hx) δ hδ
  have hxball : x ∈ ball x r := mem_ball_self hr
  have hdball : d ∈ ball x r := by
    rw [mem_ball, dist_comm]
    linarith
  have hnear (k : ℕ) : dist (f k x) (f k d) < ε / 4 :=
    ((hK k).dist_le_mul x hxball d hdball).trans_lt
      ((mul_le_mul_of_nonneg_left hxd.le K.coe_nonneg).trans_lt hKδ)
  obtain ⟨l, hl⟩ := hconv d hdD
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hl.cauchySeq (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hmn := hN m hm n hn
  have htri := dist_triangle (f m x) (f m d) (f n x)
  have htri' := dist_triangle (f m d) (f n d) (f n x)
  have hmnear := hnear m
  have hnnear := hnear n
  rw [dist_comm (f n x) (f n d)] at hnnear
  linarith

/-- Actual completeness produces finite real limits everywhere from only the original finite dense-point limits. -/
theorem exists_pointwise_limit_of_dense_convex_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l)) :
    ∃ g : E → ℝ, ∀ x ∈ C, Tendsto (fun k ↦ f k x) atTop (𝓝 (g x)) := by
  classical
  have hlim (x : C) : ∃ l : ℝ, Tendsto (fun k ↦ f k x) atTop (𝓝 l) :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_dense_convex_convergence hC hDC hdense hf hconv x.property)
  choose g hg using hlim
  refine ⟨fun x ↦ if hx : x ∈ C then g ⟨x, hx⟩ else 0, ?_⟩
  intro x hx
  simpa only [dif_pos hx] using hg ⟨x, hx⟩

/-- The actual constructed local Lipschitz neighborhoods produce genuine equicontinuity at every original domain point. -/
theorem equicontinuousAt_of_dense_convex_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l))
    {x : E} (hx : x ∈ C) : EquicontinuousAt f x := by
  obtain ⟨r, hr, _, K, hK⟩ :=
    exists_local_uniform_lipschitz_of_dense_convergence hC hDC hdense hf hconv hx
  have hlocal := (LipschitzOnWith.uniformEquicontinuousOn f K hK).equicontinuousOn
    x (mem_ball_self hr)
  rw [equicontinuousWithinAt_iff_continuousWithinAt] at hlocal
  rw [equicontinuousAt_iff_continuousAt]
  exact hlocal.continuousAt (ball_mem_nhds x hr)

omit [FiniteDimensional ℝ E] in
/-- Actual pointwise limits preserve each original convex inequality and the genuine original domain. -/
theorem convexOn_of_pointwise_tendsto {C : Set E} {f : ℕ → E → ℝ} {g : E → ℝ}
    (hf : ∀ k, ConvexOn ℝ C (f k))
    (hlim : ∀ x ∈ C, Tendsto (fun k ↦ f k x) atTop (𝓝 (g x))) : ConvexOn ℝ C g := by
  refine ⟨(hf 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz := (hf 0).1 hx hy ha hb hab
  exact le_of_tendsto_of_tendsto (hlim _ hz)
    (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b))
    (Eventually.of_forall (fun k ↦ (hf k).2 hx hy ha hb hab))

/-- Genuine Ascoli converts the produced original equicontinuity and actual pointwise limits into true uniform convergence on every original compact subset. -/
theorem tendstoUniformlyOn_of_dense_convex_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} {g : E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l))
    (hlim : ∀ x ∈ C, Tendsto (fun k ↦ f k x) atTop (𝓝 (g x)))
    {K : Set E} (hK : IsCompact K) (hKC : K ⊆ C) : TendstoUniformlyOn f g atTop K := by
  have hEK : EquicontinuousOn f K := fun x hx ↦
    (equicontinuousAt_of_dense_convex_convergence hC hDC hdense hf hconv (hKC hx)).equicontinuousWithinAt K
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hER : Equicontinuous (fun k ↦ K.domRestrict (f k)) :=
    (equicontinuous_restrict_iff f).mpr hEK
  have hp : Tendsto (fun k ↦ K.domRestrict (f k)) atTop (𝓝 (K.domRestrict g)) :=
    tendsto_pi_nhds.mpr (fun x ↦ hlim x (hKC x.property))
  have hu := (hER.tendsto_uniformFun_iff_pi atTop (K.domRestrict g)).mpr hp
  have h := UniformFun.tendsto_iff_tendstoUniformly.mp hu
  exact tendstoUniformlyOn_iff_restrict.mpr h

/-- Full exact source `thm:seqconv`: the actual finite dense-point limits produce a convex real limit everywhere and genuine uniform convergence on every original compact subset. -/
theorem exists_convex_limit_of_dense_convex_convergence {C D : Set E}
    (hC : IsOpen C) (hDC : D ⊆ C) (hdense : C ⊆ closure D)
    {f : ℕ → E → ℝ} (hf : ∀ k, ConvexOn ℝ C (f k))
    (hconv : ∀ d ∈ D, ∃ l : ℝ, Tendsto (fun k ↦ f k d) atTop (𝓝 l)) :
    ∃ g : E → ℝ, ConvexOn ℝ C g ∧
      (∀ x ∈ C, Tendsto (fun k ↦ f k x) atTop (𝓝 (g x))) ∧
      ∀ K : Set E, IsCompact K → K ⊆ C → TendstoUniformlyOn f g atTop K := by
  obtain ⟨g, hg⟩ := exists_pointwise_limit_of_dense_convex_convergence hC hDC hdense hf hconv
  exact ⟨g, convexOn_of_pointwise_tendsto hf hg, hg,
    fun _ hK hKC ↦ tendstoUniformlyOn_of_dense_convex_convergence hC hDC hdense hf hconv hg hK hKC⟩

end SGPT.Convex
