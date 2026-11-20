import SGPT.Okounkov.LegendreEnergy
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section

namespace SGPT.Okounkov.TestCurve

open Set Filter Metric
open scoped Topology Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Genuine point approximants for an arbitrary original Hausdorff net. -/
theorem exists_members_tendsto {J : Type*} {F : Filter J}
    {u : J → ConvexBody V} {K : ConvexBody V}
    (hu : Tendsto u F (𝓝 K)) {x : V} (hx : x ∈ K) :
    ∃ v : J → V, (∀ i, v i ∈ u i) ∧ Tendsto v F (𝓝 x) := by
  have hc : Continuous (fun B : ConvexBody V ↦ infDist x (B : Set V)) :=
    (Metric.lipschitz_infDist_set x).continuous.comp
      SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous
  have ht := hc.tendsto K |>.comp hu
  rw [infDist_zero_of_mem hx] at ht
  choose v hv hd using fun i ↦ (u i).isCompact.exists_infDist_eq_dist (u i).nonempty x
  refine ⟨v, hv, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  change Tendsto (fun i ↦ infDist x (u i : Set V)) F (𝓝 0) at ht
  convert ht using 1
  funext i
  exact (dist_comm _ _).trans (hd i).symm

/-- Actual convergent original members lie in the genuine compact limit carrier. -/
theorem mem_of_tendsto_bodies {J : Type*} {F : Filter J} [F.NeBot]
    {u : J → ConvexBody V} {K : ConvexBody V}
    (hu : Tendsto u F (𝓝 K)) {v : J → V} {x : V}
    (hv : ∀ᶠ i in F, v i ∈ u i) (hvt : Tendsto v F (𝓝 x)) : x ∈ K := by
  have ht := (Metric.uniformContinuous_infDist_Hausdorff_dist.continuous.tendsto (x,
      SGPT.AlmostSemigroup.Hyperspace.carrierMap K)).comp
    (hvt.prodMk_nhds (SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous.tendsto K |>.comp hu))
  change Tendsto (fun i ↦ infDist (v i) (u i : Set V)) F
    (𝓝 (infDist x (K : Set V))) at ht
  have hz : ∀ᶠ i in F, infDist (v i) (u i : Set V) = 0 :=
    hv.mono fun _ hi ↦ infDist_zero_of_mem hi
  have heq : infDist x (K : Set V) = 0 :=
    tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hz.mono fun _ hi ↦ hi.symm))
  exact (K.isCompact.isClosed.mem_iff_infDist_zero K.nonempty).mpr heq

/-- True compact inner-ball persistence for any original Hausdorff net. -/
theorem eventually_mem_of_interior_limit {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {J : Type*} {F : Filter J} {u : J → ConvexBody W} {K : ConvexBody W}
    (hu : Tendsto u F (𝓝 K)) {x : W} (hx : x ∈ interior (K : Set W)) :
    ∀ᶠ i in F, x ∈ u i := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  have hclosed : closedBall x (r / 2) ⊆ (K : Set W) :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans (hball.trans interior_subset)
  filter_upwards [(Metric.tendsto_nhds.mp hu) (r / 2) (half_pos hr)] with i hi
  exact SGPT.AlmostSemigroup.Hyperspace.mem_of_closedBall_subset_of_hausdorff_lt
    K (u i) (half_pos hr) hclosed (by simpa only [dist_comm] using hi)

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {D : I → ConvexBody V} (L : ∀ i, SGPT.Okounkov.TestCurve (D i))
  {m : ℝ} (B : Iio m → ConvexBody V)

/-- Original increasing cutoffs are bounded by their genuine finite limit. -/
theorem cutoff_le_of_increasing
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m)) (i : I) : (L i).max ≤ m := by
  apply ge_of_tendsto hm
  filter_upwards [eventually_ge_atTop i] with j hij
  exact (hmono i j hij).choose

/-- Every actual original level is contained in its genuine increasing Hausdorff limit. -/
theorem source_level_subset_increasing_limit
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t)))
    (i : I) (t : Iio (L i).max) :
    ((L i).body t : Set V) ⊆ B ⟨t, t.property.trans_le (cutoff_le_of_increasing L hmono hm i)⟩ := by
  intro x hx
  apply mem_of_tendsto_bodies (hb ⟨t, t.property.trans_le (cutoff_le_of_increasing L hmono hm i)⟩)
    (v := fun _ ↦ x) _ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop i] with j hij
  have ht : (t : ℝ) < (L j).max := t.property.trans_le (hmono i j hij).choose
  rw [bodyAt, dif_pos ht]
  exact (hmono i j hij).choose_spec t hx

/-- True level Hausdorff limits lie in the actual original ambient Hausdorff limit. -/
theorem increasing_body_subset_base_limit {Δ : ConvexBody V}
    (hD : Tendsto D atTop (𝓝 Δ))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t)))
    (t : Iio m) : (B t : Set V) ⊆ Δ := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := exists_members_tendsto (hb t) hx
  exact mem_of_tendsto_bodies hD
    (Eventually.of_forall (fun i ↦ (L i).bodyAt_subset t (hp i))) hpx

/-- Actual original antitonicity passes through the genuine level Hausdorff limits. -/
theorem increasing_body_antitone
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t)))
    (s t : Iio m) (hst : s ≤ t) : (B t : Set V) ⊆ B s := by
  intro x hx
  obtain ⟨p, hp, hpx⟩ := exists_members_tendsto (hb t) hx
  apply mem_of_tendsto_bodies (hb s) _ hpx
  filter_upwards [(tendsto_order.mp hm).1 (t : ℝ) t.property] with i hi
  have hs : (s : ℝ) < (L i).max := (show (s : ℝ) ≤ t from hst).trans_lt hi
  have hmem := hp i
  rw [bodyAt, dif_pos hi] at hmem
  rw [bodyAt, dif_pos hs]
  exact (L i).antitone ⟨s, hs⟩ ⟨t, hi⟩ hst hmem

/-- Genuine member approximants transport the actual original Minkowski concavity. -/
theorem increasing_body_concave
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t)))
    (s t : Iio m) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ((a • B s + (1 - a) • B t : ConvexBody V) : Set V) ⊆
      B ⟨a * (s : ℝ) + (1 - a) * (t : ℝ),
        (convex_Iio m) s.property t.property ha (sub_nonneg.mpr ha1) (by ring)⟩ := by
  intro z hz
  rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hu
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hv
  obtain ⟨p, hp, hpx⟩ := exists_members_tendsto (hb s) hx
  obtain ⟨q, hq, hqy⟩ := exists_members_tendsto (hb t) hy
  let r : Iio m := ⟨a * (s : ℝ) + (1 - a) * (t : ℝ),
    (convex_Iio m) s.property t.property ha (sub_nonneg.mpr ha1) (by ring)⟩
  apply mem_of_tendsto_bodies (hb r) (v := fun i ↦ a • p i + (1 - a) • q i) _
    ((tendsto_const_nhds.smul hpx).add (tendsto_const_nhds.smul hqy))
  filter_upwards [(tendsto_order.mp hm).1 (s : ℝ) s.property,
    (tendsto_order.mp hm).1 (t : ℝ) t.property] with i hsi hti
  have hri : (r : ℝ) < (L i).max :=
    (convex_Iio (L i).max) hsi hti ha (sub_nonneg.mpr ha1) (by ring)
  have hpi := hp i
  have hqi := hq i
  rw [bodyAt, dif_pos hsi] at hpi
  rw [bodyAt, dif_pos hti] at hqi
  rw [bodyAt, dif_pos hri]
  apply (L i).concave ⟨s, hsi⟩ ⟨t, hti⟩ a ha ha1
  rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
  exact Set.mem_add.mpr ⟨a • p i, smul_mem_smul_set hpi,
    (1 - a) • q i, smul_mem_smul_set hqi, rfl⟩

/-- The actual original ambient and level limits produce the required minus-infinity limit. -/
theorem tendsto_increasing_body_atBot {Δ : ConvexBody V}
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t))) :
    Tendsto B atBot (𝓝 Δ) := by
  apply (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset Δ.isCompact).tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall (fun t ↦ increasing_body_subset_base_limit L B hD hb t)
  intro Q hQ hcluster
  apply ConvexBody.ext
  apply subset_antisymm hQ
  have hlevels (i : I) (u : Iio (L i).max) : ((L i).body u : Set V) ⊆ Q := by
    intro x hx
    have hclosed : IsClosed {C : ConvexBody V | x ∈ C} := by
      have hc : Continuous (fun C : ConvexBody V ↦ infDist x (C : Set V)) :=
        (Metric.lipschitz_infDist_set x).continuous.comp
          SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous
      have heq : {C : ConvexBody V | x ∈ C} =
          {C : ConvexBody V | infDist x (C : Set V) = 0} := by
        ext C
        exact C.isCompact.isClosed.mem_iff_infDist_zero C.nonempty
      rw [heq]
      exact isClosed_eq hc continuous_const
    apply hclosed.mem_of_mapClusterPt hcluster
    let u' : Iio m := ⟨u, u.property.trans_le (cutoff_le_of_increasing L hmono hm i)⟩
    filter_upwards [eventually_le_atBot u'] with t ht
    exact increasing_body_antitone L B hm hb t u' ht
      (source_level_subset_increasing_limit L B hmono hm hb i u hx)
  have hsource (i : I) : (D i : Set V) ⊆ Q :=
    (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset Q.isCompact).isClosed.mem_of_tendsto
      (L i).limit (Eventually.of_forall (hlevels i))
  exact (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset Q.isCompact).isClosed.mem_of_tendsto
    hD (Eventually.of_forall hsource)

/-- The actual original increasing-net hypotheses construct the source test curve itself. -/
def ofIncreasingLimits {Δ : ConvexBody V}
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t))) :
    SGPT.Okounkov.TestCurve Δ where
  max := m
  body := B
  antitone := increasing_body_antitone L B hm hb
  concave := increasing_body_concave L B hm hb
  limit := tendsto_increasing_body_atBot L B hD hmono hm hb

section Interior

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Δ : ConvexBody W} (K : SGPT.Okounkov.TestCurve Δ)

/-- Actual low-level Hausdorff approximation persists a true inner ball around each original interior point. -/
theorem exists_earlier_level_interior (x : Δ) (hx : (x : W) ∈ interior (Δ : Set W))
    (t : Iio K.max) : ∃ s : Iio K.max, s < t ∧ (x : W) ∈ interior (K.body s : Set W) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let δ : ℝ := r / 4
  have hδ : 0 < δ := div_pos hr (by norm_num)
  have hbig : closedBall (x : W) (2 * δ) ⊆ (Δ : Set W) :=
    (closedBall_subset_ball (by dsimp only [δ]; linarith : 2 * δ < r)).trans
      (hball.trans interior_subset)
  obtain ⟨s, hs, hst⟩ := ((Metric.tendsto_nhds.mp K.limit) δ hδ).and
    (eventually_lt_atBot t) |>.exists
  have hsmall : ball (x : W) δ ⊆ (K.body s : Set W) := by
    intro y hy
    apply SGPT.AlmostSemigroup.Hyperspace.mem_of_closedBall_subset_of_hausdorff_lt
      Δ (K.body s) hδ _ (by simpa only [dist_comm] using hs)
    intro z hz
    apply hbig
    change dist z (x : W) ≤ 2 * δ
    have hzy : dist z y ≤ δ := hz
    have hyx : dist y (x : W) < δ := hy
    calc
      dist z (x : W) ≤ dist z y + dist y (x : W) := dist_triangle _ _ _
      _ ≤ 2 * δ := by linarith
  exact ⟨s, hst, (isOpen_ball.subset_interior_iff.mpr hsmall) (mem_ball_self hδ)⟩

/-- Actual original concavity makes every strict sub-transform level contain the point in its true ordinary interior. -/
theorem mem_interior_body_of_lt_transform (x : Δ)
    (hx : (x : W) ∈ interior (Δ : Set W)) (t : Iio K.max)
    (ht : ((t : ℝ) : EReal) < K.transform x) :
    (x : W) ∈ interior (K.body t : Set W) := by
  obtain ⟨u, htu, hxu⟩ := (K.lt_transform_iff x t).mp ht
  obtain ⟨s, hst, hxs⟩ := K.exists_earlier_level_interior x hx t
  let a : ℝ := ((u : ℝ) - t) / ((u : ℝ) - s)
  have hden : 0 < (u : ℝ) - s := by
    have hst' : (s : ℝ) < t := hst
    linarith
  have ha : 0 < a := div_pos (sub_pos.mpr htu) hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (by
    have hst' : (s : ℝ) < t := hst
    linarith)
  have hpar : a * (s : ℝ) + (1 - a) * (u : ℝ) = t := by
    dsimp only [a]
    field_simp
    ring
  let A : W → W := fun p ↦ a • p + (1 - a) • (x : W)
  have hAopen : IsOpenMap A :=
    (Homeomorph.addRight ((1 - a) • (x : W))).isOpenMap.comp (isOpenMap_smul₀ ha.ne')
  have hsub : A '' interior (K.body s : Set W) ⊆ (K.body t : Set W) := by
    rintro _ ⟨p, hp, rfl⟩
    have hmem := K.concave s u a ha.le ha1
      (show A p ∈ ((a • K.body s + (1 - a) • K.body u : ConvexBody W) : Set W) by
        rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
        exact Set.mem_add.mpr ⟨a • p, smul_mem_smul_set (interior_subset hp),
          (1 - a) • (x : W), smul_mem_smul_set hxu, rfl⟩)
    have hidx : (⟨a * (s : ℝ) + (1 - a) * (u : ℝ),
        (convex_Iio K.max) s.property u.property ha.le (sub_nonneg.mpr ha1) (by ring)⟩ :
        Iio K.max) = t := Subtype.ext hpar
    rw [hidx] at hmem
    exact hmem
  apply (hAopen _ isOpen_interior).subset_interior_iff.mpr hsub
  refine ⟨x, hxs, ?_⟩
  dsimp only [A]
  rw [← add_smul]
  simp

end Interior

section IncreasingTransform

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Δ : ConvexBody W} {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {D : I → ConvexBody W} (K : SGPT.Okounkov.TestCurve Δ)
  (L : ∀ i, SGPT.Okounkov.TestCurve (D i))

/-- Each actual original transform is bounded above by the genuine limiting transform at every common source point. -/
theorem transform_le_of_increasing_limit
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t)))
    (x : Δ) (i : I) (hxi : (x : W) ∈ D i) :
    (L i).transform ⟨x, hxi⟩ ≤ K.transform x := by
  apply sSup_le
  rintro _ ⟨t, hx, rfl⟩
  exact K.le_transform_of_mem x
    ⟨t, t.property.trans_le (cutoff_le_of_increasing L hmono hm i)⟩
    (source_level_subset_increasing_limit L K.body hmono hm hb i t hx)

/-- Exact original interior-point convergence for the genuine original increasing net. -/
theorem tendsto_transform_of_increasing
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t)))
    (x : Δ) (hx : (x : W) ∈ interior (Δ : Set W)) :
    Tendsto (fun i ↦ (L i).toTestFunction.valueAt x) atTop (𝓝 (K.transform x)) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r, har, hrG⟩ := EReal.exists_between_coe_real ha
    have hrm : r < K.max := EReal.coe_lt_coe_iff.mp (hrG.trans_le (K.transform_le_max x))
    let t : Iio K.max := ⟨r, hrm⟩
    have hxt := K.mem_interior_body_of_lt_transform x hx t hrG
    filter_upwards [eventually_mem_of_interior_limit (hb t) hxt,
      (tendsto_order.mp hm).1 r hrm] with i hxi hri
    change (x : W) ∈ (L i).bodyAt r at hxi
    rw [bodyAt, dif_pos hri] at hxi
    have hxD : (x : W) ∈ D i := (L i).body_subset ⟨r, hri⟩ hxi
    rw [TestFunction.valueAt, dif_pos hxD]
    exact har.trans_le ((L i).le_transform_of_mem ⟨x, hxD⟩ ⟨r, hri⟩ hxi)
  · intro b hbgt
    filter_upwards [eventually_mem_of_interior_limit hD hx] with i hxi
    rw [TestFunction.valueAt, dif_pos hxi]
    exact (K.transform_le_of_increasing_limit L hmono hm hb x i hxi).trans_lt hbgt

/-- Source prop:incnetLegend: the actual original limits produce the curve and its original interior-point Legendre limit. -/
theorem exists_curve_of_increasing_limits {m : ℝ} (B : Iio m → ConvexBody W)
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t))) :
    ∃ K : SGPT.Okounkov.TestCurve Δ, K.max = m ∧
      (∀ t : Iio m, K.bodyAt t = B t) ∧
      ∀ (x : Δ), (x : W) ∈ interior (Δ : Set W) →
        Tendsto (fun i ↦ (L i).toTestFunction.valueAt x) atTop (𝓝 (K.transform x)) := by
  let K := ofIncreasingLimits L B hD hmono hm hb
  refine ⟨K, rfl, ?_, ?_⟩
  · intro t
    exact K.bodyAt_coe t
  · intro x hx
    exact K.tendsto_transform_of_increasing L hD hmono hm hb x hx

end IncreasingTransform

end SGPT.Okounkov.TestCurve
