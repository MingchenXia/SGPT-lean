import SGPT.Okounkov.TestCurve

noncomputable section

namespace SGPT.Okounkov.TestCurve

open Set Filter Metric
open scoped Topology Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Δ : ConvexBody V} (K : SGPT.Okounkov.TestCurve Δ)

/-- The actual source maximal-cutoff intersection. -/
def endpointSet : Set V := ⋂ t : Iio K.max, (K.body t : Set V)

theorem endpointSet_nonempty : K.endpointSet.Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro s t
    exact ⟨Max.max s t, K.antitone s (Max.max s t) (le_max_left s t),
      K.antitone t (Max.max s t) (le_max_right s t)⟩
  · intro t
    exact (K.body t).nonempty
  · intro t
    exact (K.body t).isCompact
  · intro t
    exact (K.body t).isCompact.isClosed

theorem endpointSet_convex : Convex ℝ K.endpointSet :=
  convex_iInter (fun t ↦ (K.body t).convex)

theorem endpointSet_isCompact : IsCompact K.endpointSet := by
  apply Δ.isCompact.of_isClosed_subset
  · exact isClosed_iInter (fun t ↦ (K.body t).isCompact.isClosed)
  · intro x hx
    let t : Iio K.max := ⟨K.max - 1, show K.max - 1 < K.max by linarith⟩
    exact K.body_subset t (mem_iInter.mp hx t)

/-- Actual original endpoint convex body; no endpoint membership/nonemptiness certificate. -/
def endpoint : ConvexBody V :=
  ⟨K.endpointSet, K.endpointSet_convex, K.endpointSet_isCompact, K.endpointSet_nonempty⟩

@[simp] theorem mem_endpoint (x : V) : x ∈ K.endpoint ↔ ∀ t : Iio K.max, x ∈ K.body t := by
  change x ∈ ⋂ t : Iio K.max, (K.body t : Set V) ↔ _
  exact mem_iInter

/-- Actual original source Legendre supremum; an empty membership fiber has value bottom. -/
def transform (x : Δ) : EReal :=
  sSup {a : EReal | ∃ t : Iio K.max, (x : V) ∈ K.body t ∧ a = ((t : ℝ) : EReal)}

theorem transform_le_max (x : Δ) : K.transform x ≤ (K.max : EReal) := by
  apply sSup_le
  rintro _ ⟨t, _, rfl⟩
  exact EReal.coe_le_coe (show (t : ℝ) ≤ K.max from t.property.le)

theorem transform_lt_top (x : Δ) : K.transform x < ⊤ :=
  (K.transform_le_max x).trans_lt (EReal.coe_lt_top K.max)

theorem le_transform_of_mem (x : Δ) (t : Iio K.max) (hx : (x : V) ∈ K.body t) :
    ((t : ℝ) : EReal) ≤ K.transform x :=
  le_sSup ⟨t, hx, rfl⟩

theorem lt_transform_iff (x : Δ) (r : ℝ) :
    (r : EReal) < K.transform x ↔
      ∃ t : Iio K.max, r < (t : ℝ) ∧ (x : V) ∈ K.body t := by
  rw [transform, lt_sSup_iff]
  constructor
  · rintro ⟨a, ⟨t, hx, rfl⟩, hr⟩
    exact ⟨t, EReal.coe_lt_coe_iff.mp hr, hx⟩
  · rintro ⟨t, hr, hx⟩
    exact ⟨((t : ℝ) : EReal), ⟨t, hx, rfl⟩, EReal.coe_lt_coe_iff.mpr hr⟩

theorem mem_body_of_lt_transform (x : Δ) (t : Iio K.max)
    (ht : ((t : ℝ) : EReal) < K.transform x) : (x : V) ∈ K.body t := by
  obtain ⟨u, htu, hx⟩ := (K.lt_transform_iff x t).mp ht
  exact K.antitone t u htu.le hx

theorem isClosed_member_parameters (x : V) :
    IsClosed {t : Iio K.max | x ∈ K.body t} := by
  have hc : Continuous (fun t : Iio K.max ↦ infDist x (K.body t : Set V)) :=
    (Metric.lipschitz_infDist_set x).continuous.comp
      (SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous.comp K.continuous_body)
  have heq : {t : Iio K.max | x ∈ K.body t} =
      {t : Iio K.max | infDist x (K.body t : Set V) = 0} := by
    ext t
    exact (K.body t).isCompact.isClosed.mem_iff_infDist_zero (K.body t).nonempty
  rw [heq]
  exact isClosed_eq hc continuous_const

/-- Actual sub-cutoff superlevels of the genuine Legendre supremum are exactly the original bodies. -/
theorem mem_body_iff_le_transform (x : Δ) (t : Iio K.max) :
    (x : V) ∈ K.body t ↔ ((t : ℝ) : EReal) ≤ K.transform x := by
  constructor
  · exact K.le_transform_of_mem x t
  · intro ht
    have hsub : Iio t ⊆ {u : Iio K.max | (x : V) ∈ K.body u} := by
      intro u hu
      apply K.mem_body_of_lt_transform x u
      exact (EReal.coe_lt_coe (show (u : ℝ) < t from hu)).trans_le ht
    have hself : t ∈ closure (Iio t) := by
      rw [closure_Iio t]
      change t ≤ t
      exact le_rfl
    have hc := closure_mono hsub hself
    rw [(K.isClosed_member_parameters x).closure_eq] at hc
    exact hc

/-- Actual maximum-cutoff level is exactly the produced original endpoint intersection. -/
theorem transform_eq_max_iff (x : Δ) :
    K.transform x = (K.max : EReal) ↔ (x : V) ∈ K.endpoint := by
  constructor
  · intro hx
    apply (K.mem_endpoint x).mpr
    intro t
    apply (K.mem_body_iff_le_transform x t).mpr
    rw [hx]
    exact EReal.coe_le_coe (show (t : ℝ) ≤ K.max from t.property.le)
  · intro hx
    apply le_antisymm (K.transform_le_max x)
    by_contra hle
    obtain ⟨r, hxr, hrm⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
    let t : Iio K.max := ⟨r, EReal.coe_lt_coe_iff.mp hrm⟩
    have hrx := K.le_transform_of_mem x t ((K.mem_endpoint x).mp hx t)
    exact not_le_of_gt hxr hrx

/-- Every actual real superlevel of the original Legendre supremum is closed. -/
theorem isClosed_transform_superlevel (r : ℝ) :
    IsClosed {x : Δ | (r : EReal) ≤ K.transform x} := by
  rcases lt_trichotomy r K.max with hr | hr | hr
  · let t : Iio K.max := ⟨r, hr⟩
    have heq : {x : Δ | (r : EReal) ≤ K.transform x} =
        ((↑) : Δ → V) ⁻¹' (K.body t : Set V) := by
      ext x
      exact (K.mem_body_iff_le_transform x t).symm
    rw [heq]
    exact (K.body t).isCompact.isClosed.preimage continuous_subtype_val
  · rw [hr]
    have heq : {x : Δ | (K.max : EReal) ≤ K.transform x} =
        ((↑) : Δ → V) ⁻¹' (K.endpoint : Set V) := by
      ext x
      change (K.max : EReal) ≤ K.transform x ↔ (x : V) ∈ K.endpoint
      rw [← K.transform_eq_max_iff x]
      exact ⟨fun h ↦ le_antisymm (K.transform_le_max x) h, fun h ↦ h.ge⟩
    rw [heq]
    exact K.endpoint.isCompact.isClosed.preimage continuous_subtype_val
  · have heq : {x : Δ | (r : EReal) ≤ K.transform x} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_le_of_gt ((K.transform_le_max x).trans_lt (EReal.coe_lt_coe hr)) hx
    rw [heq]
    exact isClosed_empty

/-- Genuine USC of the original Legendre transform, including its bottom boundary values. -/
theorem upperSemicontinuous_transform : UpperSemicontinuous K.transform := by
  apply upperSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  cases a using EReal.rec with
  | bot => simpa only [Ici_bot, preimage_univ] using (isClosed_univ : IsClosed (univ : Set Δ))
  | top =>
    have heq : K.transform ⁻¹' Ici ⊤ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact not_le_of_gt (K.transform_lt_top x) hx
    rw [heq]
    exact isClosed_empty
  | coe r => exact K.isClosed_transform_superlevel r

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Δw : ConvexBody W}

/-- Genuine original Hausdorff limit and actual inner-ball persistence give a finite Legendre value at every original interior point. -/
theorem transform_ne_bot_of_mem_interior (K : SGPT.Okounkov.TestCurve Δw) (x : Δw)
    (hx : (x : W) ∈ interior (Δw : Set W)) : K.transform x ≠ ⊥ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  have hhalf : 0 < r / 2 := half_pos hr
  have hclosed : closedBall (x : W) (r / 2) ⊆ (Δw : Set W) :=
    (closedBall_subset_ball (by linarith : r / 2 < r)).trans (hball.trans interior_subset)
  obtain ⟨t, ht⟩ := ((Metric.tendsto_nhds.mp K.limit) (r / 2) hhalf).exists
  have hmem : (x : W) ∈ K.body t :=
    SGPT.AlmostSemigroup.Hyperspace.mem_of_closedBall_subset_of_hausdorff_lt
      Δw (K.body t) hhalf hclosed (by simpa only [dist_comm] using ht)
  exact ne_of_gt ((EReal.bot_lt_coe (t : ℝ)).trans_le (K.le_transform_of_mem x t hmem))

end SGPT.Okounkov.TestCurve

namespace SGPT.Okounkov

open Set Filter Metric MeasureTheory
open scoped Topology Pointwise
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The literal real-height hypograph of a source function on the original body. -/
def hypograph (Δ : ConvexBody V) (G : Δ → EReal) : Set (V × ℝ) :=
  {p | ∃ hx : p.1 ∈ Δ, (p.2 : EReal) ≤ G ⟨p.1, hx⟩}

/-- Actual source `def:tf`: concavity is actual hypograph convexity, with the original finite-interior and USC conditions. -/
structure TestFunction (Δ : ConvexBody V) where
  value : Δ → EReal
  ne_top : ∀ x, value x ≠ ⊤
  concave : Convex ℝ (hypograph Δ value)
  finite_interior : ∀ x : Δ, (x : V) ∈ interior (Δ : Set V) → value x ≠ ⊥
  upperSemicontinuous : UpperSemicontinuous value

/-- Actual USC on the original compact body gives a genuinely closed ambient hypograph. -/
theorem isClosed_hypograph (Δ : ConvexBody V) {G : Δ → EReal}
    (hG : UpperSemicontinuous G) : IsClosed (hypograph Δ G) := by
  let S : Set (Δ × ℝ) := {p | (p.2 : EReal) ≤ G p.1}
  have hS : IsClosed S :=
    hG.IsClosed_hypograph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  let F : Δ × ℝ → V × ℝ := Prod.map Subtype.val id
  have hF : Topology.IsClosedEmbedding F :=
    Δ.isCompact.isClosed.isClosedEmbedding_subtypeVal.prodMap
      (Homeomorph.refl ℝ).isClosedEmbedding
  have heq : F '' S = hypograph Δ G := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.property, hq⟩
    · rintro ⟨hp, hG⟩
      exact ⟨(⟨p.1, hp⟩, p.2), hG, rfl⟩
  rw [← heq]
  exact hF.isClosedMap S hS

namespace TestFunction

variable {Δ : ConvexBody V} (G : TestFunction Δ)

/-- Original bounded test functions are bounded below by a finite real constant. -/
def IsBounded : Prop := ∃ c : ℝ, ∀ x : Δ, (c : EReal) ≤ G.value x

/-- An ambient representative used only on the actual original integration body. -/
def valueAt (x : V) : EReal := by
  classical
  exact if hx : x ∈ Δ then G.value ⟨x, hx⟩ else 0

@[simp] theorem valueAt_coe (x : Δ) : G.valueAt x = G.value x := by
  rw [valueAt, dif_pos x.property]

/-- Actual compactness and genuine USC produce a finite real upper bound; it is not stored in the source object. -/
theorem exists_real_upper_bound : ∃ c : ℝ, ∀ x : Δ, G.value x ≤ (c : EReal) := by
  let : CompactSpace Δ := isCompact_iff_compactSpace.mp Δ.isCompact
  have hne : (univ : Set Δ).Nonempty := by
    obtain ⟨x, hx⟩ := Δ.nonempty
    exact ⟨⟨x, hx⟩, mem_univ _⟩
  obtain ⟨x, _, hx⟩ := UpperSemicontinuousOn.exists_isMaxOn hne isCompact_univ
    (G.upperSemicontinuous.upperSemicontinuousOn univ)
  cases hv : G.value x using EReal.rec with
  | bot =>
    refine ⟨0, fun y ↦ ?_⟩
    have hy : G.value y ≤ (⊥ : EReal) := by
      simpa only [hv, mem_ofPred_eq] using hx (mem_univ y)
    exact hy.trans bot_le
  | top => exact False.elim (G.ne_top x hv)
  | coe c =>
    refine ⟨c, fun y ↦ ?_⟩
    simpa only [hv, mem_ofPred_eq] using hx (mem_univ y)

/-- Literal original supremum cutoff before taking its proved finite real representative. -/
def maxValue : EReal := ⨆ x : Δ, G.value x

def maxReal : ℝ := G.maxValue.toReal

theorem maxValue_ne_top : G.maxValue ≠ ⊤ := by
  obtain ⟨c, hc⟩ := G.exists_real_upper_bound
  exact ne_of_lt ((iSup_le hc).trans_lt (EReal.coe_lt_top c))

theorem maxValue_ne_bot (hint : (interior (Δ : Set V)).Nonempty) : G.maxValue ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hint
  let x' : Δ := ⟨x, interior_subset hx⟩
  exact ne_of_gt ((bot_lt_iff_ne_bot.mpr (G.finite_interior x' hx)).trans_le
    (le_iSup G.value x'))

theorem coe_maxReal (hint : (interior (Δ : Set V)).Nonempty) :
    (G.maxReal : EReal) = G.maxValue :=
  EReal.coe_toReal G.maxValue_ne_top (G.maxValue_ne_bot hint)

/-- Actual original ambient superlevel set, without a convex-body/nonemptiness certificate. -/
def superlevel (t : ℝ) : Set V := (fun x : V ↦ (x, t)) ⁻¹' hypograph Δ G.value

theorem superlevel_subset (t : ℝ) : G.superlevel t ⊆ (Δ : Set V) := by
  rintro x ⟨hx, _⟩
  exact hx

theorem superlevel_isClosed (t : ℝ) : IsClosed (G.superlevel t) :=
  (isClosed_hypograph Δ G.upperSemicontinuous).preimage
    (continuous_id.prodMk continuous_const)

theorem superlevel_isCompact (t : ℝ) : IsCompact (G.superlevel t) :=
  Δ.isCompact.of_isClosed_subset (G.superlevel_isClosed t) (G.superlevel_subset t)

theorem superlevel_convex (t : ℝ) : Convex ℝ (G.superlevel t) := by
  intro x hx y hy a b ha hb hab
  have hc := G.concave hx hy ha hb hab
  have hpair : a • (x, t) + b • (y, t) = (a • x + b • y, t) := by
    apply Prod.ext
    · rfl
    · change a * t + b * t = t
      rw [← add_mul, hab, one_mul]
  rw [hpair] at hc
  exact hc

theorem superlevel_nonempty (hint : (interior (Δ : Set V)).Nonempty)
    {t : ℝ} (ht : t < G.maxReal) : (G.superlevel t).Nonempty := by
  have hlt : (t : EReal) < G.maxValue := by
    rw [← G.coe_maxReal hint]
    exact EReal.coe_lt_coe ht
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
  exact ⟨x, x.property, hx.le⟩

/-- Genuine original inverse-Legendre bodies, constructed from actual compact convex nonempty superlevels. -/
def levelBody (hint : (interior (Δ : Set V)).Nonempty) (t : Iio G.maxReal) :
    ConvexBody V :=
  ⟨G.superlevel t, G.superlevel_convex t, G.superlevel_isCompact t,
    G.superlevel_nonempty hint t.property⟩

@[simp] theorem mem_levelBody (hint : (interior (Δ : Set V)).Nonempty)
    (t : Iio G.maxReal) (x : V) :
    x ∈ G.levelBody hint t ↔ ∃ hx : x ∈ Δ, ((t : ℝ) : EReal) ≤ G.value ⟨x, hx⟩ := Iff.rfl

theorem levelBody_antitone (hint : (interior (Δ : Set V)).Nonempty)
    (s t : Iio G.maxReal) (hst : s ≤ t) :
    (G.levelBody hint t : Set V) ⊆ G.levelBody hint s := by
  rintro x ⟨hx, ht⟩
  exact ⟨hx, (EReal.coe_le_coe (show (s : ℝ) ≤ t from hst)).trans ht⟩

/-- Actual hypograph convexity supplies the original weighted-body inclusion. -/
theorem levelBody_concave (hint : (interior (Δ : Set V)).Nonempty)
    (s t : Iio G.maxReal) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ((a • G.levelBody hint s + (1 - a) • G.levelBody hint t : ConvexBody V) : Set V) ⊆
      G.levelBody hint ⟨a * (s : ℝ) + (1 - a) * (t : ℝ),
        (convex_Iio G.maxReal) s.property t.property ha (sub_nonneg.mpr ha1) (by ring)⟩ := by
  intro z hz
  rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul] at hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨x, hx, rfl⟩ := Set.mem_smul_set.mp hu
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hv
  exact G.concave hx hy ha (sub_nonneg.mpr ha1) (by ring)

/-- Every actual original interior point belongs to all sufficiently low genuine superlevels. -/
theorem eventually_mem_levelBody (hint : (interior (Δ : Set V)).Nonempty)
    {x : V} (hx : x ∈ interior (Δ : Set V)) :
    ∀ᶠ t in (atBot : Filter (Iio G.maxReal)), x ∈ G.levelBody hint t := by
  let x' : Δ := ⟨x, interior_subset hx⟩
  let c : ℝ := (G.value x').toReal
  have hc : (c : EReal) = G.value x' :=
    EReal.coe_toReal (G.ne_top x') (G.finite_interior x' hx)
  let u : Iio G.maxReal := ⟨min c (G.maxReal - 1),
    lt_of_le_of_lt (min_le_right c (G.maxReal - 1))
      (show G.maxReal - 1 < G.maxReal by linarith)⟩
  filter_upwards [eventually_le_atBot u] with t ht
  refine ⟨x'.property, ?_⟩
  rw [← hc]
  exact EReal.coe_le_coe ((show (t : ℝ) ≤ u from ht).trans (min_le_left _ _))

/-- Genuine compact-family cluster uniqueness gives the original minus-infinity Hausdorff limit. -/
theorem tendsto_levelBody_atBot (hint : (interior (Δ : Set V)).Nonempty) :
    Tendsto (G.levelBody hint) atBot (𝓝 Δ) := by
  refine (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset Δ.isCompact).tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · exact Eventually.of_forall (fun t ↦ G.superlevel_subset (t : ℝ))
  intro L hL hcluster
  apply ConvexBody.ext
  apply subset_antisymm hL
  have hdense : closure (interior (Δ : Set V)) = (Δ : Set V) := by
    rw [Δ.convex.closure_interior_eq_closure_of_nonempty_interior hint,
      Δ.isCompact.isClosed.closure_eq]
  rw [← hdense]
  apply closure_minimal _ L.isCompact.isClosed
  intro x hx
  have hclosed : IsClosed {B : ConvexBody V | x ∈ B} := by
    have hc : Continuous (fun B : ConvexBody V ↦ infDist x (B : Set V)) :=
      (Metric.lipschitz_infDist_set x).continuous.comp
        SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous
    have heq : {B : ConvexBody V | x ∈ B} =
        {B : ConvexBody V | infDist x (B : Set V) = 0} := by
      ext B
      exact B.isCompact.isClosed.mem_iff_infDist_zero B.nonempty
    rw [heq]
    exact isClosed_eq hc continuous_const
  exact hclosed.mem_of_mapClusterPt hcluster (G.eventually_mem_levelBody hint hx)

/-- Actual inverse source `lma:convbodyLegendre`: all original test-curve conditions are proved. -/
def toTestCurve (hint : (interior (Δ : Set V)).Nonempty) : SGPT.Okounkov.TestCurve Δ where
  max := G.maxReal
  body := G.levelBody hint
  antitone := G.levelBody_antitone hint
  concave := G.levelBody_concave hint
  limit := G.tendsto_levelBody_atBot hint

/-- The genuine supremum over original inverse levels recovers every original extended-real value. -/
theorem transform_toTestCurve (hint : (interior (Δ : Set V)).Nonempty) (x : Δ) :
    (G.toTestCurve hint).transform x = G.value x := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨t, hx, rfl⟩
    exact hx.choose_spec
  · by_contra hle
    obtain ⟨r, htr, hrG⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
    have hrm : (r : EReal) < (G.maxReal : EReal) := by
      rw [G.coe_maxReal hint]
      exact hrG.trans_le (le_iSup G.value x)
    let t : Iio G.maxReal := ⟨r, EReal.coe_lt_coe_iff.mp hrm⟩
    have hx : (x : V) ∈ (G.toTestCurve hint).body t := ⟨x.property, hrG.le⟩
    exact not_le_of_gt htr ((G.toTestCurve hint).le_transform_of_mem x t hx)

variable {n : ℕ} {Δe : ConvexBody (EuclideanSpace ℝ (Fin n))}

/-- Exact original inverse Legendre transform on the positive-volume body fixed by the source section. -/
def inverseLegendre (G : TestFunction Δe)
    (hΔ : 0 < volume (Δe : Set (EuclideanSpace ℝ (Fin n)))) : SGPT.Okounkov.TestCurve Δe :=
  G.toTestCurve (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos
    volume Δe.convex hΔ)

/-- The produced original cutoff is the actual supremum of the original function. -/
theorem inverseLegendre_cutoff (G : TestFunction Δe)
    (hΔ : 0 < volume (Δe : Set (EuclideanSpace ℝ (Fin n)))) :
    ((G.inverseLegendre hΔ).max : EReal) = ⨆ x : Δe, G.value x :=
  G.coe_maxReal (SGPT.AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos
    volume Δe.convex hΔ)

/-- Exact original inverse levels, with the actual original carrier and function inequality. -/
theorem mem_inverseLegendre_body (G : TestFunction Δe)
    (hΔ : 0 < volume (Δe : Set (EuclideanSpace ℝ (Fin n))))
    (t : Iio (G.inverseLegendre hΔ).max) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (G.inverseLegendre hΔ).body t ↔
      ∃ hx : x ∈ Δe, ((t : ℝ) : EReal) ≤ G.value ⟨x, hx⟩ := Iff.rfl

/-- Exact source `eq:EF`, retaining the actual signed integral of the original function. -/
def energy (G : TestFunction Δe) : EReal :=
  (n.factorial : EReal) * SGPT.Convex.extendedSignedIntegral
    (volume.restrict (Δe : Set (EuclideanSpace ℝ (Fin n)))) G.valueAt

/-- The exact source finite-energy test-function condition. -/
def HasFiniteEnergy (G : TestFunction Δe) : Prop := (⊥ : EReal) < G.energy

/-- The genuine positive integral part is finite, so the signed source energy cannot contain an infinity-minus-infinity ambiguity. -/
theorem energy_positive_lintegral_lt_top (G : TestFunction Δe) :
    (∫⁻ x, (G.valueAt x).toENNReal
      ∂volume.restrict (Δe : Set (EuclideanSpace ℝ (Fin n)))) < ⊤ := by
  obtain ⟨c, hc⟩ := G.exists_real_upper_bound
  apply SGPT.Convex.lintegral_toENNReal_lt_top_of_bound volume Δe.isCompact.measure_lt_top (r := c)
  intro x hx
  rw [valueAt, dif_pos (show x ∈ Δe from hx)]
  exact hc ⟨x, hx⟩

end TestFunction

namespace TestCurve

variable {Δ : ConvexBody V} (K : SGPT.Okounkov.TestCurve Δ)

/-- Actual original body-height graph below the genuine cutoff. -/
def subCutoffGraph : Set (V × ℝ) :=
  {p | ∃ ht : p.2 < K.max, p.1 ∈ K.body ⟨p.2, ht⟩}

/-- Genuine original Minkowski concavity produces actual convexity of the body-height graph. -/
theorem convex_subCutoffGraph : Convex ℝ K.subCutoffGraph := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hpmax, hp⟩ := hp
  obtain ⟨hqmax, hq⟩ := hq
  have ha1 : a ≤ 1 := by linarith
  have hba : b = 1 - a := by linarith
  have hr : a * p.2 + b * q.2 < K.max :=
    (convex_Iio K.max) hpmax hqmax ha hb hab
  refine ⟨hr, ?_⟩
  have hc := K.concave ⟨p.2, hpmax⟩ ⟨q.2, hqmax⟩ a ha ha1
    (show a • p.1 + (1 - a) • q.1 ∈
      ((a • K.body ⟨p.2, hpmax⟩ + (1 - a) • K.body ⟨q.2, hqmax⟩ : ConvexBody V) : Set V) by
      rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
      exact Set.mem_add.mpr ⟨a • p.1, smul_mem_smul_set hp,
        (1 - a) • q.1, smul_mem_smul_set hq, rfl⟩)
  change a • p.1 + b • q.1 ∈ (K.body ⟨a * p.2 + b * q.2, hr⟩ : Set V)
  simpa only [hba] using hc

theorem subCutoffGraph_subset_hypograph :
    K.subCutoffGraph ⊆ hypograph Δ K.transform := by
  rintro p ⟨ht, hp⟩
  have hx := K.body_subset ⟨p.2, ht⟩ hp
  exact ⟨hx, K.le_transform_of_mem ⟨p.1, hx⟩ ⟨p.2, ht⟩ hp⟩

/-- The actual Legendre hypograph is the genuine closure of the convex source body-height graph. -/
theorem closure_subCutoffGraph_eq_hypograph :
    closure K.subCutoffGraph = hypograph Δ K.transform := by
  apply Subset.antisymm
  · exact closure_minimal K.subCutoffGraph_subset_hypograph
      (isClosed_hypograph Δ K.upperSemicontinuous_transform)
  · rintro p ⟨hx, hp⟩
    let F : ℝ → V × ℝ := fun t ↦ (p.1, t)
    have hF : Continuous F := continuous_const.prodMk continuous_id
    have hself : p.2 ∈ closure (Iio p.2) := by
      rw [closure_Iio p.2]
      change p.2 ≤ p.2
      exact le_rfl
    have hpcl : p ∈ closure (F '' Iio p.2) := by
      exact image_closure_subset_closure_image hF (mem_image_of_mem F hself)
    apply closure_mono (fun q hq ↦ ?_) hpcl
    obtain ⟨t, ht, rfl⟩ := hq
    have htm : t < K.max := by
      have hpm := hp.trans (K.transform_le_max ⟨p.1, hx⟩)
      have hpm' := EReal.coe_le_coe_iff.mp hpm
      exact lt_of_lt_of_le ht hpm'
    refine ⟨htm, ?_⟩
    apply (K.mem_body_iff_le_transform ⟨p.1, hx⟩ ⟨t, htm⟩).mpr
    exact (EReal.coe_lt_coe ht).le.trans hp

/-- Genuine concavity of the original Legendre transform, including bottom-valued boundary points. -/
theorem convex_hypograph_transform : Convex ℝ (hypograph Δ K.transform) := by
  rw [← K.closure_subCutoffGraph_eq_hypograph]
  exact K.convex_subCutoffGraph.closure

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {Δw : ConvexBody W}

/-- Actual forward source `lma:convbodyLegendre`; every test-function condition is produced from the original curve. -/
def toTestFunction (K : SGPT.Okounkov.TestCurve Δw) : TestFunction Δw where
  value := K.transform
  ne_top := fun x ↦ ne_of_lt (K.transform_lt_top x)
  concave := K.convex_hypograph_transform
  finite_interior := K.transform_ne_bot_of_mem_interior
  upperSemicontinuous := K.upperSemicontinuous_transform

end TestCurve
end SGPT.Okounkov
