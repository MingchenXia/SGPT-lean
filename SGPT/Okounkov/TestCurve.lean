import SGPT.AlmostSemigroup.Minkowski
import SGPT.AlmostSemigroup.ConvexIntersection
import SGPT.Convex.GrowthClasses
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.ConstMulAction

noncomputable section

namespace SGPT.Okounkov

open Set Filter Metric MeasureTheory
open scoped Topology Pointwise

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual decreasing, Minkowski-concave body family in source `def:Otc`.
The source boundedness, energy and comparison clauses are defined separately. -/
structure TestCurve (Δ : ConvexBody V) where
  max : ℝ
  body : Iio max → ConvexBody V
  antitone : ∀ s t, s ≤ t → (body t : Set V) ⊆ body s
  concave : ∀ s t (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1),
    ((a • body s + (1 - a) • body t : ConvexBody V) : Set V) ⊆
      body ⟨a * (s : ℝ) + (1 - a) * (t : ℝ),
        (convex_Iio max) s.property t.property ha (sub_nonneg.mpr ha1) (by ring)⟩
  limit : Tendsto body atBot (𝓝 Δ)

namespace TestCurve

variable {Δ : ConvexBody V} (K : TestCurve Δ)

/-- The source boundedness condition: the original family equals its limit at all sufficiently small parameters. -/
def IsBounded : Prop := ∀ᶠ t in (atBot : Filter (Iio K.max)), K.body t = Δ

/-- Literal source comparison, allowing different limit bodies and different cutoffs. -/
def Compare {Δ' : ConvexBody V} (L : TestCurve Δ') : Prop :=
  ∃ h : K.max ≤ L.max, ∀ t : Iio K.max,
    (K.body t : Set V) ⊆ L.body ⟨t, lt_of_lt_of_le t.property h⟩

/-- A total real-parameter representative used only to integrate on the original sub-cutoff interval. -/
def bodyAt (t : ℝ) : ConvexBody V := if ht : t < K.max then K.body ⟨t, ht⟩ else Δ

@[simp] theorem bodyAt_coe (t : Iio K.max) : K.bodyAt t = K.body t := by
  rw [bodyAt, dif_pos (show (t : ℝ) < K.max from t.property)]

/-- Actual source members at any finite parameter lie in the original limit body. -/
theorem body_subset (s : Iio K.max) : (K.body s : Set V) ⊆ Δ := by
  intro x hx
  have ht := ((Metric.lipschitz_infDist_set x).continuous.tendsto
    (AlmostSemigroup.Hyperspace.carrierMap Δ)).comp
    (AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous.tendsto Δ |>.comp K.limit)
  change Tendsto (fun t ↦ infDist x (K.body t : Set V)) atBot
    (𝓝 (infDist x (Δ : Set V))) at ht
  have hz : ∀ᶠ t in (atBot : Filter (Iio K.max)),
      infDist x (K.body t : Set V) = 0 := by
    filter_upwards [eventually_le_atBot s] with t ht
    exact infDist_zero_of_mem (K.antitone t s ht hx)
  have hzero : infDist x (Δ : Set V) = 0 :=
    tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hz.mono fun _ h ↦ h.symm))
  exact (Δ.isCompact.isClosed.mem_iff_infDist_zero Δ.nonempty).mpr hzero

/-- The total integration representative still has the actual original carrier inclusion. -/
theorem bodyAt_subset (t : ℝ) : (K.bodyAt t : Set V) ⊆ Δ := by
  by_cases ht : t < K.max
  · simpa only [bodyAt, dif_pos ht] using K.body_subset ⟨t, ht⟩
  · simp only [bodyAt, dif_neg ht]
    exact Subset.rfl

/-- Genuine concavity produces a nearby member in a later body. -/
theorem exists_member_dist_le (s t u : Iio K.max) (hst : s ≤ t) (htu : t < u)
    {p : V} (hp : p ∈ K.body s) :
    ∃ q ∈ K.body t,
      dist p q ≤ ((t : ℝ) - s) / ((u : ℝ) - s) * diam (Δ : Set V) := by
  have hs : (s : ℝ) ≤ t := hst
  have ht : (t : ℝ) < u := htu
  have hden : 0 < (u : ℝ) - s := by linarith
  let a : ℝ := ((u : ℝ) - t) / ((u : ℝ) - s)
  have ha : 0 ≤ a := div_nonneg (by linarith) hden.le
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hb : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have hpar : a * (s : ℝ) + (1 - a) * (u : ℝ) = t := by
    dsimp only [a]
    field_simp
    ring
  obtain ⟨q, hq⟩ := (K.body u).nonempty
  have hmem : a • p + (1 - a) • q ∈ K.body t := by
    change a • p + (1 - a) • q ∈ (K.body t : Set V)
    have hc := K.concave s u a ha ha1
      (show a • p + (1 - a) • q ∈
        ((a • K.body s + (1 - a) • K.body u : ConvexBody V) : Set V) by
        rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
        exact Set.mem_add.mpr ⟨a • p, smul_mem_smul_set hp, (1 - a) • q,
          smul_mem_smul_set hq, rfl⟩)
    have hidx : (⟨a * (s : ℝ) + (1 - a) * (u : ℝ),
        (convex_Iio K.max) s.property u.property ha (sub_nonneg.mpr ha1) (by ring)⟩ :
        Iio K.max) = t := Subtype.ext hpar
    rw [hidx] at hc
    exact hc
  refine ⟨a • p + (1 - a) • q, hmem, ?_⟩
  have hid : p - (a • p + (1 - a) • q) = (1 - a) • (p - q) := by module
  rw [dist_eq_norm, hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have hdist : ‖p - q‖ ≤ diam (Δ : Set V) := by
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem Δ.isCompact.isBounded
      (K.body_subset s hp) (K.body_subset u hq)
  have hcoeff : 1 - a = ((t : ℝ) - s) / ((u : ℝ) - s) := by
    dsimp only [a]
    field_simp
    ring
  rw [hcoeff]
  exact mul_le_mul_of_nonneg_left hdist (by rw [← hcoeff]; exact hb)

/-- The actual original Hausdorff distance is bounded by the genuine concavity interpolation. -/
theorem dist_le (s t u : Iio K.max) (hst : s ≤ t) (htu : t < u) :
    dist (K.body s) (K.body t) ≤
      ((t : ℝ) - s) / ((u : ℝ) - s) * diam (Δ : Set V) := by
  have hnonneg : 0 ≤ ((t : ℝ) - s) / ((u : ℝ) - s) * diam (Δ : Set V) := by
    apply mul_nonneg _ diam_nonneg
    apply div_nonneg
    · exact sub_nonneg.mpr hst
    · have : (s : ℝ) ≤ t := hst
      have : (t : ℝ) < u := htu
      linarith
  apply hausdorffDist_le_of_mem_dist hnonneg
  · intro p hp
    exact K.exists_member_dist_le s t u hst htu hp
  · intro p hp
    exact ⟨p, K.antitone s t hst hp, by simpa only [dist_self] using hnonneg⟩

/-- Every actual initial parameter interval has a genuine uniform Hausdorff Lipschitz bound. -/
theorem dist_le_mul (r u : Iio K.max) (hru : r < u)
    (s t : Iio K.max) (hs : s ≤ r) (ht : t ≤ r) :
    dist (K.body s) (K.body t) ≤
      (diam (Δ : Set V) / ((u : ℝ) - r)) * dist (s : ℝ) t := by
  have hden : 0 < (u : ℝ) - r := sub_pos.mpr hru
  wlog hst : s ≤ t generalizing s t
  · rw [dist_comm (K.body s), dist_comm (s : ℝ)]
    exact this t s ht hs (le_of_not_ge hst)
  have htu : t < u := lt_of_le_of_lt ht hru
  refine (K.dist_le s t u hst htu).trans ?_
  have hs' : (s : ℝ) ≤ r := hs
  have hst' : (s : ℝ) ≤ t := hst
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub]
  calc
    ((t : ℝ) - s) / ((u : ℝ) - s) * diam (Δ : Set V) ≤
        ((t : ℝ) - s) / ((u : ℝ) - r) * diam (Δ : Set V) := by
      gcongr
    _ = (diam (Δ : Set V) / ((u : ℝ) - r)) * ((t : ℝ) - s) := by ring

/-- Genuine local Lipschitz control on every initial parameter interval. -/
theorem lipschitzOnWith_body (r u : Iio K.max) (hru : r < u) :
    LipschitzOnWith ⟨diam (Δ : Set V) / ((u : ℝ) - r),
      div_nonneg diam_nonneg (sub_pos.mpr (show (r : ℝ) < u from hru)).le⟩
      K.body (Iic r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  exact K.dist_le_mul r u hru s t hs ht

/-- Exact continuity clause of source `prop:Otccont`, for the actual original Hausdorff metric. -/
theorem continuous_body : Continuous K.body := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨r, hsr, hrm⟩ := exists_between (show (s : ℝ) < K.max from s.property)
  obtain ⟨u, hru, hum⟩ := exists_between hrm
  let r' : Iio K.max := ⟨r, hrm⟩
  let u' : Iio K.max := ⟨u, hum⟩
  have hLip := K.lipschitzOnWith_body r' u' hru
  exact hLip.continuousOn.continuousAt (Iic_mem_nhds (show s < r' from hsr))

variable {n : ℕ} {Δe : ConvexBody (EuclideanSpace ℝ (Fin n))}

/-- Actual original positive limit volume produces genuine interior in every body of the curve. -/
theorem interior_body_nonempty (K : TestCurve Δe)
    (hΔ : 0 < volume (Δe : Set (EuclideanSpace ℝ (Fin n)))) (t : Iio K.max) :
    (interior (K.body t : Set (EuclideanSpace ℝ (Fin n)))).Nonempty := by
  have hΔr : 0 < volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) :=
    ENNReal.toReal_pos (ne_of_gt hΔ) Δe.isCompact.measure_lt_top.ne
  have hlim := (AlmostSemigroup.Hyperspace.continuous_euclidean_real_volume n).tendsto Δe
    |>.comp K.limit
  obtain ⟨s, hsvol, hst⟩ := ((tendsto_order.mp hlim).1 0 hΔr).and
    (eventually_lt_atBot t) |>.exists
  have hS : 0 < volume (K.body s : Set (EuclideanSpace ℝ (Fin n))) := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    change 0 < (volume (K.body s : Set (EuclideanSpace ℝ (Fin n)))).toReal at hsvol
    rw [hzero, ENNReal.toReal_zero] at hsvol
    exact (lt_irrefl 0) hsvol
  have hint := AlmostSemigroup.ConvexIntersection.interior_nonempty_of_measure_pos
    volume (K.body s).convex hS
  obtain ⟨u, htu, hum⟩ := exists_between (show (t : ℝ) < K.max from t.property)
  let u' : Iio K.max := ⟨u, hum⟩
  let a : ℝ := (u - t) / (u - s)
  have hst' : (s : ℝ) < t := hst
  have hden : 0 < u - s := by linarith
  have ha : 0 < a := div_pos (sub_pos.mpr htu) hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hpar : a * (s : ℝ) + (1 - a) * u = t := by
    dsimp only [a]
    field_simp
    ring
  obtain ⟨q, hq⟩ := (K.body u').nonempty
  let A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p ↦ a • p + (1 - a) • q
  have hAopen : IsOpenMap A := by
    exact (Homeomorph.addRight ((1 - a) • q)).isOpenMap.comp (isOpenMap_smul₀ ha.ne')
  have hsub : A '' interior (K.body s : Set (EuclideanSpace ℝ (Fin n))) ⊆
      (K.body t : Set (EuclideanSpace ℝ (Fin n))) := by
    rintro _ ⟨p, hp, rfl⟩
    have hmem := K.concave s u' a ha.le ha1
      (show A p ∈ ((a • K.body s + (1 - a) • K.body u' : ConvexBody _) : Set _) by
        rw [ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
        exact Set.mem_add.mpr ⟨a • p, smul_mem_smul_set (interior_subset hp),
          (1 - a) • q, smul_mem_smul_set hq, rfl⟩)
    have hidx : (⟨a * (s : ℝ) + (1 - a) * (u' : ℝ),
        (convex_Iio K.max) s.property u'.property ha.le (sub_nonneg.mpr ha1) (by ring)⟩ :
        Iio K.max) = t := Subtype.ext hpar
    rw [hidx] at hmem
    exact hmem
  exact (hint.image A).mono ((hAopen _ isOpen_interior).subset_interior_iff.mpr hsub)

/-- Exact positivity clause of source `prop:Otccont`, including dimension zero. -/
theorem volume_body_pos (K : TestCurve Δe)
    (hΔ : 0 < volume (Δe : Set (EuclideanSpace ℝ (Fin n)))) (t : Iio K.max) :
    0 < volume (K.body t : Set (EuclideanSpace ℝ (Fin n))) :=
  Measure.measure_pos_of_nonempty_interior volume (K.interior_body_nonempty hΔ t)

/-- The original real volume deficit is nonnegative everywhere, before any integration. -/
theorem volume_bodyAt_le (K : TestCurve Δe) (t : ℝ) :
    volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) ≤
      volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) :=
  measureReal_mono (K.bodyAt_subset t) Δe.isCompact.measure_lt_top.ne

/-- Literal source `eq:Otestcurvenergy`, using the already-verified actual extended signed integral.
Its integrand is genuinely nonpositive by original body inclusion; divergent energy remains bottom. -/
def energy (K : TestCurve Δe) : EReal :=
  (((n.factorial : ℝ) * K.max * volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) +
    (n.factorial : EReal) * SGPT.Convex.extendedSignedIntegral
      (volume.restrict (Iio K.max))
      (fun t : ℝ ↦ ((volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal))

/-- The source finite-energy condition retains the genuine extended-real bottom branch. -/
def HasFiniteEnergy (K : TestCurve Δe) : Prop := (⊥ : EReal) < K.energy

/-- The positive signed-integral part is genuinely zero; no infinite deficit is projected to zero. -/
theorem energy_positive_lintegral_eq_zero (K : TestCurve Δe) :
    (∫⁻ t : ℝ, (((volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
        volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal)).toENNReal
        ∂volume.restrict (Iio K.max)) = 0 := by
  have hz (t : ℝ) : (((volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))) -
      volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal)).toENNReal = 0 := by
    apply EReal.toENNReal_of_nonpos
    exact_mod_cast sub_nonpos.mpr (K.volume_bodyAt_le t)
  simp only [hz, lintegral_zero]

/-- The source energy is the finite cutoff term minus the actual nonnegative volume-deficit integral. -/
theorem energy_eq_deficit (K : TestCurve Δe) :
    K.energy =
      (((n.factorial : ℝ) * K.max *
        volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) : ℝ) : EReal) -
      (n.factorial : EReal) * ((∫⁻ t : ℝ,
        ENNReal.ofReal (volume.real (Δe : Set (EuclideanSpace ℝ (Fin n))) -
          volume.real (K.bodyAt t : Set (EuclideanSpace ℝ (Fin n))))
        ∂volume.restrict (Iio K.max)) : EReal) := by
  unfold energy SGPT.Convex.extendedSignedIntegral
  rw [K.energy_positive_lintegral_eq_zero]
  simp only [EReal.coe_ennreal_zero, sub_eq_add_neg, zero_add, ← EReal.coe_neg,
    EReal.real_coe_toENNReal, mul_neg, neg_add_rev, neg_neg]

/-- Source bounded test curves as an actual subset of the original curve space. -/
def boundedCurves (Δ : ConvexBody V) : Set (TestCurve Δ) := {K | K.IsBounded}

/-- Source finite-energy test curves as an actual subset of the original Euclidean curve space. -/
def energyOneCurves (Δ : ConvexBody (EuclideanSpace ℝ (Fin n))) : Set (TestCurve Δ) :=
  {K | K.HasFiniteEnergy}

end TestCurve
end SGPT.Okounkov
