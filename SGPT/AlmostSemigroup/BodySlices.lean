import SGPT.AlmostSemigroup.BodyLimits
import SGPT.AlmostSemigroup.BodyExtrema
import Mathlib.Topology.Algebra.Module.Equiv

noncomputable section
namespace SGPT.AlmostSemigroup.BodySlices
open Set Filter Metric
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual nonempty first-coordinate projection of the original fixed body. -/
def projectionSet (K : ConvexBody (ℝ × V)) : Set ℝ := Prod.fst '' (K : Set (ℝ × V))

theorem isCompact_projectionSet (K : ConvexBody (ℝ × V)) : IsCompact (projectionSet K) :=
  K.isCompact.image continuous_fst

theorem nonempty_projectionSet (K : ConvexBody (ℝ × V)) : (projectionSet K).Nonempty :=
  K.nonempty.image Prod.fst

/-- The genuine compact convex projection is exactly the source attained-extrema interval. -/
theorem projectionSet_eq_Icc (K : ConvexBody (ℝ × V)) :
    projectionSet K = Icc (sInf (projectionSet K)) (sSup (projectionSet K)) := by
  have hc := isCompact_projectionSet K
  have hn := nonempty_projectionSet K
  have hconv : Convex ℝ (projectionSet K) := K.convex.linear_image (LinearMap.fst ℝ ℝ V)
  have ha := hc.isClosed.csInf_mem hn hc.bddBelow
  have hb := hc.isClosed.csSup_mem hn hc.bddAbove
  apply subset_antisymm
  · intro t ht
    exact ⟨csInf_le hc.bddBelow ht, le_csSup hc.bddAbove ht⟩
  · exact hconv.ordConnected.out ha hb

/-- Actual source fiber over an actual original projection value. -/
def slice (K : ConvexBody (ℝ × V)) (t : projectionSet K) : ConvexBody V where
  carrier := {y | ((t : ℝ), y) ∈ K}
  convex' := by
    intro y hy z hz a b ha hb hab
    change ((t : ℝ), y) ∈ (K : Set (ℝ × V)) at hy
    change ((t : ℝ), z) ∈ (K : Set (ℝ × V)) at hz
    change ((t : ℝ), a • y + b • z) ∈ (K : Set (ℝ × V))
    have h := K.convex hy hz ha hb hab
    have hf : a * (t : ℝ) + b * (t : ℝ) = t := by
      calc
        _ = (a + b) * (t : ℝ) := by ring
        _ = t := by rw [hab, one_mul]
    simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hf] using h
  isCompact' := by
    have hclosed : IsClosed {y : V | ((t : ℝ), y) ∈ K} :=
      K.isClosed.preimage (continuous_const.prodMk continuous_id)
    apply (K.isCompact.image continuous_snd).of_isClosed_subset hclosed
    intro y hy
    exact ⟨((t : ℝ), y), hy, rfl⟩
  nonempty' := by
    obtain ⟨x, hx, hxt⟩ := t.property
    refine ⟨x.2, ?_⟩
    change ((t : ℝ), x.2) ∈ (K : Set (ℝ × V))
    simpa only [← hxt, Prod.mk.eta] using hx

/-- A genuine convex endpoint combination lies in the exact intermediate original fiber. -/
theorem combination_mem (K : ConvexBody (ℝ × V)) {t a s : ℝ} {y z : V}
    (hy : (t, y) ∈ K) (hz : (a, z) ∈ K)
    (ht : t ≠ a) (hc : 0 ≤ (s - t) / (a - t)) (hc1 : (s - t) / (a - t) ≤ 1) :
    (s, (1 - (s - t) / (a - t)) • y + ((s - t) / (a - t)) • z) ∈ K := by
  change (s, (1 - (s - t) / (a - t)) • y + ((s - t) / (a - t)) • z) ∈ (K : Set (ℝ × V))
  have h := K.convex hy hz (by linarith : 0 ≤ 1 - (s - t) / (a - t)) hc (by ring)
  have hf : (1 - (s - t) / (a - t)) * t + ((s - t) / (a - t)) * a = s := by
    field_simp [sub_ne_zero.mpr ht.symm]
    ring
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hf] using h

/-- Actual endpoint convex combinations approximate every original slice point along the whole original parameter sequence. -/
theorem exists_slice_member_sequence (K : ConvexBody (ℝ × V))
    {u : ℕ → projectionSet K} {t : projectionSet K}
    (hu : Tendsto u atTop (𝓝 t)) {y : V} (hy : y ∈ slice K t) :
    ∃ q : ℕ → V, (∀ i, q i ∈ slice K (u i)) ∧ Tendsto q atTop (𝓝 y) := by
  change ((t : ℝ), y) ∈ (K : Set (ℝ × V)) at hy
  let a := sInf (projectionSet K)
  let b := sSup (projectionSet K)
  have hc := isCompact_projectionSet K
  have hn := nonempty_projectionSet K
  obtain ⟨p, hp, hpa⟩ := hc.isClosed.csInf_mem hn hc.bddBelow
  obtain ⟨r, hr, hrb⟩ := hc.isClosed.csSup_mem hn hc.bddAbove
  have hpK : (a, p.2) ∈ K := by
    change (a, p.2) ∈ (K : Set (ℝ × V))
    dsimp only [a]
    simpa only [← hpa, Prod.mk.eta] using hp
  have hrK : (b, r.2) ∈ K := by
    change (b, r.2) ∈ (K : Set (ℝ × V))
    dsimp only [b]
    simpa only [← hrb, Prod.mk.eta] using hr
  have hval : Tendsto (fun i ↦ (u i : ℝ)) atTop (𝓝 (t : ℝ)) :=
    (continuous_subtype_val.tendsto t).comp hu
  let low (i : ℕ) : V :=
    (1 - ((u i : ℝ) - t) / (a - t)) • y + (((u i : ℝ) - t) / (a - t)) • p.2
  let high (i : ℕ) : V :=
    (1 - ((u i : ℝ) - t) / (b - t)) • y + (((u i : ℝ) - t) / (b - t)) • r.2
  let q (i : ℕ) : V := if (u i : ℝ) ≤ t then low i else high i
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hs : a ≤ (u i : ℝ) ∧ (u i : ℝ) ≤ b :=
      ⟨csInf_le hc.bddBelow (u i).property, le_csSup hc.bddAbove (u i).property⟩
    have ht : a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b :=
      ⟨csInf_le hc.bddBelow t.property, le_csSup hc.bddAbove t.property⟩
    change ((u i : ℝ), q i) ∈ (K : Set (ℝ × V))
    dsimp only [q]
    split_ifs with hle
    · by_cases heq : (u i : ℝ) = t
      · simpa [low, heq] using hy
      · have hat : a < (t : ℝ) := lt_of_le_of_lt hs.1 (lt_of_le_of_ne hle heq)
        exact combination_mem K hy hpK (ne_of_gt hat)
          (div_nonneg_of_nonpos (sub_nonpos.mpr hle) (sub_nonpos.mpr ht.1))
          ((div_le_one_of_neg (sub_neg.mpr hat)).mpr (by linarith [hs.1]))
    · have htb : (t : ℝ) < b := lt_of_lt_of_le (lt_of_not_ge hle) hs.2
      exact combination_mem K hy hrK (ne_of_lt htb)
        (div_nonneg (sub_nonneg.mpr (le_of_not_ge hle)) (sub_nonneg.mpr ht.2))
        ((div_le_one (sub_pos.mpr htb)).mpr (by linarith [hs.2]))
  · have hlc : Tendsto (fun i ↦ ((u i : ℝ) - t) / (a - t)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, zero_div] using
        (hval.sub (tendsto_const_nhds (x := (t : ℝ)))).div_const (a - t)
    have hhc : Tendsto (fun i ↦ ((u i : ℝ) - t) / (b - t)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, zero_div] using
        (hval.sub (tendsto_const_nhds (x := (t : ℝ)))).div_const (b - t)
    have hl : Tendsto low atTop (𝓝 y) := by
      have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hlc).smul (tendsto_const_nhds (x := y))).add
        (hlc.smul (tendsto_const_nhds (x := p.2)))
      simpa [low] using h
    have hh : Tendsto high atTop (𝓝 y) := by
      have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hhc).smul (tendsto_const_nhds (x := y))).add
        (hhc.smul (tendsto_const_nhds (x := r.2)))
      simpa [high] using h
    exact hl.if' hh

variable [ProperSpace V]

/-- Actual fixed-body fibers converge in the genuine Hausdorff metric along the whole original convergent parameter sequence. -/
theorem tendsto_slice (K : ConvexBody (ℝ × V)) {u : ℕ → projectionSet K}
    {t : projectionSet K} (hu : Tendsto u atTop (𝓝 t)) :
    Tendsto (fun i ↦ slice K (u i)) atTop (𝓝 (slice K t)) := by
  apply BodyLimits.tendsto_of_point_member_conditions
  · intro y hy
    exact exists_slice_member_sequence K hu hy
  · intro φ hφ q y hq hqy
    have ht := ((continuous_subtype_val.tendsto t).comp hu).comp hφ.tendsto_atTop
    exact K.isClosed.mem_of_tendsto (ht.prodMk_nhds hqy) (Eventually.of_forall hq)

/-- Exact source Hausdorff continuity on the full actual projection interval, including both endpoints and the degenerate interval. -/
theorem continuous_slice (K : ConvexBody (ℝ × V)) : Continuous (slice K) :=
  continuous_iff_seqContinuous.mpr (fun _ _ hu ↦ tendsto_slice K hu)

section Euclidean
variable (n : ℕ)

/-- Actual head/tail Euclidean coordinates, used for geometry and topology rather than changing the target metric. -/
def joinEuclidean : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin n) ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)).trans
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm)

theorem joinEuclidean_apply (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    joinEuclidean n (t, y) = (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (Fin.cons t ((EuclideanSpace.equiv (Fin n) ℝ) y)) := rfl

/-- Actual fixed-body image in genuine first-coordinate/product coordinates. -/
def splitBody (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    ConvexBody (ℝ × EuclideanSpace ℝ (Fin n)) where
  carrier := (joinEuclidean n).symm '' (K : Set (EuclideanSpace ℝ (Fin (n + 1))))
  convex' := K.convex.linear_image (joinEuclidean n).symm.toLinearMap
  isCompact' := K.isCompact.image (joinEuclidean n).symm.continuous
  nonempty' := K.nonempty.image (joinEuclidean n).symm

/-- The actual source coordinate projection equals the genuine product projection. -/
theorem projectionSet_splitBody (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    projectionSet (splitBody n K) =
      (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x 0) '' (K : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  ext t
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(joinEuclidean n).symm x, ⟨x, hx, rfl⟩, rfl⟩

/-- Exact source projection interval with actual attained coordinate extrema. -/
theorem projectionSet_splitBody_eq_Icc
    (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    projectionSet (splitBody n K) =
      Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K) := by
  rw [projectionSet_eq_Icc, projectionSet_splitBody]
  rfl

/-- The exact original source Euclidean first-coordinate slice on its whole original interval. -/
def euclideanSlice (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (t : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K)) :
    ConvexBody (EuclideanSpace ℝ (Fin n)) :=
  slice (splitBody n K) ⟨t, (projectionSet_splitBody_eq_Icc n K).symm ▸ t.property⟩

/-- Actual source fiber membership, preserving the genuine remaining Euclidean coordinates. -/
theorem mem_euclideanSlice_iff (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1))))
    (t : Icc (BodyExtrema.coordinateMin 0 K) (BodyExtrema.coordinateMax 0 K))
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ euclideanSlice n K t ↔ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
      (Fin.cons (t : ℝ) ((EuclideanSpace.equiv (Fin n) ℝ) y)) ∈ K := by
  change ((t : ℝ), y) ∈ (joinEuclidean n).symm '' (K : Set _) ↔ _
  rw [ContinuousLinearEquiv.image_symm_eq_preimage]
  rfl

/-- Exact original SGPT lma:Hausdorffconvslice, including zero-dimensional fibers and both endpoint slices. -/
theorem continuous_euclideanSlice (K : ConvexBody (EuclideanSpace ℝ (Fin (n + 1)))) :
    Continuous (euclideanSlice n K) := by
  apply (continuous_slice (splitBody n K)).comp
  exact continuous_subtype_val.subtype_mk _

end Euclidean

end SGPT.AlmostSemigroup.BodySlices
