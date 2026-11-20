import SGPT.AlmostSemigroup.OkounkovComparison
import SGPT.AlmostSemigroup.Intersection

/-!
# Lattice sets that fill a convex body

A purely convex-geometric criterion used for the algebraic partial Okounkov bodies of the chapter
*The theory of Okounkov bodies* (source Section *Algebraic partial Okounkov bodies*,
`thm:Gammaasg`, `cor:POBvolume`, `cor:transalgPOB`, `thm:HCP`).

Let `C` be an admissible cone (source Appendix *Almost semigroups*), `K ⊆ heightOne C` a compact
convex set of positive volume and `S ⊆ C` a lattice set such that

* (**upper**) for every `η > 0` and all `k ≫ 0`, the normalized points `k⁻¹ x`, `x ∈ S_k`, lie in
  the closed `η`-neighbourhood of `K`;
* (**lower**) `liminf_k k⁻ⁿ #S_k ≥ vol K`.

Then `S` fills almost all lattice points of the dilates `k K`: its distance `d_sg` to the
saturated semigroup `R(K) = {(x, k) : k > 0, k⁻¹ x ∈ K}` vanishes. Consequently `S` is an almost
semigroup (`S ∈ 𝒮'(C)‾_{>0}`, source `def:SpCbar`), its Okounkov body (the continuous extension of
source `thm:Okocont`) is `K`, and the degree polytopes `Conv{k⁻¹ x : x ∈ S_k}` converge to `K` in
the Hausdorff metric.

## Main results

* `bodyLatticeSemigroup K`: the semigroup `R(K)`; `generatedGroup_bodyLatticeSemigroup`: it
  generates `ℤⁿ⁺¹` (for `vol K > 0`), and `body_bodyLatticeSemigroup`: its Okounkov body is `K`.
* `tendsto_normalizedDiscrepancy_of_fills`, `dist_eq_zero_of_fills`: `d_sg(S, R(K)) = 0`.
* `mem_almostSemigroupLocus_of_fills`: `S ∈ 𝒮'(C)‾_{>0}`, with volume `vol K`.
* `bodyExtension_eq_of_fills`: the Okounkov body of `S` is `K`.
* `tendsto_hausdorffDist_of_fills`: Hausdorff convergence of the degree polytopes to `K`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.AlgPOB

open Set Filter MeasureTheory Metric
open scoped Topology Pointwise symmDiff
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.OkounkovExtension

variable {n : ℕ}

/-! ### The saturated semigroup of a convex body -/

/-- The lattice points of positive degree of the cone over a convex set `K`:
`R(K) = {(x, k) : k > 0, k⁻¹ x ∈ K}`. -/
def bodyLatticeSemigroup (K : Set (Fin n → ℝ)) (hK : Convex ℝ K) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) where
  carrier := {z | 0 < z.2 ∧ ((z.2 : ℝ))⁻¹ • Counting.integerCast z.1 ∈ K}
  add_mem' := by
    rintro ⟨x, k⟩ ⟨y, l⟩ ⟨hk, hx⟩ ⟨hl, hy⟩
    refine ⟨add_pos hk hl, ?_⟩
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hlR : (0 : ℝ) < l := by exact_mod_cast hl
    have h := convex_iff_div.mp hK hx hy hkR.le hlR.le (add_pos hkR hlR)
    have hcast : Counting.integerCast (x + y) = Counting.integerCast x + Counting.integerCast y := by
      funext i
      simp [Counting.integerCast]
    have hxcoef : (k : ℝ) / ((k : ℝ) + l) * (k : ℝ)⁻¹ = ((k : ℝ) + l)⁻¹ := by
      field_simp
    have hycoef : (l : ℝ) / ((k : ℝ) + l) * (l : ℝ)⁻¹ = ((k : ℝ) + l)⁻¹ := by
      field_simp
    change (((k + l : ℤ) : ℝ))⁻¹ • Counting.integerCast (x + y) ∈ K
    rw [hcast, Int.cast_add, smul_add]
    simpa only [smul_smul, hxcoef, hycoef] using h

variable {K : Set (Fin n → ℝ)}

theorem mem_bodyLatticeSemigroup (hK : Convex ℝ K) (z : (Fin n → ℤ) × ℤ) :
    z ∈ bodyLatticeSemigroup K hK ↔ 0 < z.2 ∧ ((z.2 : ℝ))⁻¹ • Counting.integerCast z.1 ∈ K :=
  Iff.rfl

/-- `R(K)` lies in every admissible cone whose height-one slice contains `K`. -/
theorem bodyLatticeSemigroup_le (C : AdmissibleCone n) (hK : Convex ℝ K)
    (hKC : K ⊆ heightOne C.cone) : bodyLatticeSemigroup K hK ≤ latticePoints C.cone := by
  rintro ⟨x, k⟩ ⟨hk, hx⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : ((((k : ℤ) : ℝ))⁻¹ • Counting.integerCast x, (1 : ℝ)) ∈ C.cone := hKC hx
  have h2 := C.cone.smul_mem hkR h1
  change latticeCast n (x, k) ∈ C.cone
  convert h2 using 1
  ext i
  · simp [latticeCast, Counting.integerCast, smul_smul, hkR.ne']
  · simp [latticeCast]

/-- The degree-`k` slice of `R(K)` (`k > 0`) consists of the integer points of `k K`. -/
theorem mem_slice_bodyLatticeSemigroup (hK : Convex ℝ K) {k : ℕ} (hk : 0 < k)
    (x : Fin n → ℤ) :
    x ∈ slice (bodyLatticeSemigroup K hK : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) ↔
      x ∈ Counting.integerPoints ((k : ℝ) • K) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  change (0 < (k : ℤ) ∧ (((k : ℤ) : ℝ))⁻¹ • Counting.integerCast x ∈ K) ↔
    Counting.integerCast x ∈ (k : ℝ) • K
  rw [mem_smul_set_iff_inv_smul_mem₀ hkR]
  simp only [Int.cast_natCast]
  exact ⟨fun h => h.2, fun h => ⟨by exact_mod_cast hk, h⟩⟩

/-- The normalized cardinalities of `R(K)` are the normalized lattice counts of `K`. -/
theorem normalizedCardinality_bodyLatticeSemigroup (C : AdmissibleCone n) (hK : Convex ℝ K)
    (hKC : K ⊆ heightOne C.cone) {k : ℕ} (hk : 0 < k) :
    (sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC)).normalizedCardinality k =
      (k : ℝ)⁻¹ ^ n * Counting.integerLatticeCount K k := by
  rw [ConeSubset.normalizedCardinality, card_sourceSubset_slices, Counting.integerLatticeCount,
    Set.ext (mem_slice_bodyLatticeSemigroup hK hk)]

/-- `k⁻ⁿ #R(K)_k → vol K`. -/
theorem tendsto_normalizedCardinality_bodyLatticeSemigroup (C : AdmissibleCone n)
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKC : K ⊆ heightOne C.cone) :
    Tendsto (sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC)).normalizedCardinality atTop
      (𝓝 (volume.real K)) := by
  apply (Counting.tendsto_integer_lattice_count hKc hK).congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (normalizedCardinality_bodyLatticeSemigroup C hK hKC hk).symm

/-- The Okounkov body of `R(K)` lies in `K` (`K` closed). -/
theorem body_bodyLatticeSemigroup_subset (C : AdmissibleCone n) (hKc : IsClosed K)
    (hK : Convex ℝ K) (hKC : K ⊆ heightOne C.cone) : body (bodyLatticeSemigroup K hK) ⊆ K := by
  rw [body_eq_closure_convexHull C _ (bodyLatticeSemigroup_le C hK hKC)]
  refine closure_minimal (convexHull_min ?_ hK) hKc
  rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
  exact hz.2

/-- **`R(K)` generates `ℤⁿ⁺¹`** when `vol K > 0`. -/
theorem generatedGroup_bodyLatticeSemigroup (C : AdmissibleCone n) (hKc : IsCompact K)
    (hK : Convex ℝ K) (hKC : K ⊆ heightOne C.cone) (hvol : 0 < volume.real K) :
    LatticeSlices.generatedGroup (bodyLatticeSemigroup K hK) = ⊤ :=
  Intersection.generatedGroup_eq_top_of_full_count_limit C _ (bodyLatticeSemigroup_le C hK hKC)
    hKc (body_bodyLatticeSemigroup_subset C hKc.isClosed hK hKC) hvol
    (tendsto_normalizedCardinality_bodyLatticeSemigroup C hKc hK hKC)

/-- **The Okounkov body of `R(K)` is `K`** (`K` compact convex of positive volume). -/
theorem body_bodyLatticeSemigroup (C : AdmissibleCone n) (hKc : IsCompact K)
    (hK : Convex ℝ K) (hKC : K ⊆ heightOne C.cone) (hvol : 0 < volume.real K) :
    body (bodyLatticeSemigroup K hK) = K := by
  have hsub := body_bodyLatticeSemigroup_subset C hKc.isClosed hK hKC
  have hG := generatedGroup_bodyLatticeSemigroup C hKc hK hKC hvol
  have hR := bodyLatticeSemigroup_le C hK hKC
  have hvolB : volume.real (body (bodyLatticeSemigroup K hK)) = volume.real K := by
    rw [← BodyGeometry.volume_source_eq_body C _ hR hG]
    exact (tendsto_normalizedCardinality_bodyLatticeSemigroup C hKc hK hKC).limsup_eq
  refine hsub.antisymm (Intersection.subset_of_volume_inter_eq hKc
    (isCompact_body C _ hR (nonempty_of_generatedGroup_eq_top _ hG)).isClosed hK
    (interior_nonempty_of_positive_volume hKc.isClosed hK hvol) ?_)
  rw [Set.inter_eq_right.mpr hsub, hvolB]

/-- `R(K)` as a member of the full semigroup locus `𝒮'(C)`. -/
def bodyFullSemigroup (C : AdmissibleCone n) (hKc : IsCompact K) (hK : Convex ℝ K)
    (hKC : K ⊆ heightOne C.cone) (hvol : 0 < volume.real K) : FullSemigroup C :=
  ⟨sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC),
    sourceSubset_mem_fullSemigroupLocus C _ _ (generatedGroup_bodyLatticeSemigroup C hKc hK hKC hvol)⟩

/-- The Euclidean Okounkov body of `R(K)` is the Euclidean image of `K`. -/
theorem coe_bodyMap_bodyFullSemigroup (C : AdmissibleCone n) (hKc : IsCompact K)
    (hK : Convex ℝ K) (hKC : K ⊆ heightOne C.cone) (hvol : 0 < volume.real K) :
    (bodyMap (bodyFullSemigroup C hKc hK hKC hvol) : Set (EuclideanSpace ℝ (Fin n))) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' K := by
  change (EuclideanSpace.equiv (Fin n) ℝ).symm '' body _ = _
  have hsg : (bodyFullSemigroup C hKc hK hKC hvol).semigroup = bodyLatticeSemigroup K hK :=
    AddSubsemigroup.ext fun _ => Iff.rfl
  rw [hsg, body_bodyLatticeSemigroup C hKc hK hKC hvol]

/-! ### Lattice sets filling a convex body -/

section Fills

variable (C : AdmissibleCone n) (hKc : IsCompact K) (hK : Convex ℝ K)
  (hKC : K ⊆ heightOne C.cone) (S : ConeSubset C)

include hKc in
/-- For every `ε > 0` there is `η > 0` with `vol (K^η) < vol K + ε` (closed thickening). -/
theorem exists_volume_cthickening_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ volume.real (cthickening η K) < volume.real K + ε := by
  have h := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure (Fin n → ℝ))) hKc
  have hlt : volume K < ENNReal.ofReal (volume.real K + ε) := by
    rw [← ENNReal.ofReal_toReal hKc.measure_lt_top.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by simp only [measureReal_def] at *; linarith)
  have hev := (h.eventually (gt_mem_nhds hlt)).filter_mono
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨η, hη, hη0⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨η, hη0, ?_⟩
  have hfin : volume (cthickening η K) ≠ ⊤ :=
    (hKc.cthickening (r := η)).measure_lt_top.ne
  rw [measureReal_def, ← ENNReal.toReal_ofReal (by positivity : 0 ≤ volume.real K + ε)]
  exact (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hη

include hKc hK hKC in
/-- **`S` fills `K`**: under the upper and lower hypotheses, the normalized symmetric differences
`k⁻ⁿ #(S_k Δ R(K)_k)` tend to `0`. -/
theorem tendsto_normalizedDiscrepancy_of_fills
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k) :
    Tendsto (normalizedDiscrepancy n S.slices
      (sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC)).slices) atTop (𝓝 0) := by
  classical
  set R := sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC) with hRdef
  apply tendsto_order.mpr
  refine ⟨fun δ hδ => Eventually.of_forall fun k => hδ.trans_le
    (normalizedDiscrepancy_nonneg n _ _ k), fun δ hδ => ?_⟩
  set ε := δ / 7 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨η, hη, hηvol⟩ := exists_volume_cthickening_lt hKc hε
  set K' := cthickening η K with hK'def
  have hK'c : IsCompact K' := hKc.cthickening
  have hK'v : Convex ℝ K' := hK.cthickening η
  have hcount := Counting.tendsto_integer_lattice_count hK'c hK'v
  have hcountR := tendsto_normalizedCardinality_bodyLatticeSemigroup C hKc hK hKC
  filter_upwards [(tendsto_order.mp hcount).2 _ (lt_add_of_pos_right _ hε),
    (tendsto_order.mp hcountR).1 _ (sub_lt_self _ hε), hlow ε hε, hup η hη,
    eventually_gt_atTop 0] with k hk1 hk2 hk3 hk4 hk5
  -- all points of `S_k` and `R(K)_k` are integer points of `k K'`
  set T := (Counting.finite_integerPoints_dilate hK'c k).toFinset with hTdef
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk5.ne'
  have hST : S.slices k ⊆ T := by
    intro x hx
    rw [hTdef, Set.Finite.mem_toFinset]
    change Counting.integerCast x ∈ (k : ℝ) • K'
    rw [mem_smul_set_iff_inv_smul_mem₀ hkR]
    exact hk4 x hx
  have hRT : R.slices k ⊆ T := by
    intro x hx
    rw [hTdef, Set.Finite.mem_toFinset]
    have hx' := (mem_slice_bodyLatticeSemigroup hK hk5 x).mp ((ConeSubset.mem_slices R k x).mp hx)
    exact Set.smul_set_mono (self_subset_cthickening K) hx'
  have hTcard : T.card = Counting.integerLatticeCount K' k :=
    (Nat.card_eq_card_finite_toFinset (Counting.finite_integerPoints_dilate hK'c k)).symm
  -- the finite estimate `#(S Δ R) ≤ 2 #T - #S - #R`
  have hfin : (discrepancy (S.slices k) (R.slices k) : ℝ) ≤
      2 * (T.card : ℝ) - (S.slices k).card - (R.slices k).card := by
    have h1 := discrepancy_formula (S.slices k) (R.slices k)
    have h2 := Finset.card_union_add_card_inter (S.slices k) (R.slices k)
    have h3 := Finset.card_le_card (Finset.union_subset hST hRT)
    have h1' : (discrepancy (S.slices k) (R.slices k) : ℝ) +
        2 * ((S.slices k ∩ R.slices k).card : ℝ) = (S.slices k).card + (R.slices k).card := by
      exact_mod_cast h1
    have h2' : ((S.slices k ∪ R.slices k).card : ℝ) + ((S.slices k ∩ R.slices k).card : ℝ) =
        (S.slices k).card + (R.slices k).card := by exact_mod_cast h2
    have h3' : ((S.slices k ∪ R.slices k).card : ℝ) ≤ T.card := by exact_mod_cast h3
    linarith
  have hc : (0 : ℝ) < (k : ℝ)⁻¹ ^ n := by positivity
  have hnd : normalizedDiscrepancy n S.slices R.slices k ≤
      2 * ((k : ℝ)⁻¹ ^ n * T.card) - S.normalizedCardinality k - R.normalizedCardinality k := by
    rw [normalizedDiscrepancy, ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality]
    nlinarith [mul_le_mul_of_nonneg_left hfin hc.le]
  rw [hTcard] at hnd
  have hK'vol : volume.real K' < volume.real K + ε := hηvol
  calc normalizedDiscrepancy n S.slices R.slices k
      ≤ 2 * ((k : ℝ)⁻¹ ^ n * Counting.integerLatticeCount K' k) - S.normalizedCardinality k -
          R.normalizedCardinality k := hnd
    _ ≤ 2 * (volume.real K' + ε) - (volume.real K - ε) - (volume.real K - ε) := by
        have := hk1.le
        linarith
    _ < δ := by rw [hεdef] at hK'vol ⊢; linarith

include hKc hK hKC in
/-- Under the upper and lower hypotheses, `k⁻ⁿ #S_k → vol K`. -/
theorem tendsto_normalizedCardinality_of_fills
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k) :
    Tendsto S.normalizedCardinality atTop (𝓝 (volume.real K)) := by
  set R := sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC) with hRdef
  have hdisc := tendsto_normalizedDiscrepancy_of_fills C hKc hK hKC S hup hlow
  refine (tendsto_normalizedCardinality_bodyLatticeSemigroup C hKc hK hKC).congr_dist ?_
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hdisc
  rw [Real.dist_eq, ConeSubset.normalizedCardinality, ConeSubset.normalizedCardinality,
    ← mul_sub, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
  exact mul_le_mul_of_nonneg_left (abs_card_sub_le_discrepancy _ _) (by positivity)

include hKc hK hKC in
/-- **`d_sg(S, R(K)) = 0`** under the upper and lower hypotheses. -/
theorem dist_eq_zero_of_fills
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k) :
    dist S (sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC)) = 0 := by
  rw [ConeSubset.dist_eq_distance, ConeSubset.distance, asymptoticDistance]
  exact (tendsto_normalizedDiscrepancy_of_fills C hKc hK hKC S hup hlow).limsup_eq

include hKc hK hKC in
/-- **`S` is an almost semigroup** (source `def:SpCbar`): `S ∈ 𝒮'(C)‾_{>0}`, with
`vol S = vol K`. -/
theorem mem_almostSemigroupLocus_of_fills (hvol : 0 < volume.real K)
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k) :
    S ∈ almostSemigroupLocus C ∧ S.volume = volume.real K := by
  have hd := dist_eq_zero_of_fills C hKc hK hKC S hup hlow
  set R := bodyFullSemigroup C hKc hK hKC hvol with hRdef
  have hvolR : R.val.volume = volume.real K :=
    (tendsto_normalizedCardinality_bodyLatticeSemigroup C hKc hK hKC).limsup_eq
  have hvolS : S.volume = volume.real K := by
    have h := ConeSubset.abs_volume_sub_le_distance S R.val
    rw [← ConeSubset.dist_eq_distance] at h
    change |S.volume - R.val.volume| ≤ dist S (sourceSubset C _ _) at h
    rw [hd, abs_nonpos_iff, sub_eq_zero] at h
    rw [h, hvolR]
  refine ⟨⟨Metric.mem_closure_iff.mpr fun ε hε => ⟨R.val, R.property, ?_⟩, ?_⟩, hvolS⟩
  · change dist S (sourceSubset C _ _) < ε
    rw [hd]
    exact hε
  · change 0 < S.volume
    rw [hvolS]
    exact hvol

include hKc hK hKC in
/-- **The Okounkov body of `S` is `K`**: the value of the continuous extension of the Okounkov
body map (source `thm:Okocont`) at `S` is the Euclidean image of `K`. -/
theorem bodyExtension_eq_of_fills (hvol : 0 < volume.real K)
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k)
    (hS : S ∈ almostSemigroupLocus C) :
    (bodyExtension (⟨S, hS⟩ : AlmostSpace C) : Set (EuclideanSpace ℝ (Fin n))) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm '' K := by
  have hd := dist_eq_zero_of_fills C hKc hK hKC S hup hlow
  set R := bodyFullSemigroup C hKc hK hKC hvol with hRdef
  have hins : Inseparable (⟨S, hS⟩ : AlmostSpace C) (fullToAlmost R) :=
    Metric.inseparable_iff.mpr hd
  have heq := (hins.map (continuous_bodyExtension C)).eq
  rw [heq, bodyExtension_source]
  exact coe_bodyMap_bodyFullSemigroup C hKc hK hKC hvol

include hKc hK hKC in
/-- **Density**: every open set meeting `K` contains normalized points of `S_k` for all `k ≫ 0`. -/
theorem eventually_exists_normalized_mem_of_fills (hvol : 0 < volume.real K)
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hUK : (K ∩ U).Nonempty) :
    ∀ᶠ k : ℕ in atTop, ∃ x ∈ S.slices k, ((k : ℝ))⁻¹ • Counting.integerCast x ∈ U := by
  classical
  obtain ⟨z, hzK, hzU⟩ := hUK
  have hint := interior_nonempty_of_positive_volume hKc.isClosed hK hvol
  have hzcl : z ∈ closure (interior K) := by
    rw [hK.closure_interior_eq_closure_of_nonempty_interior hint, hKc.isClosed.closure_eq]
    exact hzK
  obtain ⟨y, hyU, hyK⟩ := mem_closure_iff.mp hzcl U hU hzU
  have hnhds : K ∩ U ∈ 𝓝 y :=
    inter_mem (Filter.mem_of_superset (isOpen_interior.mem_nhds hyK) interior_subset)
      (hU.mem_nhds hyU)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhds
  set Q := closedBall y r with hQdef
  have hQc : IsCompact Q := isCompact_closedBall y r
  have hvolQ : 0 < volume.real Q := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (Measure.measure_pos_of_nonempty_interior volume
        ⟨y, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)⟩)
    · exact hQc.measure_lt_top.ne
  have hcount := Counting.tendsto_integer_lattice_count hQc (convex_closedBall y r)
  have hdisc := tendsto_normalizedDiscrepancy_of_fills C hKc hK hKC S hup hlow
  set R := sourceSubset C _ (bodyLatticeSemigroup_le C hK hKC) with hRdef
  filter_upwards [(tendsto_order.mp hcount).1 (volume.real Q / 2) (by linarith),
    (tendsto_order.mp hdisc).2 (volume.real Q / 2) (by linarith), eventually_gt_atTop 0]
    with k hk1 hk2 hk3
  by_contra hnone
  push Not at hnone
  -- the integer points of `k Q` lie in `R(K)_k \ S_k`
  set F := (Counting.finite_integerPoints_dilate hQc k).toFinset with hFdef
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk3.ne'
  have hFsub : F ⊆ R.slices k \ S.slices k := by
    intro x hx
    rw [hFdef, Set.Finite.mem_toFinset] at hx
    change Counting.integerCast x ∈ (k : ℝ) • Q at hx
    rw [mem_smul_set_iff_inv_smul_mem₀ hkR] at hx
    rw [Finset.mem_sdiff]
    refine ⟨(ConeSubset.mem_slices R k x).mpr ((mem_slice_bodyLatticeSemigroup hK hk3 x).mpr ?_),
      fun hxS => hnone x hxS (hball hx).2⟩
    change Counting.integerCast x ∈ (k : ℝ) • K
    rw [mem_smul_set_iff_inv_smul_mem₀ hkR]
    exact (hball hx).1
  have hFcard : F.card = Counting.integerLatticeCount Q k :=
    (Nat.card_eq_card_finite_toFinset (Counting.finite_integerPoints_dilate hQc k)).symm
  have hle : (F.card : ℝ) ≤ discrepancy (S.slices k) (R.slices k) := by
    have h1 := Finset.card_le_card hFsub
    have h2 : (R.slices k \ S.slices k) ⊆ S.slices k ∆ R.slices k := by
      intro x hx
      rw [Finset.mem_symmDiff]
      exact Or.inr (Finset.mem_sdiff.mp hx)
    exact_mod_cast h1.trans (Finset.card_le_card h2)
  have hc : (0 : ℝ) ≤ (k : ℝ)⁻¹ ^ n := by positivity
  have := mul_le_mul_of_nonneg_left hle hc
  rw [hFcard] at this
  change _ ≤ normalizedDiscrepancy n S.slices R.slices k at this
  linarith

/-- The degree polytope `Conv{k⁻¹ x : x ∈ S_k}` of a lattice set, in Euclidean coordinates. -/
def euclideanDegreePolytope (S : Set ((Fin n → ℤ) × ℤ)) (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm ''
    convexHull ℝ ((fun x => ((k : ℝ))⁻¹ • Counting.integerCast x) '' slice S (k : ℤ))

include hKc hK hKC in
/-- **Hausdorff convergence of the degree polytopes**: `Conv{k⁻¹ x : x ∈ S_k} → K` in the
Euclidean Hausdorff metric. -/
theorem tendsto_hausdorffDist_of_fills (hvol : 0 < volume.real K)
    (hup : ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast x ∈ cthickening η K)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, volume.real K - ε ≤ S.normalizedCardinality k) :
    Tendsto (fun k => hausdorffDist (euclideanDegreePolytope S.val k)
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' K)) atTop (𝓝 0) := by
  classical
  set e := (EuclideanSpace.equiv (Fin n) ℝ).symm with he
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x y : Fin n → ℝ, dist (e x) (e y) ≤ c * dist x y := by
    refine ⟨‖(e : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ + 1, by positivity, fun x y => ?_⟩
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖e (x - y)‖ ≤ ‖(e : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ * ‖x - y‖ :=
          (e : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)).le_opNorm (x - y)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have heK : IsCompact (e '' K) := hKc.image e.continuous
  apply tendsto_order.mpr
  refine ⟨fun r hr => Eventually.of_forall fun k => hr.trans_le hausdorffDist_nonneg,
    fun ε hε => ?_⟩
  set r := ε / 3 with hrdef
  have hr : 0 < r := by positivity
  -- finitely many centres covering `e '' K`
  obtain ⟨t, ht⟩ := heK.elim_finite_subcover
    (fun x : e '' K => Metric.ball x.val r) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self hr⟩)
  have hevent (x : e '' K) : ∀ᶠ k : ℕ in atTop, ∃ y ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast y ∈ e ⁻¹' Metric.ball x.val r := by
    obtain ⟨z, hz, hzx⟩ := x.property
    refine eventually_exists_normalized_mem_of_fills C hKc hK hKC S hvol hup hlow
      (Metric.isOpen_ball.preimage e.continuous) ⟨z, hz, ?_⟩
    change e z ∈ Metric.ball x.val r
    rw [hzx]
    exact Metric.mem_ball_self hr
  have hall : ∀ᶠ k : ℕ in atTop, ∀ x ∈ t, ∃ y ∈ S.slices k,
      ((k : ℝ))⁻¹ • Counting.integerCast y ∈ e ⁻¹' Metric.ball x.val r :=
    (Filter.eventually_all_finset t).mpr fun x _ => hevent x
  filter_upwards [hall, hup (r / c) (by positivity)] with k hk hkup
  have hbound : hausdorffDist (euclideanDegreePolytope S.val k) (e '' K) ≤ 2 * r := by
    apply hausdorffDist_le_of_mem_dist (by positivity)
    · rintro _ ⟨x, hx, rfl⟩
      have hxK : x ∈ cthickening (r / c) K := by
        refine convexHull_min ?_ (hK.cthickening _) hx
        rintro _ ⟨y, hy, rfl⟩
        exact hkup y ((ConeSubset.mem_slices S k y).mpr hy)
      obtain ⟨z, hz, hdz⟩ := hKc.exists_infDist_eq_dist
        ((interior_nonempty_of_positive_volume hKc.isClosed hK hvol).mono interior_subset) x
      refine ⟨e z, mem_image_of_mem e hz, ?_⟩
      have h1 : infDist x K ≤ r / c :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) (mem_cthickening_iff.mp hxK)
      calc dist (e x) (e z) ≤ c * dist x z := hc x z
        _ ≤ c * (r / c) := by rw [← hdz]; exact mul_le_mul_of_nonneg_left h1 hc0.le
        _ = r := by field_simp
        _ ≤ 2 * r := by linarith
    · intro x hx
      obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp (ht hx)
      obtain ⟨y, hy, hyw⟩ := hk w hw
      refine ⟨e (((k : ℝ))⁻¹ • Counting.integerCast y), mem_image_of_mem e
        (subset_convexHull ℝ _ ⟨y, (ConeSubset.mem_slices S k y).mp hy, rfl⟩), ?_⟩
      have h1 : dist x w.val < r := hxw
      have h2 : dist (e (((k : ℝ))⁻¹ • Counting.integerCast y)) w.val < r := hyw
      calc dist x (e (((k : ℝ))⁻¹ • Counting.integerCast y))
          ≤ dist x w.val + dist w.val (e (((k : ℝ))⁻¹ • Counting.integerCast y)) :=
            dist_triangle _ _ _
        _ ≤ 2 * r := by rw [dist_comm w.val]; linarith
  exact hbound.trans_lt (by linarith)

end Fills

end SGPT.Okounkov.AlgPOB
