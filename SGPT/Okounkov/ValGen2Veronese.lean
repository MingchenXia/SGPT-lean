import SGPT.Okounkov.ValGenSections
import SGPT.Okounkov.AlgebraicBodyCones

/-!
# Veronese subsets of almost semigroups and their Okounkov bodies

Lane POB-VALGEN2, blueprint `claude-val-gen2.tex`. Source: chapter *The theory of Okounkov
bodies*, `prop:res` (`Δ_ν(aθ, aφ) = a Δ_ν(θ, φ)`), whose proof in the source reduces, through
log resolutions, to `prop:Okourescaling`. For an arbitrary valuation we argue directly with the
section sets: `Γ(aθ, aφ)` is the Veronese subset `{(x, k) : (x, ak) ∈ Γ(θ, φ)}` of `Γ(θ, φ)`
(`SGPT.Okounkov.ValGen2.mem_multiplierSectionSet_tensorPower_iff`), and this file shows that the
continuous extension `Δ` of the Okounkov body map (source `thm:Okocont`) commutes with Veronese
subsets: `Δ(S^{(a)}) = a Δ(S)` for every almost semigroup `S` (source `def:SpCbar`).

## Main results

* `veroneseCone C hr`: the admissible cone `C^{(r)} = {(x, t) : (x, r t) ∈ C}`;
  `veroneseSubset`: `S ↦ S^{(r)} = {(x, k) : (x, r k) ∈ S}`, `ConeSubset C → ConeSubset C^{(r)}`.
* `dist_veroneseSubset_le`: `d_sg(S^{(r)}, T^{(r)}) ≤ rⁿ d_sg(S, T)`.
* `veroneseSubset_mem_fullSemigroupLocus`: Veronese subsets of semigroups generating `ℤⁿ⁺¹`
  generate `ℤⁿ⁺¹` (via the conductor of `S`).
* `volume_veroneseSubset_of_mem_closure`: `vol S^{(r)} = rⁿ vol S` on the closure of `𝒮'(C)`.
* `veroneseSubset_mem_almostSemigroupLocus`: `S ∈ 𝒮'(C)‾_{>0} ⟹ S^{(r)} ∈ 𝒮'(C^{(r)})‾_{>0}`.
* **`bodyExtension_veroneseAlmost`**, `setBody_veroneseSet`: `Δ(S^{(r)}) = r Δ(S)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov.ValGen2

open Set Filter MeasureTheory Metric
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov SGPT.AlmostSemigroup.Class
  SGPT.AlmostSemigroup.OkounkovExtension
open scoped Topology Pointwise

variable {n : ℕ}

/-! ### Hausdorff distance of dilated convex bodies -/

/-- `d_Haus(c K, c L) ≤ |c| d_Haus(K, L)`. -/
theorem dist_smul_convexBody_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ)
    (K L : ConvexBody V) : dist (c • K) (c • L) ≤ |c| * dist K L := by
  rw [← ConvexBody.hausdorffDist_coe, ← ConvexBody.hausdorffDist_coe, ConvexBody.coe_smul,
    ConvexBody.coe_smul]
  have hd : 0 ≤ hausdorffDist (K : Set V) L := hausdorffDist_nonneg
  have key : ∀ (A B : ConvexBody V), ∀ x ∈ c • (A : Set V), ∃ y ∈ c • (B : Set V),
      dist x y ≤ |c| * hausdorffDist (A : Set V) B := by
    intro A B x hx
    obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp hx
    obtain ⟨b, hb, hab⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty a
    refine ⟨c • b, Set.smul_mem_smul_set hb, ?_⟩
    rw [dist_smul₀, Real.norm_eq_abs, ← hab]
    exact mul_le_mul_of_nonneg_left
      (infDist_le_hausdorffDist_of_mem ha ConvexBody.hausdorffEDist_ne_top) (abs_nonneg c)
  refine hausdorffDist_le_of_mem_dist (mul_nonneg (abs_nonneg c) hd) (key K L) ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := key L K x hx
  exact ⟨y, hy, hxy.trans_eq (by rw [hausdorffDist_comm])⟩

/-! ### The Veronese cone and Veronese subsets -/

/-- The Veronese cone `C^{(r)} = {(x, t) : (x, r t) ∈ C}` of an admissible cone. -/
def veroneseCone (C : AdmissibleCone n) {r : ℕ} (hr : 0 < r) : AdmissibleCone n where
  cone := C.cone.comap (SGPT.Okounkov.AlgebraicBody.degreeScaling (n := n) (r : ℝ)
    (by exact_mod_cast hr.ne')).toLinearMap
  closed := by
    rw [ConvexCone.coe_comap]
    exact C.closed.preimage
      (SGPT.Okounkov.AlgebraicBody.degreeScaling (n := n) (r : ℝ) _).continuous
  nonnegativeHeight := by
    intro z hz
    have h := C.nonnegativeHeight _ (ConvexCone.mem_comap.mp hz)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    change 0 ≤ (r : ℝ) * z.2 at h
    exact (mul_nonneg_iff_of_pos_left hrR).mp h
  zeroHeight := by
    intro x hx
    apply C.zeroHeight x
    have h := ConvexCone.mem_comap.mp hx
    change (x, (r : ℝ) * 0) ∈ C.cone at h
    rwa [mul_zero] at h

theorem mem_veroneseCone {C : AdmissibleCone n} {r : ℕ} (hr : 0 < r) (z : (Fin n → ℝ) × ℝ) :
    z ∈ (veroneseCone C hr).cone ↔ (z.1, (r : ℝ) * z.2) ∈ C.cone := Iff.rfl

/-- The Veronese subset `S^{(r)} = {(x, k) : (x, r k) ∈ S}`. -/
def veroneseSet (r : ℕ) (S : Set ((Fin n → ℤ) × ℤ)) : Set ((Fin n → ℤ) × ℤ) :=
  {z | (z.1, (r : ℤ) * z.2) ∈ S}

@[simp] theorem mem_veroneseSet {r : ℕ} {S : Set ((Fin n → ℤ) × ℤ)} {z : (Fin n → ℤ) × ℤ} :
    z ∈ veroneseSet r S ↔ (z.1, (r : ℤ) * z.2) ∈ S := Iff.rfl

theorem veroneseSet_subset_latticePoints {C : AdmissibleCone n} {r : ℕ} (hr : 0 < r)
    {S : Set ((Fin n → ℤ) × ℤ)} (hS : S ⊆ (latticePoints C.cone : Set _)) :
    veroneseSet r S ⊆ (latticePoints (veroneseCone C hr).cone : Set _) := by
  intro z hz
  have h := hS hz
  change latticeCast n z ∈ (veroneseCone C hr).cone
  rw [mem_veroneseCone]
  change latticeCast n (z.1, (r : ℤ) * z.2) ∈ C.cone at h
  convert h using 1
  ext i <;> simp [latticeCast]

variable {C : AdmissibleCone n} {r : ℕ} (hr : 0 < r)

/-- The Veronese map `S ↦ S^{(r)}` on lattice subsets of the cone. -/
def veroneseSubset (S : ConeSubset C) : ConeSubset (veroneseCone C hr) :=
  ⟨veroneseSet r S.val, veroneseSet_subset_latticePoints hr S.property⟩

theorem slices_veroneseSubset (S : ConeSubset C) (k : ℕ) :
    (veroneseSubset hr S).slices k = S.slices (r * k) := by
  ext x
  rw [ConeSubset.mem_slices, ConeSubset.mem_slices]
  change (x, (r : ℤ) * (k : ℤ)) ∈ S.val ↔ (x, ((r * k : ℕ) : ℤ)) ∈ S.val
  push_cast
  rfl

include hr in
theorem inv_natCast_pow_eq (k : ℕ) :
    ((k : ℝ)⁻¹) ^ n = (r : ℝ) ^ n * (((r * k : ℕ) : ℝ)⁻¹) ^ n := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  rw [mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hrR, one_pow, one_mul]

theorem normalizedCardinality_veroneseSubset (S : ConeSubset C) (k : ℕ) :
    (veroneseSubset hr S).normalizedCardinality k =
      (r : ℝ) ^ n * S.normalizedCardinality (r * k) := by
  unfold ConeSubset.normalizedCardinality
  rw [slices_veroneseSubset, inv_natCast_pow_eq hr k, mul_assoc]

/-- **`d_sg(S^{(r)}, T^{(r)}) ≤ rⁿ d_sg(S, T)`.** -/
theorem dist_veroneseSubset_le (S T : ConeSubset C) :
    dist (veroneseSubset hr S) (veroneseSubset hr T) ≤ (r : ℝ) ^ n * dist S T := by
  rw [ConeSubset.dist_eq_distance, ConeSubset.dist_eq_distance, ConeSubset.distance,
    ConeSubset.distance, asymptoticDistance, asymptoticDistance]
  set g := normalizedDiscrepancy n S.slices T.slices with hg
  have hfun : normalizedDiscrepancy n (veroneseSubset hr S).slices (veroneseSubset hr T).slices =
      (fun x : ℝ => (r : ℝ) ^ n * x) ∘ (g ∘ fun k : ℕ => r * k) := by
    funext k
    simp only [Function.comp, hg, normalizedDiscrepancy, slices_veroneseSubset]
    rw [inv_natCast_pow_eq hr k, mul_assoc]
  rw [hfun]
  have hmono : Monotone (fun x : ℝ => (r : ℝ) ^ n * x) := fun a b h =>
    mul_le_mul_of_nonneg_left h (by positivity)
  have hb : IsBoundedUnder (· ≤ ·) atTop g :=
    bounded_normalizedDiscrepancy_of_growth n S.slices T.slices S.hasPolynomialGrowth
      T.hasPolynomialGrowth
  have htend : Tendsto (fun k : ℕ => r * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k hr) tendsto_id
  have hnn : ∀ k, 0 ≤ g k := fun k => normalizedDiscrepancy_nonneg n _ _ k
  have hb' : IsBoundedUnder (· ≤ ·) atTop (g ∘ fun k : ℕ => r * k) := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, htend.eventually hB⟩
  have hcob' : IsCoboundedUnder (· ≤ ·) atTop (g ∘ fun k : ℕ => r * k) :=
    isCoboundedUnder_le_of_le atTop (fun k => hnn _)
  rw [← hmono.map_limsup_of_continuousAt _ (continuous_const.mul continuous_id).continuousAt hb'
    hcob']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact htend.limsup_comp_le_limsup (isCoboundedUnder_le_of_le _ (fun k => hnn _)) hb

theorem lipschitzWith_veroneseSubset :
    LipschitzWith ((r : NNReal) ^ n) (veroneseSubset (C := C) hr) :=
  LipschitzWith.of_dist_le_mul fun S T => by
    push_cast
    exact dist_veroneseSubset_le hr S T

/-! ### Full semigroups -/

/-- `x ∈ S`, `f ∈ S` give `m f + x ∈ S` for an additive subsemigroup. -/
theorem nsmul_add_mem {A : Type*} [AddCommMonoid A] (S : AddSubsemigroup A) {f x : A}
    (hf : f ∈ S) (hx : x ∈ S) (m : ℕ) : m • f + x ∈ S := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [succ_nsmul, add_assoc, add_comm f x, ← add_assoc]
    exact S.add_mem ih hf

/-- The lattice points `(eᵢ, 0)` and `(0, 1)` generate `ℤⁿ⁺¹`. -/
theorem closure_eq_top_of_basis (G : AddSubgroup ((Fin n → ℤ) × ℤ))
    (he : ∀ i : Fin n, ((Pi.single i 1 : Fin n → ℤ), (0 : ℤ)) ∈ G)
    (h1 : ((0 : Fin n → ℤ), (1 : ℤ)) ∈ G) : G = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, k⟩ -
  have hx : (x, k) = (∑ i, x i • ((Pi.single i 1 : Fin n → ℤ), (0 : ℤ))) +
      k • ((0 : Fin n → ℤ), (1 : ℤ)) := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_sum]
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    · rw [Prod.snd_add, Prod.snd_sum]
      simp
  rw [hx]
  exact G.add_mem (G.sum_mem fun i _ => G.zsmul_mem (he i) _) (G.zsmul_mem h1 _)

/-- **Veronese subsets of full semigroups are full semigroups**: if `S` is an additive semigroup
generating `ℤⁿ⁺¹`, so is `S^{(r)}` (`r ≥ 1`). -/
theorem veroneseSubset_mem_fullSemigroupLocus {S : ConeSubset C}
    (hS : S ∈ fullSemigroupLocus C) : veroneseSubset hr S ∈ fullSemigroupLocus (veroneseCone C hr) := by
  obtain ⟨hsg, hgen⟩ := hS
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have h := hsg _ hx _ hy
    change ((x + y).1, (r : ℤ) * (x + y).2) ∈ S.val
    convert h using 1
    ext <;> simp [mul_add]
  · let T : AddSubsemigroup ((Fin n → ℤ) × ℤ) := ⟨S.val, fun hx hy => hsg _ hx _ hy⟩
    have hne : (T : Set ((Fin n → ℤ) × ℤ)).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h' : AddSubgroup.closure S.val = ⊥ := by
        change AddSubgroup.closure (T : Set ((Fin n → ℤ) × ℤ)) = ⊥
        rw [h, AddSubgroup.closure_empty]
      rw [hgen] at h'
      have : ((0 : Fin n → ℤ), (1 : ℤ)) ∈ (⊥ : AddSubgroup ((Fin n → ℤ) × ℤ)) := by
        rw [← h']; trivial
      rw [AddSubgroup.mem_bot] at this
      exact one_ne_zero (congrArg Prod.snd this)
    let R : Set ((Fin n → ℤ) × ℤ) := insert ((0 : Fin n → ℤ), (r : ℤ))
      (insert 0 (Set.range fun i : Fin n => ((Pi.single i 1 : Fin n → ℤ), (0 : ℤ))))
    have hRfin : R.Finite := ((Set.finite_range _).insert 0).insert _
    have hRgen : R ⊆ AddSubgroup.closure (T : Set ((Fin n → ℤ) × ℤ)) := by
      change R ⊆ AddSubgroup.closure S.val
      rw [hgen]
      exact Set.subset_univ _
    obtain ⟨f, hf, hR⟩ := SGPT.AlmostSemigroup.Conductor.exists_translate_of_finite T hne hRfin
      hRgen
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    -- the three kinds of elements of `S^{(r)}`
    have helt : ∀ u ∈ R, r' • f + (u + f) ∈ S.val := fun u hu =>
      nsmul_add_mem T hf (hR u hu) r'
    have hA0 : ((r' + 1) • f.1, f.2) ∈ veroneseSet (r' + 1) S.val := by
      have h := helt 0 (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      rw [mem_veroneseSet]
      convert h using 1
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, zero_add]
        rw [succ_nsmul]
      · simp only [Prod.snd_add, Prod.smul_snd, zero_add]
        push_cast
        ring
    have hAi : ∀ i : Fin n, ((r' + 1) • f.1 + Pi.single i 1, f.2) ∈
        veroneseSet (r' + 1) S.val := by
      intro i
      have h := helt ((Pi.single i 1 : Fin n → ℤ), (0 : ℤ))
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
      rw [mem_veroneseSet]
      convert h using 1
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst]
        rw [succ_nsmul, add_assoc, add_comm f.1]
      · simp only [Prod.snd_add, Prod.smul_snd, zero_add]
        push_cast
        ring
    have hB : ((r' + 1) • f.1, f.2 + 1) ∈ veroneseSet (r' + 1) S.val := by
      have h := helt ((0 : Fin n → ℤ), ((r' + 1 : ℕ) : ℤ)) (Set.mem_insert _ _)
      rw [mem_veroneseSet]
      convert h using 1
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, zero_add]
        rw [succ_nsmul]
      · simp only [Prod.snd_add, Prod.smul_snd]
        push_cast
        ring
    set G := AddSubgroup.closure (veroneseSet (r' + 1) S.val)
    have hsub : ∀ z ∈ veroneseSet (r' + 1) S.val, z ∈ G := fun z hz => AddSubgroup.subset_closure hz
    apply closure_eq_top_of_basis G
    · intro i
      have h := G.sub_mem (hsub _ (hAi i)) (hsub _ hA0)
      convert h using 1
      ext <;> simp
    · have h := G.sub_mem (hsub _ hB) (hsub _ hA0)
      convert h using 1
      ext <;> simp

/-- For a full semigroup `S`, `vol S^{(r)} = rⁿ vol S`. -/
theorem volume_veroneseSubset_of_full {S : ConeSubset C} (hS : S ∈ fullSemigroupLocus C) :
    (veroneseSubset hr S).volume = (r : ℝ) ^ n * S.volume := by
  let T : FullSemigroup C := ⟨S, hS⟩
  have hlim := tendsto_source_of_generatedGroup_eq_top C T.semigroup T.semigroup_le_source
    T.generatedGroup_eq_top
  change Tendsto S.normalizedCardinality atTop _ at hlim
  have htend : Tendsto (fun k : ℕ => r * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k hr) tendsto_id
  have hV : Tendsto (veroneseSubset hr S).normalizedCardinality atTop
      (𝓝 ((r : ℝ) ^ n * volume.real (body T.semigroup))) := by
    have h := (hlim.comp htend).const_mul ((r : ℝ) ^ n)
    refine h.congr fun k => ?_
    rw [normalizedCardinality_veroneseSubset]
    rfl
  rw [ConeSubset.volume, ConeSubset.volume, hV.limsup_eq, hlim.limsup_eq]

/-- `vol S^{(r)} = rⁿ vol S` on the closure of the full semigroups. -/
theorem volume_veroneseSubset_of_mem_closure {S : ConeSubset C}
    (hS : S ∈ closure (fullSemigroupLocus C)) :
    (veroneseSubset hr S).volume = (r : ℝ) ^ n * S.volume := by
  have hclosed : IsClosed {T : ConeSubset C |
      (veroneseSubset hr T).volume = (r : ℝ) ^ n * T.volume} :=
    isClosed_eq (ConeSubset.continuous_volume.comp (lipschitzWith_veroneseSubset hr).continuous)
      (continuous_const.mul ConeSubset.continuous_volume)
  exact closure_minimal (fun T hT => volume_veroneseSubset_of_full hr hT) hclosed hS

/-- **Veronese subsets of almost semigroups are almost semigroups.** -/
theorem veroneseSubset_mem_almostSemigroupLocus {S : ConeSubset C}
    (hS : S ∈ almostSemigroupLocus C) :
    veroneseSubset hr S ∈ almostSemigroupLocus (veroneseCone C hr) := by
  refine ⟨map_mem_closure (lipschitzWith_veroneseSubset hr).continuous hS.1
    fun T hT => veroneseSubset_mem_fullSemigroupLocus hr hT, ?_⟩
  change 0 < (veroneseSubset hr S).volume
  rw [volume_veroneseSubset_of_mem_closure hr hS.1]
  exact mul_pos (by positivity) hS.2

/-- The Veronese map on full semigroups. -/
def veroneseFull (S : FullSemigroup C) : FullSemigroup (veroneseCone C hr) :=
  ⟨veroneseSubset hr S.val, veroneseSubset_mem_fullSemigroupLocus hr S.property⟩

/-- The Veronese map on almost semigroups. -/
def veroneseAlmost (S : AlmostSpace C) : AlmostSpace (veroneseCone C hr) :=
  ⟨veroneseSubset hr S.val, veroneseSubset_mem_almostSemigroupLocus hr S.property⟩

theorem lipschitzWith_veroneseAlmost :
    LipschitzWith ((r : NNReal) ^ n) (veroneseAlmost (C := C) hr) :=
  LipschitzWith.of_dist_le_mul fun S T => by
    push_cast
    exact dist_veroneseSubset_le hr S.val T.val

/-- `Δ(S^{(r)}) = r Δ(S)` for full semigroups (source `prop:Okourescaling`, via
`SGPT.Okounkov.AlgebraicBody.body_eq_smul_of_veronese`). -/
theorem bodyMap_veroneseFull (S : FullSemigroup C) :
    bodyMap (veroneseFull hr S) = (r : ℝ) • bodyMap S := by
  apply ConvexBody.ext
  rw [ConvexBody.coe_smul]
  change BodyGeometry.euclideanBody (veroneseFull hr S).semigroup =
    (r : ℝ) • BodyGeometry.euclideanBody S.semigroup
  unfold BodyGeometry.euclideanBody
  rw [SGPT.Okounkov.AlgebraicBody.body_eq_smul_of_veronese S.semigroup
    (veroneseFull hr S).semigroup hr (fun x k => Iff.rfl)]
  exact image_smul_set _ _ _

/-- **`Δ(S^{(r)}) = r Δ(S)` for every almost semigroup** (continuity and density). -/
theorem bodyExtension_veroneseAlmost (S : AlmostSpace C) :
    bodyExtension (veroneseAlmost hr S) = (r : ℝ) • bodyExtension S := by
  obtain ⟨u, hu⟩ := SGPT.AlmostSemigroup.OkounkovComparison.exists_full_sequence S
  have h1 : Tendsto (fun i => bodyExtension (veroneseAlmost hr (fullToAlmost (u i)))) atTop
      (𝓝 (bodyExtension (veroneseAlmost hr S))) :=
    ((continuous_bodyExtension _).tendsto _).comp
      (((lipschitzWith_veroneseAlmost hr).continuous.tendsto _).comp hu)
  have h2 : Tendsto (fun i => (r : ℝ) • bodyExtension (fullToAlmost (u i))) atTop
      (𝓝 ((r : ℝ) • bodyExtension S)) := by
    have hc := ((continuous_bodyExtension C).tendsto S).comp hu
    rw [tendsto_iff_dist_tendsto_zero] at hc ⊢
    refine squeeze_zero (fun i => dist_nonneg) (fun i => ?_) (by
      simpa using hc.const_mul (r : ℝ))
    have h := dist_smul_convexBody_le (r : ℝ) (bodyExtension (fullToAlmost (u i)))
      (bodyExtension S)
    rwa [abs_of_nonneg (Nat.cast_nonneg r)] at h
  have heq : ∀ i, bodyExtension (veroneseAlmost hr (fullToAlmost (u i))) =
      (r : ℝ) • bodyExtension (fullToAlmost (u i)) := by
    intro i
    have hfa : veroneseAlmost hr (fullToAlmost (u i)) = fullToAlmost (veroneseFull hr (u i)) := rfl
    rw [hfa, bodyExtension_source, bodyExtension_source, bodyMap_veroneseFull]
  exact tendsto_nhds_unique (h1.congr heq) h2

/-- **The partial-body form**: for a lattice set `S ⊆ C` which is an almost semigroup in `C`,
`Δ(S^{(r)}) = r Δ(S)` (with `SGPT.Okounkov.ValGen.setBody`). -/
theorem setBody_veroneseSet {S : Set ((Fin n → ℤ) × ℤ)} (hsub : S ⊆ (latticePoints C.cone : Set _))
    (hS : (⟨S, hsub⟩ : ConeSubset C) ∈ almostSemigroupLocus C) :
    SGPT.Okounkov.ValGen.setBody (veroneseCone C hr) (veroneseSet r S) =
      (r : ℝ) • SGPT.Okounkov.ValGen.setBody C S := by
  rw [SGPT.Okounkov.ValGen.setBody_eq hsub hS,
    SGPT.Okounkov.ValGen.setBody_eq (veroneseSet_subset_latticePoints hr hsub)
      (veroneseSubset_mem_almostSemigroupLocus hr hS)]
  have h := bodyExtension_veroneseAlmost hr ⟨⟨S, hsub⟩, hS⟩
  rw [← ConvexBody.coe_smul]
  exact congrArg (fun K : ConvexBody (EuclideanSpace ℝ (Fin n)) =>
    (K : Set (EuclideanSpace ℝ (Fin n)))) h

end SGPT.Okounkov.ValGen2
