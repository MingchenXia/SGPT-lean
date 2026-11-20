import SGPT.AlmostSemigroup.Volume
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Convex.Measure

/-!
# Actual lattice counting limits

The convex-body counting and lattice normalization ingredients of Appendix C,
`thm:KK12growth`, and the actual limit for a saturated cone semigroup. The general
nonsaturated semigroup conductor and divisible-degree assertions remain separate.
-/

noncomputable section

namespace SGPT.AlmostSemigroup.Counting

open Set Filter MeasureTheory Module
open scoped Pointwise Topology

/-- Dilation identifies the actual grid points with points in the dilated body. -/
def dilationEquiv {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) (r : ℝ) (hr : r ≠ 0) :
    ↥(K ∩ r⁻¹ • L) ≃ ↥((r • K) ∩ L) where
  toFun x := ⟨r • x.val, ⟨Set.smul_mem_smul_set x.property.1,
    (Set.mem_inv_smul_set_iff₀ hr L x.val).mp x.property.2⟩⟩
  invFun y := ⟨r⁻¹ • y.val, ⟨by
    rcases y.property.1 with ⟨x, hx, hxy⟩
    simpa [← hxy, smul_smul, hr] using hx,
    Set.smul_mem_smul_set y.property.2⟩⟩
  left_inv x := by ext; simp [smul_smul, hr]
  right_inv y := by ext; simp [smul_smul, hr]

/-- The source dilation leaves the cardinality unchanged in every nonzero degree. -/
theorem card_dilated_inter {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K L : Set E) (r : ℝ) (hr : r ≠ 0) :
    Nat.card ↥((r • K) ∩ L) = Nat.card ↥(K ∩ r⁻¹ • L) :=
  (Nat.card_congr (dilationEquiv K L r hr)).symm

/-- The integer-coordinate embedding used by the source. -/
def integerCast {n : ℕ} (x : Fin n → ℤ) : Fin n → ℝ := fun i => (x i : ℝ)

theorem integerCast_injective {n : ℕ} : Function.Injective (integerCast (n := n)) := by
  intro x y h
  ext i
  have hi := congrFun h i
  dsimp [integerCast] at hi
  exact_mod_cast hi

/-- The actual standard integer lattice inside the real coordinate space. -/
def standardLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

theorem mem_standardLattice_iff {n : ℕ} (y : Fin n → ℝ) :
    y ∈ standardLattice n ↔ ∀ i, ∃ z : ℤ, (z : ℝ) = y i := by
  simp [standardLattice, Basis.mem_span_iff_repr_mem, Pi.basisFun_repr]

theorem integerCast_mem_standardLattice {n : ℕ} (x : Fin n → ℤ) :
    integerCast x ∈ standardLattice n :=
  (mem_standardLattice_iff _).mpr (fun i => ⟨x i, rfl⟩)

/-- Coordinatewise integer casting is a bijection onto the standard lattice. -/
def integerLatticeEquiv (n : ℕ) : (Fin n → ℤ) ≃ standardLattice n :=
  Equiv.ofBijective (fun x => ⟨integerCast x, integerCast_mem_standardLattice x⟩) (by
    constructor
    · intro x y h
      exact integerCast_injective (congrArg Subtype.val h)
    · intro y
      choose z hz using (mem_standardLattice_iff y.val).mp y.property
      refine ⟨z, ?_⟩
      apply Subtype.ext
      funext i
      exact hz i)

/-- Integer points of a real set, without changing the source's integer coordinates. -/
def integerPoints {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℤ) :=
  integerCast ⁻¹' K

/-- The coordinate embedding restricts to the actual lattice points of a real set. -/
def integerPointsEquiv {n : ℕ} (K : Set (Fin n → ℝ)) :
    integerPoints K ≃ ↥(K ∩ standardLattice n) where
  toFun x := ⟨integerCast x.val, x.property, integerCast_mem_standardLattice x.val⟩
  invFun y := ⟨(integerLatticeEquiv n).symm ⟨y.val, y.property.2⟩, by
    have h := congrArg Subtype.val
      ((integerLatticeEquiv n).apply_symm_apply ⟨y.val, y.property.2⟩)
    change integerCast ((integerLatticeEquiv n).symm ⟨y.val, y.property.2⟩) = y.val at h
    change integerCast _ ∈ K
    rw [h]
    exact y.property.1⟩
  left_inv x := by
    apply Subtype.ext
    exact (integerLatticeEquiv n).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    have h := congrArg Subtype.val
      ((integerLatticeEquiv n).apply_symm_apply ⟨y.val, y.property.2⟩)
    exact h

theorem card_integerPoints {n : ℕ} (K : Set (Fin n → ℝ)) :
    Nat.card (integerPoints K) = Nat.card ↥(K ∩ standardLattice n) :=
  Nat.card_congr (integerPointsEquiv K)

/-- Bounded real sets have finitely many actual integer-coordinate points. -/
theorem finite_integerPoints {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : Bornology.IsBounded K) : (integerPoints K).Finite := by
  apply Set.Finite.of_injOn (t := K ∩ standardLattice n)
    (f := integerCast) (fun x hx => ⟨hx, integerCast_mem_standardLattice x⟩)
    integerCast_injective.injOn
  exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin n)) hK

/-- The source's actual integer lattice count in degree `k`. -/
def integerLatticeCount {n : ℕ} (K : Set (Fin n → ℝ)) (k : ℕ) : ℕ :=
  Nat.card (integerPoints ((k : ℝ) • K))

/-- Every degree of a compact body's actual integer lattice count is finite. -/
theorem finite_integerPoints_dilate {n : ℕ} {K : Set (Fin n → ℝ)}
    (hcompact : IsCompact K) (k : ℕ) :
    (integerPoints ((k : ℝ) • K)).Finite := by
  apply finite_integerPoints
  have h : IsCompact ((k : ℝ) • K) := by
    exact hcompact.image (continuous_id.const_smul (k : ℝ))
  exact h.isBounded

/-- The frontier of every convex coordinate set is Lebesgue-null. -/
theorem null_frontier_convex {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) : MeasureTheory.volume (frontier K) = 0 :=
  hK.addHaar_frontier MeasureTheory.volume

/-- Compact convex bodies satisfy the source's actual standard-lattice counting limit. -/
theorem tendsto_integer_lattice_count {n : ℕ} {K : Set (Fin n → ℝ)}
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) :
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n * integerLatticeCount K k)
      atTop (𝓝 (MeasureTheory.volume.real K)) := by
  have h := tendsto_card_div_pow_atTop_volume K hcompact.isBounded
    hcompact.measurableSet (null_frontier_convex hconvex)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [integerLatticeCount, card_integerPoints,
    card_dilated_inter K (standardLattice n : Set _) (k : ℝ) hk0]
  simp [standardLattice, div_eq_mul_inv, inv_pow, mul_comm]

/-- Every dilated compact body meets a discrete lattice in a finite set. -/
theorem finite_lattice_dilate {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] {K : Set (Fin n → ℝ)}
    (hcompact : IsCompact K) (k : ℕ) :
    (((k : ℝ) • K) ∩ L : Set (Fin n → ℝ)).Finite := by
  change (((k : ℝ) • K) ∩ L.toAddSubgroup : Set (Fin n → ℝ)).Finite
  have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (hcompact.image (continuous_id.const_smul (k : ℝ))).isBounded inferInstance

/-- The lattice-covolume version of the same actual convex-body limit. -/
theorem tendsto_lattice_count {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {K : Set (Fin n → ℝ)}
    (hcompact : IsCompact K) (hconvex : Convex ℝ K) :
    Tendsto (fun k : ℕ => (k : ℝ)⁻¹ ^ n *
      (Nat.card ↥(((k : ℝ) • K) ∩ L) : ℝ))
      atTop (𝓝 (MeasureTheory.volume.real K / ZLattice.covolume L)) := by
  have h := ZLattice.covolume.tendsto_card_div_pow L (IsZLattice.basis L) hcompact.isBounded
    hcompact.measurableSet (null_frontier_convex hconvex)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [card_dilated_inter K (L : Set _) (k : ℝ) hk0]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

/-- A cone's actual height-one section is convex. -/
theorem convex_heightOne {n : ℕ} (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) :
    Convex ℝ (heightOne C) := by
  intro x hx y hy a b ha hb hab
  have h := C.convex hx hy ha hb hab
  change (a • x + b • y, (1 : ℝ)) ∈ C
  simpa [Prod.smul_mk, hab] using h

/-- Positive-degree cone slices are exactly integer points of the dilated height-one body. -/
theorem mem_slice_iff_integerPoints_heightOne {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (k : ℕ) (hk : 0 < k)
    (x : Fin n → ℤ) :
    (x, (k : ℤ)) ∈ latticePoints C ↔
      x ∈ integerPoints ((k : ℝ) • heightOne C) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk0 := hkpos.ne'
  constructor
  · intro hx
    change integerCast x ∈ (k : ℝ) • heightOne C
    refine ⟨(k : ℝ)⁻¹ • integerCast x, ?_, ?_⟩
    · change ((k : ℝ)⁻¹ • integerCast x, (1 : ℝ)) ∈ C
      have heq : ((k : ℝ)⁻¹ • integerCast x, (1 : ℝ)) =
          (k : ℝ)⁻¹ • latticeCast n (x, (k : ℤ)) := by
        ext i <;> simp [latticeCast, integerCast, smul_eq_mul, hk0]
      rw [heq]
      exact C.smul_mem (inv_pos.mpr hkpos) hx
    · simp [smul_smul, hk0]
  · rintro ⟨y, hy, hxy⟩
    change latticeCast n (x, (k : ℤ)) ∈ C
    have heq : latticeCast n (x, (k : ℤ)) = (k : ℝ) • (y, (1 : ℝ)) := by
      apply Prod.ext
      · change integerCast x = (k : ℝ) • y
        exact hxy.symm
      · simp [latticeCast]
    rw [heq]
    exact C.smul_mem hkpos hy

/-- The saturated cone semigroup as an actual allowed cone subset. -/
def coneSubset {n : ℕ} (C : AdmissibleCone n) : ConeSubset C :=
  ⟨latticePoints C.cone, Set.Subset.rfl⟩

/-- Degreewise cardinality identification for the canonical finite cone slices. -/
theorem card_cone_slices {n : ℕ} (C : AdmissibleCone n) (k : ℕ) (hk : 0 < k) :
    ((coneSubset C).slices k).card = integerLatticeCount (heightOne C.cone) k := by
  change ((coneSubset C).finite_slice k).toFinset.card = _
  rw [integerLatticeCount, ← Nat.card_eq_card_finite_toFinset ((coneSubset C).finite_slice k)]
  have hs : slice (coneSubset C).val (k : ℤ) =
      integerPoints ((k : ℝ) • heightOne C.cone) := by
    ext x
    exact mem_slice_iff_integerPoints_heightOne C.cone k hk x
  rw [hs]

/-- Actual canonical lattice slices converge from the original cone geometry hypotheses. -/
theorem tendsto_cone_lattice_slices {n : ℕ} (C : AdmissibleCone n) :
    Tendsto (fun k : ℕ => (coneSubset C).normalizedCardinality k)
      atTop (𝓝 (MeasureTheory.volume.real (heightOne C.cone))) := by
  have h := tendsto_integer_lattice_count
    (isCompact_heightOne C.cone C.closed C.nonnegativeHeight C.zeroHeight)
    (convex_heightOne C.cone)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [ConeSubset.normalizedCardinality, card_cone_slices C k hk]

/-- The source's volume formula equals height-one Lebesgue volume for saturated cones. -/
theorem volume_coneSubset {n : ℕ} (C : AdmissibleCone n) :
    (coneSubset C).volume = MeasureTheory.volume.real (heightOne C.cone) :=
  (tendsto_cone_lattice_slices C).limsup_eq

/-- The saturated cone lattice subset belongs to the source's actual semigroup locus. -/
theorem coneSubset_mem_semigroupLocus {n : ℕ} (C : AdmissibleCone n) :
    coneSubset C ∈ ConeSubset.semigroupLocus C := by
  intro x hx y hy
  exact (latticePoints C.cone).add_mem hx hy

end SGPT.AlmostSemigroup.Counting
