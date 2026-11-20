import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Int.Interval
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Lattice slices and the almost-semigroup discrepancy

This module proves the finite combinatorial estimates underlying Appendix C
of Mingchen Xia's SGPT, `eq:dsgdefapp`, `lma:dpsapp`, and `lma:dBilapp`.
The fixed-cone hypotheses produce finite slices and bounded polynomial growth.
The final API gives the actual pseudometric on all lattice subsets of that cone
and continuity of intersection. The Okounkov-body construction is separate.
-/

namespace SGPT.AlmostSemigroup

open Filter
open scoped symmDiff

variable {α : Type*}

/-- The lattice slice in degree `k`, without an additive closure assumption. -/
def slice {n : ℕ} (S : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) : Set (Fin n → ℤ) :=
  {x | (x, k) ∈ S}

@[simp] theorem mem_slice {n : ℕ} {S : Set ((Fin n → ℤ) × ℤ)}
    {k : ℤ} {x : Fin n → ℤ} : x ∈ slice S k ↔ (x, k) ∈ S := Iff.rfl

/-- Additive closure of the lattice set gives addition of its graded slices. -/
theorem add_mem_slice {n : ℕ} (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    {k l : ℤ} {x y : Fin n → ℤ}
    (hx : x ∈ slice (S : Set ((Fin n → ℤ) × ℤ)) k)
    (hy : y ∈ slice (S : Set ((Fin n → ℤ) × ℤ)) l) :
    x + y ∈ slice (S : Set ((Fin n → ℤ) × ℤ)) (k + l) :=
  S.add_mem hx hy

@[simp] theorem slice_inter {n : ℕ} (S T : Set ((Fin n → ℤ) × ℤ)) (k : ℤ) :
    slice (S ∩ T) k = slice S k ∩ slice T k := rfl

/-- The coordinatewise inclusion of the integer lattice into the real vector space. -/
noncomputable def latticeCast (n : ℕ) :
    ((Fin n → ℤ) × ℤ) →+ ((Fin n → ℝ) × ℝ) where
  toFun x := (fun i => (x.1 i : ℝ), (x.2 : ℝ))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

/-- The lattice-point semigroup of a convex cone.
Applied to the closed generated cone `C(S)`, this is SGPT's `Reg(S)`. -/
noncomputable def latticePoints {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) :
    AddSubsemigroup ((Fin n → ℤ) × ℤ) where
  carrier := {x | latticeCast n x ∈ C}
  add_mem' := by
    intro x y hx hy
    change latticeCast n (x + y) ∈ C
    rw [map_add]
    exact C.add_mem hx hy

@[simp] theorem mem_latticePoints {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (x : (Fin n → ℤ) × ℤ) :
    x ∈ latticePoints C ↔ latticeCast n x ∈ C := Iff.rfl

/-- Cone inclusion gives inclusion of the corresponding lattice-point semigroups. -/
theorem latticePoints_mono {n : ℕ}
    {C D : ConvexCone ℝ ((Fin n → ℝ) × ℝ)} (h : C ≤ D) :
    latticePoints C ≤ latticePoints D := fun _ hx => h hx

/-- The transverse-cone hypothesis in Appendix C forces its degree-zero slice. -/
theorem latticePoints_zero_slice {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (h0 : (0 : (Fin n → ℝ) × ℝ) ∈ C)
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) :
    slice (latticePoints C : Set ((Fin n → ℤ) × ℤ)) 0 = {0} := by
  ext x
  constructor
  · intro hx
    change (fun i => (x i : ℝ), ((0 : ℤ) : ℝ)) ∈ C at hx
    simp only [Int.cast_zero] at hx
    have hr : (fun i => (x i : ℝ)) = 0 := hpointed _ hx
    have hz : x = 0 := by
      funext i
      change x i = 0
      have hi : (x i : ℝ) = 0 := by simpa only [Pi.zero_apply] using congrFun hr i
      exact_mod_cast hi
    simpa only [Set.mem_singleton_iff] using hz
  · intro hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    change latticeCast n (0 : (Fin n → ℤ) × ℤ) ∈ C
    rw [map_zero]
    exact h0

/-- The real height-one slice of the cone. -/
def heightOne {n : ℕ} (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) : Set (Fin n → ℝ) :=
  {x | (x, 1) ∈ C}

/-- The original cone hypotheses of SGPT imply compactness of its height-one slice. -/
theorem isCompact_heightOne {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ))
    (hclosed : IsClosed (C : Set ((Fin n → ℝ) × ℝ)))
    (hheight : ∀ z ∈ C, 0 ≤ z.2)
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) :
    IsCompact (heightOne C) := by
  classical
  have hcl : IsClosed (heightOne C) :=
    hclosed.preimage (continuous_id.prodMk continuous_const)
  by_cases hH : (heightOne C).Nonempty
  · let K : Set ((Fin n → ℝ) × ℝ) := (C : Set _) ∩ Metric.sphere 0 1
    have hK : IsCompact K := (isCompact_sphere (0 : (Fin n → ℝ) × ℝ) 1).inter_left hclosed
    have hnormpos : ∀ x : Fin n → ℝ, 0 < ‖(x, (1 : ℝ))‖ := by
      intro x
      apply norm_pos_iff.mpr
      intro hz
      have hi := congrArg Prod.snd hz
      norm_num at hi
    have hnormalize : ∀ x ∈ heightOne C,
        ‖(x, (1 : ℝ))‖⁻¹ • (x, (1 : ℝ)) ∈ K := by
      intro x hx
      have hn := hnormpos x
      refine ⟨C.smul_mem (inv_pos.mpr hn) hx, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hKne : K.Nonempty := by
      obtain ⟨x, hx⟩ := hH
      exact ⟨_, hnormalize x hx⟩
    obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne continuous_snd.continuousOn
    have hanorm : ‖a‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ha.2
    have hapos : 0 < a.2 := by
      have hage : 0 ≤ a.2 := hheight a ha.1
      by_contra hnot
      have haz : a.2 = 0 := by linarith
      have hx : (a.1, 0) ∈ C := by
        rw [← haz]
        exact ha.1
      have ha0 : a = 0 := Prod.ext (hpointed a.1 hx) haz
      simp only [ha0, norm_zero] at hanorm
      norm_num at hanorm
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    refine ⟨hcl, isBounded_iff_forall_norm_le.mpr ⟨1 / a.2, fun x hx => ?_⟩⟩
    have hn := hnormpos x
    have hm := hmin (hnormalize x hx)
    change a.2 ≤ (‖(x, (1 : ℝ))‖⁻¹ • (x, (1 : ℝ))).2 at hm
    simp only [Prod.smul_mk, smul_eq_mul, mul_one] at hm
    have hh := mul_le_mul_of_nonneg_right hm (norm_nonneg (x, (1 : ℝ)))
    rw [inv_mul_cancel₀ hn.ne'] at hh
    have hnle : ‖(x, (1 : ℝ))‖ ≤ 1 / a.2 :=
      (le_div_iff₀ hapos).mpr (by simpa only [mul_comm] using hh)
    exact (norm_fst_le (x, (1 : ℝ))).trans hnle
  · rw [Set.not_nonempty_iff_eq_empty.mp hH]
    exact isCompact_empty

/-- Compactness of the height-one slice produces a uniform linear integer coordinate bound. -/
theorem exists_lattice_coordinate_bound_of_compact {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (hK : IsCompact (heightOne C)) :
    ∃ M : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x : Fin n → ℤ,
      (x, (k : ℤ)) ∈ latticePoints C → ∀ i, -(M * k : ℤ) ≤ x i ∧ x i ≤ M * k := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
    (f := fun x : Fin n → ℝ => x) continuous_id.continuousOn
  obtain ⟨M, hM⟩ := exists_nat_gt R
  refine ⟨M, fun k hk x hx i => ?_⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hs := C.smul_mem (inv_pos.mpr hkpos) hx
  have hs' : (fun j => (k : ℝ)⁻¹ * (x j : ℝ)) ∈ heightOne C := by
    change ((fun j => (k : ℝ)⁻¹ * (x j : ℝ)), (1 : ℝ)) ∈ C
    have he : ((fun j => (k : ℝ)⁻¹ * (x j : ℝ)), (1 : ℝ)) =
        (k : ℝ)⁻¹ • latticeCast n (x, (k : ℤ)) := by
      apply Prod.ext
      · funext j
        rfl
      · simp [latticeCast, smul_eq_mul, inv_mul_cancel₀ hkpos.ne']
    rw [he]
    exact hs
  have hb0 : |(k : ℝ)⁻¹ * (x i : ℝ)| ≤
      ‖fun j => (k : ℝ)⁻¹ * (x j : ℝ)‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun j => (k : ℝ)⁻¹ * (x j : ℝ)) i
  have hb : |(k : ℝ)⁻¹ * (x i : ℝ)| ≤ (M : ℝ) := by
    exact hb0.trans ((hR _ hs').trans hM.le)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hkpos), inv_mul_le_iff₀ hkpos] at hb
  have hlo := (abs_le.mp hb).1
  have hhi := (abs_le.mp hb).2
  constructor
  · have hlo' : -((M : ℝ) * (k : ℝ)) ≤ (x i : ℝ) := by
      simpa only [mul_comm] using hlo
    exact_mod_cast hlo'
  · have hhi' : (x i : ℝ) ≤ (M : ℝ) * (k : ℝ) := by simpa only [mul_comm] using hhi
    exact_mod_cast hhi'

/-- A finite integer box used to bound the graded lattice slices. -/
noncomputable def latticeBox (n M k : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(M * k : ℤ)) (M * k : ℤ))

@[simp] theorem mem_latticeBox {n M k : ℕ} {x : Fin n → ℤ} :
    x ∈ latticeBox n M k ↔ ∀ i, -(M * k : ℤ) ≤ x i ∧ x i ≤ M * k := by
  simp [latticeBox, Fintype.mem_piFinset]

theorem card_latticeBox (n M k : ℕ) :
    (latticeBox n M k).card = (2 * M * k + 1) ^ n := by
  rw [latticeBox, Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  have he : (M * k : ℤ) + 1 - -(M * k : ℤ) = ((2 * M * k + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he]
  exact Int.toNat_natCast _

/-- The finite-slice claim from Appendix C, assuming compactness of the height-one slice. -/
theorem finite_latticePoints_slice_of_compact {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (hK : IsCompact (heightOne C))
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) (k : ℕ) :
    (slice (latticePoints C : Set ((Fin n → ℤ) × ℤ)) (k : ℤ)).Finite := by
  by_cases hk : k = 0
  · subst k
    apply (Set.finite_singleton (0 : Fin n → ℤ)).subset
    intro x hx
    change (fun i => (x i : ℝ), ((0 : ℕ) : ℝ)) ∈ C at hx
    simp only [Nat.cast_zero] at hx
    have hr := hpointed _ hx
    apply Set.mem_singleton_iff.mpr
    funext i
    change x i = 0
    have hi : (x i : ℝ) = 0 := by simpa only [Pi.zero_apply] using congrFun hr i
    exact_mod_cast hi
  · obtain ⟨M, hM⟩ := exists_lattice_coordinate_bound_of_compact C hK
    apply (latticeBox n M k).finite_toSet.subset
    intro x hx
    exact mem_latticeBox.mpr (hM k (by omega) x hx)

/-- Canonical finite slices of the lattice points of a cone with compact height-one slice. -/
noncomputable def latticePointSlices {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (hK : IsCompact (heightOne C))
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) (k : ℕ) : Finset (Fin n → ℤ) :=
  (finite_latticePoints_slice_of_compact C hK hpointed k).toFinset

@[simp] theorem mem_latticePointSlices {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (hK : IsCompact (heightOne C))
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) (k : ℕ) (x : Fin n → ℤ) :
    x ∈ latticePointSlices C hK hpointed k ↔ (x, (k : ℤ)) ∈ latticePoints C := by
  simp [latticePointSlices]

section FiniteDiscrepancy

variable [DecidableEq α]

/-- Cardinality of the symmetric difference; the numerator of `d_sg`. -/
def discrepancy (A B : Finset α) : ℕ := (A ∆ B).card

@[simp] theorem discrepancy_self (A : Finset α) : discrepancy A A = 0 := by
  simp [discrepancy]

theorem discrepancy_comm (A B : Finset α) : discrepancy A B = discrepancy B A := by
  simp only [discrepancy, symmDiff_comm]

/-- An identity in natural numbers avoids truncated subtraction. -/
theorem discrepancy_formula (A B : Finset α) :
    discrepancy A B + 2 * (A ∩ B).card = A.card + B.card := by
  have hd : Disjoint (A \ B) (B \ A) := by
    simp only [Finset.disjoint_left, Finset.mem_sdiff]
    tauto
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  simp only [discrepancy, Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  omega

/-- The finite claim appearing in the proof of SGPT `lma:dpsapp`. -/
theorem discrepancy_triangle (A B D : Finset α) :
    discrepancy A D ≤ discrepancy A B + discrepancy B D := by
  have hsub : A ∆ D ⊆ (A ∆ B) ∪ (B ∆ D) := by
    intro x hx
    simp only [Finset.mem_symmDiff, Finset.mem_union] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The finite claim appearing in the proof of SGPT `lma:dBilapp`. -/
theorem discrepancy_inter_right (A B D : Finset α) :
    discrepancy (A ∩ D) (B ∩ D) ≤ discrepancy A B := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_symmDiff, Finset.mem_inter] at hx ⊢
  tauto

/-- Simultaneously varying intersections satisfy the two-variable estimate. -/
theorem discrepancy_inter_inter (A B A' B' : Finset α) :
    discrepancy (A ∩ B) (A' ∩ B') ≤ discrepancy A A' + discrepancy B B' := by
  calc
    discrepancy (A ∩ B) (A' ∩ B') ≤
        discrepancy (A ∩ B) (A' ∩ B) + discrepancy (A' ∩ B) (A' ∩ B') :=
      discrepancy_triangle _ _ _
    _ ≤ discrepancy A A' + discrepancy B B' := by
      apply add_le_add (discrepancy_inter_right A A' B)
      simpa only [Finset.inter_comm] using discrepancy_inter_right B B' A'

/-- The symmetric-difference cardinality bounds the difference of cardinalities. -/
theorem abs_card_sub_le_discrepancy (A B : Finset α) :
    |(A.card : ℝ) - B.card| ≤ discrepancy A B := by
  have hA : A.card ≤ discrepancy A B + B.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := A) (t := B)
    exact h.trans (Nat.add_le_add_right
      (Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := A) (t := B))) _)
  have hB : B.card ≤ discrepancy A B + A.card := by
    simpa only [discrepancy_comm] using
      (show B.card ≤ discrepancy B A + A.card from
        (Finset.card_le_card_sdiff_add_card (s := B) (t := A)).trans
          (Nat.add_le_add_right
            (Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := B) (t := A))) _))
  have hAr : (A.card : ℝ) ≤ discrepancy A B + B.card := by exact_mod_cast hA
  have hBr : (B.card : ℝ) ≤ discrepancy A B + A.card := by exact_mod_cast hB
  rw [abs_le]
  constructor <;> linarith

end FiniteDiscrepancy

section AsymptoticDistance

variable [DecidableEq α]

/-- Slice discrepancy normalized by degree to the dimension `n`.
The convention at degree zero is immaterial for the limit at infinity. -/
noncomputable def normalizedDiscrepancy (n : ℕ) (A B : ℕ → Finset α) (k : ℕ) : ℝ :=
  (k : ℝ)⁻¹ ^ n * discrepancy (A k) (B k)

/-- The actual real limit superior in SGPT `eq:dsgdefapp`.
Without a growth bound this definition need not be a pseudometric. -/
noncomputable def asymptoticDistance (n : ℕ) (A B : ℕ → Finset α) : ℝ :=
  limsup (normalizedDiscrepancy n A B) atTop

theorem normalizedDiscrepancy_nonneg (n : ℕ) (A B : ℕ → Finset α) (k : ℕ) :
    0 ≤ normalizedDiscrepancy n A B k := by
  exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)
    (Nat.cast_nonneg _)

/-- The finite triangle inequality after normalization. -/
theorem normalizedDiscrepancy_triangle (n : ℕ) (A B D : ℕ → Finset α) (k : ℕ) :
    normalizedDiscrepancy n A D k ≤
      normalizedDiscrepancy n A B k + normalizedDiscrepancy n B D k := by
  have h : (discrepancy (A k) (D k) : ℝ) ≤
      discrepancy (A k) (B k) + discrepancy (B k) (D k) := by
    exact_mod_cast discrepancy_triangle (A k) (B k) (D k)
  simpa only [normalizedDiscrepancy, mul_add] using
    mul_le_mul_of_nonneg_left h
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)

theorem normalizedDiscrepancy_inter_right (n : ℕ) (A B D : ℕ → Finset α) (k : ℕ) :
    normalizedDiscrepancy n (fun j => A j ∩ D j) (fun j => B j ∩ D j) k ≤
      normalizedDiscrepancy n A B k := by
  have h : (discrepancy (A k ∩ D k) (B k ∩ D k) : ℝ) ≤
      discrepancy (A k) (B k) := by
    exact_mod_cast discrepancy_inter_right (A k) (B k) (D k)
  exact mul_le_mul_of_nonneg_left h
    (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)

theorem normalizedDiscrepancy_inter_inter (n : ℕ)
    (A B A' B' : ℕ → Finset α) (k : ℕ) :
    normalizedDiscrepancy n (fun j => A j ∩ B j) (fun j => A' j ∩ B' j) k ≤
      normalizedDiscrepancy n A A' k + normalizedDiscrepancy n B B' k := by
  have h : (discrepancy (A k ∩ B k) (A' k ∩ B' k) : ℝ) ≤
      discrepancy (A k) (A' k) + discrepancy (B k) (B' k) := by
    exact_mod_cast discrepancy_inter_inter (A k) (B k) (A' k) (B' k)
  simpa only [normalizedDiscrepancy, mul_add] using
    mul_le_mul_of_nonneg_left h
      (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)

private theorem normalized_bounded_below (n : ℕ) (A B : ℕ → Finset α) :
    IsBoundedUnder (· ≥ ·) atTop (normalizedDiscrepancy n A B) :=
  isBoundedUnder_of_eventually_ge
    (Eventually.of_forall (normalizedDiscrepancy_nonneg n A B))

private theorem normalized_cobounded_above (n : ℕ) (A B : ℕ → Finset α) :
    IsCoboundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A B) :=
  isCoboundedUnder_le_of_le atTop (normalizedDiscrepancy_nonneg n A B)

@[simp] theorem asymptoticDistance_self (n : ℕ) (A : ℕ → Finset α) :
    asymptoticDistance n A A = 0 := by
  have h : normalizedDiscrepancy n A A = fun _ => (0 : ℝ) := by
    funext k
    simp [normalizedDiscrepancy]
  rw [asymptoticDistance, h, limsup_const]

theorem asymptoticDistance_comm (n : ℕ) (A B : ℕ → Finset α) :
    asymptoticDistance n A B = asymptoticDistance n B A := by
  apply limsup_congr
  exact Eventually.of_forall (fun k => by
    dsimp [normalizedDiscrepancy]
    rw [discrepancy_comm])

theorem asymptoticDistance_nonneg (n : ℕ) (A B : ℕ → Finset α)
    (hAB : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A B)) :
    0 ≤ asymptoticDistance n A B := by
  change 0 ≤ limsup (normalizedDiscrepancy n A B) atTop
  simpa only [limsup_const] using
    (limsup_le_limsup (Eventually.of_forall (normalizedDiscrepancy_nonneg n A B))
      (u := fun _ : ℕ => (0 : ℝ))
      (isCoboundedUnder_le_of_le atTop (fun _ => le_rfl)) hAB)

/-- SGPT's limit-superior triangle argument, with its growth requirement explicit. -/
theorem asymptoticDistance_triangle (n : ℕ) (A B D : ℕ → Finset α)
    (hAB : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A B))
    (hBD : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n B D)) :
    asymptoticDistance n A D ≤ asymptoticDistance n A B + asymptoticDistance n B D := by
  apply (limsup_le_limsup
    (Eventually.of_forall (normalizedDiscrepancy_triangle n A B D))
    (normalized_cobounded_above n A D) (isBoundedUnder_le_add hAB hBD)).trans
  exact limsup_add_le (normalized_bounded_below n A B) hAB
    (normalized_cobounded_above n B D) hBD

/-- SGPT `lma:dBilapp` for any finite-slice families with bounded normalized discrepancy. -/
theorem asymptoticDistance_inter_right (n : ℕ) (A B D : ℕ → Finset α)
    (hAB : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A B)) :
    asymptoticDistance n (fun k => A k ∩ D k) (fun k => B k ∩ D k) ≤
      asymptoticDistance n A B := by
  exact limsup_le_limsup
    (Eventually.of_forall (normalizedDiscrepancy_inter_right n A B D))
    (normalized_cobounded_above n _ _) hAB

/-- The asymptotic estimate for two independently varying intersections. -/
theorem asymptoticDistance_inter_inter (n : ℕ) (A B A' B' : ℕ → Finset α)
    (hAA' : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A A'))
    (hBB' : IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n B B')) :
    asymptoticDistance n (fun k => A k ∩ B k) (fun k => A' k ∩ B' k) ≤
      asymptoticDistance n A A' + asymptoticDistance n B B' := by
  apply (limsup_le_limsup
    (Eventually.of_forall (normalizedDiscrepancy_inter_inter n A B A' B'))
    (normalized_cobounded_above n _ _) (isBoundedUnder_le_add hAA' hBB')).trans
  exact limsup_add_le (normalized_bounded_below n A A') hAA'
    (normalized_cobounded_above n B B') hBB'

/-- Polynomial cardinal growth is independent of the discrepancy definition. -/
def HasPolynomialGrowth (n : ℕ) (A : ℕ → Finset α) : Prop :=
  ∃ M : ℝ, ∀ k : ℕ, 1 ≤ k → (A k).card ≤ M * (k : ℝ) ^ n

/-- Polynomial growth of each slice family produces the boundedness needed by real limsup. -/
theorem bounded_normalizedDiscrepancy_of_growth (n : ℕ) (A B : ℕ → Finset α)
    (hA : HasPolynomialGrowth n A) (hB : HasPolynomialGrowth n B) :
    IsBoundedUnder (· ≤ ·) atTop (normalizedDiscrepancy n A B) := by
  obtain ⟨M, hM⟩ := hA
  obtain ⟨N, hN⟩ := hB
  apply isBoundedUnder_of_eventually_le (a := M + N)
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hc : (discrepancy (A k) (B k) : ℝ) ≤ (A k).card + (B k).card := by
    exact_mod_cast ((Finset.card_le_card (Finset.symmDiff_subset_union
      (s := A k) (t := B k))).trans (Finset.card_union_le _ _))
  have hbound : (discrepancy (A k) (B k) : ℝ) ≤ (M + N) * (k : ℝ) ^ n :=
    hc.trans (by simpa only [add_mul] using add_le_add (hM k hk) (hN k hk))
  calc
    normalizedDiscrepancy n A B k ≤ (k : ℝ)⁻¹ ^ n * ((M + N) * (k : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hbound
        (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) n)
    _ = M + N := by
      rw [mul_left_comm, ← mul_pow, inv_mul_cancel₀ hk0, one_pow, mul_one]

/-- Intersecting a family with another preserves its polynomial cardinal growth. -/
theorem HasPolynomialGrowth.inter_right {n : ℕ} {A : ℕ → Finset α}
    (hA : HasPolynomialGrowth n A) (B : ℕ → Finset α) :
    HasPolynomialGrowth n (fun k => A k ∩ B k) := by
  obtain ⟨M, hM⟩ := hA
  refine ⟨M, fun k hk => ?_⟩
  have hc : ((A k ∩ B k).card : ℝ) ≤ (A k).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₁ := A k) (s₂ := B k))
  exact hc.trans (hM k hk)

/-- The compact cone-slice geometry itself supplies the independent cardinal-growth bound. -/
theorem latticePoints_hasPolynomialGrowth_of_compact {n : ℕ}
    (C : ConvexCone ℝ ((Fin n → ℝ) × ℝ)) (hK : IsCompact (heightOne C))
    (hpointed : ∀ x : Fin n → ℝ, (x, 0) ∈ C → x = 0) :
    HasPolynomialGrowth n (latticePointSlices C hK hpointed) := by
  obtain ⟨M, hM⟩ := exists_lattice_coordinate_bound_of_compact C hK
  refine ⟨((2 * M + 1 : ℕ) : ℝ) ^ n, fun k hk => ?_⟩
  have hsub : latticePointSlices C hK hpointed k ⊆ latticeBox n M k := by
    intro x hx
    exact mem_latticeBox.mpr (hM k hk x ((mem_latticePointSlices C hK hpointed k x).mp hx))
  have hc := Finset.card_le_card hsub
  rw [card_latticeBox] at hc
  have hbase : 2 * M * k + 1 ≤ (2 * M + 1) * k := by nlinarith
  have hp := Nat.pow_le_pow_left hbase n
  have hnat : (latticePointSlices C hK hpointed k).card ≤ (2 * M + 1) ^ n * k ^ n := by
    simpa only [mul_pow] using hc.trans hp
  exact_mod_cast hnat

/-- The distance triangle inequality for polynomially bounded finite slice families. -/
theorem asymptoticDistance_triangle_of_growth (n : ℕ) (A B D : ℕ → Finset α)
    (hA : HasPolynomialGrowth n A) (hB : HasPolynomialGrowth n B)
    (hD : HasPolynomialGrowth n D) :
    asymptoticDistance n A D ≤ asymptoticDistance n A B + asymptoticDistance n B D :=
  asymptoticDistance_triangle n A B D
    (bounded_normalizedDiscrepancy_of_growth n A B hA hB)
    (bounded_normalizedDiscrepancy_of_growth n B D hB hD)

/-- SGPT's intersection contraction with ordinary polynomial growth hypotheses. -/
theorem asymptoticDistance_inter_right_of_growth (n : ℕ) (A B D : ℕ → Finset α)
    (hA : HasPolynomialGrowth n A) (hB : HasPolynomialGrowth n B) :
    asymptoticDistance n (fun k => A k ∩ D k) (fun k => B k ∩ D k) ≤
      asymptoticDistance n A B :=
  asymptoticDistance_inter_right n A B D
    (bounded_normalizedDiscrepancy_of_growth n A B hA hB)

/-- The convergence statement of SGPT `lma:dBilapp` on finite-slice families.
The eventual cardinal growth furnished by the fixed cone remains an explicit input. -/
theorem tendsto_asymptoticDistance_inter (n : ℕ)
    (A B : ℕ → ℕ → Finset α) (S T : ℕ → Finset α)
    (hA : ∀ i, HasPolynomialGrowth n (A i))
    (hB : ∀ i, HasPolynomialGrowth n (B i))
    (hS : HasPolynomialGrowth n S) (hT : HasPolynomialGrowth n T)
    (hAS : Tendsto (fun i => asymptoticDistance n (A i) S) atTop (nhds 0))
    (hBT : Tendsto (fun i => asymptoticDistance n (B i) T) atTop (nhds 0)) :
    Tendsto (fun i => asymptoticDistance n
      (fun k => A i k ∩ B i k) (fun k => S k ∩ T k)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hAS.add hBT)
  · intro i
    exact asymptoticDistance_nonneg n _ _
      (bounded_normalizedDiscrepancy_of_growth n _ _
        ((hA i).inter_right (B i)) (hS.inter_right T))
  · intro i
    exact asymptoticDistance_inter_inter n (A i) (B i) S T
      (bounded_normalizedDiscrepancy_of_growth n (A i) S (hA i) hS)
      (bounded_normalizedDiscrepancy_of_growth n (B i) T (hB i) hT)

end AsymptoticDistance

/-- The original geometric hypotheses on the fixed cone in Appendix C. -/
structure AdmissibleCone (n : ℕ) where
  cone : ConvexCone ℝ ((Fin n → ℝ) × ℝ)
  closed : IsClosed (cone : Set ((Fin n → ℝ) × ℝ))
  nonnegativeHeight : ∀ z ∈ cone, 0 ≤ z.2
  zeroHeight : ∀ x : Fin n → ℝ, (x, 0) ∈ cone → x = 0

/-- All lattice subsets of the fixed cone, SGPT's `hat S(C)`.
An additive closure condition is deliberately not imposed. -/
def ConeSubset {n : ℕ} (C : AdmissibleCone n) :=
  {S : Set ((Fin n → ℤ) × ℤ) // S ⊆ (latticePoints C.cone : Set _)}

namespace ConeSubset

variable {n : ℕ} {C : AdmissibleCone n}

private theorem compactHeightOne (C : AdmissibleCone n) : IsCompact (heightOne C.cone) :=
  isCompact_heightOne C.cone C.closed C.nonnegativeHeight C.zeroHeight

/-- Every nonnegative integer slice of every lattice subset of the cone is finite. -/
theorem finite_slice (S : ConeSubset C) (k : ℕ) : (slice S.val (k : ℤ)).Finite :=
  (finite_latticePoints_slice_of_compact C.cone (compactHeightOne C) C.zeroHeight k).subset
    (fun _ hx => S.property hx)

/-- The finite slices of the actual lattice subset. -/
noncomputable def slices (S : ConeSubset C) (k : ℕ) : Finset (Fin n → ℤ) :=
  (S.finite_slice k).toFinset

@[simp] theorem mem_slices (S : ConeSubset C) (k : ℕ) (x : Fin n → ℤ) :
    x ∈ S.slices k ↔ (x, (k : ℤ)) ∈ S.val := by
  simp [slices]

/-- The source cone assumptions produce polynomial growth for every allowed lattice subset. -/
theorem hasPolynomialGrowth (S : ConeSubset C) : HasPolynomialGrowth n S.slices := by
  obtain ⟨M, hM⟩ := latticePoints_hasPolynomialGrowth_of_compact C.cone
    (compactHeightOne C) C.zeroHeight
  refine ⟨M, fun k hk => ?_⟩
  have hsub : S.slices k ⊆ latticePointSlices C.cone (compactHeightOne C) C.zeroHeight k := by
    intro x hx
    exact (mem_latticePointSlices _ _ _ _ _).mpr (S.property ((mem_slices S k x).mp hx))
  have hc : ((S.slices k).card : ℝ) ≤
      (latticePointSlices C.cone (compactHeightOne C) C.zeroHeight k).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hM k hk)

/-- The source distance on all lattice subsets of the fixed cone. -/
noncomputable def distance (S T : ConeSubset C) : ℝ :=
  asymptoticDistance n S.slices T.slices

/-- The formal distance is exactly the manuscript's cardinality formula, with real subtraction. -/
theorem distance_eq_limsup_card (S T : ConeSubset C) :
    distance S T = limsup (fun k : ℕ => (k : ℝ)⁻¹ ^ n *
      ((S.slices k).card + (T.slices k).card - 2 * (S.slices k ∩ T.slices k).card)) atTop := by
  apply limsup_congr
  apply Eventually.of_forall
  intro k
  have h := discrepancy_formula (S.slices k) (T.slices k)
  have hr : (discrepancy (S.slices k) (T.slices k) : ℝ) +
      2 * (S.slices k ∩ T.slices k).card = (S.slices k).card + (T.slices k).card := by
    exact_mod_cast h
  dsimp [normalizedDiscrepancy]
  congr 1
  linarith

/-- SGPT `lma:dpsapp`: the actual distance on the cone's lattice subsets is a pseudometric. -/
noncomputable instance pseudoMetricSpace : PseudoMetricSpace (ConeSubset C) where
  dist := distance
  dist_self S := asymptoticDistance_self n S.slices
  dist_comm S T := asymptoticDistance_comm n S.slices T.slices
  dist_triangle S T U := asymptoticDistance_triangle_of_growth n S.slices T.slices U.slices
    S.hasPolynomialGrowth T.hasPolynomialGrowth U.hasPolynomialGrowth

@[simp] theorem dist_eq_distance (S T : ConeSubset C) : dist S T = distance S T := rfl

/-- Intersection of lattice subsets stays in the fixed cone. -/
def inter (S T : ConeSubset C) : ConeSubset C :=
  ⟨S.val ∩ T.val, fun _ hx => S.property hx.1⟩

@[simp] theorem slices_inter (S T : ConeSubset C) (k : ℕ) :
    (inter S T).slices k = S.slices k ∩ T.slices k := by
  ext x
  rw [mem_slices, Finset.mem_inter, mem_slices, mem_slices]
  rfl

theorem slices_inter_fun (S T : ConeSubset C) :
    (inter S T).slices = fun k => S.slices k ∩ T.slices k :=
  funext (slices_inter S T)

/-- SGPT `lma:dBilapp`, the contraction assertion under exactly the fixed-cone assumptions. -/
theorem distance_inter_right (S T U : ConeSubset C) :
    distance (inter S U) (inter T U) ≤ distance S T := by
  rw [distance, slices_inter_fun, slices_inter_fun]
  exact asymptoticDistance_inter_right_of_growth n S.slices T.slices U.slices
    S.hasPolynomialGrowth T.hasPolynomialGrowth

/-- SGPT `lma:dBilapp`, the convergence assertion with no assumed growth interface. -/
theorem tendsto_distance_inter (S T : ℕ → ConeSubset C) (S₀ T₀ : ConeSubset C)
    (hS : Tendsto (fun i => distance (S i) S₀) atTop (nhds 0))
    (hT : Tendsto (fun i => distance (T i) T₀) atTop (nhds 0)) :
    Tendsto (fun i => distance (inter (S i) (T i)) (inter S₀ T₀)) atTop (nhds 0) := by
  simp only [distance, slices_inter_fun] at hS hT ⊢
  exact tendsto_asymptoticDistance_inter n (fun i => (S i).slices)
    (fun i => (T i).slices) S₀.slices T₀.slices
    (fun i => (S i).hasPolynomialGrowth) (fun i => (T i).hasPolynomialGrowth)
    S₀.hasPolynomialGrowth T₀.hasPolynomialGrowth hS hT

/-- The source intersection-convergence assertion in the induced pseudometric topology. -/
theorem tendsto_inter (S T : ℕ → ConeSubset C) (S₀ T₀ : ConeSubset C)
    (hS : Tendsto S atTop (nhds S₀)) (hT : Tendsto T atTop (nhds T₀)) :
    Tendsto (fun i => inter (S i) (T i)) atTop (nhds (inter S₀ T₀)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact tendsto_distance_inter S T S₀ T₀
    (tendsto_iff_dist_tendsto_zero.mp hS) (tendsto_iff_dist_tendsto_zero.mp hT)

end ConeSubset

end SGPT.AlmostSemigroup
