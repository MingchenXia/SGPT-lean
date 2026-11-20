import SGPT.Toric.ToricFullSubfacesStrictSlack
import SGPT.Toric.ToricAugmentedBaseLocusNecessity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology BigOperators Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem convex_toricDivisorFace (D : ToricDivisor γ hs)
    (R : Set (PolytopeToricRays γ hs)) : Convex ℝ (toricDivisorFace D R) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_toricDivisorPolytope D) hx.1 hy.1 ha hb hab, ?_⟩
  intro ρ hρ
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hx.2 ρ hρ, hy.2 ρ hρ]
  rw [← add_mul, hab, one_mul]

theorem toricDivisorSlack_affine_combination (D : ToricDivisor γ hs)
    (ρ : PolytopeToricRays γ hs) (x y : E) {a b : ℝ} (hab : a + b = 1) :
    toricDivisorSlack D ρ (a • x + b • y) =
      a * toricDivisorSlack D ρ x + b * toricDivisorSlack D ρ y := by
  simp only [toricDivisorSlack, map_add, map_smul, smul_eq_mul]
  linear_combination -(D ρ : ℝ) * hab

/-- Finitely many genuine positive slack witnesses can be combined within
the SAME actual original face, retaining all already positive constraints. -/
theorem exists_face_point_pos_slack_finite (D : ToricDivisor γ hs)
    (R : Set (PolytopeToricRays γ hs)) (hne : (toricDivisorFace D R).Nonempty)
    {S : Set (PolytopeToricRays γ hs)} (hS : S.Finite)
    (hpos : ∀ ρ ∈ S, ∃ x ∈ toricDivisorFace D R, 0 < toricDivisorSlack D ρ x) :
    ∃ x ∈ toricDivisorFace D R, ∀ ρ ∈ S, 0 < toricDivisorSlack D ρ x := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, by simp⟩
  | @insert ρ S hnot hS ih =>
    obtain ⟨x, hx, hxpos⟩ := ih (fun σ hσ => hpos σ (Set.mem_insert_of_mem ρ hσ))
    obtain ⟨y, hy, hypos⟩ := hpos ρ (Set.mem_insert ρ S)
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y,
      convex_toricDivisorFace D R hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
    intro σ hσ
    rw [toricDivisorSlack_affine_combination D σ x y (by norm_num)]
    rcases Set.mem_insert_iff.mp hσ with rfl | hσ
    · have hxnonneg := toricDivisorSlack_nonneg hx.1 σ
      nlinarith
    · have hxstrict := hxpos σ hσ
      have hynonneg := toricDivisorSlack_nonneg hy.1 σ
      nlinarith

theorem exists_face_point_pos_slack_outside_vertex
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hfull : ∀ I : Set (Fin n), I ⊆ J →
      ToricDivisorFaceFull D (polytopeToricRay γ hs v '' I)) :
    ∃ q ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J),
      ∀ ρ : PolytopeToricRays γ hs, ρ ∉ Set.range (polytopeToricRay γ hs v) →
        0 < toricDivisorSlack D ρ q := by
  let _ := (finite_polytopeToricRays γ hs).fintype
  exact exists_face_point_pos_slack_finite D _ (hfull J (Set.Subset.refl J)).1
    (Set.toFinite _) (fun ρ hρ =>
      exists_pos_toricDivisorSlack_of_all_subfaces_full D v J hfull ρ hρ)

theorem toricAmpleDivisorSlack_vertex_ray_eq_zero (v : latticePolytopeVertices γ)
    (j : Fin n) :
    toricDivisorSlack (polytopeToricAmpleDivisor γ hs) (polytopeToricRay γ hs v j)
      (latticeVector v.val) = 0 := by
  exact toricDivisorSlack_eq_zero_of_mem_face
    (toricAmpleDivisorFace_vertex_mem (hs := hs) v Set.univ) ⟨j, Set.mem_univ j, rfl⟩

/-- A genuine positive INTEGER dominates all finitely many required
original reference slacks, including an empty outside-ray family. -/
theorem exists_nat_ample_slack_le_mul (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) {q : E} (hq : q ∈ toricDivisorPolytope D)
    (hpos : ∀ ρ : PolytopeToricRays γ hs, ρ ∉ Set.range (polytopeToricRay γ hs v) →
      0 < toricDivisorSlack D ρ q) :
    ∃ N : ℕ, 0 < N ∧ ∀ ρ : PolytopeToricRays γ hs,
      toricDivisorSlack (polytopeToricAmpleDivisor γ hs) ρ (latticeVector v.val) ≤
        (N : ℝ) * toricDivisorSlack D ρ q := by
  let _ := (finite_polytopeToricRays γ hs).fintype
  have hb : ∀ ρ : PolytopeToricRays γ hs, ∃ N : ℕ,
      toricDivisorSlack (polytopeToricAmpleDivisor γ hs) ρ (latticeVector v.val) ≤
        (N : ℝ) * toricDivisorSlack D ρ q := by
    intro ρ
    by_cases hin : ρ ∈ Set.range (polytopeToricRay γ hs v)
    · obtain ⟨j, rfl⟩ := hin
      refine ⟨0, ?_⟩
      rw [toricAmpleDivisorSlack_vertex_ray_eq_zero]
      norm_num
    · obtain ⟨N, hN⟩ := exists_nat_gt
        (toricDivisorSlack (polytopeToricAmpleDivisor γ hs) ρ (latticeVector v.val) /
          toricDivisorSlack D ρ q)
      exact ⟨N, le_of_lt ((div_lt_iff₀ (hpos ρ hin)).mp hN)⟩
  choose bound hbound using hb
  let N := Finset.univ.sup bound + 1
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro ρ
  apply (hbound ρ).trans
  apply mul_le_mul_of_nonneg_right _ (toricDivisorSlack_nonneg hq ρ)
  have hh : bound ρ ≤ N :=
    (Finset.le_sup (f := bound) (Finset.mem_univ ρ)).trans (Nat.le_add_right _ _)
  exact_mod_cast hh

theorem scaled_sub_vertex_mem_perturbed_face (D : ToricDivisor γ hs)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {q : E}
    (hq : q ∈ toricDivisorFace D (polytopeToricRay γ hs v '' J))
    (N : ℕ)
    (hbound : ∀ ρ : PolytopeToricRays γ hs,
      toricDivisorSlack (polytopeToricAmpleDivisor γ hs) ρ (latticeVector v.val) ≤
        (N : ℝ) * toricDivisorSlack D ρ q) :
    (N : ℝ) • q - latticeVector v.val ∈
      toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs)
        (polytopeToricRay γ hs v '' J) := by
  have hslack (ρ : PolytopeToricRays γ hs) :
      toricDivisorSlack ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) ρ
        ((N : ℝ) • q - latticeVector v.val) =
      (N : ℝ) * toricDivisorSlack D ρ q -
        toricDivisorSlack (polytopeToricAmpleDivisor γ hs) ρ (latticeVector v.val) := by
    simp only [toricDivisorSlack, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, map_sub, map_smul]
    ring
  refine ⟨?_, ?_⟩
  · intro ρ
    have hh := hbound ρ
    have hz : 0 ≤ toricDivisorSlack ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) ρ
        ((N : ℝ) • q - latticeVector v.val) := by rw [hslack]; linarith
    unfold toricDivisorSlack at hz
    change -(((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) ρ : ℝ) ≤ _
    linarith
  · rintro ρ ⟨j, hj, rfl⟩
    have hz := hslack (polytopeToricRay γ hs v j)
    rw [toricDivisorSlack_eq_zero_of_mem_face hq ⟨j, hj, rfl⟩,
      toricAmpleDivisorSlack_vertex_ray_eq_zero, mul_zero, sub_zero] at hz
    unfold toricDivisorSlack at hz
    linarith

theorem exists_perturbed_face_nonempty_of_all_subfaces_full
    (D : ToricDivisor γ hs) (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hfull : ∀ I : Set (Fin n), I ⊆ J →
      ToricDivisorFaceFull D (polytopeToricRay γ hs v '' I)) :
    ∃ N : ℕ, 0 < N ∧
      (toricDivisorFace ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs)
        (polytopeToricRay γ hs v '' J)).Nonempty := by
  obtain ⟨q, hq, hpos⟩ := exists_face_point_pos_slack_outside_vertex D v J hfull
  obtain ⟨N, hN, hbound⟩ := exists_nat_ample_slack_le_mul D v hq.1 hpos
  exact ⟨N, hN, _, scaled_sub_vertex_mem_perturbed_face D v J hq N hbound⟩

/-- The whole original UNION formula, with the original empty-face
convention. There is no incoming face/fullness/base-locus certificate. -/
theorem toricAugmentedBaseLocus_eq_deficient_faces (D : ToricDivisor γ hs) :
    toricAugmentedBaseLocus D =
      ⋃ (R : Set (PolytopeToricRays γ hs)) (_ : IsToricFanCone R)
        (_ : ToricDivisorFaceDeficient D R), toricOrbitClosure R := by
  apply Set.Subset.antisymm _ (deficient_toricOrbitClosure_union_subset_augmentedBaseLocus D)
  intro p hp
  by_contra hnot
  have hnondef (R : Set (PolytopeToricRays γ hs)) (hR : IsToricFanCone R)
      (hRp : R ⊆ orbitRays p) : ¬ ToricDivisorFaceDeficient D R := by
    intro hdef
    apply hnot
    simp only [mem_iUnion, exists_prop]
    exact ⟨R, hR, hdef, mem_toricOrbitClosure_iff.mpr hRp⟩
  obtain ⟨v, J, hJ⟩ := isToricFanCone_orbitRays p
  have hfull (I : Set (Fin n)) (hIJ : I ⊆ J) :
      ToricDivisorFaceFull D (polytopeToricRay γ hs v '' I) := by
    apply (toricDivisorFaceFull_iff_not_deficient D ⟨v, I, rfl⟩).mpr
    apply hnondef _ ⟨v, I, rfl⟩
    rw [hJ]
    exact Set.image_mono hIJ
  obtain ⟨N, hN, hface⟩ := exists_perturbed_face_nonempty_of_all_subfaces_full D v J hfull
  have hstable : p ∈ toricStableBaseLocus ((N : ℤ) • D - polytopeToricAmpleDivisor γ hs) :=
    Set.mem_iInter.mp (Set.mem_iInter.mp hp N) hN
  have hexit := (not_mem_toricStableBaseLocus_iff_face_nonempty _ p).mpr
    (by rw [hJ]; exact hface)
  exact hexit hstable

end SGPT.Toric
