import SGPT.Toric.OriginalLatticeEdges
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Join

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {n : ℕ} {K : Type*}

/-- The literal original generator image with the chosen vertex removed. -/
def latticeVertexOtherGenerators (γ : K → Fin n → ℤ) (v : Fin n → ℤ) :
    Set (Fin n → ℝ) :=
  Set.range (fun k => integerCast (γ k)) \ {integerCast v}

/-- The literal normalized original generator family, including negative
original exponents without any coordinate-positivity input. -/
def latticeVertexDirectionGenerators (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ) : Set (Fin n → ℝ) :=
  (fun x => (h (x - integerCast v))⁻¹ • (x - integerCast v)) ''
    latticeVertexOtherGenerators γ v

/-- The actual finite normalized-generator convex hull. -/
def latticeVertexDirectionSection (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ (latticeVertexDirectionGenerators γ v h)

/-- A nonsingleton original polytope has an actual original generator other
than the chosen vertex; no nonempty section is assumed. -/
theorem latticeVertexOtherGenerators_nonempty (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ)
    (hP : latticePolytope γ ≠ {integerCast v.val}) :
    (latticeVertexOtherGenerators γ v.val).Nonempty := by
  by_contra hempty
  apply hP
  apply Set.Subset.antisymm
  · calc
      latticePolytope γ ⊆ convexHull ℝ {integerCast v.val} := by
        apply convexHull_mono
        intro x hx
        by_contra hxv
        exact hempty ⟨x, hx, hxv⟩
      _ = {integerCast v.val} := convexHull_singleton _
  · exact Set.singleton_subset_iff.mpr v.property.1

/-- Genuine strict point/closed-hull separation internally manufactures a
positive original vertex-direction functional. -/
theorem exists_latticeVertex_positive_functional [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (hP : latticePolytope γ ≠ {integerCast v.val}) :
    ∃ h : (Fin n → ℝ) →L[ℝ] ℝ,
      ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val → 0 < h (x - integerCast v.val) := by
  let A := latticeVertexOtherGenerators γ v.val
  have hA : A.Nonempty := latticeVertexOtherGenerators_nonempty γ v hP
  have hAfin : A.Finite := (Set.finite_range (fun k => integerCast (γ k))).sdiff
  have hvnot : integerCast v.val ∉ convexHull ℝ A := by
    have hv := ((convex_latticePolytope γ).mem_extremePoints_iff_mem_sdiff_convexHull_sdiff.mp
      v.property.2).2
    intro hcontra
    apply hv
    apply convexHull_mono (t := latticePolytope γ \ {integerCast v.val}) _ hcontra
    intro x hx
    exact ⟨subset_convexHull ℝ _ hx.1, hx.2⟩
  obtain ⟨h, c, hvc, hAc⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ A) (hAfin.isClosed_convexHull ℝ) hvnot
  refine ⟨h, ?_⟩
  intro x hx hne
  have hvgen := latticePolytope_extremePoints_subset_generators γ v.property.2
  have hinsert : insert (integerCast v.val) A = Set.range (fun k => integerCast (γ k)) := by
    ext y
    change (y = integerCast v.val ∨
      y ∈ Set.range (fun k => integerCast (γ k)) ∧ y ∉ {integerCast v.val}) ↔ _
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hy, _⟩)
      · exact hvgen
      · exact hy
    · intro hy
      by_cases heq : y = integerCast v.val
      · exact Or.inl heq
      · exact Or.inr ⟨hy, heq⟩
  have hxjoin : x ∈ convexJoin ℝ {integerCast v.val} (convexHull ℝ A) := by
    rw [← convexHull_insert hA, hinsert]
    exact hx
  obtain ⟨y, hy, z, hz, hxseg⟩ := mem_convexJoin.mp hxjoin
  obtain rfl : y = integerCast v.val := hy
  rw [segment_eq_image'] at hxseg
  obtain ⟨t, ht, rfl⟩ := hxseg
  dsimp only at hne ⊢
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    exact hne (by rw [← heq, zero_smul, add_zero]))
  rw [add_sub_cancel_left, map_smul]
  exact mul_pos htpos (by rw [map_sub]; linarith [hAc z hz])

/-- The actual normalized original generator set is finite. -/
theorem finite_latticeVertexDirectionGenerators [Fintype K]
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ) :
    (latticeVertexDirectionGenerators γ v h).Finite :=
  ((Set.finite_range (fun k => integerCast (γ k))).sdiff).image _

/-- Nonemptiness of the original source section is manufactured from an
original generator different from the vertex. -/
theorem nonempty_latticeVertexDirectionGenerators (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hP : latticePolytope γ ≠ {integerCast v.val}) :
    (latticeVertexDirectionGenerators γ v.val h).Nonempty :=
  (latticeVertexOtherGenerators_nonempty γ v hP).image _

/-- Existing genuine finite-hull compactness applies to the literal section. -/
theorem isCompact_latticeVertexDirectionSection [Fintype K]
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ) :
    IsCompact (latticeVertexDirectionSection γ v h) :=
  (finite_latticeVertexDirectionGenerators γ v h).isCompact_convexHull ℝ

/-- Existing hull convexity applies to the SAME normalized section. -/
theorem convex_latticeVertexDirectionSection (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ) : Convex ℝ (latticeVertexDirectionSection γ v h) :=
  convex_convexHull ℝ _

/-- Genuine source positivity excludes every denominator zero before the
normalization is evaluated by its actual linear functional. -/
theorem latticeVertexDirectionSection_functional_eq_one
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {r : Fin n → ℝ} (hr : r ∈ latticeVertexDirectionSection γ v h) : h r = 1 := by
  have hsub : latticeVertexDirectionGenerators γ v h ⊆ h ⁻¹' {(1 : ℝ)} := by
    rintro _ ⟨x, hx, rfl⟩
    have hp := hpos x (subset_convexHull ℝ _ hx.1) hx.2
    change h ((h (x - integerCast v))⁻¹ • (x - integerCast v)) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ hp.ne'
  exact convexHull_min hsub ((convex_singleton (1 : ℝ)).linear_preimage h.toLinearMap) hr

/-- Genuine finite convex combinations normalize every original nonvertex
point into the SAME original finite-generator section.  Vertex terms have
zero weight before division; an actual section point supplies their harmless
zero-weight representative. -/
theorem latticeVertexDirectionSection_normalized_mem
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
      0 < h (x - integerCast v.val))
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) (hne : x ≠ integerCast v.val) :
    (h (x - integerCast v.val))⁻¹ • (x - integerCast v.val) ∈
      latticeVertexDirectionSection γ v.val h := by
  classical
  have hP : latticePolytope γ ≠ {integerCast v.val} := by
    intro heq
    exact hne (by simpa only [heq, Set.mem_singleton_iff] using hx)
  obtain ⟨r₀, hr₀⟩ := nonempty_latticeVertexDirectionGenerators γ v h hP
  obtain ⟨ι, hι, w, z, hw, hw1, hz, hzx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  let := hι
  have hzP (i : ι) : z i ∈ latticePolytope γ := subset_convexHull ℝ _ (hz i)
  let H := h (x - integerCast v.val)
  have hH : 0 < H := hpos x hx hne
  have hzn (i : ι) : 0 ≤ h (z i - integerCast v.val) := by
    by_cases heq : z i = integerCast v.val
    · simp [heq]
    · exact (hpos (z i) (hzP i) heq).le
  let s : ι → ℝ := fun i => w i * h (z i - integerCast v.val) / H
  let f : ι → Fin n → ℝ := fun i => if z i = integerCast v.val then r₀ else
    (h (z i - integerCast v.val))⁻¹ • (z i - integerCast v.val)
  have hs (i : ι) : 0 ≤ s i := div_nonneg (mul_nonneg (hw i) (hzn i)) hH.le
  have hdiffsum : ∑ i, w i • (z i - integerCast v.val) = x - integerCast v.val := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, hzx]
  have hHsum : ∑ i, w i * h (z i - integerCast v.val) = H := by
    calc
      _ = h (∑ i, w i • (z i - integerCast v.val)) := by simp
      _ = H := by rw [hdiffsum]
  have hs1 : ∑ i, s i = 1 := by
    simp only [s, div_eq_mul_inv, ← Finset.sum_mul, hHsum]
    exact mul_inv_cancel₀ hH.ne'
  have hf (i : ι) : f i ∈ latticeVertexDirectionGenerators γ v.val h := by
    dsimp only [f]
    split_ifs with heq
    · exact hr₀
    · exact ⟨z i, ⟨hz i, heq⟩, rfl⟩
  have hterm (i : ι) : s i • f i = H⁻¹ • (w i • (z i - integerCast v.val)) := by
    by_cases heq : z i = integerCast v.val
    · simp [s, f, heq]
    · have hp := hpos (z i) (hzP i) heq
      dsimp only [s, f]
      rw [if_neg heq, smul_smul, smul_smul]
      congr 1
      field_simp
  apply mem_convexHull_of_exists_fintype s f hs hs1 hf
  calc
    ∑ i, s i • f i = ∑ i, H⁻¹ • (w i • (z i - integerCast v.val)) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = H⁻¹ • (x - integerCast v.val) := by rw [← Finset.smul_sum, hdiffsum]

/-- Positivity away from the actual vertex gives genuine nonnegativity on
ALL of the original polytope, including that vertex. -/
theorem latticeVertex_functional_nonneg (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) : 0 ≤ h (x - integerCast v) := by
  by_cases heq : x = integerCast v
  · simp [heq]
  · exact (hpos x hx heq).le

/-- A source point has zero functional height exactly at the original vertex. -/
theorem latticeVertex_functional_eq_zero_iff (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {x : Fin n → ℝ} (hx : x ∈ latticePolytope γ) :
    h (x - integerCast v) = 0 ↔ x = integerCast v := by
  constructor
  · intro hz
    by_contra hne
    exact (hpos x hx hne).ne' hz
  · rintro rfl
    simp

/-- Existing finite-hull extremality places each ACTUAL extreme direction
in the literal normalized ORIGINAL generator family. -/
theorem latticeVertexDirectionSection_extremePoints_subset_generators
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ) :
    (latticeVertexDirectionSection γ v h).extremePoints ℝ ⊆
      latticeVertexDirectionGenerators γ v h :=
  extremePoints_convexHull_subset

/-- The original rank-zero normalized generator family is genuinely empty. -/
theorem latticeVertexDirectionGenerators_zero_eq_empty (γ : K → Fin 0 → ℤ)
    (v : Fin 0 → ℤ) (h : (Fin 0 → ℝ) →L[ℝ] ℝ) :
    latticeVertexDirectionGenerators γ v h = ∅ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, _⟩
    exact False.elim (hx.2 (Subsingleton.elim x (integerCast v)))
  · exact Set.empty_subset _

/-- Only ORIGINAL finite generators, an ACTUAL original vertex and the
nonsingleton branch enter this final producer.  Strict functional positivity,
nonempty compact convex section, height one and every normalized original
point are all manufactured internally. -/
theorem exists_latticeVertex_direction_section [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (hP : latticePolytope γ ≠ {integerCast v.val}) :
    ∃ h : (Fin n → ℝ) →L[ℝ] ℝ,
      (∀ x ∈ latticePolytope γ, x ≠ integerCast v.val → 0 < h (x - integerCast v.val)) ∧
      (latticeVertexDirectionSection γ v.val h).Nonempty ∧
      IsCompact (latticeVertexDirectionSection γ v.val h) ∧
      Convex ℝ (latticeVertexDirectionSection γ v.val h) ∧
      (∀ r ∈ latticeVertexDirectionSection γ v.val h, h r = 1) ∧
      (∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
        (h (x - integerCast v.val))⁻¹ • (x - integerCast v.val) ∈
          latticeVertexDirectionSection γ v.val h) := by
  obtain ⟨h, hpos⟩ := exists_latticeVertex_positive_functional γ v hP
  exact ⟨h, hpos, (nonempty_latticeVertexDirectionGenerators γ v h hP).convexHull,
    isCompact_latticeVertexDirectionSection γ v.val h,
    convex_latticeVertexDirectionSection γ v.val h,
    fun _ hr => latticeVertexDirectionSection_functional_eq_one γ v.val h hpos hr,
    fun _ hx hne => latticeVertexDirectionSection_normalized_mem γ v h hpos hx hne⟩

end SGPT.Toric
