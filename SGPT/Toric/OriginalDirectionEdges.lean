import SGPT.Toric.OriginalVertexDirectionSection

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

variable {n : ℕ} {K : Type*}

/-- The SAME original source points on the nonnegative ray of an actual
direction.  No edge, face, compactness or coordinate sign is supplied. -/
def latticeVertexDirectionFace (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (r : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ latticePolytope γ ∧ ∃ t : ℝ, 0 ≤ t ∧ x - integerCast v = t • r}

/-- The original vertex belongs to the actual ray set. -/
theorem latticeVertexDirectionFace_vertex_mem (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ) (r : Fin n → ℝ) :
    integerCast v.val ∈ latticeVertexDirectionFace γ v.val r :=
  ⟨v.property.1, 0, le_rfl, by simp⟩

/-- Actual height one identifies the ray parameter with the SAME original
functional value; its nonnegativity is produced from original positivity. -/
theorem mem_latticeVertexDirectionFace_iff (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {r x : Fin n → ℝ} (hr : r ∈ latticeVertexDirectionSection γ v h) :
    x ∈ latticeVertexDirectionFace γ v r ↔
      x ∈ latticePolytope γ ∧ x - integerCast v = h (x - integerCast v) • r := by
  have hr1 := latticeVertexDirectionSection_functional_eq_one γ v h hpos hr
  constructor
  · rintro ⟨hx, t, ht, hxt⟩
    have hheight : h (x - integerCast v) = t := by rw [hxt, map_smul, hr1, smul_eq_mul, mul_one]
    exact ⟨hx, by rw [hheight]; exact hxt⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨hx, h (x - integerCast v), latticeVertex_functional_nonneg γ v h hpos hx, hxt⟩

/-- The actual ray set is compact by its produced closed equality description
inside the SAME actual compact source polytope. -/
theorem isCompact_latticeVertexDirectionFace [Fintype K]
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {r : Fin n → ℝ} (hr : r ∈ latticeVertexDirectionSection γ v h) :
    IsCompact (latticeVertexDirectionFace γ v r) := by
  have heq : latticeVertexDirectionFace γ v r = latticePolytope γ ∩
      {x | x - integerCast v = h (x - integerCast v) • r} :=
    Set.ext (fun _ => mem_latticeVertexDirectionFace_iff γ v h hpos hr)
  rw [heq]
  exact (isCompact_latticePolytope γ).inter_right
    (isClosed_eq (continuous_id.sub continuous_const)
      ((h.continuous.comp (continuous_id.sub continuous_const)).smul continuous_const))

/-- Actual source convexity and literal nonnegative ray parameters give
convexity of the original ray set. -/
theorem convex_latticeVertexDirectionFace (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (r : Fin n → ℝ) : Convex ℝ (latticeVertexDirectionFace γ v r) := by
  rintro x ⟨hx, t, ht, hxt⟩ y ⟨hy, s, hs, hys⟩ a b ha hb hab
  refine ⟨convex_latticePolytope γ hx hy ha hb hab, a * t + b * s,
    add_nonneg (mul_nonneg ha ht) (mul_nonneg hb hs), ?_⟩
  calc
    a • x + b • y - integerCast v =
        a • (x - integerCast v) + b • (y - integerCast v) := by
      conv_lhs => rw [← one_smul ℝ (integerCast v), ← hab]
      module
    _ = (a * t + b * s) • r := by rw [hxt, hys]; module

/-- An ACTUAL extreme direction belongs to the original normalized generator
family, and hence the SAME original ray set contains an original nonvertex
point.  Its positive height is proved before cancellation. -/
theorem exists_latticeVertexDirectionFace_nonvertex (γ : K → Fin n → ℤ)
    (v : Fin n → ℤ) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v → 0 < h (x - integerCast v))
    {r : Fin n → ℝ} (hr : r ∈ (latticeVertexDirectionSection γ v h).extremePoints ℝ) :
    ∃ y ∈ latticeVertexDirectionFace γ v r, y ≠ integerCast v := by
  obtain ⟨y, hy, hyr⟩ := latticeVertexDirectionSection_extremePoints_subset_generators γ v h hr
  have hyP : y ∈ latticePolytope γ := subset_convexHull ℝ _ hy.1
  have hp := hpos y hyP hy.2
  refine ⟨y, ⟨hyP, h (y - integerCast v), hp.le, ?_⟩, hy.2⟩
  change (h (y - integerCast v))⁻¹ • (y - integerCast v) = r at hyr
  rw [← hyr, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]

/-- Actual extremality in the produced section manufactures the genuine
IsExtreme predicate for the SAME original ray set.  Vertex/zero-height terms
are handled before division, with no extreme-ray or edge-generation premise. -/
theorem isExtreme_latticeVertexDirectionFace (γ : K → Fin n → ℤ)
    (v : latticePolytopeVertices γ) (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
      0 < h (x - integerCast v.val))
    {r : Fin n → ℝ} (hr : r ∈ (latticeVertexDirectionSection γ v.val h).extremePoints ℝ) :
    IsExtreme ℝ (latticePolytope γ) (latticeVertexDirectionFace γ v.val r) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hzseg
  by_cases hxv : x = integerCast v.val
  · rw [hxv]
    exact latticeVertexDirectionFace_vertex_mem γ v r
  obtain ⟨a, b, ha, hb, hab, hzabc⟩ := hzseg
  let α := h (x - integerCast v.val)
  let β := h (y - integerCast v.val)
  let T := h (z - integerCast v.val)
  have hα : 0 < α := hpos x hx hxv
  have hβ : 0 ≤ β := latticeVertex_functional_nonneg γ v.val h hpos hy
  have hdecomp : z - integerCast v.val =
      a • (x - integerCast v.val) + b • (y - integerCast v.val) := by
    rw [← hzabc]
    conv_lhs => rw [← one_smul ℝ (integerCast v.val), ← hab]
    module
  have hTsum : T = a * α + b * β := by
    dsimp only [T, α, β]
    rw [hdecomp, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hT : 0 < T := by rw [hTsum]; positivity
  have hzheight := (mem_latticeVertexDirectionFace_iff γ v.val h hpos hr.1).mp hz |>.2
  change z - integerCast v.val = T • r at hzheight
  by_cases hyv : y = integerCast v.val
  · have hax : a • (x - integerCast v.val) = T • r := by
      simpa only [hyv, sub_self, smul_zero, add_zero] using hdecomp.symm.trans hzheight
    refine ⟨hx, T / a, div_nonneg hT.le ha.le, ?_⟩
    calc
      x - integerCast v.val = a⁻¹ • (a • (x - integerCast v.val)) :=
        (inv_smul_smul₀ ha.ne' _).symm
      _ = a⁻¹ • (T • r) := by rw [hax]
      _ = (T / a) • r := by rw [smul_smul, div_eq_mul_inv, mul_comm]
  have hβpos : 0 < β := hpos y hy hyv
  let rx := α⁻¹ • (x - integerCast v.val)
  let ry := β⁻¹ • (y - integerCast v.val)
  have hrx : rx ∈ latticeVertexDirectionSection γ v.val h :=
    latticeVertexDirectionSection_normalized_mem γ v h hpos hx hxv
  have hry : ry ∈ latticeVertexDirectionSection γ v.val h :=
    latticeVertexDirectionSection_normalized_mem γ v h hpos hy hyv
  have hcx : (a * α / T) * α⁻¹ = T⁻¹ * a := by field_simp
  have hcy : (b * β / T) * β⁻¹ = T⁻¹ * b := by field_simp
  have hropen : r ∈ openSegment ℝ rx ry := by
    refine ⟨a * α / T, b * β / T, div_pos (mul_pos ha hα) hT,
      div_pos (mul_pos hb hβpos) hT, ?_, ?_⟩
    · rw [← add_div, ← hTsum, div_self hT.ne']
    · dsimp only [rx, ry]
      rw [smul_smul, smul_smul, hcx, hcy, mul_smul, mul_smul,
        ← smul_add, ← hdecomp, hzheight, smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  have hrxeq : rx = r := hr.2 hrx hry hropen
  refine ⟨hx, α, hα.le, ?_⟩
  calc
    x - integerCast v.val = α • rx := by
      dsimp only [rx]
      rw [smul_smul, mul_inv_cancel₀ hα.ne', one_smul]
    _ = α • r := by rw [hrxeq]

/-- A genuine compact maximum of original height turns the manufactured
nontrivial extreme ray set into an ACTUAL nondegenerate closed segment face
of the SAME source polytope. -/
theorem latticeVertexDirectionFace_isOriginalEdge [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (h : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ x ∈ latticePolytope γ, x ≠ integerCast v.val →
      0 < h (x - integerCast v.val))
    {r : Fin n → ℝ} (hr : r ∈ (latticeVertexDirectionSection γ v.val h).extremePoints ℝ) :
    IsOriginalPolytopeEdgeAt (latticePolytope γ) (integerCast v.val)
      (latticeVertexDirectionFace γ v.val r) := by
  have hvE := latticeVertexDirectionFace_vertex_mem γ v r
  have hcompact := isCompact_latticeVertexDirectionFace γ v.val h hpos hr.1
  obtain ⟨w, hwE, hwmax⟩ := hcompact.exists_isMaxOn ⟨integerCast v.val, hvE⟩
    (h.continuous.comp (continuous_id.sub continuous_const)).continuousOn
  let L := h (w - integerCast v.val)
  obtain ⟨y, hyE, hyne⟩ := exists_latticeVertexDirectionFace_nonvertex γ v.val h hpos hr
  have hL : 0 < L := lt_of_lt_of_le (hpos y hyE.1 hyne) (hwmax hyE)
  have hwne : w ≠ integerCast v.val := by
    intro heq
    simp [L, heq] at hL
  have hwheight := (mem_latticeVertexDirectionFace_iff γ v.val h hpos hr.1).mp hwE |>.2
  change w - integerCast v.val = L • r at hwheight
  have heq : latticeVertexDirectionFace γ v.val r = segment ℝ (integerCast v.val) w := by
    apply Set.Subset.antisymm
    · intro x hxE
      have hxheight := (mem_latticeVertexDirectionFace_iff γ v.val h hpos hr.1).mp hxE |>.2
      have hxnonneg := latticeVertex_functional_nonneg γ v.val h hpos hxE.1
      have hxle : h (x - integerCast v.val) ≤ L := hwmax hxE
      rw [segment_eq_image']
      refine ⟨h (x - integerCast v.val) / L,
        ⟨div_nonneg hxnonneg hL.le, (div_le_one hL).mpr hxle⟩, ?_⟩
      dsimp only
      rw [hwheight, smul_smul, div_mul_cancel₀ _ hL.ne', ← hxheight]
      abel
    · exact (convex_latticeVertexDirectionFace γ v.val r).segment_subset hvE hwE
  exact ⟨w, hwne, heq, isExtreme_latticeVertexDirectionFace γ v h hpos hr⟩

/-- ORIGINAL finite generators and an ACTUAL original vertex alone manufacture
a genuine normalized section whose EVERY actual extreme direction gives an
actual original edge.  No direction/edge/coordinate certificate is input. -/
theorem exists_latticeVertex_original_direction_edges [Fintype K]
    (γ : K → Fin n → ℤ) (v : latticePolytopeVertices γ)
    (hP : latticePolytope γ ≠ {integerCast v.val}) :
    ∃ h : (Fin n → ℝ) →L[ℝ] ℝ,
      (∀ x ∈ latticePolytope γ, x ≠ integerCast v.val → 0 < h (x - integerCast v.val)) ∧
      ∀ r ∈ (latticeVertexDirectionSection γ v.val h).extremePoints ℝ,
        IsOriginalPolytopeEdgeAt (latticePolytope γ) (integerCast v.val)
          (latticeVertexDirectionFace γ v.val r) := by
  obtain ⟨h, hpos⟩ := exists_latticeVertex_positive_functional γ v hP
  exact ⟨h, hpos, fun _ hr => latticeVertexDirectionFace_isOriginalEdge γ v h hpos hr⟩

end SGPT.Toric
