import SGPT.Toric.MonomialVertexCoordinates

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Convex
open scoped BigOperators Topology
attribute [local instance] monomialProjectiveTopology

variable {I J : Type*} [Fintype J]

/-- Literal homogeneous coordinate norm bounds, stated for EVERY original
nonzero representative. No geometric or correspondence certificate is stored. -/
def projectiveCoordinateNormBound (ν : J → I) (i : I) (R : ℝ) :
    Set (Projectivization ℂ (I → ℂ)) :=
  {p | ∀ (w : I → ℂ) (hw : w ≠ 0), Projectivization.mk ℂ w hw = p →
    ‖w i‖ ^ 2 ≤ R * ∑ j, ‖w (ν j)‖ ^ 2}

/-- Actual original scalar fibers give the precise representative inequality. -/
theorem mem_projectiveCoordinateNormBound_mk_iff (ν : J → I) (i : I) (R : ℝ)
    (w : I → ℂ) (hw : w ≠ 0) :
    Projectivization.mk ℂ w hw ∈ projectiveCoordinateNormBound ν i R ↔
      ‖w i‖ ^ 2 ≤ R * ∑ j, ‖w (ν j)‖ ^ 2 := by
  constructor
  · intro h
    exact h w hw rfl
  · intro h w' hw' heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp heq
    rw [← hc]
    change ‖(c : ℂ) * w i‖ ^ 2 ≤ R * ∑ j, ‖(c : ℂ) * w (ν j)‖ ^ 2
    simp_rw [norm_mul, mul_pow]
    rw [← Finset.mul_sum]
    calc
      ‖(c : ℂ)‖ ^ 2 * ‖w i‖ ^ 2 ≤
          ‖(c : ℂ)‖ ^ 2 * (R * ∑ j, ‖w (ν j)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by ring

/-- Actual coinduced quotient topology and continuous coordinate inequalities
make the homogeneous bound a genuinely closed projective subset. -/
theorem isClosed_projectiveCoordinateNormBound (ν : J → I) (i : I) (R : ℝ) :
    IsClosed (projectiveCoordinateNormBound ν i R) := by
  have hq : Topology.IsCoinducing (fun w : {w : I → ℂ // w ≠ 0} =>
      Projectivization.mk ℂ w.val w.property) := ⟨rfl⟩
  apply hq.isClosed_preimage.mp
  have hpre : (fun w : {w : I → ℂ // w ≠ 0} => Projectivization.mk ℂ w.val w.property) ⁻¹'
      projectiveCoordinateNormBound ν i R =
        {w : {w : I → ℂ // w ≠ 0} | ‖w.val i‖ ^ 2 ≤ R * ∑ j, ‖w.val (ν j)‖ ^ 2} := by
    ext w
    exact mem_projectiveCoordinateNormBound_mk_iff ν i R w.val w.property
  rw [hpre]
  exact isClosed_le (((continuous_apply i).comp continuous_subtype_val).norm.pow 2)
    (continuous_const.mul (continuous_finsetSum _
      (fun j _ => ((continuous_apply (ν j)).comp continuous_subtype_val).norm.pow 2)))

variable {n d : ℕ} [Nonempty J]

/-- The EXISTING exact Laurent quotient criterion manufactures actual finite
homogeneous coordinate bounds from ORIGINAL convex-hull membership. -/
theorem exists_projectiveCoordinateNormBound_orbit
    (β : Fin (d + 1) → Fin n → ℤ) (ν : J → Fin (d + 1)) (i : Fin (d + 1))
    (hi : (fun k => (β i k : ℝ)) ∈
      convexHull ℝ (Set.range (fun j k => (β (ν j) k : ℝ)))) :
    ∃ R : ℝ, Set.range (monomialProjectiveOrbit β) ⊆ projectiveCoordinateNormBound ν i R := by
  obtain ⟨R, hR⟩ := (bddAbove_laurentRatio_iff (fun j => β (ν j)) (β i)).mpr hi
  refine ⟨R, ?_⟩
  rintro p ⟨a, rfl⟩
  apply (mem_projectiveCoordinateNormBound_mk_iff ν i R _ _).mpr
  have h := (div_le_iff₀ (laurentDenominator_pos (fun j => β (ν j)) (latticeTorusPoint a))).mp
    (hR ⟨latticeTorusPoint a, rfl⟩)
  simpa only [laurentRatio, laurentDenominator, monomialOrbitVector,
    latticeCharacter_eq_laurentMonomial] using h

/-- Genuine original quotient-closedness extends the PRODUCED homogeneous
bounds to the SAME actual monomial orbit closure. -/
theorem exists_projectiveCoordinateNormBound_closure
    (β : Fin (d + 1) → Fin n → ℤ) (ν : J → Fin (d + 1)) (i : Fin (d + 1))
    (hi : (fun k => (β i k : ℝ)) ∈
      convexHull ℝ (Set.range (fun j k => (β (ν j) k : ℝ)))) :
    ∃ R : ℝ, monomialProjectiveOrbitClosure β ⊆ projectiveCoordinateNormBound ν i R := by
  obtain ⟨R, hR⟩ := exists_projectiveCoordinateNormBound_orbit β ν i hi
  exact ⟨R, closure_minimal hR (isClosed_projectiveCoordinateNormBound ν i R)⟩

/-- ORIGINAL convex-hull membership manufactures a global actual vertex-open
cover of the SAME monomial orbit closure, rather than assuming a cover field. -/
theorem monomialProjectiveOrbitClosure_vertex_opens_cover
    (β : Fin (d + 1) → Fin n → ℤ) (ν : J → Fin (d + 1))
    (hhull : ∀ i, (fun k => (β i k : ℝ)) ∈
      convexHull ℝ (Set.range (fun j k => (β (ν j) k : ℝ))))
    (p : Projectivization ℂ (Fin (d + 1) → ℂ)) (hp : p ∈ monomialProjectiveOrbitClosure β) :
    ∃ j, p ∈ Set.range (monomialProjectiveRatioPoint d (ν j)) := by
  by_contra hnone
  let w := p.rep
  have hzero (j : J) : w (ν j) = 0 := by
    by_contra hnz
    apply hnone
    refine ⟨j, ?_⟩
    simpa only [w, Projectivization.mk_rep] using
      (monomialProjectiveRatioPoint_mem_mk_iff d (ν j) w p.rep_nonzero).mpr hnz
  apply p.rep_nonzero
  funext i
  obtain ⟨R, hR⟩ := exists_projectiveCoordinateNormBound_closure β ν i (hhull i)
  have hi := hR hp w p.rep_nonzero p.mk_rep
  have hnorm : ‖w i‖ ^ 2 ≤ 0 := by simpa only [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero] using hi
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hnorm (sq_nonneg _)))

/-- The produced selected-coordinate opens cover the SAME original closure as
an actual union of genuine existing native ambient opens, including rank zero. -/
theorem monomialProjectiveOrbitClosure_subset_vertex_opens
    (β : Fin (d + 1) → Fin n → ℤ) (ν : J → Fin (d + 1))
    (hhull : ∀ i, (fun k => (β i k : ℝ)) ∈
      convexHull ℝ (Set.range (fun j k => (β (ν j) k : ℝ)))) :
    monomialProjectiveOrbitClosure β ⊆
      ⋃ j, Set.range (monomialProjectiveRatioPoint d (ν j)) := by
  intro p hp
  exact Set.mem_iUnion.mpr (monomialProjectiveOrbitClosure_vertex_opens_cover β ν hhull p hp)

end SGPT.Toric
