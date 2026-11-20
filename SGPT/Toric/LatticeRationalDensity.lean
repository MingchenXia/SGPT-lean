import SGPT.Toric.Toric5IOrder
import SGPT.Okounkov.PartialBodyDSConvex

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory Metric
open scoped Topology

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Original normalized lattice points, with a literal positive common
denominator and actual integral numerator. -/
def normalizedLatticePoints (C : Set E) : Set E :=
  {p | p ∈ C ∧ ∃ (q : ℕ) (_ : 0 < q) (m : Fin n → ℤ), p = (q : ℝ)⁻¹ • latticeVector m}

/-- Interior points are approximated by actual rounded original lattice
vectors, with no rational-density or common-denominator certificate. -/
theorem interior_subset_closure_normalizedLatticePoints (C : Set E) :
    interior C ⊆ closure (normalizedLatticePoints C) := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hδ : 0 < min r ε := lt_min hr hε
  obtain ⟨q, hq⟩ := exists_nat_gt (((n : ℝ) + 1) / min r ε)
  have hqR : (0 : ℝ) < q := (div_pos (by positivity) hδ).trans hq
  have hqN : 0 < q := by exact_mod_cast hqR
  let m : Fin n → ℤ := fun i => round ((q : ℝ) * x i)
  let p : E := (q : ℝ)⁻¹ • latticeVector m
  have hdist : dist p x ≤ ((n : ℝ) + 1) / q := by
    have hsub : p - x = (q : ℝ)⁻¹ • (latticeVector m - (q : ℝ) • x) := by
      dsimp only [p]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hqR.ne', one_smul]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hqR)]
    calc (q : ℝ)⁻¹ * ‖latticeVector m - (q : ℝ) • x‖ ≤
        (q : ℝ)⁻¹ * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (norm_latticeVector_round_sub_le x q) (inv_nonneg.mpr hqR.le)
      _ = ((n : ℝ) + 1) / q := by ring
  have hlt : ((n : ℝ) + 1) / q < min r ε := by
    apply (div_lt_iff₀ hqR).mpr
    have h := (div_lt_iff₀ hδ).mp hq
    nlinarith
  have hpC : p ∈ C := interior_subset (hball ((mem_ball).mpr
    (hdist.trans_lt (hlt.trans_le (min_le_left _ _)))))
  exact ⟨p, ⟨hpC, q, hqN, m, rfl⟩,
    by rw [dist_comm]; exact hdist.trans_lt (hlt.trans_le (min_le_right _ _))⟩

/-- Every full-dimensional closed convex body is the closure of its actual
normalized lattice points. Degenerate bodies are deliberately not asserted. -/
theorem closure_normalizedLatticePoints_eq {C : Set E} (hC : Convex ℝ C)
    (hc : IsClosed C) (hi : (interior C).Nonempty) :
    closure (normalizedLatticePoints C) = C := by
  apply Subset.antisymm
  · exact closure_minimal (fun _ hp => hp.1) hc
  · have hcl := hC.closure_interior_eq_closure_of_nonempty_interior hi
    rw [hc.closure_eq] at hcl
    calc C = closure (interior C) := hcl.symm
      _ ⊆ closure (normalizedLatticePoints C) :=
        closure_minimal (interior_subset_closure_normalizedLatticePoints C) isClosed_closure

/-- Inclusion and equality of finite positive Haar volumes determine the
actual compact convex body. The volume-gap ball is genuinely produced. -/
theorem eq_of_subset_of_equal_haar_volume {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] {A B : Set V}
    (hA : Convex ℝ A) (hcA : IsClosed A) (hB : Convex ℝ B)
    (hbB : Bornology.IsBounded B) (hAB : A ⊆ B)
    (hpos : 0 < μ A) (hfin : μ A ≠ ⊤) (hvol : μ A = μ B) : A = B := by
  apply Subset.antisymm hAB
  intro x hx
  by_contra hxA
  obtain ⟨a, ha⟩ := SGPT.Okounkov.PartialBody.interior_nonempty_of_convex_of_measure_pos μ hA hpos
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  obtain ⟨R, hR⟩ := hbB.subset_closedBall a
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hcA.isOpen_compl x hxA
  have hfar : ∀ y ∈ A, ε ≤ dist x y := by
    intro y hy
    by_contra! hno
    have hyball : y ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hno
    exact (hεball hyball) hy
  obtain ⟨c, hc, _, hgap⟩ :=
    SGPT.Okounkov.PartialBody.exists_measure_add_le_of_far μ a hr R hε
  have hμ := hgap B A hB ((hball.trans interior_subset).trans hAB) hR hAB x hx hfar
  rw [← hvol] at hμ
  exact (not_le.mpr (ENNReal.lt_add_right hfin hc.ne')) hμ

end SGPT.Toric
