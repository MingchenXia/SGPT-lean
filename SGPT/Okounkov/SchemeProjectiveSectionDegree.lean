import SGPT.Okounkov.SchemeProjectiveSectionSemigroup
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Positive degrees of the actual section semigroup

Actual projective H0 gives a finite degree-zero slice. Genuine additive closure
and torsion freeness of the literal value lattice force this slice to be {0}.
The resulting positivity concerns original semigroup points, not its closed cone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

private theorem finite_zero_slice_value_eq_zero {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hfin : (SGPT.AlmostSemigroup.slice (S : Set ((Fin n → ℤ) × ℤ)) 0).Finite)
    (u : Fin n → ℤ) (hu : u ∈ SGPT.AlmostSemigroup.slice (S : Set ((Fin n → ℤ) × ℤ)) 0) :
    u = 0 := by
  let := hfin.to_subtype
  have hm (k : ℕ) : (k + 1) • u ∈
      SGPT.AlmostSemigroup.slice (S : Set ((Fin n → ℤ) × ℤ)) 0 := by
    have hp (k : ℕ) : (k + 1) • (u, (0 : ℤ)) ∈ S := by
      induction k with
      | zero => simpa using hu
      | succ k ih =>
          rw [succ_nsmul]
          exact S.add_mem ih hu
    simpa using hp k
  obtain ⟨r, t, hrt, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => (⟨(k + 1) • u, hm k⟩ :
      SGPT.AlmostSemigroup.slice (S : Set ((Fin n → ℤ) × ℤ)) 0))
  ext i
  by_contra hne
  have hz : ((r + 1 : ℕ) : ℤ) * u i = ((t + 1 : ℕ) : ℤ) * u i := by
    simpa [nsmul_eq_mul] using congrArg (fun v : Fin n → ℤ => v i)
      (congrArg Subtype.val heq)
  have hnat : r + 1 = t + 1 := by exact_mod_cast mul_right_cancel₀ hne hz
  exact hrt (by omega)

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionDegreeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionDegreeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- Actual finite H0 and genuine additive closure make the literal zero slice a singleton. -/
theorem schemeProjectiveSectionSemigroup_slice_zero {L : X.Modules} (a : LineBundleAtlas L) :
    SGPT.AlmostSemigroup.slice
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) 0 = {0} := by
  ext u
  constructor
  · intro hu
    exact finite_zero_slice_value_eq_zero _
      (schemeProjectiveSectionSemigroup_slice_finite f n E Y hY a 0) u hu
  · intro hu
    have hzero : u = 0 := hu
    subst u
    exact schemeProjectiveSectionSemigroup_zero_mem f n E Y hY a

/-- Every nonzero ACTUAL section-semigroup point has strictly positive degree. -/
theorem schemeProjectiveSectionSemigroup_positive_degree {L : X.Modules}
    (a : LineBundleAtlas L) (z : (Fin n → ℤ) × ℤ)
    (hz : z ∈ schemeProjectiveSectionSemigroup f n E Y hY a) (hne : z ≠ 0) :
    0 < z.2 := by
  have hn := (schemeProjectiveSectionSemigroup_nonneg f n E Y hY a z hz).2
  by_contra hnot
  have hd : z.2 = 0 := le_antisymm (le_of_not_gt hnot) hn
  have hu : z.1 ∈ SGPT.AlmostSemigroup.slice
      (schemeProjectiveSectionSemigroup f n E Y hY a : Set ((Fin n → ℤ) × ℤ)) 0 := by
    change (z.1, 0) ∈ schemeProjectiveSectionSemigroup f n E Y hY a
    simpa [← hd] using hz
  rw [schemeProjectiveSectionSemigroup_slice_zero f n E Y hY a] at hu
  exact hne (Prod.ext hu hd)

include n E Y hY in
/-- The exact original structural degree-zero global section module has dimension one. -/
theorem schemeProjectiveSectionSemigroup_degree_zero_finrank {L : X.Modules}
    (a : LineBundleAtlas L) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L 0)
    Module.finrank ℂ (bundlePowerGlobalSections L 0) = 1 := by
  let := schemeGlobalSectionModule f (bundleTensorPower L 0)
  rw [← schemeProjectiveSectionSemigroup_slice_card_eq_finrank f n E Y hY a 0]
  simp only [Int.natCast_zero]
  rw [schemeProjectiveSectionSemigroup_slice_zero f n E Y hY a]
  exact Nat.card_unique

end SGPT.Okounkov
