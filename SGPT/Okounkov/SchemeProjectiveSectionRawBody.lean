import SGPT.Okounkov.SchemeProjectiveSectionPolytopes

/-!
# The actual raw generated section body

The native cone-over and actual closure argument need only positive degrees of
nonzero original source points. That fact is manufactured from actual projective
H0, and does not supply a uniform bound or admissibility of the closed cone.
Existing cone/body definitions and real continuous linear coordinates are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.AlmostSemigroup SGPT.AlmostSemigroup.Okounkov
open scoped Topology

private theorem positive_source_normalized_mem_convexHull {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < x.2) {z : (Fin n → ℝ) × ℝ}
    (hz : z ∈ PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))))
    (hheight : 0 < z.2) : z.2⁻¹ • z.1 ∈ convexHull ℝ (normalizedSource S) := by
  let H := convexHull ℝ (normalizedSource S)
  have hle : PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) ≤
      coneOver H (convex_convexHull ℝ _) := by
    apply Submodule.span_le.mpr
    rintro y ⟨x, hx, rfl⟩
    apply (mem_coneOver H (convex_convexHull ℝ _) (latticeCast n x)).mpr
    by_cases hzero : x = 0
    · subst x
      exact Or.inl (by apply Prod.ext <;> simp [latticeCast]; rfl)
    · have hp := hpos x hx hzero
      refine Or.inr ⟨by change (0 : ℝ) < (x.2 : ℝ); exact_mod_cast hp, ?_⟩
      exact subset_convexHull ℝ _ ⟨x, ⟨hx, hp⟩, rfl⟩
  rcases (mem_coneOver H (convex_convexHull ℝ _) z).mp (hle hz) with hzero | hnorm
  · simp [hzero] at hheight
  · exact hnorm.2

private theorem positive_source_body_eq_closure_convexHull {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < x.2) :
    body S = closure (convexHull ℝ (normalizedSource S)) := by
  have hclosed : IsClosed (body S) :=
    (isClosed_closedCone S).preimage (continuous_id.prodMk continuous_const)
  have hnorm : normalizedSource S ⊆ body S := by
    rintro y ⟨z, ⟨hz, hp⟩, rfl⟩
    exact normalizedPoint_mem_heightOne _ (mem_closedCone_of_mem S hz) hp
  apply Set.Subset.antisymm ?_ (closure_minimal (convexHull_min hnorm (convex_body S)) hclosed)
  intro x hx
  let P : Set ((Fin n → ℝ) × ℝ) := {z | 0 < z.2}
  let T : Set ((Fin n → ℝ) × ℝ) :=
    (PointedCone.hull ℝ (latticeCast n '' (S : Set ((Fin n → ℤ) × ℤ))) :
      Set ((Fin n → ℝ) × ℝ)) ∩ P
  have hP : IsOpen P := isOpen_lt continuous_const continuous_snd
  have hxT : (x, (1 : ℝ)) ∈ closure T := by
    apply mem_closure_iff.mpr
    intro o ho hxo
    obtain ⟨z, hzo, hzcone⟩ := mem_closure_iff.mp hx (o ∩ P) (ho.inter hP)
      ⟨hxo, by change (0 : ℝ) < 1; exact zero_lt_one⟩
    exact ⟨z, hzo.1, hzcone, hzo.2⟩
  have hcontinuous : ContinuousAt (fun z : (Fin n → ℝ) × ℝ => z.2⁻¹ • z.1) (x, 1) :=
    (continuous_snd.continuousAt.inv₀ one_ne_zero).smul continuous_fst.continuousAt
  have hmap : MapsTo (fun z : (Fin n → ℝ) × ℝ => z.2⁻¹ • z.1) T
      (convexHull ℝ (normalizedSource S)) := by
    intro z hz
    exact positive_source_normalized_mem_convexHull S hpos hz.1 hz.2
  simpa only [inv_one, one_smul] using hcontinuous.continuousWithinAt.mem_closure hxT hmap

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionRawBodyTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionRawBodyCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The EXISTING actual generated height-one body, in genuine Euclidean coordinates. -/
def schemeProjectiveSectionRawBody {L : X.Modules} (a : LineBundleAtlas L) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  SGPT.AlmostSemigroup.BodyGeometry.euclideanBody
    (schemeProjectiveSectionSemigroup f n E Y hY a)

/-- Source H0-derived positive degrees genuinely produce the native normalized-hull identity. -/
theorem schemeProjectiveSectionBody_eq_closure_convexHull {L : X.Modules}
    (a : LineBundleAtlas L) :
    body (schemeProjectiveSectionSemigroup f n E Y hY a) =
      closure (convexHull ℝ (normalizedSource (schemeProjectiveSectionSemigroup f n E Y hY a))) :=
  positive_source_body_eq_closure_convexHull _
    (schemeProjectiveSectionSemigroup_positive_degree f n E Y hY a)

/-- The actual raw body is closed by the native closed cone and genuine coordinate homeomorphism. -/
theorem schemeProjectiveSectionRawBody_isClosed {L : X.Modules}
    (a : LineBundleAtlas L) : IsClosed (schemeProjectiveSectionRawBody f n E Y hY a) := by
  apply (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isClosed_image.mpr
  exact (isClosed_closedCone _).preimage (continuous_id.prodMk continuous_const)

/-- The actual raw body is convex, with no nonemptiness or global bound premise. -/
theorem schemeProjectiveSectionRawBody_convex {L : X.Modules}
    (a : LineBundleAtlas L) : Convex ℝ (schemeProjectiveSectionRawBody f n E Y hY a) :=
  (convex_body _).linear_image (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap

/-- Actual continuous linear coordinates transport the whole closure/convex-hull identity. -/
theorem schemeProjectiveSectionRawBody_eq_closure_convexHull {L : X.Modules}
    (a : LineBundleAtlas L) :
    schemeProjectiveSectionRawBody f n E Y hY a =
      closure (convexHull ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        normalizedSource (schemeProjectiveSectionSemigroup f n E Y hY a))) := by
  unfold schemeProjectiveSectionRawBody SGPT.AlmostSemigroup.BodyGeometry.euclideanBody
  rw [schemeProjectiveSectionBody_eq_closure_convexHull f n E Y hY a]
  calc
    _ = closure ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
        convexHull ℝ (normalizedSource (schemeProjectiveSectionSemigroup f n E Y hY a))) :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.image_closure _
    _ = _ := congrArg closure
      ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap.image_convexHull _)

/-- The SAME whole source semigroup gives the SAME actual closed generated cone for any atlas. -/
theorem schemeProjectiveSectionClosedCone_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) :
    closedCone (schemeProjectiveSectionSemigroup f n E Y hY a) =
      closedCone (schemeProjectiveSectionSemigroup f n E Y hY b) := by
  rw [schemeProjectiveSectionSemigroup_atlas_independent f n E Y hY a b]

/-- Genuine original frame independence preserves the whole actual raw body. -/
theorem schemeProjectiveSectionRawBody_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) :
    schemeProjectiveSectionRawBody f n E Y hY a = schemeProjectiveSectionRawBody f n E Y hY b := by
  unfold schemeProjectiveSectionRawBody
  rw [schemeProjectiveSectionSemigroup_atlas_independent f n E Y hY a b]

end SGPT.Okounkov
