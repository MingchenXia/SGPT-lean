import SGPT.Okounkov.SchemeProjectiveSectionDegree
import SGPT.AlmostSemigroup.BodyGeometry

/-!
# Actual degree polytopes of original projective sections

The existing normalized-slice and Euclidean convex-hull definitions are used
literally. Source projective H0 makes the actual samples finite; normalization
in positive degree preserves their exact original section dimension. Compactness
is degreewise and makes no assertion about a bound for the generated raw body.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.Okounkov

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology

variable {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)

local instance sectionPolytopeTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance sectionPolytopeCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n

variable (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- The EXISTING normalized slice of the actual original section semigroup. -/
def schemeProjectiveSectionNormalizedPoints {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    Set (Fin n → ℝ) :=
  SGPT.AlmostSemigroup.BodyGeometry.normalizedSlice
    (schemeProjectiveSectionSemigroup f n E Y hY a) m

/-- Literal nonzero original sections supply all and only the actual normalized samples. -/
theorem schemeProjectiveSectionNormalizedPoints_mem {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (v : Fin n → ℝ) :
    v ∈ schemeProjectiveSectionNormalizedPoints f n E Y hY a m ↔
      ∃ (s : bundlePowerGlobalSections L m) (hs : s ≠ 0),
        v = (m : ℝ)⁻¹ • (fun i =>
          (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℝ)) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨s, hs, hu⟩ := (schemeProjectiveSectionSemigroup_mem_slice f n E Y hY a m u).mp hu
    refine ⟨s, hs, ?_⟩
    rw [hu]
    ext i
    simp [SGPT.AlmostSemigroup.Counting.integerCast]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(fun i => (schemeFubiniStudySectionVector f n E Y hY a m s hs i : ℤ)),
      (schemeProjectiveSectionSemigroup_mem_slice f n E Y hY a m _).mpr ⟨s, hs, rfl⟩, ?_⟩
    ext i
    simp [SGPT.AlmostSemigroup.Counting.integerCast]

/-- Every actual degree has finitely many normalized samples, including empty degrees. -/
theorem schemeProjectiveSectionNormalizedPoints_finite {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    (schemeProjectiveSectionNormalizedPoints f n E Y hY a m).Finite :=
  (schemeProjectiveSectionSemigroup_slice_finite f n E Y hY a m).image _

/-- Positive-degree normalization counts actual samples, exactly the original H0 dimension. -/
theorem schemeProjectiveSectionNormalizedPoints_card_eq_finrank {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (hm : 0 < m) :
    letI := schemeGlobalSectionModule f (bundleTensorPower L m)
    Nat.card (schemeProjectiveSectionNormalizedPoints f n E Y hY a m) =
      Module.finrank ℂ (bundlePowerGlobalSections L m) := by
  let := schemeGlobalSectionModule f (bundleTensorPower L m)
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hinj : Function.Injective
      (fun u : Fin n → ℤ => (m : ℝ)⁻¹ • SGPT.AlmostSemigroup.Counting.integerCast u) := by
    intro u v huv
    apply SGPT.AlmostSemigroup.Counting.integerCast_injective
    simpa [smul_smul, hmr] using congrArg (fun w : Fin n → ℝ => (m : ℝ) • w) huv
  exact (Nat.card_congr (Equiv.Set.image _ _ hinj)).symm.trans
    (schemeProjectiveSectionSemigroup_slice_card_eq_finrank f n E Y hY a m)

/-- The EXISTING Euclidean degree body of the actual original section semigroup. -/
def schemeProjectiveSectionDegreeBody {L : X.Modules} (a : LineBundleAtlas L) (m : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  SGPT.AlmostSemigroup.BodyGeometry.euclideanDegreeBody
    (schemeProjectiveSectionSemigroup f n E Y hY a) m

/-- Actual source finiteness manufactures compactness of every degree polytope. -/
theorem schemeProjectiveSectionDegreeBody_isCompact {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    IsCompact (schemeProjectiveSectionDegreeBody f n E Y hY a m) := by
  apply Set.Finite.isCompact_convexHull ℝ
  exact (schemeProjectiveSectionNormalizedPoints_finite f n E Y hY a m).image _

/-- These are the actual convex hulls of the original normalized section samples. -/
theorem schemeProjectiveSectionDegreeBody_convex {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) :
    Convex ℝ (schemeProjectiveSectionDegreeBody f n E Y hY a m) :=
  convex_convexHull ℝ _

/-- Genuine original stalk-unit frame independence preserves the whole degree body. -/
theorem schemeProjectiveSectionDegreeBody_atlas_independent {L : X.Modules}
    (a b : LineBundleAtlas L) (m : ℕ) :
    schemeProjectiveSectionDegreeBody f n E Y hY a m =
      schemeProjectiveSectionDegreeBody f n E Y hY b m := by
  unfold schemeProjectiveSectionDegreeBody
  rw [schemeProjectiveSectionSemigroup_atlas_independent f n E Y hY a b]

/-- Every positive-degree polytope lies in the actual raw generated height-one body. -/
theorem schemeProjectiveSectionDegreeBody_subset_rawBody {L : X.Modules}
    (a : LineBundleAtlas L) (m : ℕ) (hm : 0 < m) :
    schemeProjectiveSectionDegreeBody f n E Y hY a m ⊆
      SGPT.AlmostSemigroup.BodyGeometry.euclideanBody
        (schemeProjectiveSectionSemigroup f n E Y hY a) :=
  SGPT.AlmostSemigroup.BodyGeometry.euclideanDegreeBody_subset_body _ hm

end SGPT.Okounkov
