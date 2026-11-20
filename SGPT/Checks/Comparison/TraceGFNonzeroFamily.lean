import SGPT.Checks.Comparison.GFRationalHull

/-! The ACTUAL original section maximum formula needs only one nonzero term.
Source `thm:comp_traceop`, `eq:varphiAncordF`; blueprint `trace-gf-nonzero-family.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.BJSections
open SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.BJ.GfIm.RationalHull
open scoped ENNReal Classical

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]

local instance traceNonzeroProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceNonzeroPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance traceNonzeroPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance traceNonzeroPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable (H : SchemeLineBundleMetric f n E L)

omit [IsProjective f] [IsIntegral X] in
/-- The entire ACTUAL finite physical maximum is unchanged after removing
exactly the actual zero sections; its common zero loci remain intact. -/
theorem sectionMaximum_erase_zero (a : LineBundleAtlas L) (N : ℕ)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∃ j, t j ≠ 0) :
    letI : Nonempty {j : J // t j ≠ 0} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
    sectionsMaxLog f n E a N t H =
      sectionsMaxLog f n E a N (fun j : {j : J // t j ≠ 0} => t j) H := by
  let : Nonempty {j : J // t j ≠ 0} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  funext p
  change RationalHull.finiteMaximum (fun j => H.sectionLogNormSq a N (t j)) p =
    RationalHull.finiteMaximum (fun j : {j : J // t j ≠ 0} => H.sectionLogNormSq a N (t j)) p
  rw [finiteMaximum_eq_iSup, finiteMaximum_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hj : t j = 0
    · rw [hj, H.sectionLogNormSq_zero]
      exact bot_le
    · exact le_iSup (fun j : {j : J // t j ≠ 0} => H.sectionLogNormSq a N (t j) p) ⟨j, hj⟩
  · apply iSup_le
    intro j
    exact le_iSup (fun j => H.sectionLogNormSq a N (t j) p) j.val

/-- The value of the WHOLE ACTUAL original section ideal is unchanged by
removing its zero sections, at EVERY original semi-valuation. -/
theorem idealVal_sectionFamily_erase_zero (a : LineBundleAtlas L) (N : ℕ)
    {J : Type} [Fintype J] [Nonempty J] (t : J → bundlePowerGlobalSections L N)
    (ht : ∃ j, t j ≠ 0) (v : BerkovichPoint f) :
    v.idealVal (sectionsIdeal a N (fun j : {j : J // t j ≠ 0} => t j)) =
      v.idealVal (sectionsIdeal a N t) := by
  let : Nonempty {j : J // t j ≠ 0} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  rw [idealVal_sectionsIdeal, idealVal_sectionsIdeal]
  apply le_antisymm
  · apply le_iInf
    intro j
    by_cases hj : t j = 0
    · rw [hj, powerSectionValue_zero]
      exact le_top
    · exact iInf_le (fun j : {j : J // t j ≠ 0} =>
        toENNReal (powerSectionValue a N (t j) v)) ⟨j, hj⟩
  · apply le_iInf
    intro j
    exact iInf_le (fun j => toENNReal (powerSectionValue a N (t j) v)) j.val

/-- The ORIGINAL normalized section-maximum formula on ALL X^An requires
only one actual nonzero section. This includes sections that become zero
under true restriction, all common zero loci, and dimension zero. -/
theorem potentialAn_sectionMaximum_of_exists_nonzero (a : LineBundleAtlas L)
    (N K : ℕ) (hK : 0 < K) {J : Type} [Fintype J] [Nonempty J]
    (t : J → bundlePowerGlobalSections L N) (ht : ∃ j, t j ≠ 0) (v : BerkovichPoint f) :
    potentialAn n E (fun p => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n E a N t H p) v =
      -((v.idealVal (sectionsIdeal a N t) / K : ℝ≥0∞) : EReal) := by
  let : Nonempty {j : J // t j ≠ 0} := ⟨⟨ht.choose, ht.choose_spec⟩⟩
  rw [sectionMaximum_erase_zero f n E H a N t ht,
    potentialAn_sectionsMaxLog_all_narrow f n E H a N
      (fun j : {j : J // t j ≠ 0} => t j) (fun j => j.property) hK,
    idealVal_sectionFamily_erase_zero f a N t ht v]

end SGPT.NAPotential.TraceComparison
