import SGPT.Checks.Comparison.BJPair3DivOriginalGenericSupport
import SGPT.Foundations.Envelope.AlgGeom.OriginalProjectiveFamilyNativeChartValues
import SGPT.Foundations.Envelope.Global.FiniteFibres

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/NativeOriginalFamilyValuation.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-! # Actual whole original/native generic valuations for a projective family

The full original chart evaluation API gives genuine generic support and
all K(X) values under its SAME Segre/diagonal point homeomorphism. No
support matching, field identification or divisorial certificate is input.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open SGPT.Support.Alterations
open scoped Classical NNReal

namespace SGPT.NAPotential.BJ.Pair3Div
open SGPT.Foundations.Envelope SGPT.Foundations.Envelope.Berkovich
open ProjectiveFixedNativeAnalyticGluing ProjectiveChartFunctionFieldGeneration

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  {r : ℕ} {d : Fin (r+1) → ℕ}
  (q : ∀ c, X ⟶ projectiveSpace k (d c)) (p : X ⟶ Spec (.of k))
  (hp : ∀ c, q c ≫ projectiveSpaceStructure k (d c) = p)
  [IsClosedImmersion (q 0)]

private abbrev f := FiniteSegreOriginalProjectiveMaps.morphism d q p hp
private abbrev b := f q p hp ≫ projectiveSpaceStructure k (FiniteSegreOriginalProjectiveMaps.dimension d)
private abbrev hb := fun c => (hp c).trans (FiniteSegreOriginalProjectiveMaps.morphism_structure d q p hp).symm
private abbrev pivot := FiniteProjectiveNativeFieldModels.pivot q
private abbrev hU := fun c => (FiniteProjectiveNativeFieldModels.chartSite (q c)).property
private abbrev P := letI := (b q p hp).stalkAlgebra (genericPoint X)
  FiniteProjectiveNativeFieldModels.model q (b q p hp) (hb q p hp)
private abbrev e := OriginalProjectiveFamilyNativeChartValues.homeomorph q p hp

private theorem actual_coords_nonzero (j : ∀ c, Fin (d c+1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c))) :
    letI := (b q p hp).stalkAlgebra (genericPoint X)
    ∀ c, (P q p hp).coord c (j c) ≠ 0 := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  intro c
  let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot q c)) := hU q c
  let := hj c
  exact ProjectiveChartGenericTransitions.coordinate_pivot_ne_zero (q c) (pivot q c) (j c)

private theorem actual_chart_mem
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (j : ∀ c, Fin (d c+1))
    (hj : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)))
    (hv : letI := (b q p hp).stalkAlgebra (genericPoint X)
      ∀ c, (e q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) ≠ 0) :
    y.1.point ∈ f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j) := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp (pivot q) (hU q)
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hj
  apply (nativeToModel_mem_chartDomain_iff (f q p hp)
    (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y _).mp
  apply (fullFieldModel (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))).mem_chartDomain_iff.mpr
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  change (nativeModelHomeomorph (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q)) y).1.val
    ((fullFieldModel (f q p hp) (FiniteSegreOriginalProjectiveMaps.index d (pivot q))).coordElem
      ⟨0,FiniteSegreOriginalProjectiveMaps.index d j⟩) ≠ 0
  rw [OriginalProjectiveFamilyNativeChartValues.coordinate_val q p hp y j]
  exact Finset.prod_ne_zero_iff.mpr (fun c _ => hv c)

/-- Native generic support forces actual generic support of the SAME
original point, through the full original affine-chart evaluation formula. -/
theorem family_original_generic_support
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (hg : letI := (b q p hp).stalkAlgebra (genericPoint X)
      (P q p hp).HasGenericSupport (e q p hp y).1) :
    y.1.point = genericPoint X := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  obtain ⟨j,hj,hv⟩ := (P q p hp).exists_chartIndex (e q p hp y)
  have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := by
    intro c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot q c)) := hU q c
    exact (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty
      (q c) (pivot q c) (j c)).mp (hj c)
  have hv0 : ∀ c, (e q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) ≠ 0 :=
    fun c => by rw [hv c]; exact one_ne_zero
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let U := f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)
  let := (b q p hp).sectionsAlgebra U
  apply original_generic_support_of_eval_ne_zero y.1 U
    ((coordinateOpen_isAffineOpen _).preimage (f q p hp))
    (actual_chart_mem q p hp y j hJ hv0)
  intro s hs
  rw [← OriginalProjectiveFamilyNativeChartValues.chart_val q p hp y j hJ hv0 s]
  exact (P q p hp).chartMap_val_ne_zero (actual_coords_nonzero q p hp j hJ) hv0 hg
    ((map_ne_zero_iff _ (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ).injective).mpr hs)

/-- The WHOLE original K(X) valuation is the actual native fieldVal,
including EVERY rational fraction, at the SAME original/native point. -/
theorem family_original_genericValuation_eq
    (y : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) (b q p hp))
    (hg : letI := (b q p hp).stalkAlgebra (genericPoint X)
      (P q p hp).HasGenericSupport (e q p hp y).1) :
    letI := (b q p hp).stalkAlgebra (genericPoint X)
    SchemeValuedPoint.genericValuation y.1 (family_original_generic_support q p hp y hg) =
      (P q p hp).fieldVal (e q p hp y) hg := by
  let := (b q p hp).stalkAlgebra (genericPoint X)
  obtain ⟨j,hj,hv⟩ := (P q p hp).exists_chartIndex (e q p hp y)
  have hJ : ∀ c, Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (j c)) := by
    intro c
    let : Nonempty (q c ⁻¹ᵁ coordinateOpen (R := k) (pivot q c)) := hU q c
    exact (ProjectiveNativeCoordinateChartSupport.coordinate_ne_zero_iff_nonempty
      (q c) (pivot q c) (j c)).mp (hj c)
  have hv0 : ∀ c, (e q p hp y).1.val ((P q p hp).coordElem ⟨c,j c⟩) ≠ 0 :=
    fun c => by rw [hv c]; exact one_ne_zero
  let := FiniteSegreOriginalProjectiveMaps.morphism_isClosedImmersion d q p hp
  let := FiniteSegreNativeCoordinateAlgebra.chart_nonempty d q p hp j hJ
  let U := f q p hp ⁻¹ᵁ coordinateOpen (R := k) (FiniteSegreOriginalProjectiveMaps.index d j)
  let := (b q p hp).sectionsAlgebra U
  let ν := SchemeValuedPoint.genericValuation y.1 (family_original_generic_support q p hp y hg)
  have hchart (x : (P q p hp).chartAlg j) : ν x = (P q p hp).fieldVal (e q p hp y) hg x := by
    obtain ⟨s, rfl⟩ := (OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv q p hp j hJ).surjective x
    rw [OriginalProjectiveFamilyChartAlgebras.wholeChartSectionsEquiv_apply q p hp j hJ s]
    rw [SchemeValuedPoint.genericValuation_eval y.1 _ U (actual_chart_mem q p hp y j hJ hv0) s]
    rw [← OriginalProjectiveFamilyNativeChartValues.chart_val q p hp y j hJ hv0 s]
    exact ((P q p hp).fieldVal_coe_chartAlg (actual_coords_nonzero q p hp j hJ)
      (e q p hp y) hg hv0 _).symm
  let := (P q p hp).isFractionRing_chartAlg (actual_coords_nonzero q p hp j hJ)
  apply Valuation.ext
  intro a
  obtain ⟨s,t,ht,rfl⟩ := IsFractionRing.div_surjective ((P q p hp).chartAlg j) a
  rw [map_div₀, map_div₀]
  change ν (s : X.functionField) / ν (t : X.functionField) = _
  rw [hchart, hchart]
  rfl

end SGPT.NAPotential.BJ.Pair3Div
