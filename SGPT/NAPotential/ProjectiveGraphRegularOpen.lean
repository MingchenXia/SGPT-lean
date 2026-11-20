import SGPT.NAPotential.ProjectiveGraphRegularFractions

/-!
# A genuine original regular open with nonvanishing denominator values

Actual section identities are proved by injective original generic evaluation;
the denominator open is constructed from genuine original basic opens.
Blueprint: `projective-graph-regular-fractions.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularOpen

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.NAPotential.FSPos SGPT.Okounkov
open ProjectiveGraphSegre ProjectiveGraphMembership ProjectiveGraphRegularFractions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {m s : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance regularOpenTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance regularOpenCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance regularOpenManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- An actual original rational numerator/denominator identity gives its actual value at every regular point. -/
theorem regular_fraction_value (V : X.Opens) (hV : genericPoint X ∈ V)
    (hVU : V ≤ coordOpen E (genericCoordinateIndex E))
    (b : X.functionField) (r : Γ(X, V))
    (hr : X.presheaf.germ V (genericPoint X) hV r = b)
    (d a : Γ(X, coordOpen E (genericCoordinateIndex E)))
    (hrel : X.presheaf.germ _ (genericPoint X) (genericCoordinateIndex_mem E) d * b =
      X.presheaf.germ _ (genericPoint X) (genericCoordinateIndex_mem E) a)
    (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) :
    schemeOpenRegularFunction f (m + 1) E (coordOpen E (genericCoordinateIndex E)) a x =
      schemeOpenRegularFunction f (m + 1) E (coordOpen E (genericCoordinateIndex E)) d x *
        schemeOpenRegularFunction f (m + 1) E V r x := by
  let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  have hs : X.presheaf.map (homOfLE hVU).op d * r = X.presheaf.map (homOfLE hVU).op a := by
    apply X.germToFunctionField_injective V
    change X.presheaf.germ V (genericPoint X) hV _ =
      X.presheaf.germ V (genericPoint X) hV _
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, hr]
    exact hrel
  have hd : sectionPointEval (m := m) V x hx (X.presheaf.map (homOfLE hVU).op d) =
      schemeOpenRegularFunction f (m + 1) E (coordOpen E (genericCoordinateIndex E)) d x := by
    rw [sectionPointEval_apply E]
    exact schemeOpenRegularFunction_restrict f (m + 1) E V _ hVU d hx
  have ha : sectionPointEval (m := m) V x hx (X.presheaf.map (homOfLE hVU).op a) =
      schemeOpenRegularFunction f (m + 1) E (coordOpen E (genericCoordinateIndex E)) a x := by
    rw [sectionPointEval_apply E]
    exact schemeOpenRegularFunction_restrict f (m + 1) E V _ hVU a hx
  calc
    _ = sectionPointEval (m := m) V x hx (X.presheaf.map (homOfLE hVU).op a) := ha.symm
    _ = sectionPointEval (m := m) V x hx (X.presheaf.map (homOfLE hVU).op d * r) :=
      congrArg (sectionPointEval (m := m) V x hx) hs.symm
    _ = _ := by rw [map_mul, hd, sectionPointEval_apply E]

/-- Actual polynomial fractions, actual regular representatives, and their nonvanishing pointwise values
are produced on one genuine original nonempty open. -/
theorem exists_regular_fraction_open (b : Fin s → X.functionField) :
    letI := schemeFunctionFieldAlgebra f
    ∃ (V : X.Opens) (hV : genericPoint X ∈ V)
      (_hVU : V ≤ coordOpen E (genericCoordinateIndex E)) (r : Fin s → Γ(X, V))
      (d a : Fin s → MvPolynomial (Fin E.ambientDimension) ℂ),
      (∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i) ∧
      (∀ i, aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) (d i) * b i =
        aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) (a i)) ∧
      ∀ (x : SchemeComplexPoint f), schemeComplexPointImage f x ∈ V → ∀ i,
        MvPolynomial.eval (fun k => homCoords f E (m + 1) (genericCoordinateIndex E) x
          ((genericCoordinateIndex E).succAbove k)) (d i) ≠ 0 ∧
        MvPolynomial.eval (fun k => homCoords f E (m + 1) (genericCoordinateIndex E) x
          ((genericCoordinateIndex E).succAbove k)) (a i) =
          MvPolynomial.eval (fun k => homCoords f E (m + 1) (genericCoordinateIndex E) x
            ((genericCoordinateIndex E).succAbove k)) (d i) *
              schemeOpenRegularFunction f (m + 1) E V (r i) x := by
  let := schemeFunctionFieldAlgebra f
  classical
  obtain ⟨d, a, h⟩ := exists_affine_fraction_polynomials E b
  let U := coordOpen E (genericCoordinateIndex E)
  let U₁ : X.Opens := U ⊓ ⨅ i, X.basicOpen (affinePresentation f E (genericCoordinateIndex E) (d i))
  have hηd (i : Fin s) : genericPoint X ∈ X.basicOpen
      (affinePresentation f E (genericCoordinateIndex E) (d i)) := by
    rw [Scheme.mem_basicOpen _ _ _ (genericCoordinateIndex_mem E),
      generic_affinePresentation E, isUnit_iff_ne_zero]
    exact (h i).1
  have hηU₁ : genericPoint X ∈ U₁ := by
    refine ⟨genericCoordinateIndex_mem E, ?_⟩
    change genericPoint X ∈ ((⨅ i, X.basicOpen
      (affinePresentation f E (genericCoordinateIndex E) (d i)) : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hηd
  obtain ⟨V, hVU₁, hV, r, hr⟩ := exists_common_regular_open U₁ hηU₁ b
  have hVU : V ≤ U := hVU₁.trans inf_le_left
  have hVd (i : Fin s) : V ≤ X.basicOpen (affinePresentation f E (genericCoordinateIndex E) (d i)) :=
    hVU₁.trans (inf_le_right.trans (iInf_le _ i))
  refine ⟨V, hV, hVU, r, d, a, hr, fun i => (h i).2, ?_⟩
  intro x hx i
  have hval (p : MvPolynomial (Fin E.ambientDimension) ℂ) :
      schemeOpenRegularFunction f (m + 1) E U (affinePresentation f E (genericCoordinateIndex E) p) x =
        MvPolynomial.eval (fun k => homCoords f E (m + 1) (genericCoordinateIndex E) x
          ((genericCoordinateIndex E).succAbove k)) p :=
    schemeOpenRegularFunction_affinePresentation f E (m + 1) _ p x (hVU hx)
  refine ⟨?_, ?_⟩
  · rw [← hval]
    exact (schemeOpenRegularFunction_ne_zero_iff f E (m + 1) U _ x (hVU hx)).mpr (hVd i hx)
  · have hrel : X.presheaf.germ U (genericPoint X) (genericCoordinateIndex_mem E)
        (affinePresentation f E (genericCoordinateIndex E) (d i)) * b i =
      X.presheaf.germ U (genericPoint X) (genericCoordinateIndex_mem E)
        (affinePresentation f E (genericCoordinateIndex E) (a i)) := by
      rw [generic_affinePresentation E, generic_affinePresentation E]
      exact (h i).2
    have hpoint := regular_fraction_value (m := m) E V hV hVU (b i) (r i) (hr i)
      (affinePresentation f E (genericCoordinateIndex E) (d i))
      (affinePresentation f E (genericCoordinateIndex E) (a i)) hrel x hx
    rw [hval, hval] at hpoint
    exact hpoint

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphRegularOpen
