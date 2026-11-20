import SGPT.NAPotential.ProjectiveGraphSegre
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Actual regular graph points satisfy the full global relations

Common regular representatives come from the actual generic stalk. Injectivity
of the original section-to-function-field map turns each actual rational
polynomial relation into a zero section, and native complex evaluation reads
the same original coefficients and functions.

Blueprint: `projective-graph-membership.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphMembership

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos SGPT.Okounkov
open ProjectiveGraphSegre ProjectiveGraphAnalyticZero
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

variable {X : Scheme.{0}} [IsIntegral X] {s : ℕ}

/-- Actual rational functions have actual common regular representatives inside a prescribed generic open. -/
theorem exists_common_regular_open (U₀ : X.Opens) (hU₀ : genericPoint X ∈ U₀)
    (b : Fin s → X.functionField) :
    ∃ V ≤ U₀, ∃ hV : genericPoint X ∈ V, ∃ r : Fin s → Γ(X, V),
      ∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i := by
  classical
  choose U hUU₀ hU r hr using fun i => X.presheaf.exists_le_germ_eq (b i) hU₀
  let V : X.Opens := U₀ ⊓ ⨅ i, U i
  have hηi : genericPoint X ∈ (⨅ i, U i : X.Opens) := by
    change genericPoint X ∈ ((⨅ i, U i : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hU
  have hV : genericPoint X ∈ V := ⟨hU₀, hηi⟩
  have hVi (i : Fin s) : V ≤ U i := inf_le_right.trans (iInf_le _ i)
  refine ⟨V, inf_le_left, hV, fun i => X.presheaf.map (homOfLE (hVi i)).op (r i), ?_⟩
  intro i
  rw [X.presheaf.germ_res_apply]
  exact hr i

variable {f : X ⟶ Spec (.of ℂ)} {m : ℕ}
  [SmoothOfRelativeDimension (m + 1) f] [IsProper f]

local instance membershipTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance membershipCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance membershipManifold : IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-- The actual original structural constants restricted to an actual open. -/
def sectionConstants (V : X.Opens) : ℂ →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (schemeGlobalConstants f)

omit [SmoothOfRelativeDimension (m + 1) f] [IsProper f] in
/-- Original generic evaluation retains the original structure-induced complex coefficients. -/
theorem functionField_sectionConstants (V : X.Opens) [Nonempty V] :
    letI := schemeFunctionFieldAlgebra f
    (X.germToFunctionField V).hom.comp (sectionConstants (f := f) V) = algebraMap ℂ X.functionField := by
  let := schemeFunctionFieldAlgebra f
  ext c
  change X.presheaf.germ V (genericPoint X) _
    (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (schemeGlobalConstants f c)) =
      X.presheaf.germ ⊤ (genericPoint X) trivial (schemeGlobalConstants f c)
  exact X.presheaf.germ_res_apply _ _ _ _

/-- The actual original section-to-complex-point ring homomorphism. -/
def sectionPointEval (V : X.Opens) (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) :
    Γ(X, V) →+* ℂ :=
  (pointEval f (m + 1) x).comp (X.presheaf.germ V (schemeComplexPointImage f x) hx).hom

omit [IsIntegral X] in
theorem sectionPointEval_constants (V : X.Opens) (x : SchemeComplexPoint f)
    (hx : schemeComplexPointImage f x ∈ V) (c : ℂ) :
    sectionPointEval (m := m) V x hx (sectionConstants (f := f) V c) = c := by
  change pointEval f (m + 1) x
    (X.presheaf.germ V (schemeComplexPointImage f x) hx
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (schemeGlobalConstants f c))) = c
  rw [X.presheaf.germ_res_apply]
  exact pointEval_germ_const f (m + 1) x c

omit [IsIntegral X] in
theorem sectionPointEval_apply (E : ClosedProjectiveEmbedding f) (V : X.Opens)
    (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) (a : Γ(X, V)) :
    sectionPointEval (m := m) V x hx a = schemeOpenRegularFunction f (m + 1) E V a x :=
  (schemeOpenRegularFunction_apply f (m + 1) E V a x hx).symm

/-- An actual rational polynomial identity vanishes at every original point where its sections are regular. -/
theorem regular_polynomial_vanish {I : Type*} (V : X.Opens) (hV : genericPoint X ∈ V)
    (w : I → Γ(X, V)) (p : MvPolynomial I ℂ)
    (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) :
    letI := schemeFunctionFieldAlgebra f
    aeval (fun i => X.presheaf.germ V (genericPoint X) hV (w i)) p = 0 →
      MvPolynomial.eval (fun i => sectionPointEval (m := m) V x hx (w i)) p = 0 := by
  let := schemeFunctionFieldAlgebra f
  intro hp
  let : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  let φ : Γ(X, V) →+* X.functionField := (X.germToFunctionField V).hom
  let q := eval₂Hom (sectionConstants (f := f) V) w p
  have hφq : φ q = 0 := by
    calc
      φ q = eval₂Hom (φ.comp (sectionConstants (f := f) V)) (fun i => φ (w i)) p :=
        map_eval₂Hom _ _ _ _
      _ = aeval (fun i => X.presheaf.germ V (genericPoint X) hV (w i)) p := by
        rw [show φ.comp (sectionConstants (f := f) V) = algebraMap ℂ X.functionField from
          functionField_sectionConstants (f := f) V]
        rfl
      _ = 0 := hp
  have hq : q = 0 := (X.germToFunctionField_injective V) (hφq.trans (map_zero φ).symm)
  have hcoef : (sectionPointEval (m := m) V x hx).comp (sectionConstants (f := f) V) =
      RingHom.id ℂ := by
    ext c
    exact sectionPointEval_constants V x hx c
  have heq : sectionPointEval (m := m) V x hx q =
      MvPolynomial.eval (fun i => sectionPointEval (m := m) V x hx (w i)) p := by
    dsimp only [q]
    rw [map_eval₂Hom, hcoef]
    rfl
  rw [← heq, hq, map_zero]

variable (E : ClosedProjectiveEmbedding f)

/-- The actual regular Segre lift on an original open inside the chosen generic coordinate chart. -/
def regularSegreCoordinates (V : X.Opens) (hVU : V ≤ coordOpen E (genericCoordinateIndex E))
    (r : Fin s → Γ(X, V)) : Fin (segreDim E.ambientDimension s + 1) → Γ(X, V) :=
  fun k => X.presheaf.map (homOfLE hVU).op
    (ratio E (genericCoordinateIndex E) (segreIdx E.ambientDimension s k).1) *
      (Fin.cons (1 : Γ(X, V)) r : Fin (s + 1) → Γ(X, V))
        (segreIdx E.ambientDimension s k).2

omit [SmoothOfRelativeDimension (m + 1) f] [IsProper f] in
/-- Its original generic germ is exactly the previously constructed actual rational Segre vector. -/
theorem generic_regularSegreCoordinates (V : X.Opens) (hV : genericPoint X ∈ V)
    (hVU : V ≤ coordOpen E (genericCoordinateIndex E))
    (b : Fin s → X.functionField) (r : Fin s → Γ(X, V))
    (hr : ∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i) :
    (fun k => X.presheaf.germ V (genericPoint X) hV (regularSegreCoordinates E V hVU r k)) =
      rationalSegreCoordinates E b := by
  have hC (j : Fin (E.ambientDimension + 1)) :
      X.presheaf.germ V (genericPoint X) hV
        (X.presheaf.map (homOfLE hVU).op (ratio E (genericCoordinateIndex E) j)) =
          genericCoordinates E j := by
    change X.presheaf.germ V (genericPoint X) hV
      (X.presheaf.map (homOfLE hVU).op (ratio E (genericCoordinateIndex E) j)) =
        X.presheaf.germ (coordOpen E (genericCoordinateIndex E)) (genericPoint X) _
          (ratio E (genericCoordinateIndex E) j)
    exact X.presheaf.germ_res_apply _ _ _ _
  have hR (j : Fin (s + 1)) : X.presheaf.germ V (genericPoint X) hV
      ((Fin.cons (1 : Γ(X, V)) r : Fin (s + 1) → Γ(X, V)) j) =
        (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField) j := by
    refine Fin.cases (by simp) (fun i => ?_) j
    simpa using hr i
  funext k
  change X.presheaf.germ V (genericPoint X) hV
    (X.presheaf.map (homOfLE hVU).op
      (ratio E (genericCoordinateIndex E) (segreIdx E.ambientDimension s k).1) *
        (Fin.cons (1 : Γ(X, V)) r : Fin (s + 1) → Γ(X, V))
          (segreIdx E.ambientDimension s k).2) = _
  rw [map_mul, hC, hR]
  rfl

/-- Actual original point evaluation of the regular Segre lift retains the same projective-coordinate values. -/
theorem point_regularSegreCoordinates (V : X.Opens)
    (hVU : V ≤ coordOpen E (genericCoordinateIndex E)) (r : Fin s → Γ(X, V))
    (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) :
    (fun k => sectionPointEval (m := m) V x hx (regularSegreCoordinates E V hVU r k)) =
      segreVec (homCoords f E (m + 1) (genericCoordinateIndex E) x) (graphLift (m := m) E r x) := by
  have hC (j : Fin (E.ambientDimension + 1)) :
      sectionPointEval (m := m) V x hx
        (X.presheaf.map (homOfLE hVU).op (ratio E (genericCoordinateIndex E) j)) =
          homCoords f E (m + 1) (genericCoordinateIndex E) x j := by
    rw [sectionPointEval_apply E]
    exact schemeOpenRegularFunction_restrict f (m + 1) E V
      (coordOpen E (genericCoordinateIndex E)) hVU _ hx
  have hR (j : Fin (s + 1)) : sectionPointEval (m := m) V x hx
      ((Fin.cons (1 : Γ(X, V)) r : Fin (s + 1) → Γ(X, V)) j) = graphLift (m := m) E r x j := by
    refine Fin.cases (by simp [graphLift]) (fun i => ?_) j
    simpa [graphLift] using sectionPointEval_apply E V x hx (r i)
  funext k
  change sectionPointEval (m := m) V x hx
    (X.presheaf.map (homOfLE hVU).op
      (ratio E (genericCoordinateIndex E) (segreIdx E.ambientDimension s k).1) *
        (Fin.cons (1 : Γ(X, V)) r : Fin (s + 1) → Γ(X, V))
          (segreIdx E.ambientDimension s k).2) = _
  rw [map_mul, hC, hR]
  rfl

/-- **Actual graph membership** in the constructed global full-relation analytic set. -/
theorem graphMap_mem_globalRelationGraph (V : X.Opens) (hV : genericPoint X ∈ V)
    (hVU : V ≤ coordOpen E (genericCoordinateIndex E))
    (b : Fin s → X.functionField) (r : Fin s → Γ(X, V))
    (hr : ∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i)
    (x : SchemeComplexPoint f) (hx : schemeComplexPointImage f x ∈ V) :
    graphMap (m := m) E r x ∈ globalRelationGraph (m := m) E b := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨F, hF, hset⟩ := exists_finite_globalRelationEquations (m := m) E b
  apply (hset (graphMap (m := m) E r x)).mpr
  intro p hp
  obtain ⟨n, hn, hzero⟩ := hF p hp
  have hfield : aeval (fun k => X.presheaf.germ V (genericPoint X) hV
      (regularSegreCoordinates E V hVU r k)) p = 0 := by
    rw [generic_regularSegreCoordinates E V hV hVU b r hr]
    exact hzero
  have heval := regular_polynomial_vanish (m := m) V hV
    (regularSegreCoordinates E V hVU r) p x hx hfield
  rw [point_regularSegreCoordinates E V hVU r x hx] at heval
  have hc0 := homCoords_ne_zero f E (m + 1) (genericCoordinateIndex E) (hVU hx)
  have hr0 := graphLift_ne_zero (m := m) E r x
  have hpoint : segreAmbientMap E (graphMap (m := m) E r x) =
      mk (segreVec (homCoords f E (m + 1) (genericCoordinateIndex E) x)
        (graphLift (m := m) E r x)) (segreVec_ne_zero hc0 hr0) := by
    change segreMap (projectivePoint f E (m + 1) x)
      (mk (graphLift (m := m) E r x) hr0) = _
    rw [projectivePoint_eq f E (m + 1) (genericCoordinateIndex E) (hVU hx)]
    exact ProjectiveGraphSegre.segreMap_mk hc0 hr0
  exact (eval_rep_eq_zero_iff hn _ _ (segreVec_ne_zero hc0 hr0) hpoint).mpr heval

/-- Common actual regular representatives and their actual global graph membership are produced together. -/
theorem exists_regularGraph_membership (b : Fin s → X.functionField) :
    ∃ (V : X.Opens) (hV : genericPoint X ∈ V)
      (_hVU : V ≤ coordOpen E (genericCoordinateIndex E)) (r : Fin s → Γ(X, V)),
      (∀ i, X.presheaf.germ V (genericPoint X) hV (r i) = b i) ∧
      ∀ x ∉ graphBase f V, graphMap (m := m) E r x ∈ globalRelationGraph (m := m) E b := by
  obtain ⟨V, hVU, hV, r, hr⟩ := exists_common_regular_open
    (coordOpen E (genericCoordinateIndex E)) (genericCoordinateIndex_mem E) b
  refine ⟨V, hV, hVU, r, hr, ?_⟩
  intro x hx
  have hxV : schemeComplexPointImage f x ∈ V := by
    simpa only [mem_graphBase, not_not] using hx
  exact graphMap_mem_globalRelationGraph (m := m) E V hV hVU b r hr x hxV

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphMembership
