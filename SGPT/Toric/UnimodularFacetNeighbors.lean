import SGPT.Toric.IntegralRealCoordinates
import SGPT.Toric.LatticePolytopeSource
import SGPT.Toric.FacetEntropy

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators Topology

variable {n : ℕ} {F : Type*}

/-- The literal original integer facets, specialized through the EXISTING
original affine-facet definition. -/
def integralFacetValue (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (ρ : F) (x : Fin n → ℝ) : ℝ :=
  facetValue (fun ρ => integralRealFunctional (u ρ)) (fun ρ => (a ρ : ℝ)) ρ x

/-- The original halfspace intersection, retaining the existing facet object. -/
def integralFacetRegion (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ) :
    Set (Fin n → ℝ) :=
  facetRegion (fun ρ => integralRealFunctional (u ρ)) (fun ρ => (a ρ : ℝ))

/-- Actual real axis direction manufactured from the original integral normal
coordinate equivalence, not a supplied chart or desired neighbor. -/
def unimodularVertexDirection (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (j : Fin n) : Fin n → ℝ :=
  (integralRealCoordinates c).symm (Pi.basisFun ℝ (Fin n) j)

/-- Selected original zero facets give exactly the original vertex differences
in the manufactured real coordinate system. -/
theorem integralFacetValue_selected (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (v : Fin n → ℤ) (σ : Fin n → F) (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    (x : Fin n → ℝ) (j : Fin n) :
    integralRealCoordinates c (x - integerCast v) j = integralFacetValue u a (σ j) x := by
  rw [integralRealCoordinates_coord, ← hσ j, map_sub]
  have hz := hzero j
  dsimp [integralFacetValue, facetValue] at hz ⊢
  linarith

/-- Genuine original facet inequalities manufacture every real nonnegative
vertex coordinate, rather than assuming exponent positivity. -/
theorem integralFacetRegion_coordinate_nonneg (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (a : F → ℤ) (v : Fin n → ℤ) (σ : Fin n → F)
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    {x : Fin n → ℝ} (hx : x ∈ integralFacetRegion u a) (j : Fin n) :
    0 ≤ integralRealCoordinates c (x - integerCast v) j := by
  rw [integralFacetValue_selected u a v σ c hσ hzero]
  exact hx (σ j)

/-- The produced real nonnegative coordinates retain the SAME integral
coefficients of the original source lattice point. -/
theorem integralFacetRegion_integer_coordinate_nonneg (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ)
    (a : F → ℤ) (v : Fin n → ℤ) (σ : Fin n → F)
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    {m : Fin n → ℤ} (hm : integerCast m ∈ integralFacetRegion u a) (j : Fin n) :
    0 ≤ c (m - v) j := by
  have h := integralFacetRegion_coordinate_nonneg u a v σ c hσ hzero hm j
  have hcast : integerCast m - integerCast v = integerCast (m - v) := by
    ext i
    simp [integerCast]
  rw [hcast, integralRealCoordinates_integerCast] at h
  change 0 ≤ (c (m - v) j : ℝ) at h
  exact_mod_cast h

/-- Strict original inactive facet slacks manufacture a genuine positive short
axis segment inside the SAME original halfspace region. -/
theorem exists_positive_unimodular_axis_mem [Fintype F]
    (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ) (v : Fin n → ℤ)
    (σ : Fin n → F) (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    (hinactive : ∀ ρ, ρ ∉ Set.range σ → 0 < integralFacetValue u a ρ (integerCast v))
    (j : Fin n) : ∃ ε : ℝ, 0 < ε ∧
      integerCast v + ε • unimodularVertexDirection c j ∈ integralFacetRegion u a := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ ρ, ρ ∉ Set.range σ →
      0 < integralFacetValue u a ρ (integerCast v + t • unimodularVertexDirection c j) := by
    apply Filter.eventually_all.mpr
    intro ρ
    by_cases hρ : ρ ∈ Set.range σ
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hρ))
    · have hcont : Continuous (fun t : ℝ =>
          integralFacetValue u a ρ (integerCast v + t • unimodularVertexDirection c j)) := by
        exact ((integralRealFunctional (u ρ)).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))).add continuous_const
      have hpos : 0 < integralFacetValue u a ρ
          (integerCast v + (0 : ℝ) • unimodularVertexDirection c j) := by
        simpa using hinactive ρ hρ
      exact (hcont.continuousAt.eventually (lt_mem_nhds hpos)).mono (fun _ ht _ => ht)
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp hev
  have hε : 0 < r / 2 := half_pos hr
  have hdist : dist (r / 2) (0 : ℝ) < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    exact half_lt_self hr
  refine ⟨r / 2, hε, ?_⟩
  intro ρ
  change 0 ≤ integralFacetValue u a ρ
    (integerCast v + (r / 2) • unimodularVertexDirection c j)
  by_cases hρ : ρ ∈ Set.range σ
  · obtain ⟨k, rfl⟩ := hρ
    rw [← integralFacetValue_selected u a v σ c hσ hzero]
    have hvec : integralRealCoordinates c
        (integerCast v + (r / 2) • unimodularVertexDirection c j - integerCast v) =
          (r / 2) • Pi.basisFun ℝ (Fin n) j := by
      rw [add_sub_cancel_left, map_smul]
      simp [unimodularVertexDirection]
    rw [hvec]
    simp only [Pi.smul_apply, Pi.basisFun_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> positivity
  · exact (hsmall hdist ρ hρ).le

/-- The EXISTING finite sum of literal coordinate functionals exposes the
original nonnegative coordinate axis face. -/
private def axisFaceFunctional (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (j : Fin n) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  -∑ k ∈ Finset.univ.erase j, integralRealFunctional ((LinearMap.proj k).comp c.toLinearMap)

private theorem axisFaceFunctional_sub (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (j : Fin n) (x y : Fin n → ℝ) :
    axisFaceFunctional c j x - axisFaceFunctional c j y =
      -∑ k ∈ Finset.univ.erase j, integralRealCoordinates c (x - y) k := by
  rw [← map_sub]
  simp only [axisFaceFunctional, neg_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact (integralRealCoordinates_coord c k (x - y)).symm

/-- Genuine compact exposed-face/extreme-point machinery manufactures an
ACTUAL original integer vertex on the positive coordinate axis. The hypotheses
here are supplied internally by the original facet producer below. -/
private theorem exists_integer_axis_vertex {K : Type*} [Fintype K]
    (γ : K → Fin n → ℤ) (v : Fin n → ℤ)
    (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ)) (j : Fin n)
    (hv : integerCast v ∈ latticePolytope γ)
    (hnonneg : ∀ x ∈ latticePolytope γ, ∀ k, 0 ≤ integralRealCoordinates c (x - integerCast v) k)
    (ε : ℝ) (hε : 0 < ε)
    (hshort : integerCast v + ε • unimodularVertexDirection c j ∈ latticePolytope γ) :
    ∃ w : Fin n → ℤ, integerCast w ∈ (latticePolytope γ).extremePoints ℝ ∧
      0 < c (w - v) j ∧ ∀ k, k ≠ j → c (w - v) k = 0 := by
  let E := (axisFaceFunctional c j).toExposed (latticePolytope γ)
  have hexposed : IsExposed ℝ (latticePolytope γ) E :=
    ContinuousLinearMap.toExposed.isExposed
  have hvE : integerCast v ∈ E := by
    refine ⟨hv, fun x hx => ?_⟩
    have hsum := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ.erase j) => hnonneg x hx k)
    have heq := axisFaceFunctional_sub c j x (integerCast v)
    linarith
  have hqshort : integralRealCoordinates c
      (integerCast v + ε • unimodularVertexDirection c j - integerCast v) =
        ε • Pi.basisFun ℝ (Fin n) j := by
    rw [add_sub_cancel_left, map_smul]
    simp [unimodularVertexDirection]
  have hshortE : integerCast v + ε • unimodularVertexDirection c j ∈ E := by
    refine ⟨hshort, fun x hx => ?_⟩
    have hs := axisFaceFunctional_sub c j
      (integerCast v + ε • unimodularVertexDirection c j) (integerCast v)
    rw [hqshort] at hs
    have hsumzero : (∑ k ∈ Finset.univ.erase j,
        (ε • Pi.basisFun ℝ (Fin n) j) k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
      simp [Pi.basisFun_apply, Ne.symm hk]
    rw [hsumzero, neg_zero, sub_eq_zero] at hs
    rw [hs]
    exact hvE.2 x hx
  have hEcompact := hexposed.isCompact (isCompact_latticePolytope γ)
  let f := integralRealFunctional ((LinearMap.proj j).comp c.toLinearMap)
  obtain ⟨z, hz, hzmax⟩ := hEcompact.exists_isMaxOn ⟨integerCast v, hvE⟩ f.continuous.continuousOn
  let A := f.toExposed E
  have hAexposed : IsExposed ℝ E A := ContinuousLinearMap.toExposed.isExposed
  have hAnonempty : A.Nonempty := ⟨z, hz, hzmax⟩
  obtain ⟨w, hw⟩ := (hAexposed.isCompact hEcompact).extremePoints_nonempty hAnonempty
  have hwE : w ∈ E := hw.1.1
  have hwP : w ∈ (latticePolytope γ).extremePoints ℝ :=
    hexposed.isExtreme.extremePoints_subset_extremePoints
      (hAexposed.isExtreme.extremePoints_subset_extremePoints hw)
  obtain ⟨i, hi⟩ := latticePolytope_extremePoints_subset_generators γ hwP
  have hcast : integerCast (γ i) = w := hi
  have hH : axisFaceFunctional c j w = axisFaceFunctional c j (integerCast v) :=
    le_antisymm (hvE.2 w hwE.1) (hwE.2 (integerCast v) hv)
  have hsumzero : (∑ k ∈ Finset.univ.erase j,
      integralRealCoordinates c (w - integerCast v) k) = 0 := by
    have h := axisFaceFunctional_sub c j w (integerCast v)
    rw [hH, sub_self] at h
    linarith
  have hqzero : ∀ k, k ≠ j → integralRealCoordinates c (w - integerCast v) k = 0 := by
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ.erase j) => hnonneg w hwE.1 k)).mp hsumzero k
        (by simp [hk])
  have hmax := hw.1.2 (integerCast v + ε • unimodularVertexDirection c j) hshortE
  have hpos : 0 < integralRealCoordinates c (w - integerCast v) j := by
    have h : integralRealCoordinates c
        (integerCast v + ε • unimodularVertexDirection c j - integerCast v) j = ε := by
      rw [hqshort]
      simp [Pi.basisFun_apply]
    simp only [f, ← integralRealCoordinates_coord] at hmax
    rw [map_sub, Pi.sub_apply] at h ⊢
    linarith
  have hcastdiff : w - integerCast v = integerCast (γ i - v) := by
    rw [← hcast]
    ext k
    simp [integerCast]
  rw [hcastdiff, integralRealCoordinates_integerCast] at hpos hqzero
  refine ⟨γ i, ?_, ?_, ?_⟩
  · rwa [hcast]
  · change 0 < (c (γ i - v) j : ℝ) at hpos
    exact_mod_cast hpos
  · intro k hk
    have h := hqzero k hk
    change (c (γ i - v) k : ℝ) = 0 at h
    exact_mod_cast h

/-- ONLY original finite lattice generators, literal integral facet presentation
and raw active unimodular normal data manufacture the genuine first lattice
neighbor. Neither vertex membership, exponent signs nor a neighbor is supplied. -/
theorem latticePolytope_unimodular_neighbor_mem {K : Type*} [Fintype K] [Fintype F]
    (γ : K → Fin n → ℤ) (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (v : Fin n → ℤ) (σ : Fin n → F) (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hP : latticePolytope γ = integralFacetRegion u a)
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    (hinactive : ∀ ρ, ρ ∉ Set.range σ → 0 < integralFacetValue u a ρ (integerCast v))
    (j : Fin n) :
    v + c.symm (Pi.basisFun ℤ (Fin n) j) ∈ latticePolytopeIntegerPoints γ := by
  have hv : integerCast v ∈ latticePolytope γ := by
    rw [hP]
    intro ρ
    change 0 ≤ integralFacetValue u a ρ (integerCast v)
    by_cases hρ : ρ ∈ Set.range σ
    · obtain ⟨k, rfl⟩ := hρ
      rw [hzero]
    · exact (hinactive ρ hρ).le
  have hnonneg : ∀ x ∈ latticePolytope γ, ∀ k,
      0 ≤ integralRealCoordinates c (x - integerCast v) k := by
    intro x hx k
    exact integralFacetRegion_coordinate_nonneg u a v σ c hσ hzero (hP ▸ hx) k
  obtain ⟨ε, hε, hshort⟩ := exists_positive_unimodular_axis_mem u a v σ c hσ hzero hinactive j
  rw [← hP] at hshort
  obtain ⟨w, hw, hL, hother⟩ := exists_integer_axis_vertex γ v c j hv hnonneg ε hε hshort
  let L : ℤ := c (w - v) j
  let b : Fin n → ℤ := c.symm (Pi.basisFun ℤ (Fin n) j)
  have hcoord : c (w - v) = L • Pi.basisFun ℤ (Fin n) j := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [L, Pi.basisFun_apply]
    · simp [Pi.basisFun_apply, Ne.symm hk, hother k hk]
  have hdiff : w - v = L • b := by
    apply c.injective
    rw [map_smul]
    change c (w - v) = L • c (c.symm (Pi.basisFun ℤ (Fin n) j))
    rw [LinearEquiv.apply_symm_apply]
    exact hcoord
  have hcastdiff : integerCast w - integerCast v = (L : ℝ) • integerCast b := by
    ext k
    have h := congrFun hdiff k
    change w k - v k = L * b k at h
    change (w k : ℝ) - (v k : ℝ) = (L : ℝ) * (b k : ℝ)
    exact_mod_cast h
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast hL
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (Int.add_one_le_iff.mpr hL)
  have htzero : 0 ≤ (L : ℝ)⁻¹ := (inv_pos.mpr hLpos).le
  have htone : (L : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hLpos).mpr hLone
  have hcombo := (convex_latticePolytope γ) hv hw.1 (sub_nonneg.mpr htone) htzero
    (sub_add_cancel (1 : ℝ) (L : ℝ)⁻¹)
  have heq : (1 - (L : ℝ)⁻¹) • integerCast v + (L : ℝ)⁻¹ • integerCast w =
      integerCast (v + b) := by
    calc
      _ = integerCast v + (L : ℝ)⁻¹ • (integerCast w - integerCast v) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      _ = integerCast v + (L : ℝ)⁻¹ • ((L : ℝ) • integerCast b) := by rw [hcastdiff]
      _ = integerCast v + integerCast b := by
        rw [smul_smul, inv_mul_cancel₀ hLpos.ne', one_smul]
      _ = integerCast (v + b) := by
        ext k
        simp [integerCast]
  rw [heq] at hcombo
  exact hcombo

/-- The literal original halfspace presentation internally manufactures every
nonnegative integral exponent for the full source lattice-point family. -/
theorem latticePolytope_unimodular_coordinate_nonneg {K : Type*}
    (γ : K → Fin n → ℤ) (u : F → (Fin n → ℤ) →ₗ[ℤ] ℤ) (a : F → ℤ)
    (v : Fin n → ℤ) (σ : Fin n → F) (c : (Fin n → ℤ) ≃ₗ[ℤ] (Fin n → ℤ))
    (hP : latticePolytope γ = integralFacetRegion u a)
    (hσ : ∀ j, u (σ j) = (LinearMap.proj j).comp c.toLinearMap)
    (hzero : ∀ j, integralFacetValue u a (σ j) (integerCast v) = 0)
    (m : latticePolytopeIntegerPoints γ) (j : Fin n) : 0 ≤ c (m.val - v) j :=
  integralFacetRegion_integer_coordinate_nonneg u a v σ c hσ hzero (hP ▸ m.property) j

end SGPT.Toric
