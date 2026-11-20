import SGPT.Toric.BigToricNewtonBody
import SGPT.Toric.PolytopeToricEnergyClasses

/-!
# The ample divisor `D_P` and its Guillemin metric

Source `chapter_toric_big.tex`, section `sec:toricsetup2` and the proof of
`lma:exist_Ftheta` (Step 1, Guillemin's metrics), and `ex:P2` for the general principle:
for the Delzant polytope `P` defining `X`, the torus-invariant divisor
`D_P = ∑_ρ a_ρ D_ρ`, `a_ρ = -min_{m ∈ P} ⟨m, u_ρ⟩`, has Cartier data `m_{σ_v} = v`, its
line bundle carries the Guillemin metric with curvature the Kähler form `ω` of
`PolytopeToricVariety`, and `P_{D_P} = P`.

This shows that `BigToricMetric` is inhabited for every `X` and that the theory of the
big chapter specializes to the ample chapter (`PolytopeToric*`): the profile, `PSH_tor`
and Newton bodies are those of the ample case.

## Main results

* `vertex_pairing_rayGenerator_nonneg`: `⟨w - v, u_j(v)⟩ ≥ 0` for all vertices `v, w`
  (the cone of `P` at `v` is spanned by the edges);
* `polytopeToricAmpleDivisor`, `toricCartierDatum_ampleDivisor`: `D_P` and `m_{σ_v} = v`;
* `guilleminBigToricMetric`: the Guillemin metric on `O(D_P)` with `θ = ω`;
* `guilleminBigToricMetric_potential`: `F_θ = F_0`;
* `toricDivisorPolytope_ampleDivisor`: `P_{D_P} = P`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)

theorem intPairing_sub (a b u : Fin n → ℤ) :
    intPairing (a - b) u = intPairing a u - intPairing b u := by
  simp only [intPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- `-t u_j(v) ∈ -σ_v` for `t ≥ 0`. -/
theorem neg_smul_rayVector_mem_negCone (v : latticePolytopeVertices γ) (j : Fin n) {t : ℝ}
    (ht : 0 ≤ t) :
    (-t) • latticeVector (polytopeToricRayGenerator γ hs v j) ∈ polytopeToricNegCone hs v := by
  intro i
  simp only [map_smul, smul_eq_mul, latticeFunctional_latticeVector,
    intPairing_basis_rayGenerator]
  split_ifs <;> simp [ht]

/-- The Guillemin weight `F_0 - ⟨v, ·⟩` is bounded on `-σ_v`. -/
theorem exists_abs_reference_sub_le (v : latticePolytopeVertices γ) :
    ∃ C : ℝ, ∀ x ∈ polytopeToricNegCone hs v,
      |polytopeToricReference γ hs x - latticeFunctional v.val x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ComplexModel n) (Real.sqrt n)).exists_bound_of_continuousOn
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).continuous.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have heq := originalGuilleminGeometricNativeWeight_chart_embedding γ hs v (positiveTorusPoint x)
  rw [unitTorusLog_positiveTorusPoint] at heq
  rw [← heq]
  apply hC
  rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ j, ‖originalPolytopeNativeModelChart γ hs v
        (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j‖ ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        have h1 := BigToricMetric.norm_chart_positive_le_one v hx j
        have h0 := norm_nonneg (originalPolytopeNativeModelChart γ hs v
          (polytopeToricEmbedding γ hs (positiveTorusPoint x)) j)
        nlinarith
    _ = n := by simp

/-- The cone of `P` at the vertex `v` is spanned by the edges: `⟨w - v, u_j(v)⟩ ≥ 0` for
every vertex `w`. -/
theorem vertex_pairing_rayGenerator_nonneg (v w : latticePolytopeVertices γ) (j : Fin n) :
    0 ≤ intPairing (w.val - v.val) (polytopeToricRayGenerator γ hs v j) := by
  obtain ⟨C, hC⟩ := exists_abs_reference_sub_le γ hs v
  obtain ⟨E, hE⟩ := (SGPT.PSH.singularityLE_iff_exists_real _ _).mp
    ((SGPT.PSH.singularityEquiv_iff _ _).mp (polytopeToricReference_singularityEquiv_support γ hs)).2
  have hwP : latticeVector w.val ∈ polytopeToricMomentPolytope γ := w.property.1
  by_contra hneg
  push Not at hneg
  set k := intPairing (w.val - v.val) (polytopeToricRayGenerator γ hs v j)
  have hk : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
  set t : ℝ := |C| + |E| + 1
  have ht : 0 ≤ t := by positivity
  set x := (-t) • latticeVector (polytopeToricRayGenerator γ hs v j)
  have hx := neg_smul_rayVector_mem_negCone γ hs v j ht
  have h1 := (abs_le.mp (hC x hx)).2
  have h2 : (latticeFunctional w.val x : EReal) ≤ (polytopeToricReference γ hs x : EReal) + (E : EReal) := by
    have hsupp : (latticeFunctional w.val x : EReal) ≤
        support (innerₗ (EuclideanSpace ℝ (Fin n))).flip (polytopeToricMomentPolytope γ) x := by
      apply le_iSup_of_le (⟨latticeVector w.val, hwP⟩ : polytopeToricMomentPolytope γ)
      apply EReal.coe_le_coe_iff.mpr
      change latticeFunctional w.val x ≤ inner ℝ x (latticeVector w.val)
      rw [real_inner_comm, inner_latticeVector]
    exact hsupp.trans (hE x)
  rw [← EReal.coe_add] at h2
  have h3 := EReal.coe_le_coe_iff.mp h2
  have hdiff : latticeFunctional w.val x - latticeFunctional v.val x = -t * k := by
    simp only [x, map_smul, smul_eq_mul, latticeFunctional_latticeVector]
    simp only [k, intPairing_sub]
    push_cast; ring
  have : t * 1 ≤ t * (-(k : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) ht
  nlinarith [abs_nonneg C, abs_nonneg E, le_abs_self C, le_abs_self E]

/-- The pairing `⟨v, u_ρ⟩` does not depend on the vertex `v` at which `ρ` is a ray. -/
theorem intPairing_vertex_eq_of_ray_eq {v w : latticePolytopeVertices γ} {i j : Fin n}
    (hij : polytopeToricRayGenerator γ hs v i = polytopeToricRayGenerator γ hs w j) :
    intPairing v.val (polytopeToricRayGenerator γ hs v i) =
      intPairing w.val (polytopeToricRayGenerator γ hs v i) := by
  have h1 := vertex_pairing_rayGenerator_nonneg γ hs v w i
  have h2 := vertex_pairing_rayGenerator_nonneg γ hs w v j
  rw [← hij] at h2
  rw [intPairing_sub] at h1 h2
  omega

/-- Source `sec:toricsetup2` (the ample divisor of `P`): `D_P = ∑_ρ a_ρ D_ρ` with
`a_ρ = -⟨v, u_ρ⟩` for any vertex `v` at which `ρ` is a ray, i.e. `a_ρ = -min_P ⟨·, u_ρ⟩`. -/
def polytopeToricAmpleDivisor : ToricDivisor γ hs :=
  fun ρ => -intPairing ρ.property.choose.val ρ.val

/-- The Cartier datum of `D_P` on `σ_v` is the vertex `v`. -/
theorem toricCartierDatum_ampleDivisor (v : latticePolytopeVertices γ) :
    toricCartierDatum (polytopeToricAmpleDivisor γ hs) v = v.val := by
  symm
  apply toricCartierDatum_unique
  intro j
  simp only [polytopeToricAmpleDivisor, neg_neg]
  set ρ := polytopeToricRay γ hs v j
  obtain ⟨j', hj'⟩ := ρ.property.choose_spec
  exact intPairing_vertex_eq_of_ray_eq γ hs (hj'.trans rfl).symm

/-- Source `lma:exist_Ftheta`, Step 1: the Guillemin metric on `O(D_P)`, with curvature the
Kähler form `ω`. -/
def guilleminBigToricMetric : BigToricMetric (polytopeToricAmpleDivisor γ hs) where
  form := polytopeToricKahlerForm γ hs
  weight := originalGuilleminGeometricNativeWeight γ hs
  smooth := contDiff_originalGuilleminGeometricNativeWeight γ hs
  coeff v z := originalGuilleminClosedForm_native_coeff γ hs v z
  invariant v a ha z := originalGuilleminGeometricNativeWeight_compact_action γ hs v a ha z
  transition v w a := by
    rw [toricCartierDatum_ampleDivisor, toricCartierDatum_ampleDivisor,
      originalGuilleminGeometricNativeWeight_chart_embedding,
      originalGuilleminGeometricNativeWeight_chart_embedding]
    ring

/-- For the Guillemin metric, `F_θ = F_0`. -/
theorem guilleminBigToricMetric_potential :
    (guilleminBigToricMetric γ hs).potential = polytopeToricReference γ hs := by
  funext x
  change originalGuilleminGeometricNativeWeight γ hs (polytopeToricBaseVertex γ) _ +
    latticeFunctional (toricCartierDatum _ _) x = _
  rw [toricCartierDatum_ampleDivisor, originalGuilleminGeometricNativeWeight_chart_embedding,
    unitTorusLog_positiveTorusPoint]
  ring

/-- For the Guillemin metric, `PSH_tor(X, θ) = PSH_tor(X, ω)` and the profiles agree. -/
theorem guilleminBigToricMetric_PSHTor :
    (guilleminBigToricMetric γ hs).PSHTor = PolytopeToricPSH γ hs := rfl

theorem guilleminBigToricMetric_profile (u : PolytopeToricVariety γ hs → EReal) :
    (guilleminBigToricMetric γ hs).profile u = polytopeToricProfile γ hs u := by
  funext x
  rw [BigToricMetric.profile, guilleminBigToricMetric_potential]
  rfl

theorem latticeVector_vertex_mem_ampleDivisorPolytope (v : latticePolytopeVertices γ) :
    latticeVector v.val ∈ toricDivisorPolytope (polytopeToricAmpleDivisor γ hs) := by
  intro ρ
  obtain ⟨w, j, hwj⟩ := ρ.property
  simp only [polytopeToricAmpleDivisor]
  rw [latticeFunctional_latticeVector]
  obtain ⟨j', hj'⟩ := ρ.property.choose_spec
  have h1 := vertex_pairing_rayGenerator_nonneg γ hs ρ.property.choose v j'
  rw [intPairing_sub, hj'] at h1
  have hsym : intPairing ρ.val v.val = intPairing v.val ρ.val := by
    unfold intPairing; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : intPairing ρ.property.choose.val ρ.val ≤ intPairing v.val ρ.val := by linarith
  rw [hsym]
  simp only [Int.cast_neg, neg_neg]
  exact_mod_cast h2

/-- `P_{D_P} = P`: the polytope of the ample divisor `D_P` is the Delzant polytope `P`
(through `Δ(θ, V_θ) = P_D` and `V_ω = 0`, `Δ(ω, 0) = P`). -/
theorem toricDivisorPolytope_ampleDivisor :
    toricDivisorPolytope (polytopeToricAmpleDivisor γ hs) = polytopeToricMomentPolytope γ := by
  set h := guilleminBigToricMetric γ hs
  have hP : (toricDivisorPolytope (polytopeToricAmpleDivisor γ hs)).Nonempty := by
    obtain ⟨v, hv⟩ := nonempty_latticePolytopeVertices γ
    exact ⟨_, latticeVector_vertex_mem_ampleDivisorPolytope γ hs ⟨v, hv⟩⟩
  have hV : h.minimalEnvelope = 0 := polytopeToric_sourceMinimalEnvelope_eq_zero γ hs
  rw [← h.newtonBody_minimalEnvelope hP, hV, BigToricMetric.newtonBody,
    guilleminBigToricMetric_profile]
  exact (polytopeToricNewtonBody_eq_closure_rawSubgradientImage γ hs
    (zero_mem_polytopeToricPSH γ hs)).symm.trans (polytopeToricNewtonBody_zero γ hs)

end SGPT.Toric
