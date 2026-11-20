import SGPT.Toric.GeodesicChart
import SGPT.Foundations.Analysis.BallRotation

/-!
# The compact torus acts on subgeodesics

Used in the proof of `cor:toricgeodgeneral` ("the geodesic is the upper envelope of toric
subgeodesics"): for `a ∈ T_c`, the translate `(φ_t ∘ a)_t` of a subgeodesic `(φ_t)_t` from
`φ₀` to `φ₁` is a subgeodesic from `φ₀ ∘ a` to `φ₁ ∘ a`.  In a vertex chart the action is a
diagonal unitary linear map `A_a`, which preserves the local potential `ψ_v` of `θ`, the
complexification (composition with the complex-linear map `A_a × id`) and the Lebesgue
measure (`A_a` is a real linear isometry), hence the chart-local `L¹` topology.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

theorem vertexAction_apply (v : latticePolytopeVertices γ) (t : Fin n → ℂˣ)
    (z : ComplexModel n) (j : Fin n) :
    originalPolytopeNativeModelActionLinear γ hs v t z j =
      (latticeCharacter (originalPolytopeNativeBasis γ hs v j) t : ℂ) * z j := rfl

theorem norm_latticeCharacter_of_compact (m : Fin n → ℤ) {a : Fin n → ℂˣ}
    (ha : IsCompactTorusElement a) : ‖(latticeCharacter m a : ℂ)‖ = 1 := by
  change ‖((∏ j, a j ^ m j : ℂˣ) : ℂ)‖ = 1
  rw [Units.coe_prod, norm_prod]
  apply Finset.prod_eq_one
  intro j _
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, ha j, one_zpow]

/-- The vertex chart action of a compact torus element, as a real linear isometry. -/
def vertexActionIsometry (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ}
    (ha : IsCompactTorusElement a) : ComplexModel n ≃ₗᵢ[ℝ] ComplexModel n where
  toFun := originalPolytopeNativeModelActionLinear γ hs v a
  invFun := originalPolytopeNativeModelActionLinear γ hs v a⁻¹
  map_add' := map_add _
  map_smul' c z := by
    ext j
    simp only [vertexAction_apply, PiLp.smul_apply, RingHom.id_apply, Complex.real_smul]
    ring
  left_inv z := by
    ext j
    simp only [vertexAction_apply]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mul]
  right_inv z := by
    ext j
    simp only [vertexAction_apply]
    rw [← mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul]
  norm_map' z := by
    change ‖originalPolytopeNativeModelActionLinear γ hs v a z‖ = ‖z‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [vertexAction_apply, norm_mul, norm_latticeCharacter_of_compact _ ha, one_mul]

theorem vertexActionIsometry_apply (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ}
    (ha : IsCompactTorusElement a) (z : ComplexModel n) :
    vertexActionIsometry (hs := hs) v ha z = originalPolytopeNativeModelActionLinear γ hs v a z :=
  rfl

/-- The action in vertex coordinates: `a · e_v⁻¹(z) = e_v⁻¹(A_a z)`. -/
theorem action_vertexChart_symm (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ)
    (z : ComplexModel n) :
    polytopeToricAction γ hs a ((originalPolytopeNativeModelChart γ hs v).symm z) =
      (originalPolytopeNativeModelChart γ hs v).symm
        (originalPolytopeNativeModelActionLinear γ hs v a z) := by
  let e := originalPolytopeNativeModelChart γ hs v
  have hz : z ∈ e.target := by
    rw [originalPolytopeNativeModelChart_target]; exact mem_univ _
  have hp := e.map_target hz
  have hpa : originalPolytopeNativeAction γ a (e.symm z) ∈ e.source := by
    rw [originalPolytopeNativeModelChart_source] at hp ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a _).mpr hp
  rw [← originalPolytopeNativeModelChart_action_symm γ hs v a z]
  exact (e.left_inv hpa).symm

/-- The chart-local `L¹` distance of translates is the `L¹` distance on the image compact. -/
theorem chartL1EDistance_comp_action (u w : PolytopeToricVariety γ hs → EReal)
    (v : latticePolytopeVertices γ) {a : Fin n → ℂˣ} (ha : IsCompactTorusElement a)
    (Kc : Set (ComplexModel n)) :
    chartL1EDistance (fun p => u (polytopeToricAction γ hs a p))
        (fun p => w (polytopeToricAction γ hs a p)) (polytopeToricVertexChart γ hs v) Kc =
      chartL1EDistance u w (polytopeToricVertexChart γ hs v)
        (vertexActionIsometry (hs := hs) v ha '' Kc) := by
  let A := vertexActionIsometry (hs := hs) v ha
  have hmp : MeasurePreserving A volume volume :=
    measurePreserving_linearIsometryEquiv_addHaar volume A
  have hemb : MeasurableEmbedding A := A.toHomeomorph.measurableEmbedding
  let f : ComplexModel n → ENNReal := fun y =>
    canonicalERealAbsDiff (chartFunction u (polytopeToricVertexChart γ hs v) y)
      (chartFunction w (polytopeToricVertexChart γ hs v) y)
  have h := hmp.setLIntegral_comp_emb hemb f Kc
  unfold chartL1EDistance
  rw [← h]
  apply lintegral_congr
  intro z
  change canonicalERealAbsDiff
      (u (polytopeToricAction γ hs a ((originalPolytopeNativeModelChart γ hs v).symm z)))
      (w (polytopeToricAction γ hs a ((originalPolytopeNativeModelChart γ hs v).symm z))) = _
  rw [action_vertexChart_symm v a z]
  rfl

namespace BigToricMetric

variable {D : ToricDivisor γ hs} (h : BigToricMetric D)
variable (omega : KahlerBackground n (PolytopeToricVariety γ hs))

/-- `T_c` acts on subgeodesics: for `a ∈ T_c`, `(φ_t ∘ a)_t` is a subgeodesic from `φ₀ ∘ a` to
`φ₁ ∘ a`. -/
theorem sourceSubgeodesicFrom_comp_action {curve : ℝ → PolytopeToricVariety γ hs → EReal}
    {u₀ u₁ : PolytopeToricVariety γ hs → EReal}
    (hsub : SourceSubgeodesicFrom omega h.atlasForm curve u₀ u₁) {a : Fin n → ℂˣ}
    (ha : IsCompactTorusElement a) :
    SourceSubgeodesicFrom omega h.atlasForm (fun t p => curve t (polytopeToricAction γ hs a p))
      (fun p => u₀ (polytopeToricAction γ hs a p)) (fun p => u₁ (polytopeToricAction γ hs a p)) := by
  have hn := (sourceSubgeodesicFrom_iff_native omega h.atlasForm curve u₀ u₁).mp hsub
  apply (sourceSubgeodesicFrom_iff_native omega h.atlasForm _ _ _).mpr
  have hnat (f : PolytopeToricVariety γ hs → EReal)
      (hf : (ofFixedModel n (PolytopeToricVariety γ hs)).IsThetaPSH h.atlasForm f) :
      IsThetaPshPotential (atlasClosedFormToNative h.atlasForm).val
        (fun p => f (polytopeToricAction γ hs a p)) :=
    (isThetaPSH_iff_nativeThetaPotential _ _).mp (h.isThetaPSH_comp_action hf ha)
  refine ⟨hnat u₀ hsub.1, hnat u₁ hsub.2.1, ⟨fun t ht => hnat _ (hsub.2.2.1.1 t ht), ?_⟩, ?_, ?_⟩
  · intro e z _
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    refine ⟨univ, h.weight v, mem_univ z, h.isSmoothLocalPotential_weight v, ?_⟩
    have hpsh := sourceJointThetaPSH_corrected hsub.2.2.1.2 (polytopeToricVertexChart γ hs v)
      (h.isSmoothLocalPotential_weight v)
    let L : ComplexModel n × ℂ →L[ℂ] ComplexModel n × ℂ :=
      (originalPolytopeNativeModelActionLinear γ hs v a).prodMap (ContinuousLinearMap.id ℂ ℂ)
    have hL := hpsh.comp_continuousLinearMap L
    have hpre : (L : ComplexModel n × ℂ → ComplexModel n × ℂ) ⁻¹'
        geodesicChartDomain (univ : Set (ComplexModel n)) =
          geodesicChartDomain (univ : Set (ComplexModel n)) := by
      ext p
      simp [L, geodesicChartDomain]
    rw [hpre] at hL
    intro p hp
    apply (hL p hp).congr
    filter_upwards with q
    change curve (q.2).re ((originalPolytopeNativeModelChart γ hs v).symm
        (originalPolytopeNativeModelActionLinear γ hs v a q.1)) +
        (h.weight v (originalPolytopeNativeModelActionLinear γ hs v a q.1) : EReal) =
      curve q.2.re (polytopeToricAction γ hs a ((originalPolytopeNativeModelChart γ hs v).symm q.1)) +
        (h.weight v q.1 : EReal)
    rw [action_vertexChart_symm v a q.1, h.invariant v a ha q.1]
  · intro e Kc hK _
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    have := hn.tendsto_left (polytopeToricVertexChart γ hs v)
      (vertexActionIsometry (hs := hs) v ha '' Kc) (hK.image (vertexActionIsometry v ha).continuous)
      (fun y _ => by
        change y ∈ (originalPolytopeNativeModelChart γ hs v).target
        rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
    apply this.congr
    intro t
    exact (chartL1EDistance_comp_action (curve t) u₀ v ha Kc).symm
  · intro e Kc hK _
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    have := hn.tendsto_right (polytopeToricVertexChart γ hs v)
      (vertexActionIsometry (hs := hs) v ha '' Kc) (hK.image (vertexActionIsometry v ha).continuous)
      (fun y _ => by
        change y ∈ (originalPolytopeNativeModelChart γ hs v).target
        rw [originalPolytopeNativeModelChart_target]; exact mem_univ _)
    apply this.congr
    intro t
    exact (chartL1EDistance_comp_action (curve t) u₁ v ha Kc).symm

end BigToricMetric

end SGPT.Toric
