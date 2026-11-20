import SGPT.Toric.NativeOriginalEdgeOrbit
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter Manifold
open SGPT.Foundations.Analysis.FirstPass
open scoped BigOperators Topology Manifold ContDiff
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The SAME already produced original quotient action, on the SAME closure. -/
def originalPolytopeNativeAction (γ : K → Fin n → ℤ) (a : Fin n → ℂˣ) :
    originalPolytopeNativeSpace γ ≃ₜ originalPolytopeNativeSpace γ :=
  monomialOrbitClosureHomeomorph (originalPolytopeFullExponents γ) a

theorem originalPolytopeNativeAction_one (γ : K → Fin n → ℤ)
    (p : originalPolytopeNativeSpace γ) : originalPolytopeNativeAction γ 1 p = p :=
  monomialOrbitClosureHomeomorph_one _ p

theorem originalPolytopeNativeAction_mul (γ : K → Fin n → ℤ) (a b : Fin n → ℂˣ)
    (p : originalPolytopeNativeSpace γ) :
    originalPolytopeNativeAction γ (a * b) p =
      originalPolytopeNativeAction γ a (originalPolytopeNativeAction γ b p) :=
  monomialOrbitClosureHomeomorph_mul _ a b p

/-- Exact action on EVERY nonzero original homogeneous representative, including
boundary representatives. Nonvanishing is proved by the genuine linear equivalence. -/
theorem originalPolytopeNativeAction_representative (γ : K → Fin n → ℤ)
    (a : Fin n → ℂˣ) (p : originalPolytopeNativeSpace γ)
    (w : Fin (originalPolytopeFullIndexSize γ + 1) → ℂ) (hw : w ≠ 0)
    (hpw : p.val = Projectivization.mk ℂ w hw) :
    (originalPolytopeNativeAction γ a p).val =
      Projectivization.mk ℂ (monomialDiagonal (originalPolytopeFullExponents γ) a w)
        (by simpa only [map_zero] using
          (monomialDiagonal (originalPolytopeFullExponents γ) a).injective.ne hw) := by
  change monomialProjectiveAction (originalPolytopeFullExponents γ) a p.val = _
  rw [hpw]
  exact monomialProjectiveAction_mk _ a w hw

/-- EVERY actual original vertex source is invariant, because its original
homogeneous coordinate is multiplied by an actual nonzero character. -/
theorem originalPolytopeNativeAction_mem_chart_source_iff (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (p : originalPolytopeNativeSpace γ) :
    originalPolytopeNativeAction γ a p ∈ (originalPolytopeNativePiChart γ hsmooth v).source ↔
      p ∈ (originalPolytopeNativePiChart γ hsmooth v).source := by
  have hpw := p.val.mk_rep.symm
  rw [originalPolytopeNativePiChart_mem_source_iff γ hsmooth v p p.val.rep p.val.rep_nonzero hpw,
    originalPolytopeNativePiChart_mem_source_iff γ hsmooth v _ _ _
      (originalPolytopeNativeAction_representative γ a p _ p.val.rep_nonzero hpw)]
  have hc : (latticeCharacter (originalPolytopeFullExponents γ
      (originalPolytopeNativeVertexIndex γ v)) a : ℂ) ≠ 0 := Units.ne_zero _
  simp only [monomialDiagonal_apply, mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨hc, h⟩⟩

/-- The literal original edge-character diagonal formula on the WHOLE actual
vertex source, retaining all original boundary points and zero coordinates. -/
theorem originalPolytopeNativePiChart_action (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (p : originalPolytopeNativeSpace γ)
    (hp : p ∈ (originalPolytopeNativePiChart γ hsmooth v).source) (j : Fin n) :
    originalPolytopeNativePiChart γ hsmooth v (originalPolytopeNativeAction γ a p) j =
      (latticeCharacter (originalPolytopeNativeBasis γ hsmooth v j) a : ℂ) *
        originalPolytopeNativePiChart γ hsmooth v p j := by
  have hpw := p.val.mk_rep.symm
  have hsrc := (originalPolytopeNativeAction_mem_chart_source_iff γ hsmooth v a p).mpr hp
  have h₁ := (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.2.2 p hp
    p.val.rep p.val.rep_nonzero hpw
  have h₂ := (originalPolytopeNativePiChart_spec γ hsmooth v).2.2.2.2.2 _ hsrc _ _
    (originalPolytopeNativeAction_representative γ a p _ p.val.rep_nonzero hpw)
  rw [h₂.2 j, h₁.2 j]
  simp only [monomialDiagonal_apply]
  rw [mul_div_mul_comm]
  have hc :
      (latticeCharacter (originalPolytopeFullExponents γ
        (originalPolytopeNativeNeighborIndex γ hsmooth v j)) a : ℂ) /
      (latticeCharacter (originalPolytopeFullExponents γ
        (originalPolytopeNativeVertexIndex γ v)) a : ℂ) =
      (latticeCharacter (originalPolytopeNativeBasis γ hsmooth v j) a : ℂ) := by
    rw [← Units.val_div_eq_div_val, ← originalLatticeCharacter_sub]
    have hv := latticePolytopeExponentFamily_vertexIndex γ (originalPolytopeFullEnumeration γ) v
    change originalPolytopeFullExponents γ (originalPolytopeNativeVertexIndex γ v) = v.val at hv
    rw [hv, (originalPolytopeNativePiChart_spec γ hsmooth v).1 j]
  rw [hc]

/-- The actual finite-dimensional original character diagonal as a genuine
continuous complex linear map, using existing finite-dimensional continuity. -/
def originalPolytopeNativePiActionLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  (monomialDiagonal (originalPolytopeNativeBasis γ hsmooth v) a).toLinearMap.toContinuousLinearMap

/-- The genuine native Euclidean linear action is transported through the
EXISTING continuous complex-linear model equivalence, not a norm identification. -/
def originalPolytopeNativeModelActionLinear (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) : ComplexModel n →L[ℂ] ComplexModel n :=
  (originalPolytopeNativeModelEquiv n).symm.toContinuousLinearMap.comp
    ((originalPolytopeNativePiActionLinear γ hsmooth v a).comp
      (originalPolytopeNativeModelEquiv n).toContinuousLinearMap)

/-- The literal original diagonal formula in the native Euclidean model. -/
theorem originalPolytopeNativeModelChart_action (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (p : originalPolytopeNativeSpace γ)
    (hp : p ∈ (originalPolytopeNativeModelChart γ hsmooth v).source) :
    originalPolytopeNativeModelChart γ hsmooth v (originalPolytopeNativeAction γ a p) =
      originalPolytopeNativeModelActionLinear γ hsmooth v a
        (originalPolytopeNativeModelChart γ hsmooth v p) := by
  apply (originalPolytopeNativeModelEquiv n).injective
  ext j
  exact originalPolytopeNativePiChart_action γ hsmooth v a p
    (by rwa [originalPolytopeNativeModelChart_source] at hp) j

/-- WHOLE model targets make the actual fixed-action coordinate representative
the genuine continuous linear diagonal at EVERY coordinate point. -/
theorem originalPolytopeNativeModelChart_action_symm (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (z : ComplexModel n) :
    originalPolytopeNativeModelChart γ hsmooth v
      (originalPolytopeNativeAction γ a ((originalPolytopeNativeModelChart γ hsmooth v).symm z)) =
      originalPolytopeNativeModelActionLinear γ hsmooth v a z := by
  have hz : z ∈ (originalPolytopeNativeModelChart γ hsmooth v).target := by
    rw [originalPolytopeNativeModelChart_target]; exact Set.mem_univ _
  rw [originalPolytopeNativeModelChart_action γ hsmooth v a _
    ((originalPolytopeNativeModelChart γ hsmooth v).map_target hz),
    (originalPolytopeNativeModelChart γ hsmooth v).right_inv hz]

/-- The actual fixed action is a genuine native holomorphic map on ALL original
points, including the boundary, by the produced continuous linear chart formula. -/
theorem contMDiff_originalPolytopeNativeAction (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ) (r : ℕ∞ω) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) r
      (originalPolytopeNativeAction γ a) := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  let := originalPolytopeNativeIsManifold γ hsmooth r
  intro p
  obtain ⟨v, hv⟩ := originalPolytopeNativeModelChart_cover γ hsmooth p
  have hpa : originalPolytopeNativeAction γ a p ∈
      (originalPolytopeNativeModelChart γ hsmooth v).source := by
    rw [originalPolytopeNativeModelChart_source] at hv ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hsmooth v a p).mpr hv
  have hm : originalPolytopeNativeModelChart γ hsmooth v ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) r (originalPolytopeNativeSpace γ) :=
    IsManifold.subset_maximalAtlas (show originalPolytopeNativeModelChart γ hsmooth v ∈
      atlas (ComplexModel n) (originalPolytopeNativeSpace γ) from ⟨v, rfl⟩)
  apply (contMDiffAt_iff_of_mem_maximalAtlas hm hm hv hpa).mpr
  refine ⟨(originalPolytopeNativeAction γ a).continuous.continuousAt, ?_⟩
  simp only [mfld_simps, contDiffWithinAt_univ]
  have heq : ((originalPolytopeNativeModelChart γ hsmooth v) ∘
      originalPolytopeNativeAction γ a ∘ (originalPolytopeNativeModelChart γ hsmooth v).symm) =
      originalPolytopeNativeModelActionLinear γ hsmooth v a := by
    funext z
    exact originalPolytopeNativeModelChart_action_symm γ hsmooth v a z
  rw [heq]
  exact (originalPolytopeNativeModelActionLinear γ hsmooth v a).contDiff.contDiffAt

/-- Existing actual inverse action gives a genuine native holomorphic
diffeomorphism, of every smoothness order, on the original entire closure. -/
def originalPolytopeNativeActionDiffeomorph (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ) (r : ℕ∞ω) :
    letI := originalPolytopeNativeChartedSpace γ hsmooth
    Diffeomorph 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (originalPolytopeNativeSpace γ) (originalPolytopeNativeSpace γ) r := by
  let := originalPolytopeNativeChartedSpace γ hsmooth
  exact {
    toEquiv := (originalPolytopeNativeAction γ a).toEquiv
    contMDiff_toFun := contMDiff_originalPolytopeNativeAction γ hsmooth a r
    contMDiff_invFun := contMDiff_originalPolytopeNativeAction γ hsmooth a⁻¹ r }

/-- The original character multipliers are genuinely jointly continuous with
the actual chart coordinates. No joint-action continuity is an input. -/
theorem continuous_originalPolytopeNativeAction (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    Continuous (fun q : (Fin n → ℂˣ) × originalPolytopeNativeSpace γ =>
      originalPolytopeNativeAction γ q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨v, hv⟩ := originalPolytopeNativePiChart_cover γ hsmooth q.2
  let C := originalPolytopeNativePiChart γ hsmooth v
  let g := fun t : (Fin n → ℂˣ) × originalPolytopeNativeSpace γ => fun j =>
    (latticeCharacter (originalPolytopeNativeBasis γ hsmooth v j) t.1 : ℂ) * C t.2 j
  have hg : ContinuousAt g q := by
    apply continuousAt_pi.mpr
    intro j
    exact ((Units.continuous_val.comp (continuous_latticeCharacter
      (originalPolytopeNativeBasis γ hsmooth v j))).continuousAt.comp continuousAt_fst).mul
        ((continuous_apply j).continuousAt.comp ((C.continuousAt hv).comp continuousAt_snd))
  have htarget : g q ∈ C.target := by
    rw [originalPolytopeNativePiChart_target]; exact Set.mem_univ _
  apply ((C.continuousAt_symm htarget).comp hg).congr
  have hn : ∀ᶠ t : (Fin n → ℂˣ) × originalPolytopeNativeSpace γ in 𝓝 q, t.2 ∈ C.source :=
    continuousAt_snd.eventually (C.open_source.mem_nhds hv)
  filter_upwards [hn] with t ht
  have ha := (originalPolytopeNativeAction_mem_chart_source_iff γ hsmooth v t.1 t.2).mpr ht
  have heq : g t = C (originalPolytopeNativeAction γ t.1 t.2) := by
    funext j
    exact (originalPolytopeNativePiChart_action γ hsmooth v t.1 t.2 ht j).symm
  change C.symm (g t) = originalPolytopeNativeAction γ t.1 t.2
  rw [heq]
  exact C.left_inv ha

/-- The actual global action retains the original integer-character group law
on the SAME original torus parametrization. -/
theorem originalPolytopeNativeAction_orbit (γ : K → Fin n → ℤ)
    (a b : Fin n → ℂˣ) :
    originalPolytopeNativeAction γ a (originalPolytopeNativeOrbitMap γ b) =
      originalPolytopeNativeOrbitMap γ (a * b) := by
  apply Subtype.ext
  exact monomialProjectiveAction_orbit (originalPolytopeFullExponents γ) a b

/-- The genuine native diffeomorphism is EXACTLY the original quotient action. -/
theorem originalPolytopeNativeActionDiffeomorph_apply (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ) (r : ℕ∞ω)
    (p : originalPolytopeNativeSpace γ) :
    originalPolytopeNativeActionDiffeomorph γ hsmooth a r p =
      originalPolytopeNativeAction γ a p := rfl

/-- The original action in the actual native group-action API, from its proved
original quotient unit and multiplication laws. -/
@[instance_reducible]
def originalPolytopeNativeMulAction (γ : K → Fin n → ℤ) :
    MulAction (Fin n → ℂˣ) (originalPolytopeNativeSpace γ) where
  smul := fun a p => originalPolytopeNativeAction γ a p
  one_smul := originalPolytopeNativeAction_one γ
  mul_smul := originalPolytopeNativeAction_mul γ

/-- Genuine native joint action continuity, produced from the original
boundary-inclusive chart formula rather than supplied as a source certificate. -/
theorem originalPolytopeNativeContinuousSMul (γ : K → Fin n → ℤ)
    (hsmooth : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeMulAction γ
    ContinuousSMul (Fin n → ℂˣ) (originalPolytopeNativeSpace γ) := by
  let := originalPolytopeNativeMulAction γ
  exact ⟨continuous_originalPolytopeNativeAction γ hsmooth⟩

end SGPT.Toric
