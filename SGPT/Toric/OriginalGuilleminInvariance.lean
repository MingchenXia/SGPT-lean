import SGPT.Toric.OriginalGuilleminGlobalForm
import SGPT.Toric.NativeOriginalEdgeAction
import SGPT.Foundations.Analysis.FirstPass.FormPullback

/-!
# Compact invariance and smooth-extension uniqueness on the original closure

The action and global form are the existing genuine original objects. Dense
orbit arguments equate finite continuous potentials; complete tensor invariance
then follows from actual holomorphic ddC pullback on the whole model. Uniqueness
is from the full geometric vertex-weight ddC restriction to the original torus.
No algebraic Chern class or literal F0 differentiation bridge is claimed here.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators
attribute [local instance] monomialProjectiveTopology

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- The actual squared-log convention is unchanged by every compact-torus
multiplier, for all original nonzero torus points. -/
theorem torusLogCoordinates_compact_mul (a b : Fin n → ℂˣ)
    (ha : ∀ j, ‖(a j : ℂ)‖ = 1) :
    torusLogCoordinates (latticeTorusPoint (a * b)) =
      torusLogCoordinates (latticeTorusPoint b) := by
  funext j
  simp only [torusLogCoordinates, latticeTorusPoint, Pi.mul_apply, Units.val_mul,
    norm_mul, ha j, one_mul]

private theorem invariantPotential_continuousOn (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    ContinuousOn (originalGuilleminVertexPotential γ hs v)
      (originalPolytopeNativeModelChart γ hs v).source := by
  have h := (contDiff_originalGuilleminNativeCornerWeight γ hs v).continuous.comp_continuousOn
    (originalGuilleminCornerModelChart γ hs v).continuousOn
  have hsrc : (originalGuilleminCornerModelChart γ hs v).source =
      (originalPolytopeNativeModelChart γ hs v).source := by
    rw [originalPolytopeNativeModelChart_source]
    simpa only [originalGuilleminCornerModelChart, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ] using
        (originalGuilleminCornerPiChart_spec γ hs v).2.2.1
  rwa [hsrc] at h

/-- Equality of finite continuous potentials on the dense actual original torus
extends to the WHOLE true vertex open, including every boundary stratum. -/
theorem originalGuilleminVertexPotential_compact_action (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (ha : ∀ j, ‖(a j : ℂ)‖ = 1)
    (p : originalPolytopeNativeSpace γ)
    (hp : p ∈ (originalPolytopeNativeModelChart γ hs v).source) :
    originalGuilleminVertexPotential γ hs v (originalPolytopeNativeAction γ a p) =
      originalGuilleminVertexPotential γ hs v p := by
  let D := (originalPolytopeNativeModelChart γ hs v).source
  have hmaps : MapsTo (originalPolytopeNativeAction γ a) D D := by
    intro q hq
    change q ∈ (originalPolytopeNativeModelChart γ hs v).source at hq
    change originalPolytopeNativeAction γ a q ∈
      (originalPolytopeNativeModelChart γ hs v).source
    rw [originalPolytopeNativeModelChart_source] at hq ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a q).mpr hq
  have hf : ContinuousOn (fun q => originalGuilleminVertexPotential γ hs v
      (originalPolytopeNativeAction γ a q)) D :=
    (invariantPotential_continuousOn γ hs v).comp
      (originalPolytopeNativeAction γ a).continuous.continuousOn hmaps
  have hg : ContinuousOn (originalGuilleminVertexPotential γ hs v) D :=
    invariantPotential_continuousOn γ hs v
  have heq : EqOn (fun q => originalGuilleminVertexPotential γ hs v
      (originalPolytopeNativeAction γ a q)) (originalGuilleminVertexPotential γ hs v)
      (originalPolytopeNativeOrbitMap γ '' (originalPolytopeNativeOrbitMap γ ⁻¹' D)) := by
    rintro q ⟨b, _, rfl⟩
    change originalGuilleminVertexPotential γ hs v
      (originalPolytopeNativeAction γ a (originalPolytopeNativeOrbitMap γ b)) = _
    rw [originalPolytopeNativeAction_orbit,
      originalGuilleminVertexPotential_orbit_eq_reference,
      originalGuilleminVertexPotential_orbit_eq_reference,
      torusLogCoordinates_compact_mul a b ha]
  exact heq.of_subset_closure hf hg (image_preimage_subset _ _)
    ((denseRange_originalPolytopeNativeOrbitMap γ).subset_closure_image_preimage_of_isOpen
      (originalPolytopeNativeModelChart γ hs v).open_source) hp

/-- Whole-model equality under the genuine actual complex-linear chart action. -/
theorem originalGuilleminGeometricNativeWeight_compact_action (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (a : Fin n → ℂˣ) (ha : ∀ j, ‖(a j : ℂ)‖ = 1) (z : ComplexModel n) :
    originalGuilleminGeometricNativeWeight γ hs v
        (originalPolytopeNativeModelActionLinear γ hs v a z) =
      originalGuilleminGeometricNativeWeight γ hs v z := by
  let e := originalPolytopeNativeModelChart γ hs v
  have hz : z ∈ e.target := by
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ _
  have hp := e.map_target hz
  have hpa : originalPolytopeNativeAction γ a (e.symm z) ∈ e.source := by
    rw [originalPolytopeNativeModelChart_source] at hp ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a _).mpr hp
  have haction := originalPolytopeNativeModelChart_action_symm γ hs v a z
  have hinv : e.symm (originalPolytopeNativeModelActionLinear γ hs v a z) =
      originalPolytopeNativeAction γ a (e.symm z) := by
    rw [← haction]
    exact e.left_inv hpa
  change originalGuilleminVertexPotential γ hs v
      (e.symm (originalPolytopeNativeModelActionLinear γ hs v a z)) =
    originalGuilleminVertexPotential γ hs v (e.symm z)
  rw [hinv]
  exact originalGuilleminVertexPotential_compact_action γ hs v a ha _ hp

/-- The full normalized alternating two-tensor is invariant under the ACTUAL
chart derivative, including all coordinate zeros and dimension zero. -/
theorem smoothDDC_originalGuilleminGeometricNativeWeight_compact_action
    (γ : K → Fin n → ℤ) (hs : latticePolytopeEdgeSmooth γ)
    (v : latticePolytopeVertices γ) (a : Fin n → ℂˣ)
    (ha : ∀ j, ‖(a j : ℂ)‖ = 1) (z : ComplexModel n) :
    (smoothDDC (originalGuilleminGeometricNativeWeight γ hs v)
      (originalPolytopeNativeModelActionLinear γ hs v a z)).compContinuousLinearMap
        (fderiv ℝ (originalPolytopeNativeModelActionLinear γ hs v a) z) =
      smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) z := by
  have hpull := HolomorphicDDC.smoothDDC_comp isOpen_univ isOpen_univ
    (originalPolytopeNativeModelActionLinear γ hs v a).contDiff.contDiffOn
    (contDiff_originalGuilleminGeometricNativeWeight γ hs v).contDiffOn
    (mapsTo_univ _ _) (mem_univ z)
  have heq : (fun y => originalGuilleminGeometricNativeWeight γ hs v
      (originalPolytopeNativeModelActionLinear γ hs v a y)) =
      originalGuilleminGeometricNativeWeight γ hs v :=
    funext (originalGuilleminGeometricNativeWeight_compact_action γ hs v a ha)
  rw [heq] at hpull
  exact hpull.symm

/-- The existing genuine global pullback by the same original holomorphic
action equals the original Guillemin form on EVERY native chart target. -/
theorem originalGuilleminClosedForm_compact_pullback (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ)
    (ha : ∀ j, ‖(a j : ℂ)‖ = 1) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    (SmoothRealForm.pullback (contMDiff_originalPolytopeNativeAction γ hs a ∞)
      (originalGuilleminClosedForm γ hs).val).GeometricallyEq
        (originalGuilleminClosedForm γ hs).val := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  intro e z hz
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  let e := originalPolytopeNativeComplexChart γ hs v
  have hp : e.val.symm z ∈ e.val.source := e.val.map_target hz
  have hpa : originalPolytopeNativeAction γ a (e.val.symm z) ∈ e.val.source := by
    change (originalPolytopeNativeModelChart γ hs v).symm z ∈
      (originalPolytopeNativeModelChart γ hs v).source at hp
    change originalPolytopeNativeAction γ a ((originalPolytopeNativeModelChart γ hs v).symm z) ∈
      (originalPolytopeNativeModelChart γ hs v).source
    rw [originalPolytopeNativeModelChart_source] at hp ⊢
    exact (originalPolytopeNativeAction_mem_chart_source_iff γ hs v a _).mpr hp
  have hdomain : z ∈ HolomorphicMaps.coordinateDomain (originalPolytopeNativeAction γ a) e e :=
    ⟨hz, hpa⟩
  rw [SmoothRealForm.pullback_coeff (contMDiff_originalPolytopeNativeAction γ hs a ∞)
    (originalGuilleminClosedForm γ hs).val e e hdomain]
  have hcoord : HolomorphicMaps.coordinateMap (originalPolytopeNativeAction γ a) e e =
      originalPolytopeNativeModelActionLinear γ hs v a :=
    funext (originalPolytopeNativeModelChart_action_symm γ hs v a)
  rw [hcoord, originalGuilleminClosedForm_native_coeff,
    originalGuilleminClosedForm_native_coeff]
  exact smoothDDC_originalGuilleminGeometricNativeWeight_compact_action γ hs v a ha z

/-- Genuine smooth forms on this unchanged original manifold are determined by
their full native coefficients on the SAME original torus. -/
theorem originalNativeSmoothForm_ext_of_torus (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    ∀ {r : ℕ} (α β : SmoothRealForm n (originalPolytopeNativeSpace γ) r),
      (∀ (v : latticePolytopeVertices γ) (z : ComplexModel n),
        (originalPolytopeNativeModelChart γ hs v).symm z ∈ originalPolytopeNativeTorus γ →
        α.coeff (originalPolytopeNativeComplexChart γ hs v) z =
          β.coeff (originalPolytopeNativeComplexChart γ hs v) z) → α = β := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  intro r α β h
  have hcoeff : ∀ e z, α.coeff e z = β.coeff e z := by
    intro e z
    obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
    let e := originalPolytopeNativeComplexChart γ hs v
    have heOpen : IsOpenMap e.val.symm := by
      intro U hU
      apply e.val.isOpen_image_symm_of_subset_target hU
      rw [originalPolytopeNativeComplexChart_target γ hs e]
      exact subset_univ _
    have hd := (dense_originalPolytopeNativeTorus γ).preimage heOpen
    have hα : Continuous (α.coeff e) := by
      have hh := α.smooth e
      rw [originalPolytopeNativeComplexChart_target γ hs e] at hh
      exact contDiffOn_univ.mp hh |>.continuous
    have hβ : Continuous (β.coeff e) := by
      have hh := β.smooth e
      rw [originalPolytopeNativeComplexChart_target γ hs e] at hh
      exact contDiffOn_univ.mp hh |>.continuous
    have heq : EqOn (α.coeff e) (β.coeff e)
        (e.val.symm ⁻¹' originalPolytopeNativeTorus γ) := fun y hy => h v y hy
    exact heq.of_subset_closure hα.continuousOn hβ.continuousOn (subset_univ _)
      (by rw [hd.closure_eq]) (mem_univ z)
  cases α with
  | mk ac asmooth acomp =>
    cases β with
    | mk bc bsmooth bcomp =>
      have hfun : ac = bc := funext fun e => funext fun z => hcoeff e z
      cases hfun
      rfl

/-- Because every original native chart has whole model target, geometric
compact invariance upgrades to literal equality of the existing smooth forms. -/
theorem originalGuilleminClosedForm_compact_pullback_eq (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (a : Fin n → ℂˣ)
    (ha : ∀ j, ‖(a j : ℂ)‖ = 1) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    SmoothRealForm.pullback (contMDiff_originalPolytopeNativeAction γ hs a ∞)
      (originalGuilleminClosedForm γ hs).val = (originalGuilleminClosedForm γ hs).val := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  apply originalNativeSmoothForm_ext_of_torus γ hs
  intro v z _
  apply originalGuilleminClosedForm_compact_pullback γ hs a ha
  rw [originalPolytopeNativeComplexChart_target]
  exact mem_univ _

/-- A genuine smooth closed real (1,1)-form extending the full actual
vertex-weight ddC restriction on the original torus is the constructed form. -/
theorem originalGuilleminClosedForm_unique_extension (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    ∀ η : ClosedRealOneOneForm n (originalPolytopeNativeSpace γ),
      (∀ (v : latticePolytopeVertices γ) (z : ComplexModel n),
        (originalPolytopeNativeModelChart γ hs v).symm z ∈ originalPolytopeNativeTorus γ →
        η.val.coeff (originalPolytopeNativeComplexChart γ hs v) z =
          smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) z) →
      η = originalGuilleminClosedForm γ hs := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  intro η hη
  apply Subtype.ext
  apply originalNativeSmoothForm_ext_of_torus γ hs
  intro v z hz
  rw [hη v z hz, originalGuilleminClosedForm_native_coeff]

end SGPT.Toric
