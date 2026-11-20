import SGPT.PSH.QuasiPSHIdentity
import SGPT.PSH.LocalIntrinsicAnalyticPullback
import SGPT.PSH.NativeThetaCompactMaximum
import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

universe u
variable {k n : ℕ} {V M : Type u}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- An actual native holomorphic map has exactly the original all-chart
holomorphicity fields on the actual chart domains, including independent dimensions. -/
theorem nativeHolomorphicMap_isHolomorphic {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (ofFixedModel k V).IsHolomorphic (ofFixedModel n M) f := by
  refine ⟨hf.continuous, ?_⟩
  intro e d
  exact (coordinateMap_contDiffOn hf e d).differentiableOn (by simp)

/-- The actual whole native tensor pullback, read through the exact
original tensor dictionary; it stores no PSH or nondegeneracy conclusion. -/
def AtlasClosedRealOneOneForm.nativeHolomorphicPullback
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) :
    AtlasClosedRealOneOneForm (ofFixedModel k V) :=
  nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hf (atlasClosedFormToNative θ))

/-- Every admissible original chart pair sees the entire actual alternating
coefficient of the same pulled background, not merely a diagonal value. -/
theorem nativeHolomorphicPullback_coeff
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (e : ComplexChart k V) (d : ComplexChart n M) {z : ComplexModel k}
    (hz : z ∈ HolomorphicMaps.coordinateDomain f e d) :
    (θ.nativeHolomorphicPullback hf).coeff e z =
      (θ.coeff d (HolomorphicMaps.coordinateMap (k := k) (n := n) f e d z)).compContinuousLinearMap
        (fderiv ℝ (HolomorphicMaps.coordinateMap (k := k) (n := n) f e d) z) :=
  SmoothRealForm.pullback_coeff hf (atlasClosedFormToNative θ).val e d hz

/-- Actual original theta-PSH pulls back with its same whole pulled background
exactly when every original source component has an actual non-pole image point. -/
theorem IsThetaPSH.comp_native_holomorphic_iff
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : M → EReal}
    (hu : (ofFixedModel n M).IsThetaPSH θ u) {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (ofFixedModel k V).IsThetaPSH (θ.nativeHolomorphicPullback hf) (u ∘ f) ↔
      ∀ x : V, ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥ := by
  constructor
  · intro hp x
    exact (IsQPSH.locallyNondegenerate ⟨θ.nativeHolomorphicPullback hf, hp⟩) x
      (connectedComponent x) ((ofFixedModel k V).isOpen_component x) mem_connectedComponent
  · intro hn
    have hnative := (isThetaPSH_iff_nativeThetaPotential θ u).mp hu
    have hraw := GlobalPotentialPullback.thetaPlurisubharmonic_comp hf hnative.1
    have hnd : LocallyNondegenerate (u ∘ f) :=
      locallyNondegenerate_of_component_nonbot_of_chart_quasiPSH
        (A := ofFixedModel k V) hraw.quasiPlurisubharmonic hn
    apply (isThetaPSH_iff_nativeThetaPotential (θ.nativeHolomorphicPullback hf) (u ∘ f)).mpr
    change IsThetaPshPotential (SmoothRealForm.pullback hf (atlasClosedFormToNative θ).val)
      (u ∘ f)
    exact ⟨hraw, hnd⟩

/-- The original existential closed background is produced upstairs under the
minimal actual component qualification; no local nondegeneracy is assumed. -/
theorem IsQPSH.comp_native_holomorphic_iff {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u) {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f) :
    (ofFixedModel k V).IsQPSH (u ∘ f) ↔
      ∀ x : V, ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥ := by
  constructor
  · intro hp x
    exact hp.locallyNondegenerate x (connectedComponent x)
      ((ofFixedModel k V).isOpen_component x) mem_connectedComponent
  · intro hn
    obtain ⟨θ, hθ⟩ := hu
    exact ⟨θ.nativeHolomorphicPullback hf, (hθ.comp_native_holomorphic_iff hf).mpr hn⟩

/-- Actual original global QPSH and intrinsic rational analytic type hold for
one and the same holomorphic pullback under its exact component qualification. -/
theorem IsQPSH.comp_native_holomorphic_analytic {u : M → EReal}
    (hu : (ofFixedModel n M).IsQPSH u)
    (han : (ofFixedModel n M).HasRationalAnalyticType u) {f : V → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hn : ∀ x : V, ∃ y ∈ connectedComponent x, u (f y) ≠ ⊥) :
    (ofFixedModel k V).IsQPSH (u ∘ f) ∧
      (ofFixedModel k V).HasRationalAnalyticType (u ∘ f) :=
  ⟨(hu.comp_native_holomorphic_iff hf).mpr hn,
    han.comp_atlasHolomorphic (nativeHolomorphicMap_isHolomorphic hf)⟩

section Modification

variable {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Genuine proper modification geometry internally supplies non-pole points
in EVERY source neighborhood, preserving the actual pulled original background. -/
theorem IsThetaPSH.comp_native_analyticModification
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    (ofFixedModel n Y).IsThetaPSH (θ.nativeHolomorphicPullback hπ.1) (u ∘ π) := by
  apply (isThetaPSH_iff_nativeThetaPotential (θ.nativeHolomorphicPullback hπ.1) (u ∘ π)).mpr
  change IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ)).val
    (u ∘ π)
  exact AnalyticModificationStrongPullback.isThetaPshPotential_comp_of_isAnalyticModification
    hπ (atlasClosedFormToNative θ) ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- The actual proper bimeromorphic geometric predicate produces genuine
original global QPSH pullback, without a source potential or finite-point premise. -/
theorem IsQPSH.comp_native_analyticModification {u : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    (ofFixedModel n Y).IsQPSH (u ∘ π) := by
  obtain ⟨θ, hθ⟩ := hu
  exact ⟨θ.nativeHolomorphicPullback hπ.1, hθ.comp_native_analyticModification hπ⟩

/-- The original analytic clause of prop:pshfunctions:L1425 on genuine native
manifolds. Non-pole neighborhoods and the actual upstairs background are produced. -/
theorem IsQPSH.comp_native_analyticModification_analytic {u : X → EReal}
    (hu : (ofFixedModel n X).IsQPSH u)
    (han : (ofFixedModel n X).HasRationalAnalyticType u) {π : Y → X}
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := n) π) :
    (ofFixedModel n Y).IsQPSH (u ∘ π) ∧
      (ofFixedModel n Y).HasRationalAnalyticType (u ∘ π) :=
  ⟨hu.comp_native_analyticModification hπ,
    han.comp_atlasHolomorphic (nativeHolomorphicMap_isHolomorphic hπ.1)⟩

end Modification
end SGPT.PSH.VariableComplexAtlas
