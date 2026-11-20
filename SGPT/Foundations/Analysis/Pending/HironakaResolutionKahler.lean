import SGPT.Foundations.Analysis.Pending.HironakaResolutionSpace
import SGPT.Foundations.Analysis.Pending.RegularAtDimTransport
import SGPT.Foundations.Analysis.Pending.AnalyticRegularStratumTopology
import SGPT.Foundations.Analysis.Pending.DominationLogResolution
import SGPT.Foundations.Analysis.Pending.SubmanifoldKahlerRestriction

/-!
# Kähler resolutions of pure embedded analytic spaces

The SAME strict transform furnished by G11a has the original pure dimension
at every point, including exceptional points. Its canonical submanifold atlas
therefore carries the restriction of an actual ambient Kähler background.
No smoothness of the original analytic set or irreducibility is assumed.
The dimension bound is explicit, including for the empty analytic set.

Blueprint: `hironaka-g11-kahler.tex`. This does not establish the intrinsic
smooth-centre modification form or the resolution of non-embeddable spaces.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler

open FirstPass FirstPass.BlowupSequences FirstPass.NonKahlerLocus FirstPass.PositiveClasses
  HironakaResolutionSpace AnalyticDimensionBasics
open HironakaEmbeddedAnalytic (singularSet)

variable {n d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {W : Set M} {σ : M' → M} {E : List (Set M')}

/-- A resolution by strict transform preserves the original pure dimension. -/
theorem isPureDim_strictTransform (h : IsStrictTransformResolution n W σ E)
    (hW : IsClosed W) (hpure : IsPureDim (n := n) W d) :
    IsPureDim (n := n) (strictTransform n σ W) d := by
  have hdense : strictTransform n σ W ⊆
      closure (regularLocus (n := n) (strictTransform n σ W) d) := by
    conv_lhs => rw [h.eq_closure]
    apply closure_mono
    intro y hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((diff_singularSet W).subset hy)
    have hreg : RegularAtDim (n := n) W (σ y) d := hpure (σ y) k hk ▸ hk
    have hny : y ∉ exceptionalLocus n σ :=
      fun he => Set.disjoint_left.mp h.isIsomorphismOver.2 hy.2 he
    exact RegularAtDimTransport.regularAtDim_of_preimage h.contMDiff hny
      ((HironakaEmbeddedAnalytic.isClosed_singularSet hW).isOpen_compl.preimage
        h.contMDiff.continuous) hy.2
      (fun z hz => ⟨fun hmem => h.strictTransform_subset_preimage hmem,
        fun hmem => (h.inter_preimage_compl.symm.subset ⟨hmem, hz⟩).1⟩) hreg
  intro y k hy
  obtain ⟨z, hz, hzd⟩ := mem_closure_iff_nhds.mp (hdense hy.2.1) _
    (RegularPatchNeighborhood.eventually_regularAtDim hy)
  exact RegularPointDimension.eq_of_regularAtDim (hz hzd.2.1) hzd

/-- Every point of the resolved pure carrier is regular in the SAME dimension. -/
theorem regularAtDim_strictTransform (h : IsStrictTransformResolution n W σ E)
    (hW : IsClosed W) (hpure : IsPureDim (n := n) W d) :
    ∀ y ∈ strictTransform n σ W, RegularAtDim (n := n) (strictTransform n σ W) y d := by
  intro y hy
  obtain ⟨k, hk⟩ := h.isClosedSubmanifold.2 y hy
  exact isPureDim_strictTransform h hW hpure y k hk ▸ hk

/-- The actual G11a strict transform of a pure analytic set in a compact Kähler
manifold is a compact Kähler manifold in its canonical native atlas. -/
theorem exists_kahler_strictTransform_resolution [CompactSpace M]
    (hWa : IsComplexAnalyticSubset (n := n) W) (hpure : IsPureDim (n := n) W d)
    (hd : d ≤ n) (omega : KahlerBackground n M) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace (ComplexModel n) M')
      (_ : IsComplexManifold n M') (σ : M' → M) (E : List (Set M'))
      (_h : IsStrictTransformResolution n W σ E)
      (hreg : ∀ y ∈ strictTransform n σ W,
        RegularAtDim (n := n) (strictTransform n σ W) y d)
      (omega' : KahlerBackground n M'),
      letI := SubmanifoldChartedSpace.chartedSpace hd hreg
      letI := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hreg
      IsComplexManifold d (strictTransform n σ W) ∧
      CompactSpace (strictTransform n σ W) ∧
      ∃ omegaW : KahlerBackground d (strictTransform n σ W),
        omegaW = SubmanifoldKahlerRestriction.kahlerBackground hd hreg omega' ∧
        ContMDiff 𝓘(ℂ, ComplexModel d) 𝓘(ℂ, ComplexModel n) ∞
          (Subtype.val : strictTransform n σ W → M') := by
  obtain ⟨M', _, _, _, σ, E, _, h⟩ :=
    exists_isStrictTransformResolution_of_isAnalytic hWa
  have hreg := regularAtDim_strictTransform h hWa.isClosed hpure
  let := SubmanifoldChartedSpace.chartedSpace hd hreg
  have := SubmanifoldChartedSpace.isComplexManifold_chartedSpace hd hreg
  obtain ⟨_, omega'⟩ :=
    DominationLogResolution.compactSpace_and_kahler_of_isBlowupSequence ⟨omega⟩
      h.isBlowupSequence
  exact ⟨M', inferInstance, inferInstance, inferInstance, σ, E, h, hreg, omega'.some,
    inferInstance, isCompact_iff_compactSpace.mp h.isCompact_strictTransform,
    SubmanifoldKahlerRestriction.kahlerBackground hd hreg omega'.some, rfl,
    SubmanifoldChartedSpace.contMDiff_val hd hreg⟩

end SGPT.Foundations.Analysis.Pending.HironakaResolutionKahler
