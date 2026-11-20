import SGPT.Foundations.Analysis.Pending.DistributionFullChartCutoffTransport
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

set_option autoImplicit false

/-! Genuine finite signed scalar-distribution gluing. Native scalar density
test relations are explicit, and output compatibility is proved internally.
ENTIRE BP precedes this source; no original current/BC embedding is asserted. -/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
open FirstPass FirstPass.HolomorphicMaps ThetaPshChartLimitGluing
  DistributionFullChartCutoffTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual derivatives and determinants give the scalar Jacobian cocycle;
there is no nonzero determinant or incoming factorization premise. -/
theorem transitionJac_chain (g e f : ComplexChart n M) (z : ComplexModel n)
    (hge : z ∈ (chartTransition g e).source)
    (hgf : z ∈ (chartTransition g f).source) :
    transitionJac g f z = transitionJac e f ((chartTransition g e) z) *
      transitionJac g e z := by
  have hd : chartTransitionDerivative g f z =
      (chartTransitionDerivative e f ((chartTransition g e) z)).comp
        (chartTransitionDerivative g e z) :=
    coordinateMap_fderiv_change_target contMDiff_id g e f hge hgf
  unfold transitionJac
  rw [hd]
  change |LinearMap.det ((chartTransitionDerivative e f ((chartTransition g e) z)).toLinearMap.comp
    (chartTransitionDerivative g e z).toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul]

/-- All full-chart transports agree on each original pair of native related
scalar density tests. Desired family compatibility is not an input. -/
theorem fullChartTestCLM_overlap (e f g : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ g.val.source)
    (η : 𝓓(overlapSource e f, ℝ)) (θ : 𝓓(overlapTarget e f, ℝ))
    (hrel : ∀ y ∈ (chartTransition e f).source,
      η y = transitionJac e f y * θ ((chartTransition e f) y)) :
    fullChartTestCLM e g χ hχ hc hs (TestFunction.monoCLM ℝ η) =
      fullChartTestCLM f g χ hχ hc hs (TestFunction.monoCLM ℝ θ) := by
  classical
  apply TestFunction.ext
  intro z
  rw [fullChartTestCLM_value, fullChartTestCLM_value]
  simp only [testFunction_inclusion_coe (overlapSource_le e f),
    testFunction_inclusion_coe (overlapTarget_le e f)]
  by_cases hz : z ∈ g.val.target
  · by_cases hxe : g.val.symm z ∈ e.val.source
    · have hge : z ∈ (chartTransition g e).source := ⟨hz, hxe⟩
      by_cases hxf : g.val.symm z ∈ f.val.source
      · have hgf : z ∈ (chartTransition g f).source := ⟨hz, hxf⟩
        have hef : (chartTransition g e) z ∈ (chartTransition e f).source := by
          change e.val (g.val.symm z) ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source
          refine ⟨e.val.map_source hxe, ?_⟩
          change e.val.symm (e.val (g.val.symm z)) ∈ f.val.source
          rw [e.val.left_inv hxe]
          exact hxf
        have hv : (chartTransition e f) ((chartTransition g e) z) =
            (chartTransition g f) z := by
          change f.val (e.val.symm (e.val (g.val.symm z))) = f.val (g.val.symm z)
          rw [e.val.left_inv hxe]
        rw [if_pos hge, if_pos hgf, hrel _ hef, hv,
          transitionJac_chain g e f z hge hgf]
        ring
      · have hgf : z ∉ (chartTransition g f).source := fun h => hxf h.2
        have hη : η ((chartTransition g e) z) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro h
          have ht := (η.tsupport_subset h).2
          change e.val.symm (e.val (g.val.symm z)) ∈ f.val.source at ht
          rw [e.val.left_inv hxe] at ht
          exact hxf ht
        rw [if_pos hge, if_neg hgf, hη, mul_zero]
    · have hge : z ∉ (chartTransition g e).source := fun h => hxe h.2
      by_cases hxf : g.val.symm z ∈ f.val.source
      · have hgf : z ∈ (chartTransition g f).source := ⟨hz, hxf⟩
        have hθ : θ ((chartTransition g f) z) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro h
          have ht := (θ.tsupport_subset h).2
          change f.val.symm (f.val (g.val.symm z)) ∈ e.val.source at ht
          rw [f.val.left_inv hxf] at ht
          exact hxe ht
        rw [if_neg hge, if_pos hgf, hθ, mul_zero]
      · have hgf : z ∉ (chartTransition g f).source := fun h => hxf h.2
        rw [if_neg hge, if_neg hgf]
  · have hge : z ∉ (chartTransition g e).source := fun h => hz h.1
    have hgf : z ∉ (chartTransition g f).source := fun h => hz h.1
    rw [if_neg hge, if_neg hgf]

/-- Coordinate scalar distributions are compatible exactly on all original
scalar density overlap test pairs, with their actual real Jacobian. -/
def ScalarFamilyCompatible (S : (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ)) : Prop :=
  ∀ (e f : ComplexChart n M) (η : 𝓓(overlapSource e f, ℝ))
    (θ : 𝓓(overlapTarget e f, ℝ)),
    (∀ y ∈ (chartTransition e f).source,
      η y = transitionJac e f y * θ ((chartTransition e f) y)) →
    S e (TestFunction.monoCLM ℝ η) = S f (TestFunction.monoCLM ℝ θ)

/-- Every summand and their finite sum are genuine full-chart continuous signed
functionals; the local input distributions need no compatibility hypothesis. -/
def finiteScalarFamily {ι : Type*} [Fintype ι] (g : ι → ComplexChart n M)
    (χ : ι → M → ℝ) (hχ : ∀ a, ChartSmooth (n := n) (χ a))
    (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) :
    (e : ComplexChart n M) → 𝓓'(chartTarget e, ℝ) :=
  fun e => ∑ a, weightedChartDistribution e (g a) (χ a) (hχ a) (hc a) (hs a) (R a)

/-- Full native overlap compatibility is an output of the actual finite gluing,
including arbitrary signed inputs, empty families and complex dimension zero. -/
theorem finiteScalarFamily_compatible {ι : Type*} [Fintype ι]
    (g : ι → ComplexChart n M) (χ : ι → M → ℝ)
    (hχ : ∀ a, ChartSmooth (n := n) (χ a)) (hc : ∀ a, IsCompact (tsupport (χ a)))
    (hs : ∀ a, tsupport (χ a) ⊆ (g a).val.source)
    (R : ∀ a, 𝓓'(chartTarget (g a), ℝ)) :
    ScalarFamilyCompatible (finiteScalarFamily g χ hχ hc hs R) := by
  intro e f η θ hrel
  simp only [finiteScalarFamily, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  change R a (fullChartTestCLM e (g a) (χ a) (hχ a) (hc a) (hs a)
      (TestFunction.monoCLM ℝ η)) =
    R a (fullChartTestCLM f (g a) (χ a) (hχ a) (hc a) (hs a)
      (TestFunction.monoCLM ℝ θ))
  rw [fullChartTestCLM_overlap e f (g a) (χ a) (hχ a) (hc a) (hs a) η θ hrel]

end SGPT.Foundations.Analysis.Pending.FiniteScalarDistributionGluing
