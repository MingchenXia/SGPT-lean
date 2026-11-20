import SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension

/-! # Genuine original signed currents from full global smooth continuous duals

Actual entire LF zero extension and genuine overlap tensor transport produce
original compatible full native local currents. No compatibility or positivity
certificate is supplied.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalGlobalSmoothDualCurrent

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents HolomorphicMaps
  NaturalChartTestGeometricExtension NaturalSupportedChartFormExtension
  NaturalCompactGeometricFormFrechetModule

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The genuine original overlap law identifies the entire geometric extensions. -/
theorem related_test_extensions_eq (e f : ComplexChart n M)
    (η : TestForm (overlapSource e f) q) (ζ : TestForm (overlapTarget e f) q)
    (hrel : OverlapTestRelated e f η ζ) :
    GeometricRealForm.ofRepresentative
      (testExtension e (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) q)) =
    GeometricRealForm.ofRepresentative
      (testExtension f (TestFunction.monoCLM ℝ ζ : TestForm (chartTarget f) q)) := by
  apply Quotient.sound
  intro g z hz
  let ηe : TestForm (chartTarget e) q := TestFunction.monoCLM ℝ η
  let ζf : TestForm (chartTarget f) q := TestFunction.monoCLM ℝ ζ
  have hη (y : ComplexModel n) : ηe y = η y :=
    testForm_inclusion_apply (overlapSource_le e f) η y
  have hζ (y : ComplexModel n) : ζf y = ζ y :=
    testForm_inclusion_apply (overlapTarget_le e f) ζ y
  change transportedCoeff e g ηe z = transportedCoeff f g ζf z
  by_cases he : g.val.symm z ∈ e.val.source
  · have hge : z ∈ (chartTransition g e).source := ⟨hz, he⟩
    have hye : chartTransition g e z ∈ e.val.target := e.val.map_source he
    have hse : e.val.symm (chartTransition g e z) = g.val.symm z := e.val.left_inv he
    by_cases hf : g.val.symm z ∈ f.val.source
    · have hgf : z ∈ (chartTransition g f).source := ⟨hz, hf⟩
      have hef : chartTransition g e z ∈ (chartTransition e f).source :=
        ⟨hye, by
          change e.val.symm (chartTransition g e z) ∈ f.val.source
          rw [hse]
          exact hf⟩
      have hmap : chartTransition g f z = chartTransition e f (chartTransition g e z) :=
        coordinateMap_change_source (f := id) (d := f) hge
      have hder : chartTransitionDerivative g f z =
          (chartTransitionDerivative e f (chartTransition g e z)).comp
            (chartTransitionDerivative g e z) :=
        coordinateMap_fderiv_change_source contMDiff_id g e f hge hgf
      simp only [transportedCoeff, indicator_of_mem hge, indicator_of_mem hgf]
      ext v
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
        hη, hζ, hmap, hder, ContinuousLinearMap.comp_apply]
      exact hrel _ hef (fun i => chartTransitionDerivative g e z (v i))
    · have hgf : z ∉ (chartTransition g f).source := fun h => hf h.2
      have hn : chartTransition g e z ∉ overlapSource e f := by
        intro h
        apply hf
        change chartTransition g e z ∈ e.val.target ∧
          e.val.symm (chartTransition g e z) ∈ f.val.source at h
        rw [hse] at h
        exact h.2
      have hzero : ηe (chartTransition g e z) = 0 := by
        rw [hη]
        exact image_eq_zero_of_notMem_tsupport (fun h => hn (η.tsupport_subset h))
      simp only [transportedCoeff, indicator_of_mem hge, indicator_of_notMem hgf, hzero]
      ext v
      rfl
  · have hge : z ∉ (chartTransition g e).source := fun h => he h.2
    by_cases hf : g.val.symm z ∈ f.val.source
    · have hgf : z ∈ (chartTransition g f).source := ⟨hz, hf⟩
      have hsf : f.val.symm (chartTransition g f z) = g.val.symm z := f.val.left_inv hf
      have hn : chartTransition g f z ∉ overlapTarget e f := by
        intro h
        apply he
        change chartTransition g f z ∈ f.val.target ∧
          f.val.symm (chartTransition g f z) ∈ e.val.source at h
        rw [hsf] at h
        exact h.2
      have hzero : ζf (chartTransition g f z) = 0 := by
        rw [hζ]
        exact image_eq_zero_of_notMem_tsupport (fun h => hn (ζ.tsupport_subset h))
      simp only [transportedCoeff, indicator_of_notMem hge, indicator_of_mem hgf, hzero]
      ext v
      rfl
    · have hgf : z ∉ (chartTransition g f).source := fun h => hf h.2
      simp only [transportedCoeff, indicator_of_notMem hge, indicator_of_notMem hgf]

section ActualModel

variable {k : CurrentDegree n}
  [AddCommGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [Module ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [TopologicalSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [IsTopologicalAddGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [ContinuousSMul ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  [LocallyConvexSpace ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val))]
  (a : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
  (hχ : ∀ i, ChartSmooth (n := n) (χ i))
  (hs : ∀ i, tsupport (χ i) ⊆ (a i).val.source)
  (K : Fin m → Compacts (ComplexModel n))
  (hK : ∀ i, (K i : Set (ComplexModel n)) = (a i).val '' tsupport (χ i))
  (S : Submodule ℝ (Π i : Fin m, 𝓓_{K i}(ComplexModel n,
    (ComplexModel n) [⋀^Fin (Module.finrank ℝ (ComplexModel n) - k.val)]→L[ℝ] ℝ)))
  (E : GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) ≃L[ℝ] S)
  (hread : ∀ (α : SmoothRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) i z,
    (E (GeometricRealForm.ofRepresentative α)).val i z =
      (a i).val.target.indicator (fun y => χ i ((a i).val.symm y) • α.coeff (a i) y) z)

/-- An arbitrary full smooth continuous functional internally supplies the original compatible family. -/
def dualCurrent
    (L : GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ) :
    GlobalCurrent n M k := by
  let T : ChartCurrentFamily n M k := fun e =>
    L.comp (chartTestExtensionCLM a χ hχ hs K hK S E hread e)
  refine ⟨T, ?_⟩
  intro e f η ζ hrel
  change L (chartTestExtensionCLM a χ hχ hs K hK S E hread e
      (TestFunction.monoCLM ℝ η : TestForm (chartTarget e) _)) =
    L (chartTestExtensionCLM a χ hχ hs K hK S E hread f
      (TestFunction.monoCLM ℝ ζ : TestForm (chartTarget f) _))
  rw [chartTestExtensionCLM_apply, chartTestExtensionCLM_apply]
  exact congrArg L (related_test_extensions_eq e f η ζ hrel)

/-- Literal original full native local evaluation of the produced current. -/
theorem dualCurrent_inChart
    (L : GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ)
    (e : ComplexChart n M) (η : TestForm (chartTarget e)
      (Module.finrank ℝ (ComplexModel n) - k.val)) :
    (dualCurrent a χ hχ hs K hK S E hread L).inChart e η =
      L (GeometricRealForm.ofRepresentative (testExtension e η)) := rfl

end ActualModel

/-- The original complete global smooth module internally produces all actual signed dual currents. -/
theorem exists_complete_dual_currents [CompactSpace M] (k : CurrentDegree n) :
    ∃ g : AddCommGroup (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
      let _ := g
      ∃ v : Module ℝ (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
        let _ := v
        ∃ u : UniformSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)),
          let _ := u
          CompleteSpace (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          T2Space (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          FirstCountableTopology
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          IsTopologicalAddGroup
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ContinuousSMul ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          LocallyConvexSpace ℝ
            (GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val)) ∧
          ∀ L : GeometricRealForm n M (Module.finrank ℝ (ComplexModel n) - k.val) →L[ℝ] ℝ,
            ∃! T : GlobalCurrent n M k, ∀ e η,
              T.inChart e η = L (GeometricRealForm.ofRepresentative (testExtension e η)) := by
  classical
  obtain ⟨m, a, χ, K, hχ, -, hs, hK, -, hmodel⟩ :=
    exists_complete_locally_convex_module (n := n) (M := M)
  obtain ⟨S, -, g, v, u, E, hc, ht, hfc, ha, hv, hl, hread⟩ :=
    hmodel (Module.finrank ℝ (ComplexModel n) - k.val)
  let _ := g
  let _ := v
  let _ := u
  let _ := ha
  let _ := hv
  let _ := hl
  refine ⟨g, v, u, hc, ht, hfc, ha, hv, hl, fun L => ?_⟩
  refine ⟨dualCurrent a χ hχ hs K hK S E hread L,
    dualCurrent_inChart a χ hχ hs K hK S E hread L, ?_⟩
  intro T hT
  apply GlobalCurrent.ext
  intro e η
  exact (hT e η).trans (dualCurrent_inChart a χ hχ hs K hK S E hread L e η).symm

end SGPT.Foundations.Analysis.Pending.NaturalGlobalSmoothDualCurrent
