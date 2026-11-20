import SGPT.Foundations.Analysis.Pending.NaturalCrossChartWeightedTensorTransport
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents
import SGPT.Foundations.Analysis.Pending.NaturalCompactGeometricFormFrechetModule

/-!
# Original whole LF chart tests in the actual global smooth module

Actual weighted tensor transport constructs stage maps with internally proved
range membership. The genuine LF universal property then supplies global
continuity of the literal original geometric zero extension.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension

open FirstPass NaturalCrossChartWeightedTensorTransport NaturalSupportedChartFormExtension
  NaturalCompactGeometricFormFrechetModule

variable {n q m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem outputCompact_le (e f : ComplexChart n M) (K L : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (χ : M → ℝ) (hs : tsupport χ ⊆ f.val.source)
    (hL : (L : Set (ComplexModel n)) = f.val '' tsupport χ) :
    outputCompact e f K hK χ hs ≤ L := by
  rintro _ ⟨x, hx, rfl⟩
  change f.val x ∈ (L : Set (ComplexModel n))
  rw [hL]
  exact ⟨x, hx.2, rfl⟩

/-- Internally constructed continuous whole coordinates of an actual chart extension. -/
def extensionCoordinatesCLM (e : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (f : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ (f i).val.source)
    (L : Fin m → Compacts (ComplexModel n))
    (_hL : ∀ i, (L i : Set (ComplexModel n)) = (f i).val '' tsupport (χ i)) :
    𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      Π i : Fin m, 𝓓_{L i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContDiffMapSupportedIn.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (K₁ := outputCompact e (f i) K hK (χ i) (hs i)) (K₂ := L i)).comp
      (chartWeightedPullCLM e (f i) K hK (χ i) (hχ i) (hs i))

/-- Literal whole localized coefficient readback, including every overlap boundary. -/
theorem extensionCoordinatesCLM_apply (e : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (f : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
    (hχ : ∀ i, ChartSmooth (n := n) (χ i))
    (hs : ∀ i, tsupport (χ i) ⊆ (f i).val.source)
    (L : Fin m → Compacts (ComplexModel n))
    (hL : ∀ i, (L i : Set (ComplexModel n)) = (f i).val '' tsupport (χ i))
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) (i : Fin m)
    (z : ComplexModel n) :
    extensionCoordinatesCLM e K hK f χ hχ hs L hL A i z =
      (f i).val.target.indicator (fun y => χ i ((f i).val.symm y) •
        (extend e A A.contDiff A.hasCompactSupport.isCompact
          (A.tsupport_subset.trans hK)).coeff (f i) y) z := by
  simp only [extensionCoordinatesCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, ContDiffMapSupportedIn.monoCLM_apply,
    le_refl, outputCompact_le e (f i) K (L i) hK (χ i) (hs i) (hL i),
    and_self, ↓reduceIte, chartWeightedPullCLM_apply]
  by_cases ho : z ∈ (chartTransition (f i) e).source
  · have ht : z ∈ (f i).val.target := ho.1
    rw [indicator_of_mem ht]
    simp only [extend, transportedCoeff, indicator_of_mem ho]
  · rw [indicator_of_notMem ho]
    by_cases ht : z ∈ (f i).val.target
    · simp only [indicator_of_mem ht, extend, transportedCoeff, indicator_of_notMem ho,
        smul_zero]
    · exact (indicator_of_notMem ht _).symm

section ActualModel

variable [AddCommGroup (GeometricRealForm n M q)] [Module ℝ (GeometricRealForm n M q)]
  [TopologicalSpace (GeometricRealForm n M q)]
  (f : Fin m → ComplexChart n M) (χ : Fin m → M → ℝ)
  (hχ : ∀ i, ChartSmooth (n := n) (χ i))
  (hs : ∀ i, tsupport (χ i) ⊆ (f i).val.source)
  (L : Fin m → Compacts (ComplexModel n))
  (hL : ∀ i, (L i : Set (ComplexModel n)) = (f i).val '' tsupport (χ i))
  (S : Submodule ℝ (Π i : Fin m,
    𝓓_{L i}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)))
  (E : GeometricRealForm n M q ≃L[ℝ] S)
  (hread : ∀ (α : SmoothRealForm n M q) i z,
    (E (GeometricRealForm.ofRepresentative α)).val i z =
      (f i).val.target.indicator (fun y => χ i ((f i).val.symm y) • α.coeff (f i) y) z)

include hread in
private theorem extensionCoordinates_eq (e : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) :
    extensionCoordinatesCLM e K hK f χ hχ hs L hL A =
      (E (GeometricRealForm.ofRepresentative (extend e A A.contDiff
        A.hasCompactSupport.isCompact (A.tsupport_subset.trans hK)))).val := by
  funext i
  apply ContDiffMapSupportedIn.ext
  intro z
  rw [extensionCoordinatesCLM_apply, hread]

/-- Continuous chart extension into the same actual geometric quotient. -/
def supportedExtensionCLM (e : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ) →L[ℝ]
      GeometricRealForm n M q :=
  E.symm.toContinuousLinearMap.comp
    ((extensionCoordinatesCLM e K hK f χ hχ hs L hL).codRestrict S (fun A => by
      rw [extensionCoordinates_eq f χ hχ hs L hL S E hread]
      exact (E (GeometricRealForm.ofRepresentative (extend e A A.contDiff
        A.hasCompactSupport.isCompact (A.tsupport_subset.trans hK)))).property))

/-- This actual stage CLM reads exactly the original zero-extended form class. -/
theorem supportedExtensionCLM_apply (e : ComplexChart n M) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (A : 𝓓_{K}(ComplexModel n, (ComplexModel n) [⋀^Fin q]→L[ℝ] ℝ)) :
    supportedExtensionCLM f χ hχ hs L hL S E hread e K hK A =
      GeometricRealForm.ofRepresentative (extend e A A.contDiff
        A.hasCompactSupport.isCompact (A.tsupport_subset.trans hK)) := by
  apply E.injective
  change E (E.symm ((extensionCoordinatesCLM e K hK f χ hχ hs L hL).codRestrict S _ A)) = _
  rw [E.apply_symm_apply]
  apply Subtype.ext
  exact extensionCoordinates_eq f χ hχ hs L hL S E hread e K hK A

/-- Actual zero extension of a native entire chart test, before all functionals. -/
def testExtension (e : ComplexChart n M)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q) :
    SmoothRealForm n M q :=
  extend e η η.contDiff η.hasCompactSupport η.tsupport_subset

variable [IsTopologicalAddGroup (GeometricRealForm n M q)]
  [ContinuousSMul ℝ (GeometricRealForm n M q)]
  [LocallyConvexSpace ℝ (GeometricRealForm n M q)]

/-- Genuine full native LF extension, using internally proved exact supported stage readback. -/
def chartTestExtensionCLM (e : ComplexChart n M) :
    _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q →L[ℝ]
      GeometricRealForm n M q :=
  TestFunction.limitCLM ℝ (fun η => GeometricRealForm.ofRepresentative (testExtension e η))
    (fun K hK => supportedExtensionCLM f χ hχ hs L hL S E hread e K hK)
    (fun K hK A => by
      have hKt : (K : Set (ComplexModel n)) ⊆ e.val.target := hK
      change GeometricRealForm.ofRepresentative (extend e A A.contDiff
        A.hasCompactSupport.isCompact (A.tsupport_subset.trans hKt)) =
          supportedExtensionCLM f χ hχ hs L hL S E hread e K hKt A
      exact (supportedExtensionCLM_apply f χ hχ hs L hL S E hread e K hKt A).symm)

/-- Exact actual native LF test readback in the original geometric quotient. -/
theorem chartTestExtensionCLM_apply (e : ComplexChart n M)
    (η : _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q) :
    chartTestExtensionCLM f χ hχ hs L hL S E hread e η =
      GeometricRealForm.ofRepresentative (testExtension e η) := rfl

end ActualModel

/-- Compactness alone internally supplies one genuine complete global space and all full LF chart extensions. -/
theorem exists_complete_chart_test_extensions [CompactSpace M] (q : ℕ) :
    ∃ g : AddCommGroup (GeometricRealForm n M q), let _ := g
      ∃ v : Module ℝ (GeometricRealForm n M q), let _ := v
        ∃ u : UniformSpace (GeometricRealForm n M q), let _ := u
          CompleteSpace (GeometricRealForm n M q) ∧ T2Space (GeometricRealForm n M q) ∧
          FirstCountableTopology (GeometricRealForm n M q) ∧
          IsTopologicalAddGroup (GeometricRealForm n M q) ∧
          ContinuousSMul ℝ (GeometricRealForm n M q) ∧
          LocallyConvexSpace ℝ (GeometricRealForm n M q) ∧
          ∀ e : ComplexChart n M, ∃ X :
            _root_.SGPT.Foundations.Analysis.LocalCurrents.TestForm (chartTarget e) q →L[ℝ]
              GeometricRealForm n M q,
            ∀ η, X η = GeometricRealForm.ofRepresentative (testExtension e η) := by
  classical
  obtain ⟨m, f, χ, K, hχ, -, hs, hK, -, hmodel⟩ :=
    exists_complete_locally_convex_module (n := n) (M := M)
  obtain ⟨S, -, g, v, u, E, hc, ht, hfc, ha, hv, hl, hread⟩ := hmodel q
  let _ := g
  let _ := v
  let _ := u
  let _ := ha
  let _ := hv
  let _ := hl
  refine ⟨g, v, u, hc, ht, hfc, ha, hv, hl, fun e => ?_⟩
  exact ⟨chartTestExtensionCLM f χ hχ hs K hK S E hread e,
    chartTestExtensionCLM_apply f χ hχ hs K hK S E hread e⟩

end SGPT.Foundations.Analysis.Pending.NaturalChartTestGeometricExtension
