import SGPT.Toric.OriginalGuilleminGeometricWeights
import SGPT.Foundations.Analysis.Pending.LocalPotentialForm

/-!
# The actual global Guillemin form on the original monomial closure

The existing genuine local-potential gluing constructor is populated from the
actual original vertex cover and the checked literal geometric weights. Its
complete coefficient readback holds for every original vertex potential.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalPotentialForm
open scoped Topology ContDiff Classical

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]

/-- Genuine local-potential data manufactured from the ORIGINAL source cover,
with all differential gluing fields proved by the actual whole-overlap theorem. -/
def originalGuilleminLocalDDCData (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    LocalDDCData n (originalPolytopeNativeSpace γ) := by
  letI := originalPolytopeNativeChartedSpace γ hs
  letI := originalPolytopeNativeIsComplexManifold γ hs
  let v := fun p => (originalPolytopeNativeModelChart_cover γ hs p).choose
  exact {
    domain := fun p => (originalPolytopeNativeModelChart γ hs (v p)).source
    isOpen_domain := fun p => (originalPolytopeNativeModelChart γ hs (v p)).open_source
    mem_domain := fun p => (originalPolytopeNativeModelChart_cover γ hs p).choose_spec
    potential := fun p => originalGuilleminVertexPotential γ hs (v p)
    smooth := fun p => originalGuilleminVertexPotential_chart_smooth γ hs (v p)
    pluriharmonic := fun p q => smoothDDC_originalGuilleminVertexPotential_sub γ hs (v p) (v q) }

/-- The actual native closed real (1,1)-form, including its genuine tensor
transition law, is the existing gluing constructor's output. -/
def originalGuilleminClosedForm (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    ClosedRealOneOneForm n (originalPolytopeNativeSpace γ) := by
  letI := originalPolytopeNativeChartedSpace γ hs
  letI := originalPolytopeNativeIsComplexManifold γ hs
  exact (originalGuilleminLocalDDCData γ hs).closedForm

/-- EVERY original vertex potential represents the complete global coefficient
on its true domain, without an equality assumption on the cover's vertex choice. -/
theorem originalGuilleminClosedForm_coeff (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    ∀ (e : ComplexChart n (originalPolytopeNativeSpace γ)) (u : ComplexModel n),
      u ∈ e.val.target →
      e.val.symm u ∈ (originalPolytopeNativeModelChart γ hs v).source →
      (originalGuilleminClosedForm γ hs).val.coeff e u =
        smoothDDC (fun z => originalGuilleminVertexPotential γ hs v (e.val.symm z)) u := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  intro e u hu hv
  let p := e.val.symm u
  let t := (originalPolytopeNativeModelChart_cover γ hs p).choose
  have ht : p ∈ (originalPolytopeNativeModelChart γ hs t).source :=
    (originalPolytopeNativeModelChart_cover γ hs p).choose_spec
  let D := originalGuilleminLocalDDCData γ hs
  have hcoeff : (originalGuilleminClosedForm γ hs).val.coeff e u =
      smoothDDC (fun z => originalGuilleminVertexPotential γ hs t (e.val.symm z)) u :=
    (D.form_coeff_eventuallyEq p e hu (D.mem_domain p)).self_of_nhds
  let Ut := e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs t).source
  let Uv := e.val.target ∩ e.val.symm ⁻¹' (originalPolytopeNativeModelChart γ hs v).source
  have hUt : IsOpen Ut := e.val.isOpen_inter_preimage_symm
    (originalPolytopeNativeModelChart γ hs t).open_source
  have hUv : IsOpen Uv := e.val.isOpen_inter_preimage_symm
    (originalPolytopeNativeModelChart γ hs v).open_source
  have hsub := PositiveClasses.smoothDDC_sub (hUt.inter hUv)
    ((originalGuilleminVertexPotential_chart_smooth γ hs t e).mono inter_subset_left)
    ((originalGuilleminVertexPotential_chart_smooth γ hs v e).mono inter_subset_right)
    (z := u) ⟨⟨hu, ht⟩, hu, hv⟩
  have hzero := smoothDDC_originalGuilleminVertexPotential_sub γ hs t v e u hu ht hv
  rw [hsub] at hzero
  exact hcoeff.trans (sub_eq_zero.mp hzero)

/-- The complete global coefficient in every entire original vertex chart is
exactly the checked literal corrected Guillemin weight's normalized ddC. -/
theorem originalGuilleminClosedForm_native_coeff (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) (v : latticePolytopeVertices γ)
    (u : ComplexModel n) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    (originalGuilleminClosedForm γ hs).val.coeff (originalPolytopeNativeComplexChart γ hs v) u =
      smoothDDC (originalGuilleminGeometricNativeWeight γ hs v) u := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  have hu : u ∈ (originalPolytopeNativeModelChart γ hs v).target := by
    rw [originalPolytopeNativeModelChart_target]
    exact mem_univ u
  exact originalGuilleminClosedForm_coeff γ hs v (originalPolytopeNativeComplexChart γ hs v) u hu
    ((originalPolytopeNativeModelChart γ hs v).map_target hu)

/-- Actual native Kähler positivity follows in EVERY genuine original chart,
including every coordinate divisor; dimension zero is valid vacuously. -/
theorem isKahler_originalGuilleminClosedForm (γ : K → Fin n → ℤ)
    (hs : latticePolytopeEdgeSmooth γ) :
    letI := originalPolytopeNativeChartedSpace γ hs
    letI := originalPolytopeNativeIsComplexManifold γ hs
    (originalGuilleminClosedForm γ hs).val.IsKahler := by
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  refine ⟨?_, (originalGuilleminClosedForm γ hs).property.1⟩
  intro e u hu
  refine ⟨(originalGuilleminClosedForm γ hs).property.2 e u hu, ?_⟩
  obtain ⟨v, rfl⟩ := originalPolytopeNativeComplexChart_exhaustive γ hs e
  rw [originalGuilleminClosedForm_native_coeff]
  exact isStrictlyPositive_smoothDDC_originalGuilleminGeometricNativeWeight γ hs v u

end SGPT.Toric
