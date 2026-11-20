import SGPT.PSH.VariableComponentPSH
import SGPT.PSH.VariableComponentCountability
import SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
open scoped Topology Manifold ContDiff ENNReal

universe u
variable {X : Type u} [TopologicalSpace X] (A : VariableComplexAtlas X)

private def lelongTransportChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem squaredLog_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (u : X → EReal) (p : U)
    (hp : p.val ∈ e.source) :
    squaredLogLelongNumber (n := d) (u ∘ e.symm) (e p.val) =
      squaredLogLelongNumber (n := n)
        ((u ∘ Subtype.val) ∘ ((lelongTransportChart e hd).subtypeRestr hU).symm)
        (((lelongTransportChart e hd).subtypeRestr hU) p) := by
  subst n
  change squaredLogLelongNumber (n := d) (u ∘ e.symm) (e p.val) =
    squaredLogLelongNumber (n := d) ((u ∘ Subtype.val) ∘ (e.subtypeRestr hU).symm)
      (e p.val)
  apply squaredLogLelongNumber_congr
  filter_upwards [(e.subtypeRestr hU).open_target.mem_nhds (e.map_subtype_source hU hp)]
    with z hz
  exact congrArg u (e.subtypeRestr_symm_apply hU hz).symm

/-- The same original point reader in an actual native restricted component chart. -/
theorem sourceLelong_componentChart_eq (u : X → EReal) (x : X)
    (i : A.ComponentChartIndex x) (p : A.componentOpen x)
    (hp : p ∈ (A.componentChart x i).source) :
    letI := A.componentChartedSpace x
    A.sourceLelong u p.val = squaredLogLelongNumber (n := A.pointDimension x)
      (chartFunction (fun q : A.componentOpen x ↦ u q.val) (A.componentComplexChart x i))
      ((A.componentChart x i) p) := by
  let := A.componentChartedSpace x
  have hi : p.val ∈ (A.chart i.val).source := by
    simpa only [A.componentChart_source x i, mem_preimage] using hp
  rw [A.sourceLelong_eq_chart u p.val i.val hi]
  exact squaredLog_subtypeRestr_cast (A.chart i.val) (A.componentChartDimension x i)
    (A.componentOpen x) (A.componentNonempty x) u p hi

/-- The book's original point reader equals the genuine same-component squared-log reader. -/
theorem sourceLelong_component_eq [T2Space X] [ParacompactSpace X]
    (u : X → EReal) (x : X) (p : A.componentOpen x) :
    letI := A.componentChartedSpace x
    A.sourceLelong u p.val = squaredLogLelongNumber (n := A.pointDimension x)
      (fun q : A.componentOpen x ↦ u q.val) p := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  obtain ⟨i, hi⟩ := A.componentChart_cover x p
  let e := A.componentComplexChart x i
  calc
    A.sourceLelong u p.val = squaredLogLelongNumber (n := A.pointDimension x)
        (chartFunction (fun q : A.componentOpen x ↦ u q.val) e) (e.val p) :=
      A.sourceLelong_componentChart_eq u x i p hi
    _ = (ofFixedModel (A.pointDimension x) (A.componentOpen x)).sourceLelong
        (fun q : A.componentOpen x ↦ u q.val) p :=
      ((ofFixedModel (A.pointDimension x) (A.componentOpen x)).sourceLelong_eq_chart
        (fun q : A.componentOpen x ↦ u q.val) p e hi).symm
    _ = squaredLogLelongNumber (n := A.pointDimension x)
        (fun q : A.componentOpen x ↦ u q.val) p := sourceLelong_ofFixedModel_eq _ _

variable {A}

/-- Original source PSH internally produces all actual native quasi-PSH chart germs. -/
theorem IsPSH.componentQuasiPlurisubharmonic [T2Space X] [ParacompactSpace X]
    {u : X → EReal} (hu : A.IsPSH u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ManifoldQuasiPlurisubharmonic (n := A.pointDimension x)
      (fun q : A.componentOpen x ↦ u q.val) := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro e z hz
  exact (hu.componentChartPlurisubharmonic x e z hz).quasiPlurisubharmonicAt

variable (A)

/-- Exact original squared-log normalization, with all infinite values retained. -/
theorem sourceLelong_component_native_eq [T2Space X] [ParacompactSpace X]
    (u : X → EReal) (x : X) (hn : A.pointDimension x ≠ 0) (p : A.componentOpen x) :
    letI := A.componentChartedSpace x
    lelongNumber (n := A.pointDimension x) (fun q : A.componentOpen x ↦ u q.val) p =
      2 * A.sourceLelong u p.val := by
  let := A.componentChartedSpace x
  rw [lelongNumber_eq_two_mul_squaredLog hn, A.sourceLelong_component_eq u x p]

variable {A}

/-- Genuine analytic minimum on the whole SAME actual native component carrier. -/
theorem IsPSH.exists_sourceLelong_component_minimum [T2Space X] [ParacompactSpace X]
    {u : X → EReal} (hu : A.IsPSH u) (x : X) :
    letI := A.componentChartedSpace x
    letI := A.componentComplexManifold_of_paracompact x
    ∀ (V : ClosedIrreducibleAnalyticSubvariety (A.pointDimension x) (A.componentOpen x))
      (U : Set (A.componentOpen x)), IsOpen U → (V.carrier ∩ U).Nonempty →
      ∃ p ∈ V.carrier ∩ U, A.sourceLelong u p.val =
        ⨅ q ∈ V.carrier, A.sourceLelong u q.val := by
  let := A.componentChartedSpace x
  let := A.componentComplexManifold_of_paracompact x
  intro V U hU hVU
  obtain ⟨p, hp, hmin⟩ :=
    SGPT.Foundations.Analysis.Pending.SourceGenericPrimeIdealOrder.exists_source_minimum_on_open_piece
      (hu.componentQuasiPlurisubharmonic x) V hU hVU
  refine ⟨p, hp, ?_⟩
  simpa only [← A.sourceLelong_component_eq u x] using hmin

end SGPT.PSH.VariableComplexAtlas
