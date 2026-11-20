import SGPT.PSH.Pluripolar
import SGPT.PSH.HermitianAtlas
import SGPT.PSH.HermitianComponents
import SGPT.PSH.VariableComponentCountability
import SGPT.PSH.VariableComponentPSH

/-! Local FPT quasi-PSH germs read back from the actual native components
of the original atlas. Only proved dimension equalities transport coordinates. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter TopologicalSpace
open scoped Topology Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

universe u
variable {X : Type u} [TopologicalSpace X]

private def transportedChart {d n : ℕ} (e : OpenPartialHomeomorph X (ComplexModel d))
    (h : d = n) : OpenPartialHomeomorph X (ComplexModel n) := h ▸ e

private theorem quasiPsh_of_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (v : X → EReal)
    (h : QuasiPlurisubharmonicOn
      (fun z => v (((transportedChart e hd).subtypeRestr hU).symm z))
      ((transportedChart e hd).subtypeRestr hU).target)
    {z : ComplexModel d} (hz : z ∈ e.target) (hzU : e.symm z ∈ U) :
    QuasiPlurisubharmonicAt (fun z => v (e.symm z)) z := by
  subst n
  have hzR : z ∈ (e.subtypeRestr hU).target := by
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
      Opens.openPartialHomeomorphSubtypeCoe_target]
    exact ⟨hz, hzU⟩
  apply (h z hzR).congr
  filter_upwards [(e.subtypeRestr hU).open_target.mem_nhds hzR] with w hw
  exact congrArg v (e.subtypeRestr_symm_apply hU hw)

private theorem locallyPluripolarOn_subtypeRestr_cast {d n : ℕ}
    (e : OpenPartialHomeomorph X (ComplexModel d)) (hd : d = n)
    (U : Opens X) (hU : Nonempty U) (S : Set X)
    (hS : SGPT.Foundations.Analysis.LocallyPluripolarOn
      (e.target ∩ e.symm ⁻¹' S) e.target) :
    SGPT.Foundations.Analysis.LocallyPluripolarOn
      (((transportedChart e hd).subtypeRestr hU).target ∩
        ((transportedChart e hd).subtypeRestr hU).symm ⁻¹' (Subtype.val ⁻¹' S))
      ((transportedChart e hd).subtypeRestr hU).target := by
  subst n
  apply (hS.mono_domain (e.subtypeRestr_target_subset hU)).mono_set
  intro z hz
  refine ⟨e.subtypeRestr_target_subset hU hz.1, ?_⟩
  have hv := e.subtypeRestr_symm_apply hU hz.1
  change (((e.subtypeRestr hU).symm z : U) : X) = e.symm z at hv
  have hp : (((e.subtypeRestr hU).symm z : U) : X) ∈ S := hz.2
  rwa [hv] at hp

/-- Original local pluripolarity supplies the actual native coordinate
pole witnesses on every genuine component, including dimension zero. -/
theorem LocallyPluripolar.nativeComponent [T2Space X] [ParacompactSpace X]
    {A : VariableComplexAtlas X} {S : Set X} (hS : A.LocallyPluripolar S) (a : X) :
    letI := A.componentChartedSpace a
    letI := A.componentComplexManifold_of_paracompact a
    ManifoldLocallyPluripolar (n := A.pointDimension a)
      (Subtype.val ⁻¹' S : Set (A.componentOpen a)) := by
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  intro e
  obtain ⟨i, hi⟩ := e.property
  change SGPT.Foundations.Analysis.LocallyPluripolarOn
    (e.val.target ∩ e.val.symm ⁻¹' (Subtype.val ⁻¹' S)) e.val.target
  rw [← hi]
  exact locallyPluripolarOn_subtypeRestr_cast (A.chart i.val)
    (A.componentChartDimension a i) (A.componentOpen a) (A.componentNonempty a) S
    (hS.in_chart i.val)

/-- A native local decomposition on the same open component gives its
actual original-atlas germ. The native atlas and dimension are produced
from the original atlas, with no chart-compatibility premise added. -/
theorem localQuasiPsh_germ_of_native_component [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (a : X) (v : X → EReal) :
    letI := A.componentChartedSpace a
    letI := A.componentComplexManifold_of_paracompact a
    ManifoldQuasiPlurisubharmonic (n := A.pointDimension a)
      (fun p : A.componentOpen a => v p.val) →
    ∀ (i : A.Index) z, z ∈ (A.chart i).target →
      (A.chart i).symm z ∈ connectedComponent a →
      QuasiPlurisubharmonicAt (A.coordinate v i) z := by
  let := A.componentChartedSpace a
  let := A.componentComplexManifold_of_paracompact a
  intro hv i z hz hza
  let j : A.ComponentChartIndex a :=
    ⟨i, ⟨(A.chart i).symm z, (A.chart i).map_target hz, hza⟩⟩
  exact quasiPsh_of_subtypeRestr_cast (A.chart i) (A.componentChartDimension a j)
    (A.componentOpen a) (A.componentNonempty a) v
    (hv (A.componentComplexChart a j)) hz hza

/-- Genuine native quasi-PSH pole potentials on the actual components glue
back into the original independently dimensional atlas. No common model
dimension, finite catalogue of components, or global closed form is needed. -/
theorem glue_native_component_localQPSH_poles [T2Space X] [ParacompactSpace X]
    (A : VariableComplexAtlas X) (S : Set X)
    (hS : ∀ c : ConnectedComponents X,
      letI := A.componentChartedSpace (HermitianComponents.representative c)
      letI := A.componentComplexManifold_of_paracompact (HermitianComponents.representative c)
      ∃ u : A.componentOpen (HermitianComponents.representative c) → EReal,
        IsGlobalQuasiPshPotential (n := A.pointDimension (HermitianComponents.representative c)) u ∧
        (∀ x, u x ≤ 0) ∧
        ∀ x : A.componentOpen (HermitianComponents.representative c), (x : X) ∈ S → u x = ⊥) :
    ∃ q : X → EReal, A.IsLocalQPSH q ∧ (∀ x, q x ≤ 0) ∧ ∀ x ∈ S, q x = ⊥ := by
  classical
  choose u hu hu0 hpole using hS
  have hx (x : X) : x ∈ A.componentOpen (HermitianComponents.representative
      (x : ConnectedComponents X)) :=
    (HermitianComponents.mem_component_iff _ x).mpr rfl
  let q : X → EReal := fun x => u (x : ConnectedComponents X) ⟨x, hx x⟩
  have heq (c : ConnectedComponents X)
      (x : A.componentOpen (HermitianComponents.representative c)) : q x = u c x := by
    rcases x with ⟨x, hxc⟩
    have hc := (HermitianComponents.mem_component_iff c x).mp hxc
    subst c
    rfl
  have hq : ∀ i, QuasiPlurisubharmonicOn (A.coordinate q i) (A.chart i).target := by
    intro i z hz
    let c : ConnectedComponents X := (A.chart i).symm z
    let a : X := HermitianComponents.representative c
    let := A.componentChartedSpace a
    let := A.componentComplexManifold_of_paracompact a
    have hlocal : ManifoldQuasiPlurisubharmonic (n := A.pointDimension a)
        (fun x : A.componentOpen a => q x) := by
      simpa only [heq] using (hu c).1
    exact A.localQuasiPsh_germ_of_native_component a q hlocal i z hz (hx _)
  refine ⟨q, ⟨hq, ?_⟩, fun x => hu0 _ _, fun x hxS => hpole _ ⟨x, hx x⟩ hxS⟩
  intro x V hV hxV
  obtain ⟨y, hyV, hy⟩ := (hu (x : ConnectedComponents X)).2 ⟨x, hx x⟩
    (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val) hxV
  exact ⟨y, hyV, by rw [heq]; exact hy⟩

end SGPT.PSH.VariableComplexAtlas
