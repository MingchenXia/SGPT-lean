import SGPT.PSH.VariableAtlas
import SGPT.Foundations.Analysis.FirstPass.QuasiPshSingularities

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Real smooth corrections preserve the pole set locally, so genuine
quasi-PSH coordinate germs produce an open closure of the actual finite locus. -/
theorem isOpen_closure_nonbot_of_local_coordinate_quasiPSH {u : X → EReal}
    (hlocal : ∀ x : X, ∃ d : ℕ, ∃ e : OpenPartialHomeomorph X (ComplexModel d),
      x ∈ e.source ∧ QuasiPlurisubharmonicAt (u ∘ e.symm) (e x)) :
    IsOpen (closure {x | u x ≠ ⊥}) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨d, e, hxe, p, b, ⟨P, hP, hexP, hpP⟩, _hsm, heq⟩ := hlocal x
  obtain ⟨G, hGsub, hG, hexG⟩ := _root_.mem_nhds_iff.mp heq
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ((hP.inter hG).inter e.open_target)
    (e x) ⟨⟨hexP, hexG⟩, e.map_source hxe⟩
  have hBt : ball (e x) r ⊆ e.target := fun _ hz => (hball hz).2
  let U := e.source ∩ e ⁻¹' ball (e x) r
  have hU : IsOpen U := e.isOpen_inter_preimage isOpen_ball
  have hxU : x ∈ U := ⟨hxe, mem_ball_self hr⟩
  have heqU : ∀ y ∈ U, u y = p (e y) + (b (e y) : EReal) := by
    intro y hy
    have h := hGsub (hball hy.2).1.2
    change u (e.symm (e y)) = p (e y) + (b (e y) : EReal) at h
    simpa only [Function.comp_apply, e.left_inv hy.1] using h
  obtain ⟨v, hvU, hvne⟩ := _root_.mem_closure_iff.mp hx U hU hxU
  have hvp : p (e v) ≠ ⊥ := by
    change u v ≠ ⊥ at hvne
    rw [heqU v hvU] at hvne
    exact (EReal.add_ne_bot_iff.mp hvne).1
  have hpB : DiscPshOn p (ball (e x) r) := hpP.mono (fun _ hz => (hball hz).1.1)
  have hlift : EqOn p ((p ∘ e) ∘ e.symm) (ball (e x) r) := by
    intro z hz
    simp only [Function.comp_apply, e.right_inv (hBt hz)]
  have hwB : PSHOn ((p ∘ e) ∘ e.symm) (ball (e x) r) :=
    ⟨hpB.congr hlift, e v, hvU.2, by
      change p (e (e.symm (e v))) ≠ ⊥
      rwa [e.right_inv (e.map_source hvU.1)]⟩
  apply mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  apply _root_.mem_closure_iff.mpr
  intro O hO hyO
  obtain ⟨z, hzUO, hzfinite⟩ := exists_ne_bot_in_open_of_coordinate_psh e hy.1
    isOpen_ball (isConnected_ball hr) hy.2 hwB (hU.inter hO) ⟨hy, hyO⟩
  refine ⟨z, hzUO.2, ?_⟩
  change u z ≠ ⊥
  rw [heqU z hzUO.1]
  exact EReal.add_ne_bot_iff.mpr ⟨hzfinite, EReal.coe_ne_bot _⟩

/-- An actual non-pole point on each original connected component propagates
through quasi-PSH germs to finite points in every original open neighborhood. -/
theorem locallyNondegenerate_of_component_nonbot_of_local_coordinate_quasiPSH
    {u : X → EReal}
    (hlocal : ∀ x : X, ∃ d : ℕ, ∃ e : OpenPartialHomeomorph X (ComplexModel d),
      x ∈ e.source ∧ QuasiPlurisubharmonicAt (u ∘ e.symm) (e x))
    (hn : ∀ x : X, ∃ y ∈ connectedComponent x, u y ≠ ⊥) :
    LocallyNondegenerate u := by
  have hopen := isOpen_closure_nonbot_of_local_coordinate_quasiPSH hlocal
  intro x O hO hxO
  obtain ⟨y, hy, hyf⟩ := hn x
  have hsub : connectedComponent x ⊆ closure {z | u z ≠ ⊥} :=
    isPreconnected_connectedComponent.subset_of_closure_inter_subset hopen
      ⟨y, hy, subset_closure hyf⟩ (by simpa only [closure_closure] using
        (Set.inter_subset_left : closure {z | u z ≠ ⊥} ∩ connectedComponent x ⊆
          closure {z | u z ≠ ⊥}))
  obtain ⟨z, hzO, hzf⟩ := _root_.mem_closure_iff.mp (hsub mem_connectedComponent) O hO hxO
  exact ⟨z, hzO, hzf⟩

namespace VariableComplexAtlas

variable {A : VariableComplexAtlas X}

/-- The same component principle on independently dimensional original charts.
No local nondegeneracy or background witness is a caller premise. -/
theorem locallyNondegenerate_of_component_nonbot_of_chart_quasiPSH
    {u : X → EReal}
    (hu : ∀ i, QuasiPlurisubharmonicOn (A.coordinate u i) (A.chart i).target)
    (hn : ∀ x : X, ∃ y ∈ connectedComponent x, u y ≠ ⊥) :
    LocallyNondegenerate u := by
  apply locallyNondegenerate_of_component_nonbot_of_local_coordinate_quasiPSH _ hn
  intro x
  obtain ⟨i, hx⟩ := A.cover x
  exact ⟨A.dimension i, A.chart i, hx, hu i _ ((A.chart i).map_source hx)⟩

end VariableComplexAtlas
end SGPT.PSH
