import SGPT.Foundations.Analysis.Pending.AnalyticModificationStrongPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshPushforward
import SGPT.Foundations.Analysis.Pending.PshAnalyticRemovable
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false

/-! # Literal potential descent under actual general analytic modifications -/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent

open FirstPass FirstPass.PositiveClasses AnalyticModificationLocalDiscrepancy
  AnalyticModificationStrongPullback ModificationMassInvariance GlobalPotentialPullback
  ThetaPshCodimTwoExtension PshAnalyticSetExtension

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Fixed-form raw PSH representatives agreeing off a genuine analytic
empty-interior set agree literally everywhere, including poles. -/
theorem eq_of_eq_off_analytic_set {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) (hAi : interior A = ∅)
    {θ : SmoothRealForm n X 2} {u v : X → EReal}
    (hu : ThetaPlurisubharmonic θ u) (hv : ThetaPlurisubharmonic θ v)
    (heq : ∀ x ∉ A, u x = v x) (x : X) : u x = v x := by
  let e := complexChartAt (n := n) x
  have hxe : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  obtain ⟨W, ρ, hxW, hρ, hpu⟩ := hu e (e.val x) hxe
  have hpv := ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic
    hv e hρ
  obtain ⟨r, hr, hBW⟩ := Metric.isOpen_iff.mp hρ.1 _ hxW
  let B := ball (e.val x) r
  have hnull : volume (pluripolarChartSet A e) = 0 :=
    (manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA hAi).chart_measure_eq_zero e volume
  have hae : (fun z => chartFunction u e z + (ρ z : EReal)) =ᵐ[volume.restrict B]
      (fun z => chartFunction v e z + (ρ z : EReal)) := by
    have hcompl : ∀ᵐ z ∂(volume.restrict B), z ∉ pluripolarChartSet A e := by
      refine measure_eq_zero_iff_ae_notMem.mp ?_
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hnull) bot_le
    filter_upwards [hcompl, ae_restrict_mem isOpen_ball.measurableSet] with z hz hzB
    have hzt : z ∈ e.val.target := hρ.2.1 (hBW hzB)
    have hzA : e.val.symm z ∉ A := fun h => hz ⟨hzt, h⟩
    simp only [chartFunction, heq _ hzA]
  have hEq := PlurisubharmonicOn.eqOn_of_ae_eq
    (fun z hz => hpu z (hBW hz)) (fun z hz => hpv z (hBW hz))
    isOpen_ball volume hae (mem_ball_self hr)
  have hleft : e.val.symm (e.val x) = x := e.val.left_inv (mem_complexChartAt_source x)
  simp only [chartFunction, hleft] at hEq
  have h := congrArg (fun a => a - ((ρ (e.val x) : ℝ) : EReal)) hEq
  simpa only [EReal.add_sub_cancel_right] using h

/-- Genuine potential descent under actual general modifications.
The upper bound, extension, nondegeneracy, and all-fiber equality are produced. -/
theorem exists_descent_of_isAnalyticModification [CompactSpace X]
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : ClosedRealOneOneForm n X) {w : Y → EReal}
    (hw : IsThetaPshPotential (ClosedRealOneOneForm.pullback hπ.1 θ).val w) :
    ∃ ψ : X → EReal, IsThetaPshPotential θ.val ψ ∧ ∀ y, ψ (π y) = w y := by
  classical
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  have hsurj := surjective_of_isAnalyticModification hπ
  rcases isEmpty_or_nonempty Y with hY | hY
  · have hX : IsEmpty X := ⟨fun x => by
      obtain ⟨y, -⟩ := hsurj x
      exact hY.false y⟩
    refine ⟨fun _ => ⊥, ⟨?_, ?_⟩, ?_⟩
    · intro e z _
      exact (hX.false (e.val.symm z)).elim
    · intro x
      exact (hX.false x).elim
    · intro y
      exact (hY.false y).elim
  obtain ⟨B, hBc, hBa, hBi, hAa, hAi, hiso⟩ :=
    exists_isIsomorphismOver_of_isAnalyticModification hπ
  let A := π ⁻¹' B
  have hAc : IsClosed A := hBc.preimage hπ.1.continuous
  let s := invOver π Bᶜ
  have hsg (y : Y) (hy : π y ∉ B) : s (π y) = y := invOver_apply hiso hy
  have hgs (x : X) (hx : x ∉ B) : π (s x) = x := (invOver_mem hiso hx).2
  have hnonexc (y : Y) (hy : π y ∉ B) : y ∉ FirstPass.BlowupSequences.exceptionalLocus n π :=
    fun he => Set.disjoint_left.mp hiso.2 hy he
  have hr : ∀ y, π y ∉ B → ∀ e : ComplexChart n Y, y ∈ e.val.source →
      ∃ W : Set (ComplexModel n), e.val y ∈ W ∧
        IsSmoothLocalPotential
          ((ClosedRealOneOneForm.pullback hπ.1 θ) - ClosedRealOneOneForm.pullback hπ.1 θ).val
          e W (fun z => (fun _ : Y => (0 : ℝ)) (e.val.symm z)) := by
    intro y _ e hye
    refine ⟨e.val.target, e.val.map_source hye, ?_⟩
    rw [sub_self]
    exact FirstPass.LocalPotentials.localPotential_zero e e.val.open_target subset_rfl
  let v := fun x => w (s x)
  have hoff : ThetaPshOff θ.val B v := by
    simpa only [EReal.coe_zero, add_zero] using
      ThetaPshPushforward.thetaPshOff_comp_section (θY := θ)
        (θZ := ClosedRealOneOneForm.pullback hπ.1 θ) (r := fun _ : Y => (0 : ℝ))
        hπ.1 hBc hnonexc hsg hgs hw.1 hr
  obtain ⟨C, hC⟩ := hw.exists_global_upper_bound
  have hbound : LocallyBoundedAboveOff B v :=
    fun _ => ⟨univ, Filter.univ_mem, C, fun y _ _ => hC (s y)⟩
  let ψ := extensionAcross B v
  have hψ : ThetaPlurisubharmonic θ.val ψ :=
    thetaPlurisubharmonic_extensionAcross_of_localClosure hBc hoff
      (PshAnalyticRemovable.thetaPshLocalClosure_of_isComplexAnalyticSubset
        (Pending.LocalPotentials.closedRealOneOne_hasLocalPotentials θ) hBa hoff hbound)
  have heoff (y : Y) (hy : y ∉ A) : ψ (π y) = w y := by
    change extensionAcross B v (π y) = w y
    rw [extensionAcross_eq_of_notMem hBc hoff hy]
    change w (s (π y)) = w y
    rw [hsg y hy]
  have hnd : LocallyNondegenerate ψ := by
    intro x O hO hxO
    obtain ⟨y, hxy⟩ := hsurj x
    have hO' : IsOpen (π ⁻¹' O) := hO.preimage hπ.1.continuous
    have hyO : y ∈ π ⁻¹' O := by change π y ∈ O; rwa [hxy]
    have hnot : ¬ π ⁻¹' O ⊆ A := by
      intro hsub
      have h := interior_maximal hsub hO'
      rw [hAi] at h
      exact h hyO
    obtain ⟨y₀, hy₀O, hy₀A⟩ := not_subset.mp hnot
    have hU : IsOpen (π ⁻¹' O ∩ Aᶜ) := hO'.inter hAc.isOpen_compl
    obtain ⟨y₁, hy₁, hy₁fin⟩ := hw.2 y₀ _ hU ⟨hy₀O, hy₀A⟩
    exact ⟨π y₁, hy₁.1, by rw [heoff y₁ hy₁.2]; exact hy₁fin⟩
  refine ⟨ψ, ⟨hψ, hnd⟩, ?_⟩
  exact eq_of_eq_off_analytic_set hAa hAi (thetaPlurisubharmonic_comp hπ.1 hψ) hw.1 heoff

end
end SGPT.Foundations.Analysis.Pending.AnalyticModificationPotentialDescent
