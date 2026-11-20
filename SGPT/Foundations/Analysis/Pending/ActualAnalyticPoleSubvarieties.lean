import SGPT.Foundations.Analysis.Pending.ActualCompactAnalyticGlobalComponents
import SGPT.Foundations.Analysis.Pending.StrictTransformLocus

set_option autoImplicit false

/-! # Finite genuine polar subvarieties of positive codimension

The weak smooth-off-pole analytic convention suffices for the actual polar
geometry. Its current Lebesgue/Siu decomposition is a separate target.
-/

noncomputable section
open Set
namespace SGPT.Foundations.Analysis.Pending.ActualAnalyticPoleSubvarieties
open FirstPass FirstPass.NumericalRestrictedVolumeScaffold
  ActualCompactAnalyticGlobalComponents

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem regular_dimension_lt_ambient_of_poles {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u) {B : Set M}
    (hBP : B ⊆ poleSet u) {x : M} {k : ℕ}
    (hk : RegularAtDim (n := n) B x k) : k < n := by
  have hkn := hk.1
  have hne : k ≠ n := by
    intro heq
    subst k
    let e := complexChartAt (n := n) x
    obtain ⟨Φ, hsub, _hcenter, hflat⟩ := hk.2.2
    obtain ⟨w, hw, hwu⟩ := hu.2.exists_chart_ne_bot e Φ.isOpen_source hsub
      (z := e.val x) Φ.center_mem_source
    have hwt : w ∈ e.val.target := hsub hw
    have hys : e.val.symm w ∈ e.val.source := e.val.map_target hwt
    have hyΦ : e.val (e.val.symm w) ∈ Φ.source := by
      rw [e.val.right_inv hwt]
      exact hw
    have hplane : Φ.toFun (e.val (e.val.symm w)) ∈ complexCoordinatePlane n n := by
      intro i hi
      exact (not_le_of_gt i.isLt hi).elim
    have hyB : e.val.symm w ∈ B := (hflat hys hyΦ).mpr hplane
    apply hwu
    exact hBP hyB
  omega

/-- Natural analytic quasi-PSH inputs internally produce every genuine finite
polar subvariety and its actual dimension strictly below the ambient one. -/
theorem exists_finite_polar_subvarieties [CompactSpace M] {u : M → EReal}
    (hu : IsGlobalQuasiPshPotential (n := n) u)
    (han : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u) :
    ∃ (N : ℕ) (V : Fin N → ClosedIrreducibleAnalyticSubvariety n M),
      Function.Injective (fun j => (V j).carrier) ∧
      range (fun j => (V j).carrier) = GlobalComponents.globalComponents (n := n) (poleSet u) ∧
      (∀ j, (V j).carrier ⊆ poleSet u ∧ (V j).dim < n) ∧
      (⋃ j, (V j).carrier) = poleSet u := by
  classical
  have hP := StrictTransformLocus.isComplexAnalyticSubset_poleSet_of_smoothOffPole han
  obtain ⟨N, B, hinj, hrange, hB, hunion⟩ := exists_finite_exact_global_components hP
  have hregular : ∀ j, ∃ x k, RegularAtDim (n := n) (B j) x k := by
    intro j
    obtain ⟨y, hy⟩ := (hB j).2.2
    obtain ⟨x, _hx, k, hk⟩ := RegularLocusDense.exists_regularAtDim_mem_of_isOpen
      (hB j).1.analytic isOpen_univ hy (mem_univ y)
    exact ⟨x, k, hk⟩
  choose x k hk using hregular
  let V : Fin N → ClosedIrreducibleAnalyticSubvariety n M := fun j =>
    { carrier := B j
      isClosed_carrier := (hB j).1.analytic.isClosed
      irreducible_carrier := (hB j).1
      dim := k j
      dim_le := (hk j).1
      regularLocus_nonempty := ⟨x j, hk j⟩ }
  refine ⟨N, V, hinj, hrange, ?_, hunion⟩
  intro j
  exact ⟨(hB j).2.1, regular_dimension_lt_ambient_of_poles hu (hB j).2.1 (hk j)⟩

end SGPT.Foundations.Analysis.Pending.ActualAnalyticPoleSubvarieties
