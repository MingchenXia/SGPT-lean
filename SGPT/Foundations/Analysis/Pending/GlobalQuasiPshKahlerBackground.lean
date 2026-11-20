import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshSmoothLocalization
import SGPT.Foundations.Analysis.Pending.SmoothDDCForm

set_option autoImplicit false

/-! # Actual compact local quasi-PSH germs produce a uniform Kähler background -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground

open FirstPass FirstPass.PositiveClasses GlobalQuasiPshSmoothLocalization SmoothDDCForm

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Actual local quasi-PSH germs supply a single positive smooth Kähler
background, including raw negative-infinite germs and zero dimension. -/
theorem exists_pos_thetaPlurisubharmonic_smul (omega : KahlerBackground n M)
    {u : M → EReal} (hu : ManifoldQuasiPlurisubharmonic (n := n) u) :
    ∃ C : ℝ, 0 < C ∧ ThetaPlurisubharmonic (C • omega.form).val u := by
  classical
  choose H hH S hS hxS hp using fun x : M =>
    exists_chartSmooth_local_psh_correction hu x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover S hS
    (fun x _ => mem_iUnion.mpr ⟨x, hxS x⟩)
  obtain ⟨C, hC, _, hCH⟩ := exists_pos_thetaPlurisubharmonic_smooth omega
    (fun _ : s => (0 : ClosedRealOneOneForm n M))
    (fun i : s => H i.val) (fun i => hH i.val)
  have hHC (i : s) : ThetaPlurisubharmonic (C • omega.form).val
      (fun x => (H i.val x : EReal)) := by
    simpa only [zero_add] using hCH i
  refine ⟨C, hC, ?_⟩
  intro e z hz
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ (e.val.symm z)))
  obtain ⟨hxs, hzS⟩ := mem_iUnion.mp hx
  let i : s := ⟨x, hxs⟩
  obtain ⟨V, ρ, hzV, hρ, hHV⟩ := hHC i e z hz
  obtain ⟨W, hWo, hzW, hqW⟩ := hp x e z hz hzS
  have hsum := (hqW.plurisubharmonicOn hWo).mono inter_subset_right |>.add
    (hHV.mono (show V ∩ W ⊆ V from inter_subset_left))
  have heq : (fun y => chartFunction (fun a => u a - (H x a : EReal)) e y +
      (chartFunction (fun a => (H i.val a : EReal)) e y + (ρ y : EReal))) =
      (fun y => chartFunction u e y + (ρ y : EReal)) := by
    funext y
    change (u (e.val.symm y) - (H x (e.val.symm y) : EReal)) +
      ((H x (e.val.symm y) : EReal) + (ρ y : EReal)) = _
    rw [← add_assoc, EReal.sub_add_cancel]
    rfl
  rw [heq] at hsum
  exact ⟨V ∩ W, ρ, ⟨hzV, hzW⟩,
    hρ.mono (hρ.1.inter hWo) inter_subset_left, hsum⟩

/-- The same internally produced background preserves genuine local
nondegeneracy of a global quasi-PSH potential. -/
theorem exists_pos_isThetaPshPotential_smul (omega : KahlerBackground n M)
    {u : M → EReal} (hu : IsGlobalQuasiPshPotential (n := n) u) :
    ∃ C : ℝ, 0 < C ∧ IsThetaPshPotential (C • omega.form).val u := by
  obtain ⟨C, hC, hCu⟩ := exists_pos_thetaPlurisubharmonic_smul omega hu.1
  exact ⟨C, hC, hCu, hu.2⟩

/-- The genuine local PSH-plus-smooth domain agrees with the actual
closed-background domain on compact Kähler manifolds. -/
theorem isGlobalQuasiPshPotential_iff_exists_closed_background
    (omega : KahlerBackground n M) (u : M → EReal) :
    IsGlobalQuasiPshPotential (n := n) u ↔
      ∃ θ : ClosedRealOneOneForm n M, IsThetaPshPotential θ.val u := by
  constructor
  · intro hu
    obtain ⟨C, _, hCu⟩ := exists_pos_isThetaPshPotential_smul omega hu
    exact ⟨C • omega.form, hCu⟩
  · rintro ⟨θ, hu⟩
    exact hu.quasiPshPotential

end

end SGPT.Foundations.Analysis.Pending.GlobalQuasiPshKahlerBackground
