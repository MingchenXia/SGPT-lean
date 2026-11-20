import SGPT.Foundations.Analysis.Pending.CompactVariableCurrentTests
import SGPT.Foundations.Analysis.FirstPass.GlobalCurrents

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.FullGeometricCurrentPositivityGluing

open FirstPass StronglyPositiveForms
  _root_.SGPT.Foundations.Analysis.LocalCurrents



private theorem nonnegative_of_local_tests {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Opens (ComplexModel n)}
    (P : F → Prop) (hP : ∀ c : ℝ, 0 ≤ c → ∀ v, P v → P (c • v))
    (T : 𝓓(U, F) →L[ℝ] ℝ)
    (hloc : ∀ x ∈ U, ∃ (V : Opens (ComplexModel n)) (_hVU : V ≤ U), x ∈ V ∧
      ∀ β : 𝓓(V, F), (∀ y, P (β y)) → 0 ≤ T (TestFunction.monoCLM ℝ β : 𝓓(U, F)))
    (α : 𝓓(U, F)) (hα : ∀ x, P (α x)) : 0 ≤ T α := by
  classical
  let K : Set (ComplexModel n) := tsupport α
  have hK : IsCompact K := α.hasCompactSupport
  have hKU : K ⊆ U := α.tsupport_subset
  choose W hWU hxW hpos using fun x : U => hloc x x.property
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : U => (W x : Set (ComplexModel n)))
    (fun x => (W x).isOpen) (fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hxW ⟨x, hKU hx⟩⟩)
  let J := ↥s
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, ComplexModel n)) hK.isClosed
    (fun a : J => (W a.val : Set (ComplexModel n))) (fun a => (W a.val).isOpen) (by
      intro x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hx)
      obtain ⟨has, hxa⟩ := mem_iUnion.mp ha
      exact mem_iUnion.mpr ⟨⟨a, has⟩, hxa⟩)
  let ψ (a : J) : 𝓓(W a.val, F) :=
    ⟨fun x => ρ a x • α x,
      (ρ a).contMDiff.contDiff.smul α.contDiff,
      α.hasCompactSupport.smul_left,
      (tsupport_smul_subset_left (ρ a) α).trans (hρ a)⟩
  let Ψ (a : J) : 𝓓(U, F) := TestFunction.monoCLM ℝ (ψ a)
  have hΨ : ∀ a : J, ∀ x, Ψ a x = ρ a x • α x := by
    intro a x
    have hi := TestFunction.monoCLM_apply (𝕜 := ℝ) (n₂ := ⊤) (Ω₂ := U) (ψ a)
    change (TestFunction.monoCLM ℝ (ψ a) : 𝓓(U, F)) x = ψ a x
    simpa only [le_refl, hWU a.val, and_self, ↓reduceIte] using congrFun hi x
  have hsum_apply : ∀ t : Finset J, ∀ x : ComplexModel n,
      (∑ a ∈ t, Ψ a) x = ∑ a ∈ t, ρ a x • α x := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro x; rfl
    | @insert a t ha ih =>
        intro x
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        change Ψ a x + (∑ b ∈ t, Ψ b) x =
          ρ a x • α x + ∑ b ∈ t, ρ b x • α x
        rw [ih x, hΨ a x]
  have hsum : α = ∑ a : J, Ψ a := by
    apply TestFunction.ext
    intro x
    rw [hsum_apply, ← Finset.sum_smul]
    by_cases hx : x ∈ K
    · have hone : ∑ a : J, ρ a x = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hone, one_smul]
    · have hzero : α x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hzero, smul_zero]
  have hn : ∀ a : J, 0 ≤ T (Ψ a) := by
    intro a
    apply hpos a.val (ψ a)
    intro x
    exact hP (ρ a x) (ρ.nonneg a x) (α x) (hα x)
  rw [hsum, map_sum]
  exact Finset.sum_nonneg fun a _ => hn a

/-- Local full-form positivity implies positivity of the actual compact-test functional. -/
theorem nonnegative_of_local_full_tests {n q : ℕ} {U : Opens (ComplexModel n)}
    (T : 𝓓(U, RealForm n (2 * q)) →L[ℝ] ℝ)
    (hloc : ∀ x ∈ U, ∃ (V : Opens (ComplexModel n)) (_hVU : V ≤ U), x ∈ V ∧
      ∀ β : 𝓓(V, RealForm n (2 * q)), (∀ y, β y ∈ spCone (n := n) q) →
        0 ≤ T (TestFunction.monoCLM ℝ β : 𝓓(U, RealForm n (2 * q))))
    (α : 𝓓(U, RealForm n (2 * q))) (hα : ∀ x, α x ∈ spCone (n := n) q) : 0 ≤ T α := by
  exact nonnegative_of_local_tests (fun v => v ∈ spCone (n := n) q)
    (fun c hc v hv => smul_mem_spCone hv hc) T hloc α hα

end SGPT.Foundations.Analysis.Pending.FullGeometricCurrentPositivityGluing
