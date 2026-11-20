import SGPT.Trace.BertiniSectionMultiplication
import SGPT.Foundations.Analysis.Pending.CoherentIdealColon

/-! Internally produced finite ORIGINAL pointwise ideal-germ tests on ALL native H0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.RelativePrincipalizationSpan
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

section Finite
variable {ι W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

theorem exists_finite_submodule_tests (M : ι → Submodule ℂ W) :
    ∃ A : Finset ι, ∀ w : W, (∀ x ∈ A, w ∈ M x) ↔ ∀ x, w ∈ M x := by
  classical
  let D : Finset ι → ℕ := fun A => Module.finrank ℂ ↥(A.inf M)
  have hex : ∃ k : ℕ, ∃ A : Finset ι, D A = k := ⟨D ∅,∅,rfl⟩
  obtain ⟨A,hA⟩ := Nat.find_spec hex
  have hmin (B : Finset ι) : D A ≤ D B := by
    rw [hA]
    exact Nat.find_min' hex ⟨B,rfl⟩
  have hle (x : ι) : A.inf M ≤ M x := by
    have hsub : (insert x A).inf M ≤ A.inf M := by
      rw [Finset.inf_insert]
      exact inf_le_right
    have heq : (insert x A).inf M = A.inf M :=
      Submodule.eq_of_le_of_finrank_le hsub (hmin (insert x A))
    rw [← heq,Finset.inf_insert]
    exact inf_le_left
  refine ⟨A,fun w => ⟨?_,fun h x _ => h x⟩⟩
  intro hw x
  apply hle x
  simpa only [Finset.inf_eq_iInf,Submodule.mem_iInf] using hw

end Finite

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (E : HermitianHolomorphicLineBundle.{0,0} n X)

omit [IsComplexManifold n X] in
private theorem originalCoherent_mem_congr (A : GermIdeal n X) (hA : A.IsCoherent)
    {x : X} {f g : X → ℂ} (hf : A.mem x f) (hfg : f =ᶠ[𝓝 x] g) : A.mem x g := by
  obtain ⟨U,_hU,hx,k,s,_hs,hspan⟩ := hA x
  exact (hspan x hx g).mpr (InvertibleIdealQuotient.IsInSpanAt.congr' ((hspan x hx f).mp hf) hfg)

private theorem originalCoherent_mem_zero (A : GermIdeal n X) (hA : A.IsCoherent) (x : X) :
    A.mem x (fun _ => 0) := by
  obtain ⟨U,_hU,hx,k,s,_hs,hspan⟩ := hA x
  exact (hspan x hx _).mpr BlowupStrictIdeal.isInSpanAt_zero

omit [IsComplexManifold n X] in
private theorem originalCoherent_mem_add (A : GermIdeal n X) (hA : A.IsCoherent)
    {x : X} {f g : X → ℂ} (hf : A.mem x f) (hg : A.mem x g) :
    A.mem x (fun y => f y + g y) := by
  obtain ⟨U,_hU,hx,k,s,_hs,hspan⟩ := hA x
  exact (hspan x hx _).mpr (IsInSpanAt.add ((hspan x hx f).mp hf) ((hspan x hx g).mp hg))

omit [IsComplexManifold n X] in
private theorem originalCoherent_mem_mul (A : GermIdeal n X) (hA : A.IsCoherent)
    {x : X} {f g : X → ℂ} (hf : HolomorphicAt n f x) (hg : A.mem x g) :
    A.mem x (fun y => f y * g y) := by
  obtain ⟨U,_hU,hx,k,s,_hs,hspan⟩ := hA x
  exact (hspan x hx _).mpr (IsInSpanAt.mul_left hf ((hspan x hx g).mp hg))

def nativePointIdealSections (A : GermIdeal n X) (hA : A.IsCoherent) (x : X) :
    Submodule ℂ (HolomorphicSections (n := n) E.Fiber) where
  carrier := {S | A.mem x (sectionCoefficient E.Fiber (preferredOriginalFrame E.Fiber x).val S)}
  zero_mem' := by
    let e := preferredOriginalFrame E.Fiber x
    have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    apply originalCoherent_mem_congr A hA (originalCoherent_mem_zero A hA x)
    filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
    change 0 = (e.val.linearEquivAt ℂ y hy) 0
    exact (map_zero _).symm
  add_mem' := by
    intro S T hS hT
    let e := preferredOriginalFrame E.Fiber x
    have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    apply originalCoherent_mem_congr A hA (originalCoherent_mem_add A hA hS hT)
    filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
    change (e.val.linearEquivAt ℂ y hy) (S y) + (e.val.linearEquivAt ℂ y hy) (T y) =
      (e.val.linearEquivAt ℂ y hy) (S y + T y)
    exact (map_add _ _ _).symm
  smul_mem' := by
    intro c S hS
    let e := preferredOriginalFrame E.Fiber x
    have hx : x ∈ e.val.baseSet := mem_baseSet_trivializationAt ℂ _ _
    apply originalCoherent_mem_congr A hA (originalCoherent_mem_mul A hA (holomorphicAt_const c) hS)
    filter_upwards [e.val.open_baseSet.mem_nhds hx] with y hy
    change c * (e.val.linearEquivAt ℂ y hy) (S y) = (e.val.linearEquivAt ℂ y hy) (c • S y)
    exact (map_smul (e.val.linearEquivAt ℂ y hy) c (S y)).symm

variable [CompactSpace X]

theorem exists_finite_nativeIdealSection_tests (A : GermIdeal n X) (hA : A.IsCoherent) :
    ∃ F : Finset X, ∀ S : HolomorphicSections (n := n) E.Fiber,
      S ∈ fullHolomorphicIdealSections (n := n) E.Fiber A ↔
      ∀ x ∈ F, A.mem x (sectionCoefficient E.Fiber (preferredOriginalFrame E.Fiber x).val S) := by
  let := holomorphicSections_finiteDimensional (n := n) E.Fiber
  obtain ⟨F,hF⟩ := exists_finite_submodule_tests (nativePointIdealSections E A hA)
  refine ⟨F,fun S => ?_⟩
  rw [fullHolomorphicIdealSections_iff_preferredCoefficient (n := n) E.Fiber A hA S]
  exact (hF S).symm

theorem exists_finite_nativeMultiplier_tests {φ : X → EReal}
    (hφ : IsGlobalQuasiPshPotential (n := n) φ) :
    ∃ F : Finset X, ∀ S : HolomorphicSections (n := n) E.Fiber,
      S ∈ fullHolomorphicIdealSections (n := n) E.Fiber (sourceDegreeMultiplierIdeal (n := n) 1 φ) ↔
      ∀ x ∈ F, (sourceDegreeMultiplierIdeal (n := n) 1 φ).mem x
        (sectionCoefficient E.Fiber (preferredOriginalFrame E.Fiber x).val S) :=
  exists_finite_nativeIdealSection_tests E (sourceDegreeMultiplierIdeal (n := n) 1 φ)
    (sourceDegreeMultiplierIdeal_isCoherent 1 hφ)

end SGPT.Trace.Bertini
