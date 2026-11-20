import SGPT.Foundations.Analysis.Pending.SingularSubgeodesicProductLocalPsh
import SGPT.Foundations.Analysis.Pending.PrincipalizationGluingLocalAssembly
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-! # Actual product reference PSH and joint subgeodesic assembly -/

open Set
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ProductPshAssembly

open scoped ProductComplexManifold
open FirstPass FirstPass.AnalyticGluingData ProductComplexManifold

noncomputable section

/-- The open first projection supplies actual local nondegeneracy; semipositivity
of the vertical background then enlarges the true pulled-back PSH background. -/
theorem isThetaPshPotential_product_reference {n m : ℕ} {M T : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace T] [ChartedSpace (ComplexModel m) T] [IsComplexManifold m T]
    (θ : ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm m T)
    {φ : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hκ : κ.val.IsSemipositive) :
    IsThetaPshPotential (prodForm θ κ).val (fun p : M × T => φ p.1) := by
  have hne : LocallyNondegenerate (fun p : M × T => φ p.1) := by
    intro p O hO hp
    obtain ⟨x, hx, hxfin⟩ := hφ.2 p.1 (Prod.fst '' O)
      (isOpenMap_fst O hO) ⟨p, hp, rfl⟩
    obtain ⟨p', hp', rfl⟩ := hx
    exact ⟨p', hp', hxfin⟩
  have hbase := GlobalPotentialPullback.isThetaPshPotential_comp
    (contMDiff_fst (n := n) (m := m) (X := M) (Y := T)) hφ.1 hne
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    (a := ClosedRealOneOneForm.pullback contMDiff_fst θ)
    (b := ClosedRealOneOneForm.pullback contMDiff_snd κ) hbase
    (SmoothRealForm.IsSemipositive.pullback contMDiff_snd hκ)

/-- The genuine joint subgeodesic is transported through the actual holomorphic
curve time, and an actual vertical PSH correction is added on the same domain. -/
theorem thetaPlurisubharmonicOn_product_subgeodesic_add_vertical
    {n : ℕ} {M T : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    [TopologicalSpace T] [ChartedSpace (ComplexModel 1) T] [IsComplexManifold 1 T]
    (θ : ClosedRealOneOneForm n M) (κ : ClosedRealOneOneForm 1 T)
    {U : ℝ → M → EReal} (hU : IsSubgeodesicInterior θ.val U)
    {q : T → EReal} (hq : ThetaPlurisubharmonic κ.val q)
    {V : Set T} (hV : IsOpen V) {τ : T → ℂ}
    (hτ : ∀ b : ComplexChart 1 T, DifferentiableOn ℂ (τ ∘ b.val.symm)
      (b.val.target ∩ b.val.symm ⁻¹' V))
    (htime : ∀ y ∈ V, (τ y).re ∈ Ioo (0 : ℝ) 1) :
    ThetaPlurisubharmonicOn (prodForm θ κ).val
      (fun p : M × T => U (τ p.2).re p.1 + q p.2) (univ ×ˢ V) := by
  have hlocal := SingularSubgeodesicProductLocalPsh.thetaPlurisubharmonicOn_product_time_pullback
    hU hV hτ htime
  have hvertical := GlobalPotentialPullback.thetaPlurisubharmonic_comp
    (contMDiff_snd (n := n) (m := 1) (X := M) (Y := T)) hq
  exact PrincipalizationGluingLocalAssembly.thetaPlurisubharmonicOn_add
    (a := ClosedRealOneOneForm.pullback contMDiff_fst θ)
    (b := ClosedRealOneOneForm.pullback contMDiff_snd κ) hlocal
    (fun e z hz _ => hvertical e z hz)

end

end SGPT.Foundations.Analysis.Pending.ProductPshAssembly
