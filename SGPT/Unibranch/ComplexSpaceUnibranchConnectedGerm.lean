import SGPT.Unibranch.ComplexSpaceUnibranchGerm
import SGPT.Foundations.Analysis.Pending.IrreducibleGermConnected

/-! Actual local connectedness off analytic traces from original
unibranch stalks. Blueprint: complex-space-unibranch-connected-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.LocalEmbedding

/-- Original unibranchness produces connected actual small carrier germs
and connected complements of the actual non-containing analytic trace. -/
theorem exists_connected_chartGerm_diff {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (e : LocalEmbedding X) (c : e.carrier)
    (B : Set e.ambient) (hB : IsComplexAnalyticSubset (n := e.dim) B)
    (hAB : ¬ AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ≤ᶠ[𝓝 0]
      AnalyticDescendingChain.chartGerm (n := e.dim) B c.val)
    {N : Set (ComplexModel e.dim)} (hN : N ∈ 𝓝 0) :
    ∃ Δ : Set (ComplexModel e.dim),IsOpen Δ ∧ (0 : ComplexModel e.dim) ∈ Δ ∧
      AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ∩ Δ ⊆ N ∧
      IsConnected (AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ∩ Δ) ∧
      IsConnected ((AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val ∩ Δ) \
        AnalyticDescendingChain.chartGerm (n := e.dim) B c.val) := by
  let A := AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val
  let T := AnalyticDescendingChain.chartGerm (n := e.dim) B c.val
  have hA0 : (0 : ComplexModel e.dim) ∈ A := by
    let E := (complexChartAt (n := e.dim) c.val).val
    have hp : c.val ∈ E.source := mem_complexChartAt_source c.val
    change 0+E c.val ∈ E.target ∩ E.symm ⁻¹' e.carrier
    rw [zero_add]
    exact ⟨E.map_source hp,by simpa only [mem_preimage,E.left_inv hp] using c.property⟩
  obtain ⟨d,Δ,G,hΔ,hΔ0,hAN,hGA,hconn,hdense,havoid,_hreg⟩ :=
    IrreducibleGermConnected.exists_connected_nhds (e.isIrreducibleGerm_of_isUnibranch hX c)
      (fun _ : Fin 1 => T) (fun _ => AnalyticDescendingChain.isAnalyticGerm_chartGerm hB c.val)
      (fun _ => hAB) hN
  have hGne : G.Nonempty := Set.Nonempty.of_closure ⟨0,hdense ⟨hA0,hΔ0⟩⟩
  have hGdiff : G ⊆ (A ∩ Δ) \ T := fun y hy => ⟨hGA hy,havoid y hy (0 : Fin 1)⟩
  exact ⟨Δ,hΔ,hΔ0,hAN,⟨⟨0,hA0,hΔ0⟩,hconn.subset_closure hGA hdense⟩,
    ⟨hGne.mono hGdiff,hconn.subset_closure hGdiff (fun y hy => hdense hy.1)⟩⟩

end SGPT.Unibranch.LocalEmbedding
