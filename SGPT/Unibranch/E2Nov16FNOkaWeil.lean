import SGPT.Unibranch.E2Nov16FNPolynomialGraphBox
import SGPT.GAGA.CoreBRunge

/-! Genuine polynomial approximation on the actual compact polynomial hull.
Blueprint: e2-nov16-fn-oka-weil.tex. All graph/extension/box data are manufactured. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology BigOperators
open SGPT.Foundations.Analysis.FirstPass
open SGPT.GAGA.Core
namespace SGPT.Unibranch.E2Nov16FNOkaWeil
open E2Nov16FNPolynomialPolyhedron E2Nov16FNPolynomialGraphBox

def graphSubstitution {n q : ℕ} (p : Fin q → Poly n) (Q : Poly (n+q)) : Poly n :=
  MvPolynomial.eval₂ MvPolynomial.C (Fin.addCases (fun i : Fin n => MvPolynomial.X i) p) Q

theorem polyEval_graphSubstitution {n q : ℕ} (p : Fin q → Poly n) (Q : Poly (n+q))
    (z : ComplexModel n) :
    polyEval (graphSubstitution p Q) z=polyEval Q (Graph.graphMap (graphFunctions p) z) := by
  have hvars (i : Fin (n+q)) :
      polyEval (Fin.addCases (fun j : Fin n => MvPolynomial.X j) p i) z=
        Graph.graphMap (graphFunctions p) z i := by
    induction i using Fin.addCases with
    | left j => simp [polyEval]
    | right j => simp [polyEval,graphFunctions]
  induction Q using MvPolynomial.induction_on with
  | C c => simp only [graphSubstitution,polyEval,MvPolynomial.eval₂_C,MvPolynomial.eval_C]
  | add Q R hQ hR =>
    simpa only [graphSubstitution,polyEval,MvPolynomial.eval₂_add,MvPolynomial.eval_add] using
      congrArg₂ (fun a b : ℂ => a+b) hQ hR
  | mul_X Q i hQ =>
    simpa only [graphSubstitution,polyEval,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,
      MvPolynomial.eval_mul,MvPolynomial.eval_X] using
      congrArg₂ (fun a b : ℂ => a*b) hQ (hvars i)

theorem exists_polynomial_approx_on_hull {n : ℕ} {K U : Set (ComplexModel n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : polyHull K⊆U)
    (f : ComplexModel n → ℂ) (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0<ε) :
    ∃ Q : Poly n,∀ z∈polyHull K,‖f z-polyEval Q z‖<ε := by
  classical
  obtain ⟨R,hR,q,p,hHullSlice,hSliceU⟩ := exists_polynomial_graph_box hK hU hKU
  let g : Fin q → ComplexModel n → ℂ := graphFunctions p
  let C : Fin (n+q) → Set ℂ := graphBox R
  have hBox : Box.IsBox C := graphBox_isBox R
  have hg : ∀ j,DifferentiableOn ℂ (g j) univ :=
    fun j => (differentiable_polyEval (p j)).differentiableOn
  obtain ⟨V,hV,hCV,F,hF,W,hW,hSliceW,hRead⟩ :=
    Laurent.exists_extend (D := univ) (g := g) (C := C) hBox isOpen_univ hg
      (polynomial_graph_closed p) (ι := Unit) (f := fun _ => f) hU hSliceU (fun _ => hf)
  obtain ⟨Q,hQ⟩ := Runge.exists_mvPolynomial_approx hBox.isCompact hBox.convex hV hCV
    (f := F ()) (hF ()) hε
  refine ⟨graphSubstitution p Q,?_⟩
  intro z hz
  have hzSlice := hHullSlice hz
  have hzBox := hzSlice.2
  have H := hQ (Graph.graphMap g z) hzBox
  have hAt := hRead z (hSliceW hzSlice) ()
  rw [← hAt,polyEval_graphSubstitution]
  exact H

end SGPT.Unibranch.E2Nov16FNOkaWeil
