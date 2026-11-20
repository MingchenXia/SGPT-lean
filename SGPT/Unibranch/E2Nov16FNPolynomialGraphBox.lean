import SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron
import SGPT.GAGA.CoreCLaurent

/-! Actual global polynomial graph and coordinate-box slice near the literal hull.
Blueprint: e2-nov16-fn-polynomial-graph-box.tex. No graph/holomorphy/Stein certificates. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology BigOperators
open SGPT.Foundations.Analysis.FirstPass
open SGPT.GAGA.Core
namespace SGPT.Unibranch.E2Nov16FNPolynomialGraphBox
open E2Nov16FNPolynomialPolyhedron

theorem differentiable_polyEval {n : ℕ} (p : Poly n) : Differentiable ℂ (polyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hfun : polyEval (MvPolynomial.C c : Poly n)=(fun _ : ComplexModel n => c) := by
      funext z
      simp only [polyEval,MvPolynomial.eval_C]
    rw [hfun]
    exact differentiable_const c
  | add p q hp hq =>
    have hfun : polyEval (p+q)=(fun z => polyEval p z+polyEval q z) := by
      funext z
      exact (MvPolynomial.eval (fun i => z i)).map_add p q
    rw [hfun]
    exact hp.add hq
  | mul_X p i hp =>
    have hfun : polyEval (p*MvPolynomial.X i)=(fun z => polyEval p z*z i) := by
      funext z
      simp only [polyEval,MvPolynomial.eval_mul,MvPolynomial.eval_X]
    rw [hfun]
    exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) i : ComplexModel n →L[ℂ] ℂ).differentiable

def graphFunctions {n q : ℕ} (p : Fin q → Poly n) : Fin q → ComplexModel n → ℂ :=
  fun j => polyEval (p j)

def graphBox {n q : ℕ} (R : ℝ) : Fin (n+q) → Set ℂ :=
  Fin.addCases (fun _ => closedBall 0 R) (fun _ => closedBall 0 1)

@[simp] theorem graphBox_castAdd {n q : ℕ} (R : ℝ) (i : Fin n) :
    graphBox (n := n) (q := q) R (Fin.castAdd q i)=closedBall (0 : ℂ) R := by simp [graphBox]

@[simp] theorem graphBox_natAdd {n q : ℕ} (R : ℝ) (j : Fin q) :
    graphBox (n := n) (q := q) R (Fin.natAdd n j)=closedBall (0 : ℂ) 1 := by simp [graphBox]

theorem graphBox_isBox {n q : ℕ} (R : ℝ) : Box.IsBox (graphBox (n := n) (q := q) R) := by
  constructor
  · intro i
    induction i using Fin.addCases with
    | left j => simpa only [graphBox_castAdd] using isCompact_closedBall (0 : ℂ) R
    | right j => simpa only [graphBox_natAdd] using isCompact_closedBall (0 : ℂ) 1
  · intro i
    induction i using Fin.addCases with
    | left j => simpa only [graphBox_castAdd] using convex_closedBall (0 : ℂ) R
    | right j => simpa only [graphBox_natAdd] using convex_closedBall (0 : ℂ) 1

theorem polynomial_graph_closed {n q : ℕ} (p : Fin q → Poly n) :
    IsClosed (Graph.graphMap (graphFunctions p) '' (univ : Set (ComplexModel n))) := by
  have hDef (j : Fin q) : Continuous (Graph.graphDef (graphFunctions p) j) :=
    (EuclideanSpace.proj (Fin.natAdd n j)).continuous.sub
      ((continuous_polyEval (p j)).comp Graph.continuous_proj)
  have hset : Graph.graphMap (graphFunctions p) '' (univ : Set (ComplexModel n))=
      ⋂ j : Fin q,(Graph.graphDef (graphFunctions p) j) ⁻¹' {0} := by
    ext z
    simp only [Graph.mem_graph_iff,mem_univ,true_and,mem_iInter,mem_preimage,mem_singleton_iff]
  rw [hset]
  exact isClosed_iInter (fun j => isClosed_singleton.preimage (hDef j))

theorem exists_polynomial_graph_box {n : ℕ} {K U : Set (ComplexModel n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : polyHull K⊆U) :
    ∃ R : ℝ,0<R ∧ ∃ (q : ℕ) (p : Fin q → Poly n),
      polyHull K⊆Laurent.slice univ (graphFunctions p) (graphBox R) ∧
      Laurent.slice univ (graphFunctions p) (graphBox R)⊆U := by
  classical
  obtain ⟨M,hM⟩ := (isCompact_polyHull hK).exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 0+1
  have hR : 0<R := by dsimp only [R];linarith [le_max_right M 0]
  have hCoord (z : ComplexModel n) (hz : z∈polyHull K) (i : Fin n) : ‖z i‖<R := by
    have H := hM z hz
    change ‖z‖≤M at H
    have Hcoord := PiLp.norm_apply_le z i
    dsimp only [R]
    linarith [le_max_left M 0]
  let C₀ : Fin n → Set ℂ := fun _ => closedBall 0 R
  have hC₀ : Box.IsBox C₀ := ⟨fun _ => isCompact_closedBall 0 R,fun _ => convex_closedBall 0 R⟩
  let D : Set (ComplexModel n) := Box.boxSet C₀\U
  have hD : IsCompact D := hC₀.isCompact_boxSet.diff hU
  have hsep (z : D) : ∃ p : Poly n,(∀ x∈polyHull K,‖polyEval p x‖<1) ∧ 1<‖polyEval p z.val‖ :=
    exists_normalized_separator (fun hz => z.property.2 (hKU hz))
  choose p hpL hpZ using hsep
  let O : D → Set (ComplexModel n) := fun z => {x | 1<‖polyEval (p z) x‖}
  have hO (z : D) : IsOpen (O z) := isOpen_lt continuous_const (continuous_polyEval (p z)).norm
  obtain ⟨s,hs⟩ := hD.elim_finite_subcover O hO (by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hpZ ⟨z,hz⟩⟩)
  let S : Finset (Poly n) := s.image p
  let q : ℕ := Fintype.card ↥S
  let e : Fin q ≃ ↥S := (Fintype.equivFin ↥S).symm
  let P : Fin q → Poly n := fun j => (e j).val
  refine ⟨R,hR,q,P,?_,?_⟩
  · intro z hz
    refine ⟨mem_univ _,?_⟩
    intro i
    induction i using Fin.addCases with
    | left j =>
      rw [Graph.graphMap_castAdd,graphBox_castAdd]
      exact mem_closedBall_zero_iff.mpr (hCoord z hz j).le
    | right j =>
      rw [Graph.graphMap_natAdd,graphBox_natAdd]
      change polyEval (P j) z∈closedBall (0 : ℂ) 1
      apply mem_closedBall_zero_iff.mpr
      obtain ⟨i,hi,hPi⟩ := Finset.mem_image.mp (e j).property
      have H := hpL i z hz
      change ‖polyEval (e j).val z‖≤1
      rw [← hPi]
      exact H.le
  · intro z hz
    by_contra hzU
    have hzD : z∈D := by
      refine ⟨?_,hzU⟩
      intro i
      have H := hz.2 (Fin.castAdd q i)
      rw [Graph.graphMap_castAdd,graphBox_castAdd] at H
      exact H
    obtain ⟨i,his,hi⟩ := mem_iUnion₂.mp (hs hzD)
    let a : ↥S := ⟨p i,Finset.mem_image.mpr ⟨i,his,rfl⟩⟩
    let j : Fin q := e.symm a
    have hPj : P j=p i := by
      dsimp only [P,j]
      rw [e.apply_symm_apply]
    have H := hz.2 (Fin.natAdd n j)
    rw [Graph.graphMap_natAdd,graphBox_natAdd] at H
    change polyEval (P j) z∈closedBall (0 : ℂ) 1 at H
    rw [hPj] at H
    exact (not_lt_of_ge (mem_closedBall_zero_iff.mp H)) hi

end SGPT.Unibranch.E2Nov16FNPolynomialGraphBox
