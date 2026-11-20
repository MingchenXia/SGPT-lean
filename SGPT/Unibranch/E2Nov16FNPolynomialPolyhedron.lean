import SGPT.Foundations.Analysis.Pending.GermParametrizationSets
import Mathlib.Topology.Algebra.MvPolynomial

/-! Literal complex-polynomial hulls and manufactured finite polyhedron neighbourhoods.
Blueprint: e2-nov16-fn-polynomial-polyhedron.tex. No Stein/Runge/PSH certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology BigOperators
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.GermParametrizationData
namespace SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℂ

def polyEval {n : ℕ} (p : Poly n) (z : ComplexModel n) : ℂ := MvPolynomial.eval (fun i => z i) p

def polyHull {n : ℕ} (K : Set (ComplexModel n)) : Set (ComplexModel n) :=
  {z | ∀ (p : Poly n) (C : ℝ),(∀ x∈K,‖polyEval p x‖≤C) → ‖polyEval p z‖≤C}

theorem continuous_polyEval {n : ℕ} (p : Poly n) : Continuous (polyEval p) := by
  have hCoord : Continuous (fun z : ComplexModel n => fun i : Fin n => z i) :=
    continuous_pi (fun i => (EuclideanSpace.proj i).continuous)
  exact p.continuous_eval.comp hCoord

theorem isClosed_polyHull {n : ℕ} (K : Set (ComplexModel n)) : IsClosed (polyHull K) := by
  have h (p : Poly n) (C : ℝ) : IsClosed {z | (∀ x∈K,‖polyEval p x‖≤C) → ‖polyEval p z‖≤C} := by
    by_cases hK : ∀ x∈K,‖polyEval p x‖≤C
    · convert (isClosed_le (continuous_polyEval p).norm
        (continuous_const : Continuous (fun _ : ComplexModel n => C))) using 1
      ext z
      exact ⟨fun hz => hz hK,fun hz _ => hz⟩
    · simp only [hK,false_implies,ofPred_true]
      exact isClosed_univ
  simpa only [polyHull,Set.ofPred_forall] using isClosed_iInter (fun p => isClosed_iInter (h p))

theorem polyHull_empty {n : ℕ} : polyHull (∅ : Set (ComplexModel n))=∅ := by
  ext z
  constructor
  · intro hz
    have H := hz (0 : Poly n) (-1) (by intro x hx; exact False.elim hx)
    norm_num [polyEval] at H
  · exact False.elim

theorem isCompact_polyHull {n : ℕ} {K : Set (ComplexModel n)} (hK : IsCompact K) :
    IsCompact (polyHull K) := by
  classical
  choose C hC using fun i : Fin n => hK.exists_bound_of_continuousOn
    (continuous_polyEval (MvPolynomial.X i)).continuousOn
  apply (isCompact_closedBall (0 : ComplexModel n) (∑ i,C i)).of_isClosed_subset (isClosed_polyHull K)
  intro z hz
  apply mem_closedBall_zero_iff.mpr
  apply (norm_le_sum_norm z).trans
  apply Finset.sum_le_sum
  intro i _
  have H := hz (MvPolynomial.X i) (C i) (hC i)
  simpa only [polyEval,MvPolynomial.eval_X] using H

theorem exists_normalized_separator {n : ℕ} {K : Set (ComplexModel n)} {x : ComplexModel n}
    (hx : x∉polyHull K) :
    ∃ p : Poly n,(∀ z∈polyHull K,‖polyEval p z‖<1) ∧ 1<‖polyEval p x‖ := by
  classical
  by_cases hK : K.Nonempty
  · change ¬ ∀ (p : Poly n) (C : ℝ),(∀ z∈K,‖polyEval p z‖≤C) → ‖polyEval p x‖≤C at hx
    push Not at hx
    obtain ⟨p,C,hCp,hxC⟩ := hx
    obtain ⟨z₀,hz₀⟩ := hK
    have hCnonneg : 0≤C := (norm_nonneg _).trans (hCp z₀ hz₀)
    let t : ℝ := (C+‖polyEval p x‖)/2
    have hCt : C<t := by dsimp only [t];linarith
    have htN : t<‖polyEval p x‖ := by dsimp only [t];linarith
    have ht : 0<t := hCnonneg.trans_lt hCt
    let q : Poly n := MvPolynomial.C ((t : ℂ)⁻¹)*p
    have hEval (z : ComplexModel n) : ‖polyEval q z‖=‖polyEval p z‖/t := by
      dsimp only [q,polyEval]
      rw [MvPolynomial.eval_mul,MvPolynomial.eval_C,norm_mul,norm_inv,Complex.norm_real,
        Real.norm_of_nonneg ht.le]
      ring
    refine ⟨q,?_,?_⟩
    · intro z hz
      rw [hEval]
      exact (div_lt_one ht).mpr ((hz p C hCp).trans_lt hCt)
    · rw [hEval]
      exact (one_lt_div ht).mpr htN
  · have hEmpty : K=∅ := Set.not_nonempty_iff_eq_empty.mp hK
    refine ⟨MvPolynomial.C 2,?_,?_⟩
    · intro z hz
      rw [hEmpty,polyHull_empty] at hz
      exact False.elim hz
    · norm_num [polyEval]

def openPolyhedron {n : ℕ} (R : ℝ) (S : Finset (Poly n)) : Set (ComplexModel n) :=
  {z | ‖z‖<R ∧ ∀ p∈S,‖polyEval p z‖<1}

def closedPolyhedron {n : ℕ} (R : ℝ) (S : Finset (Poly n)) : Set (ComplexModel n) :=
  {z | ‖z‖≤R ∧ ∀ p∈S,‖polyEval p z‖≤1}

theorem isOpen_openPolyhedron {n : ℕ} (R : ℝ) (S : Finset (Poly n)) : IsOpen (openPolyhedron R S) := by
  have h : IsOpen (⋂ p∈S,{z : ComplexModel n | ‖polyEval p z‖<1}) :=
    isOpen_biInter_finset (fun p _ => isOpen_lt (continuous_polyEval p).norm continuous_const)
  simpa only [openPolyhedron,Set.ofPred_and,Set.ofPred_forall] using
    (isOpen_lt continuous_norm continuous_const).inter h

theorem isClosed_closedPolyhedron {n : ℕ} (R : ℝ) (S : Finset (Poly n)) : IsClosed (closedPolyhedron R S) := by
  have h : IsClosed (⋂ p∈S,{z : ComplexModel n | ‖polyEval p z‖≤1}) :=
    isClosed_biInter (fun p _ => isClosed_le (continuous_polyEval p).norm continuous_const)
  simpa only [closedPolyhedron,Set.ofPred_and,Set.ofPred_forall] using
    (isClosed_le continuous_norm continuous_const).inter h

theorem isCompact_closedPolyhedron {n : ℕ} (R : ℝ) (S : Finset (Poly n)) : IsCompact (closedPolyhedron R S) := by
  apply (isCompact_closedBall (0 : ComplexModel n) R).of_isClosed_subset (isClosed_closedPolyhedron R S)
  intro z hz
  exact mem_closedBall_zero_iff.mpr hz.1

theorem closure_openPolyhedron_subset {n : ℕ} (R : ℝ) (S : Finset (Poly n)) :
    closure (openPolyhedron R S)⊆closedPolyhedron R S :=
  closure_minimal (fun _ hz => ⟨hz.1.le,fun p hp => (hz.2 p hp).le⟩) (isClosed_closedPolyhedron R S)

theorem exists_polyhedron_neighborhood {n : ℕ} {K U : Set (ComplexModel n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : polyHull K⊆U) :
    ∃ R : ℝ,0<R ∧ ∃ S : Finset (Poly n),
      polyHull K⊆openPolyhedron R S ∧ IsOpen (openPolyhedron R S) ∧
      IsCompact (closedPolyhedron R S) ∧ closure (openPolyhedron R S)⊆closedPolyhedron R S ∧
      closedPolyhedron R S⊆U := by
  classical
  obtain ⟨M,hM⟩ := (isCompact_polyHull hK).exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 0+1
  have hR : 0<R := by dsimp only [R];linarith [le_max_right M 0]
  have hRL : ∀ z∈polyHull K,‖z‖<R := by
    intro z hz
    have H := hM z hz
    change ‖z‖≤M at H
    dsimp only [R]
    linarith [le_max_left M 0]
  let D : Set (ComplexModel n) := closedBall 0 R\U
  have hD : IsCompact D := (isCompact_closedBall (0 : ComplexModel n) R).diff hU
  have hsep (z : D) : ∃ p : Poly n,(∀ x∈polyHull K,‖polyEval p x‖<1) ∧ 1<‖polyEval p z.val‖ :=
    exists_normalized_separator (fun hz => z.property.2 (hKU hz))
  choose p hpL hpZ using hsep
  let O : D → Set (ComplexModel n) := fun z => {x | 1<‖polyEval (p z) x‖}
  have hO (z : D) : IsOpen (O z) := isOpen_lt continuous_const (continuous_polyEval (p z)).norm
  obtain ⟨s,hs⟩ := hD.elim_finite_subcover O hO (by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hpZ ⟨z,hz⟩⟩)
  let S : Finset (Poly n) := s.image p
  refine ⟨R,hR,S,?_,isOpen_openPolyhedron R S,isCompact_closedPolyhedron R S,
    closure_openPolyhedron_subset R S,?_⟩
  · intro z hz
    refine ⟨hRL z hz,?_⟩
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hpL i z hz
  · intro z hz
    by_contra hzu
    have hzD : z∈D := ⟨mem_closedBall_zero_iff.mpr hz.1,hzu⟩
    obtain ⟨i,his,hi⟩ := mem_iUnion₂.mp (hs hzD)
    have hpi : p i∈S := Finset.mem_image.mpr ⟨i,his,rfl⟩
    exact (not_lt_of_ge (hz.2 (p i) hpi)) hi

end SGPT.Unibranch.E2Nov16FNPolynomialPolyhedron
