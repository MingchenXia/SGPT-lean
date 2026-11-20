import SGPT.NAPotential.FiniteNodeVertexMaximum

/-! Source finite-max theta-PSH realization of the actual all-polar simplex.
Every candidate comes from the proved actual LP vertex classification. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open SGPT.Convex.CutSimplex
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The literal source vertex list, including the printed order i<j. -/
theorem source_extremePoint_iff (D : PiecewiseLinearData θ) (s : ℝ)
    (w : Fin (D.N+1) → ℝ) :
    w∈(cut D.τ s).extremePoints ℝ ↔
      (∃ i,s≤D.τ i ∧ w=basis i) ∨
      (∃ i j,i<j ∧ D.τ j<s ∧ s<D.τ i ∧ w=pairWeights D.τ s i j) := by
  constructor
  · intro hw
    rcases extreme_eq_basis_or_pair D.τ D.strictAnti.injective s hw with h | ⟨i,j,hlo,hhi,he⟩
    · exact Or.inl h
    · have hij : i<j := lt_of_not_ge (fun hji =>
        (not_lt_of_ge (D.strictAnti.antitone hji)) (hlo.trans hhi))
      exact Or.inr ⟨i,j,hij,hlo,hhi,he⟩
  · rintro (⟨i,hi,rfl⟩ | ⟨i,j,_,hlo,hhi,rfl⟩)
    · exact basis_isExtreme D.τ s i hi
    · exact pairWeights_isExtreme D.τ s hlo hhi

/-- Attainment over the original feasible simplex is an output of the
actual polar-face optimization, rather than an incoming maximizer. -/
theorem simplexValue_attained_feasible (D : PiecewiseLinearData θ) (s : ℝ)
    (hs : s≤D.τ 0) (x : M) :
    ∃ w∈feasibleWeights D s,simplexValue D s x=weightedValue D w x := by
  obtain ⟨v,hv⟩ := simplexValue_attained_vertex D s hs x
  exact ⟨vertexVector D.τ s v,vertexVector_feasible D s v,hv⟩

theorem weightedValue_basis (D : PiecewiseLinearData θ) (i : Fin (D.N+1)) (x : M) :
    weightedValue D (basis i) x = D.A i x := by
  classical
  have he : (basis i : Fin (D.N+1) → ℝ)=vertexWeights i := by
    funext j
    by_cases h : j=i
    · simp only [SGPT.Convex.CutSimplex.basis,SimplexRevision.vertexWeights,if_pos h]
    · simp only [SGPT.Convex.CutSimplex.basis,SimplexRevision.vertexWeights,if_neg h]
  rw [he]
  exact weightedValue_vertex D i x

theorem weightedValue_pair (D : PiecewiseLinearData θ) {s : ℝ} {i j : Fin (D.N+1)}
    (hlo : D.τ j ≤ s) (hhi : s ≤ D.τ i) (htime : D.τ j < D.τ i) (x : M) :
    weightedValue D (pairWeights D.τ s i j) x =
      (((s-D.τ j)/(D.τ i-D.τ j) : ℝ) : EReal) * D.A i x +
      (((D.τ i-s)/(D.τ i-D.τ j) : ℝ) : EReal) * D.A j x := by
  have ha : 0 ≤ (s-D.τ j)/(D.τ i-D.τ j) := div_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr htime.le)
  have hb : 0 ≤ (D.τ i-s)/(D.τ i-D.τ j) := div_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr htime.le)
  change weightedValue D (mixedWeights _ _ (basis i) (basis j)) x = _
  rw [weightedValue_mixedWeights D x _ _ _ _ ha hb
    (fun k => (basis_mem_cut D.τ (D.τ i) i le_rfl).1.1 k)
    (fun k => (basis_mem_cut D.τ (D.τ j) j le_rfl).1.1 k),
    weightedValue_basis, weightedValue_basis]

theorem isThetaPSH_vertexValue (D : PiecewiseLinearData θ) (s : ℝ)
    (v : VertexIndex D.τ s) :
    (ofFixedModel n M).IsThetaPSH θ (weightedValue D (vertexVector D.τ s v)) := by
  cases v with
  | inl i =>
    have he : weightedValue D (vertexVector D.τ s (Sum.inl i)) = D.A i.val := by
      funext x
      exact weightedValue_basis D i.val x
    rw [he]
    exact D.isThetaPSH i.val
  | inr p =>
    let i := p.val.1
    let j := p.val.2
    have hlo : D.τ j < s := p.property.1
    have hhi : s < D.τ i := p.property.2
    have hd : 0 < D.τ i-D.τ j := sub_pos.mpr (hlo.trans hhi)
    let a := (s-D.τ j)/(D.τ i-D.τ j)
    let b := (D.τ i-s)/(D.τ i-D.τ j)
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hlo.le) hd.le
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hhi.le) hd.le
    have hab : a+b=1 := by
      dsimp [a,b]
      field_simp [hd.ne']
      ring
    have ha1 : a ≤ 1 := by linarith
    have hbe : b = 1-a := by linarith
    have he : weightedValue D (vertexVector D.τ s (Sum.inr p)) =
        ThetaPshConvexCombination.convexComb a (D.A i) (D.A j) := by
      funext x
      change weightedValue D (pairWeights D.τ s i j) x = _
      rw [weightedValue_pair D hlo.le hhi.le (hlo.trans hhi) x]
      change (a:EReal)*D.A i x+(b:EReal)*D.A j x = _
      rw [hbe, ThetaPshConvexCombination.convexComb_apply]
    rw [he, isThetaPSH_iff_nativeThetaPotential]
    exact EndpointMixedMassConvexCombination.isThetaPshPotential_convexComb_closed
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH i))
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (D.isThetaPSH j)) ha ha1

theorem sourceThetaPSH_finset_sup {I : Type*} (u : I → M → EReal) (S : Finset I)
    (hS : S.Nonempty) (hu : ∀ i ∈ S, (ofFixedModel n M).IsThetaPSH θ (u i)) :
    (ofFixedModel n M).IsThetaPSH θ (fun x => S.sup' hS (fun i => u i x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hS
  | @insert i S hi ih =>
    by_cases hne : S.Nonempty
    · have htail := ih hne (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      have he : (fun x => (insert i S).sup' hS (fun j => u j x)) =
          fun x => max (u i x) (S.sup' hne (fun j => u j x)) := by
        funext x
        exact Finset.sup'_insert hne _
      rw [he, isThetaPSH_iff_nativeThetaPotential]
      exact SGPT.Foundations.Analysis.Pending.IsThetaPshPotential.max
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (hu i (Finset.mem_insert_self i S)))
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp htail)
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      simpa only [Finset.insert_empty, Finset.sup'_singleton] using hu i (Finset.mem_insert_self i ∅)

/-- The original supremum equals the maximum over the exact eligible source
basis and pair vertices. No nodal-finiteness hypothesis is imposed. -/
theorem simplexValue_eq_vertex_iSup (D : PiecewiseLinearData θ) (s : ℝ) (x : M) :
    simplexValue D s x = ⨆ v : VertexIndex D.τ s, weightedValue D (vertexVector D.τ s v) x := by
  apply le_antisymm
  · by_cases hs : s ≤ D.τ 0
    · obtain ⟨v,hv⟩ := simplexValue_attained_vertex D s hs x
      rw [hv]
      exact le_iSup (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) v
    · rw [simplexValue_eq_bot_of_lt_first D (lt_of_not_ge hs)]
      exact bot_le
  · apply iSup_le
    intro v
    exact le_iSup_of_le _ (le_iSup_of_le (vertexVector_feasible D s v) le_rfl)

/-- Actual spatial theta-PSH of the whole finite-node simplex value, derived
from the finite maximum, in every dimension including zero. -/
theorem isThetaPSH_simplexValue (D : PiecewiseLinearData θ) (s : ℝ) (hs : s ≤ D.τ 0) :
    (ofFixedModel n M).IsThetaPSH θ (simplexValue D s) := by
  classical
  let : Fintype (VertexIndex D.τ s) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (VertexIndex D.τ s)).Nonempty :=
    ⟨Sum.inl ⟨0,hs⟩, Finset.mem_univ _⟩
  have he : simplexValue D s = fun x => Finset.univ.sup' hne
      (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) := by
    funext x
    rw [simplexValue_eq_vertex_iSup]
    apply le_antisymm
    · exact iSup_le (fun v => Finset.le_sup' (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) (Finset.mem_univ v))
    · exact Finset.sup'_le _ _ (fun v _ => le_iSup (fun v : VertexIndex D.τ s => weightedValue D (vertexVector D.τ s v) x) v)
  rw [he]
  exact sourceThetaPSH_finset_sup _ _ hne (fun v _ => isThetaPSH_vertexValue D s v)

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
