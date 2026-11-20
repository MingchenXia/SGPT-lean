import SGPT.NAPotential.FiniteNodeSpatialHull

/-! Genuine affinity on the ORIGINAL adjacent intervals. Exact actual LP
maximizers are mixed at the vector level, so all EReal poles and endpoint
zero coefficients are covered without a hidden continuity assumption. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas
open SGPT.Convex.CutSimplex
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Mixing actual internally attained endpoint maximizers gives the full
EReal concave inequality, not merely finite-height epigraph concavity. -/
theorem simplexValue_mixed_ge (D : PiecewiseLinearData θ) {s t a b : ℝ}
    (hs : s ≤ D.τ 0) (ht : t ≤ D.τ 0)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (x : M) :
    (a:EReal)*simplexValue D s x+(b:EReal)*simplexValue D t x ≤
      simplexValue D (a*s+b*t) x := by
  obtain ⟨v,hv⟩ := simplexValue_attained_vertex D s hs x
  obtain ⟨w,hw⟩ := simplexValue_attained_vertex D t ht x
  have hvf := vertexVector_feasible D s v
  have hwf := vertexVector_feasible D t w
  have hmf := mixedWeights_mem D hvf hwf ha hb hab
  rw [hv,hw,← weightedValue_mixedWeights D x a b _ _ ha hb
    (fun k => (hvf.1 k).1) (fun k => (hwf.1 k).1)]
  exact le_iSup_of_le _ (le_iSup_of_le hmf le_rfl)

/-- No original node lies strictly inside an original adjacent interval. -/
theorem node_above_adjacent_of_above_interior (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) {s : ℝ}
    (hlo : D.τ (D.nextIdx i hi)<s) {k : Fin (D.N+1)} (hk : s≤D.τ k) :
    D.τ i≤D.τ k := by
  have hki : k ≤ i := by
    by_contra h
    have hik : i<k := lt_of_not_ge h
    have hjk : D.nextIdx i hi≤k := by
      simp only [nextIdx,Fin.le_def,Fin.lt_def] at hik ⊢
      omega
    exact (not_lt_of_ge hk) (lt_of_le_of_lt (D.strictAnti.antitone hjk) hlo)
  exact D.strictAnti.antitone hki

theorem node_below_adjacent_of_below_interior (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) {s : ℝ}
    (hhi : s<D.τ i) {k : Fin (D.N+1)} (hk : D.τ k<s) :
    D.τ k≤D.τ (D.nextIdx i hi) := by
  have hik : i<k := by
    by_contra h
    have hki : k ≤ i := le_of_not_gt h
    exact (not_lt_of_ge (D.strictAnti.antitone hki)) (hk.trans hhi)
  have hjk : D.nextIdx i hi≤k := by
    simp only [nextIdx,Fin.le_def,Fin.lt_def] at hik ⊢
    omega
  exact D.strictAnti.antitone hjk

/-- Every actual interior vertex is the mixture of actual feasible
vectors at the two original adjacent endpoints. This is a produced
statement about the genuine LP vectors, not a vertex certificate input. -/
theorem vertexVector_adjacent_endpoint_mixture (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) (t : ℝ) (ht0 : 0<t) (ht1 : t<1)
    (v : VertexIndex D.τ ((1-t)*D.τ i+t*D.τ (D.nextIdx i hi))) :
    ∃ w0 w1 : Fin (D.N+1) → ℝ,
      w0∈feasibleWeights D (D.τ i) ∧ w1∈feasibleWeights D (D.τ (D.nextIdx i hi)) ∧
      vertexVector D.τ ((1-t)*D.τ i+t*D.τ (D.nextIdx i hi)) v =
        mixedWeights (1-t) t w0 w1 := by
  let j := D.nextIdx i hi
  let s := (1-t)*D.τ i+t*D.τ j
  have htau : D.τ j<D.τ i := D.strictAnti (D.lt_nextIdx i hi)
  have hslo : D.τ j<s := by dsimp [s]; nlinarith
  have hshi : s<D.τ i := by dsimp [s]; nlinarith
  cases v with
  | inl k =>
    have hk0 : D.τ i≤D.τ k.val := node_above_adjacent_of_above_interior D i hi hslo k.property
    have hk1 : D.τ j≤D.τ k.val := htau.le.trans hk0
    refine ⟨basis k.val,basis k.val,
      (feasibleWeights_iff_cut D _ _).mpr (basis_mem_cut D.τ _ _ hk0),
      (feasibleWeights_iff_cut D _ _).mpr (basis_mem_cut D.τ _ _ hk1),?_⟩
    funext l
    change basis k.val l=(1-t)*basis k.val l+t*basis k.val l
    ring
  | inr p =>
    have hp0 : D.τ i≤D.τ p.val.1 :=
      node_above_adjacent_of_above_interior D i hi hslo p.property.2.le
    have hp1 : D.τ p.val.2≤D.τ j :=
      node_below_adjacent_of_below_interior D i hi hshi p.property.1
    have hpair : D.τ p.val.2<D.τ p.val.1 := p.property.1.trans p.property.2
    refine ⟨pairWeights D.τ (D.τ i) p.val.1 p.val.2,
      pairWeights D.τ (D.τ j) p.val.1 p.val.2,
      (feasibleWeights_iff_cut D _ _).mpr (pairWeights_mem_cut D.τ hpair
        (hp1.trans htau.le) hp0),
      (feasibleWeights_iff_cut D _ _).mpr (pairWeights_mem_cut D.τ hpair
        hp1 (htau.le.trans hp0)),?_⟩
    exact pairWeights_affine D.τ (D.τ i) (D.τ j) (1-t) t (by ring) p.val.1 p.val.2

/-- The actual simplex hull is affine on each ORIGINAL adjacent interval,
including every EReal polar case. -/
theorem simplexValue_adjacent_affine (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) (t : ℝ) (ht0 : 0<t) (ht1 : t<1) :
    simplexValue D ((1-t)*D.τ i+t*D.τ (D.nextIdx i hi)) =
      affineComb t (simplexValue D (D.τ i)) (simplexValue D (D.τ (D.nextIdx i hi))) := by
  let j := D.nextIdx i hi
  let s := (1-t)*D.τ i+t*D.τ j
  have hs : s≤D.τ 0 := by
    have htau : D.τ j<D.τ i := D.strictAnti (D.lt_nextIdx i hi)
    have hsi : s≤D.τ i := by dsimp [s]; nlinarith
    exact hsi.trans (D.tau_le_tau_zero i)
  funext x
  apply le_antisymm
  · obtain ⟨v,hv⟩ := simplexValue_attained_vertex D s hs x
    obtain ⟨w0,w1,hw0,hw1,he⟩ := vertexVector_adjacent_endpoint_mixture D i hi t ht0 ht1 v
    rw [hv,he,weightedValue_mixedWeights D x (1-t) t w0 w1
      (sub_nonneg.mpr ht1.le) ht0.le (fun k => (hw0.1 k).1) (fun k => (hw1.1 k).1)]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (le_iSup_of_le w0 (le_iSup_of_le hw0 le_rfl))
        (EReal.coe_nonneg.mpr (sub_nonneg.mpr ht1.le)))
      (mul_le_mul_of_nonneg_left (le_iSup_of_le w1 (le_iSup_of_le hw1 le_rfl))
        (EReal.coe_nonneg.mpr ht0.le))
  · exact simplexValue_mixed_ge D (D.tau_le_tau_zero i) (D.tau_le_tau_zero j)
      (sub_nonneg.mpr ht1.le) ht0.le (by ring) x

/-- Literal endpoints are included with zero EReal coefficients. -/
theorem simplexValue_adjacent_affine_closed (D : PiecewiseLinearData θ)
    (i : Fin (D.N+1)) (hi : i.val<D.N) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    simplexValue D ((1-t)*D.τ i+t*D.τ (D.nextIdx i hi)) =
      affineComb t (simplexValue D (D.τ i)) (simplexValue D (D.τ (D.nextIdx i hi))) := by
  by_cases h0 : t=0
  · subst t
    funext x
    simp only [sub_zero,one_mul,zero_mul,add_zero,affineComb,EReal.coe_one,
      EReal.coe_zero]
  by_cases h1 : t=1
  · subst t
    funext x
    simp only [sub_self,zero_mul,one_mul,zero_add,affineComb,EReal.coe_zero,
      EReal.coe_one]
  exact simplexValue_adjacent_affine D i hi t
    (lt_of_le_of_ne ht0 (Ne.symm h0)) (lt_of_le_of_ne ht1 h1)

/-- The corrected hull data are actual theta-PSH node functions with the
same original ordered breakpoints, not a new abstract certificate model. -/
def hullData (D : PiecewiseLinearData θ) : PiecewiseLinearData θ where
  N := D.N
  A := fun i => simplexValue D (D.τ i)
  isThetaPSH := fun i => isThetaPSH_simplexValue D (D.τ i) (D.tau_le_tau_zero i)
  τ := D.τ
  strictAnti := D.strictAnti

/-- The genuine source simplex hull is exactly the piecewise linear curve
of its own corrected node data, with every original interval and tail. -/
theorem simplexValue_eq_hullData_curve (D : PiecewiseLinearData θ) :
    simplexValue D=(hullData D).curve := by
  apply (hullData D).curve_unique
  · intro i
    rfl
  · intro s hs
    funext x
    change simplexValue D s x=simplexValue D (D.τ (Fin.last D.N)) x
    rw [simplexValue_eq_nodeMaximum_of_le_last D hs x,
      simplexValue_eq_nodeMaximum_of_le_last D le_rfl x]
  · intro i hi t ht0 ht1
    exact simplexValue_adjacent_affine D i hi t ht0 ht1
  · intro s hs
    funext x
    exact simplexValue_eq_bot_of_lt_first D hs x

/-- The literal printed spatially regularized concave envelope is itself
an actual source piecewise linear curve, with internally constructed data. -/
theorem spatialHull_eq_hullData_curve (D : PiecewiseLinearData θ) :
    (fun s => uscRegularization (D.pointwiseUpperConcaveEnvelope s))=(hullData D).curve := by
  have he : (fun s => uscRegularization (D.pointwiseUpperConcaveEnvelope s))=simplexValue D := by
    funext s
    exact uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue D s
  rw [he,simplexValue_eq_hullData_curve]

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
