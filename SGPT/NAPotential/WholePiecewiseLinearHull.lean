import SGPT.NAPotential.FiniteNodeAffineHull
import SGPT.NAPotential.OriginalCurveParameterUSC

/-! WHOLE revised source rmk:pwlinhull, including its opening original
parameter-USC assertion. Every quantity is the original data/curve/raw LCE
or an internally constructed actual finite-simplex/corrected nodal object. -/
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

/-- The whole revised source remark, for all node counts and all spatial
dimensions, with the original raw LCE unchanged even at polar points. -/
theorem source_pwlinhull_whole (D : PiecewiseLinearData θ) :
    (∀ x,UpperSemicontinuous (fun s => D.curve s x)) ∧
    (∀ s,uscRegularization (D.pointwiseUpperConcaveEnvelope s)=simplexValue D s) ∧
    (∀ s,s≤D.τ 0 → ∀ x,∃ w∈feasibleWeights D s,
      simplexValue D s x=weightedValue D w x) ∧
    (∀ s,s≤D.τ 0 → ∀ x,∃ v : VertexIndex D.τ s,
      simplexValue D s x=weightedValue D (vertexVector D.τ s v) x) ∧
    (∀ s x,simplexValue D s x=⨆ v : VertexIndex D.τ s,
      weightedValue D (vertexVector D.τ s v) x) ∧
    (∀ s w,w∈(cut D.τ s).extremePoints ℝ ↔
      (∃ i,s≤D.τ i ∧ w=basis i) ∨
      (∃ i j,i<j ∧ D.τ j<s ∧ s<D.τ i ∧ w=pairWeights D.τ s i j)) ∧
    (∀ s,s≤D.τ 0 → (ofFixedModel n M).IsThetaPSH θ (simplexValue D s)) ∧
    (simplexValue D (D.τ 0)=D.A 0) ∧
    (∀ s,s≤D.τ (Fin.last D.N) → simplexValue D s=nodeMaximum D) ∧
    (∀ s,D.τ 0<s → simplexValue D s=fun _ => ⊥) ∧
    (∀ x,Antitone (fun s => simplexValue D s x)) ∧
    (∀ x,SGPT.Convex.IsConvex (fun s => -simplexValue D s x)) ∧
    (∀ s x,D.curve s x≤simplexValue D s x) ∧
    (∀ s x,(∀ i,D.A i x≠⊥) →
      D.pointwiseUpperConcaveEnvelope s x=simplexValue D s x) ∧
    (∀ (i : Fin (D.N+1)) (hi : i.val<D.N) (t : ℝ),0≤t → t≤1 →
      simplexValue D ((1-t)*D.τ i+t*D.τ (D.nextIdx i hi))=
        affineComb t (simplexValue D (D.τ i))
          (simplexValue D (D.τ (D.nextIdx i hi)))) ∧
    ((fun s => uscRegularization (D.pointwiseUpperConcaveEnvelope s))=(hullData D).curve) := by
  refine ⟨upperSemicontinuous_curve_parameter D,
    uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue D,
    simplexValue_attained_feasible D,simplexValue_attained_vertex D,
    simplexValue_eq_vertex_iSup D,source_extremePoint_iff D,
    isThetaPSH_simplexValue D,?_,?_,?_,simplexValue_antitone D,
    simplexValue_concave D,curve_le_simplexValue D,
    pointwiseUpperConcaveEnvelope_eq_simplexValue_of_nodes_ne_bot D,
    simplexValue_adjacent_affine_closed D,spatialHull_eq_hullData_curve D⟩
  · funext x
    exact simplexValue_first D x
  · intro s hs
    funext x
    exact simplexValue_eq_nodeMaximum_of_le_last D hs x
  · intro s hs
    funext x
    exact simplexValue_eq_bot_of_lt_first D hs x

end SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
