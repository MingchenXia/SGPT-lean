import SGPT.Hodge.SourceNefMixedUpperSemicontinuity

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceRemainingIntersectionDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetDraft SGPT.Hodge.BDivChain.SourceNefIntersectionDraft
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Original mixed-intersection upper semicontinuity on every natural dimension
and every nontrivial filter, with all original zero-volume cases retained. -/
theorem source_nefIntersection_limsup_le (ω : KahlerBackground n X)
    {J : Type*} {l : Filter J} [l.NeBot]
    (D : Fin n → J → WeilFamilyAny (ModelSystem.blowup n X))
    (E : Fin n → WeilFamilyAny (ModelSystem.blowup n X))
    (hD : ∀ i j,IsNefAny (D i j)) (hE : ∀ i,IsNefAny (E i))
    (hc : ∀ i,ConvergesAny l (D i) (E i)) :
    limsup (fun j => nefIntersection (fun i => D i j)) l≤nefIntersection E := by
  cases n with
  | zero =>
    have he : (fun j => nefIntersection (fun i => D i j))=fun _ : J => (1 : ENNReal) :=
      funext fun j => source_nefIntersection_dim_zero (fun i => D i j)
    rw [he,source_nefIntersection_dim_zero E,limsup_const]
  | succ m => exact nefIntersection_limsup_le_pos ω D E hD hE hc

/-- WHOLE original prop:DFusc, including arbitrary directed nets, original
modelwise convergence, every natural dimension and zero-volume limit cases.
Nefness of every limit is a conclusion of the actual closed nef cone. -/
theorem source_prop_DFusc_whole (ω : KahlerBackground n X)
    {J : Type*} [Preorder J] [IsDirected J (·≤·)] [Nonempty J]
    (D : Fin n → J → WeilFamilyAny (ModelSystem.blowup n X))
    (E : Fin n → WeilFamilyAny (ModelSystem.blowup n X))
    (hD : ∀ i j,IsNefAny (D i j)) (hc : ∀ i,ConvergesAny atTop (D i) (E i)) :
    (∀ i,IsNefAny (E i)) ∧
      limsup (fun j => nefIntersection (fun i => D i j)) atTop≤nefIntersection E := by
  have hE i := isNefAny_of_converges (D i) (E i) (hD i) (hc i)
  exact ⟨hE,source_nefIntersection_limsup_le ω D E hD hE hc⟩

end SGPT.Hodge.BDivChain.SourceRemainingIntersectionDraft
