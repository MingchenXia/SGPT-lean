import SGPT.PSH.GeometricQNestedOpenRestriction
import SGPT.PSH.AtlasLogLocalIntegral

/-! Genuine locality of the complete native logarithmic predicate. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Genuine native logarithmic data glue from actual original opens. The full
nested-open rational divisor identity and full reduced ideal transport prove
all coefficient/generator fields; a bounded remainder stays the same function
under the literal range homeomorphism. -/
theorem native_log_of_local
    (D : EffectiveGeometricQDivisor n M) (u : M → EReal)
    (hu : (ofFixedModel n M).IsQPSH u)
    (hloc : ∀ x : M,∃ (V : Opens M) (_hx : x∈V),
      NativeHasLogSingularitiesAlongAnyDimension
        (geometricQDivisorOpenRestrictionAnyDimension D V) (fun y : V => u y.val)) :
    NativeHasLogSingularitiesAlongAnyDimension D u := by
  refine ⟨hu,?_⟩
  intro x
  obtain ⟨V,hx,hV⟩ := hloc x
  obtain ⟨W,hxW,r,Z,a,p,R,C,hZ,ha,hp,hideal,hcoeff,hC,hR,hlog⟩ := hV.2 ⟨x,hx⟩
  let O := flattenOpen V W
  let e := flattenHomeomorph V W
  let he := flattenHomeomorph_contMDiff (n := n) V W
  let hei := flattenHomeomorph_symm_contMDiff (n := n) V W
  let K := biholomorphic_geometricPrimeCarrier_equiv e he hei
  let J := biholomorphic_geometricPrimeCarrier_equiv e.symm hei he
  have hxO : x∈O := ⟨⟨⟨x,hx⟩,hxW⟩,rfl⟩
  refine ⟨O,hxO,r,(fun i => J (Z i)),a,(fun i => p i ∘ e.symm),R ∘ e.symm,C,
    (J.injective.comp hZ),ha,?_,?_,?_,hC,(fun q => hR (e.symm q)),?_⟩
  · intro i q
    exact (hp i (e.symm q)).comp_contMDiff (Eventually.of_forall fun _ => hei.contMDiffAt)
  · intro i q b
    change (vanishingIdeal (n := n)
      (biholomorphic_geometricPrimeCarrier_preimage e.symm hei he (Z i)).val).mem q b ↔
      IsInSpanAt (n := n) (· = p i ∘ e.symm) q b
    rw [←biholomorphic_geometricPrimeCarrier_preimage_fullIdeal e.symm hei he (Z i)]
    exact MemberPullback.pullback_mem_iff_of_generator hei (hp i (e.symm q))
      (hideal i (e.symm q)) b
  · intro A
    have h := hcoeff (K A)
    rw [geometricQOpen_nested] at h
    change (geometricQDivisorOpenRestrictionAnyDimension D O).coefficient (K.symm (K A))=_ at h
    rw [K.symm_apply_apply] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    have hi : Z i=K A ↔ J (Z i)=A := by
      change Z i=K A ↔ K.symm (Z i)=A
      exact (K.symm_apply_eq).symm
    simp only [hi]
  · intro q
    have h := hlog (e.symm q)
    have hval : (e.symm q).val.val=q.val := flattenHomeomorph_symm_val V W q
    simpa only [Function.comp_apply,hval] using h

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
