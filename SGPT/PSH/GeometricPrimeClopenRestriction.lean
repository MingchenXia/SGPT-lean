import SGPT.PSH.GeometricQNestedOpenRestriction
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetOpens
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

/-! Actual prime restriction to a clopen subset containing its WHOLE carrier. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal identity on a clopen set, constant off it. -/
def clopenRetraction (U : Opens M) (p : U) : M → U := fun x =>
  if hx : x∈U then ⟨x,hx⟩ else p

@[simp] theorem clopenRetraction_val (U : Opens M) (p : U) (x : M) (hx : x∈U) :
    (clopenRetraction U p x).val=x := by simp [clopenRetraction,hx]

@[simp] theorem clopenRetraction_subtype (U : Opens M) (p q : U) :
    clopenRetraction U p q.val=q := by simp [clopenRetraction,q.property]

/-- Clopen piecewise holomorphy followed by the actual subtype immersion. -/
theorem clopenRetraction_contMDiff (U : Opens M) (hU : IsClopen (U : Set M)) (p : U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (clopenRetraction U p) := by
  have hval : (fun x => (clopenRetraction U p x).val)=
      Set.piecewise (U : Set M) id (fun _ => p.val) := by
    funext x
    by_cases hx : x∈U <;> simp [clopenRetraction,Set.piecewise,hx]
  have hfront : frontier (U : Set M)=∅ := by
    rw [hU.isOpen.frontier_eq,hU.isClosed.closure_eq,sdiff_self]
  have hnative : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞
      (fun x => (clopenRetraction U p x).val) := by
    rw [hval]
    exact contMDiff_id.piecewise contMDiff_const (fun x hx => by
      rw [hfront] at hx
      exact False.elim hx)
  apply (ContMDiff.iff_comp_isImmersionOfComplement
    (Manifold.IsImmersionOfComplement.of_opens.{0,0,0,u,0} U)).mpr
  exact ⟨(Topology.IsInducing.continuous_iff Topology.IsInducing.subtypeVal).mpr
    hnative.continuous,hnative⟩

/-- A genuine prime restricts to a genuine prime when its ENTIRE original
carrier lies in the actual clopen set. Full analytic irreducibility and actual
regular codimension are manufactured via the true holomorphic retraction. -/
theorem exists_prime_on_clopen_of_subset (P : GeometricPrimeCarrier n M)
    (U : Opens M) (hU : IsClopen (U : Set M)) (hPU : P.val⊆(U : Set M)) :
    ∃ Q : GeometricPrimeCarrier n U,Q.val=(Subtype.val : U → M) ⁻¹' P.val := by
  obtain ⟨x,hx⟩ := P.nonempty
  let p : U := ⟨x,hPU hx⟩
  let f := clopenRetraction U p
  have hf := clopenRetraction_contMDiff (n := n) U hU p
  have hA : IsComplexAnalyticSubset (n := n) ((Subtype.val : U → M) ⁻¹' P.val) := by
    apply AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val
    rw [←P.subvariety_carrier]
    exact P.subvariety.analytic
  have himage : f '' P.subvariety.carrier=(Subtype.val : U → M) ⁻¹' P.val := by
    ext q
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hzP : z∈P.val := by rwa [←P.subvariety_carrier]
      change (f z).val∈P.val
      rw [clopenRetraction_val U p z (hPU hzP)]
      exact hzP
    · intro hq
      refine ⟨q.val,?_,clopenRetraction_subtype U p q⟩
      rwa [P.subvariety_carrier]
  have hirr := holomorphic_analytic_image_irreducible hf P.subvariety (by rwa [himage])
  rw [himage] at hirr
  obtain ⟨z,hz⟩ := P.subvariety.regularLocus_nonempty
  have hzP : z∈P.val := by
    rw [←P.subvariety_carrier]
    exact hz.2.1
  let q : U := ⟨z,hPU hzP⟩
  have hreg : RegularAtDim (n := n) ((Subtype.val : U → M) ⁻¹' P.val) q P.subvariety.dim := by
    apply AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
    rwa [←P.subvariety_carrier]
  refine ⟨⟨_,⟨{
    carrier := (Subtype.val : U → M) ⁻¹' P.val
    isClosed_carrier := P.isClosed.preimage continuous_subtype_val
    irreducible_carrier := hirr
    dim := P.subvariety.dim
    dim_le := P.subvariety.dim_le
    regularLocus_nonempty := ⟨q,hreg⟩ },rfl,P.subvariety_codimension⟩⟩,rfl⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
