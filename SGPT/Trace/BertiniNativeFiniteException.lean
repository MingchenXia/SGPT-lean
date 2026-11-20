import SGPT.Trace.BertiniNativeFiniteAvoidance
import SGPT.Trace.BertiniSmooth
import SGPT.Foundations.Analysis.Pending.AnalyticSubsetPreimage
import SGPT.Foundations.Analysis.Pending.ConstantRankImage

/-! Literal ORIGINAL finite-point hyperplane exceptions and produced generic kernel injectivity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.Bertini
open Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace
open SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.TensorDictionaryDraft.HermitianHolomorphicLineBundle

variable {N : ℕ} {X : Type}

def finitePointHyperplaneException (p : X → ComplexProjectiveSpace N) (F : Finset X) : Set (HyperplaneSpace N) :=
  {ℓ | ∃ x ∈ F, x ∈ member p ℓ}

private theorem actualPointHyperplane_eq (p : X → ComplexProjectiveSpace N) (x : X) :
    {ℓ : HyperplaneSpace N | x ∈ member p ℓ} = hyperplane (p x) := by
  ext ℓ
  change pairing ℓ.rep (p x).rep = 0 ↔ pairing (p x).rep ℓ.rep = 0
  have heq : pairing ℓ.rep (p x).rep = pairing (p x).rep ℓ.rep :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [heq]

private theorem actualHyperplane_proper (a : HyperplaneSpace N) : hyperplane a ≠ univ := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, a.rep j ≠ 0 := by
    by_contra h
    push Not at h
    exact a.rep_ne_zero (funext h)
  let v : Fin (N + 1) → ℂ := Pi.single j 1
  have hv : v ≠ 0 := by
    intro hz
    have := congrFun hz j
    simp only [v,Pi.single_eq_same,Pi.zero_apply] at this
    exact one_ne_zero this
  have hp : pairing a.rep v = a.rep j := by
    unfold pairing
    rw [Finset.sum_eq_single j]
    · simp [v]
    · intro k _ hk
      simp [v,hk]
    · intro hj'
      exact (hj' (Finset.mem_univ j)).elim
  intro h
  have hmem : mk v hv ∈ hyperplane a := h.symm ▸ mem_univ _
  have hz := (mem_hyperplane_mk_iff a hv).mp hmem
  exact hj (hp.symm.trans hz)

theorem finitePointHyperplaneException_properties (p : X → ComplexProjectiveSpace N) (F : Finset X) :
    IsComplexAnalyticSubset (n := N) (finitePointHyperplaneException p F) ∧
    IsClosed (finitePointHyperplaneException p F) ∧
    interior (finitePointHyperplaneException p F) = ∅ ∧
    finitePointHyperplaneException p F ≠ univ ∧
    IsOpen (finitePointHyperplaneException p F)ᶜ ∧ Dense (finitePointHyperplaneException p F)ᶜ ∧
    (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (finitePointHyperplaneException p F) := by
  classical
  have ha (x : X) : IsComplexAnalyticSubset (n := N) (hyperplane (p x)) :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (isClosedSubmanifold_hyperplane (p x))
  have hi (x : X) : interior (hyperplane (p x)) = ∅ :=
    PshAnalyticSetExtension.IsComplexAnalyticSubset.interior_eq_empty_of_ne_univ (ha x) (actualHyperplane_proper (p x))
  have heq : finitePointHyperplaneException p F = ⋃ x ∈ F, hyperplane (p x) := by
    ext ℓ
    simp only [finitePointHyperplaneException,mem_ofPred_eq,mem_iUnion,exists_prop]
    exact exists_congr fun x => and_congr_right fun _ => Set.ext_iff.mp (actualPointHyperplane_eq p x) ℓ
  have hA : IsComplexAnalyticSubset (n := N) (finitePointHyperplaneException p F) := by
    rw [heq]
    exact ConstantRankImage.isComplexAnalyticSubset_biUnion F (fun x _ => ha x)
  have hI : interior (finitePointHyperplaneException p F) = ∅ := by
    have h := interior_iUnion_eq_empty_of_isClosed (s := fun x : F => hyperplane (p x.val))
      (fun x => isClosed_hyperplane (p x.val)) (fun x => hi x.val)
    convert h using 1
    congr 1
    ext ℓ
    simp only [finitePointHyperplaneException,mem_ofPred_eq,mem_iUnion,Subtype.exists,exists_prop]
    exact exists_congr fun x => and_congr_right fun _ => Set.ext_iff.mp (actualPointHyperplane_eq p x) ℓ
  have hproper : finitePointHyperplaneException p F ≠ univ := by
    intro h
    rw [h,interior_univ] at hI
    exact Set.univ_nonempty.ne_empty hI
  have hP : (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (finitePointHyperplaneException p F) := by
    have hp := ModificationMassInvariance.manifoldLocallyPluripolar_of_isComplexAnalyticSubset hA hI
    apply locallyPluripolar_of_in_chart
    intro e
    exact hp e
  exact ⟨hA,hA.isClosed,hI,hproper,hA.isClosed.isOpen_compl,interior_eq_empty_iff_dense_compl.mp hI,hP⟩

section Native
variable {d : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d + 1)) Y] [IsComplexManifold (d + 1) Y] [CompactSpace Y] [ConnectedSpace Y]
  (p : ContMDiffMap 𝓘(ℂ, ComplexModel (d + 1)) 𝓘(ℂ, ComplexModel N) Y (ComplexProjectiveSpace N) ∞)
  (L : HermitianHolomorphicLineBundle.{0,0} (d + 1) Y)
  {φ : Y → EReal} (hφ : IsGlobalQuasiPshPotential (n := d + 1) φ)

theorem exists_nativeBertini_generic_quotient_injective :
    ∃ F : Finset Y, F.Nonempty ∧ IsComplexAnalyticSubset (n := N) (finitePointHyperplaneException p F) ∧
      finitePointHyperplaneException p F ≠ univ ∧
      IsOpen (finitePointHyperplaneException p F)ᶜ ∧ Dense (finitePointHyperplaneException p F)ᶜ ∧
      (ofFixedModel N (HyperplaneSpace N)).LocallyPluripolar (finitePointHyperplaneException p F) ∧
      ∀ (i : Fin (N + 1)) (ζ : ComplexModel N)
        (hsm : IsSmoothHypersurfaceMember (d + 1) p (affinePoint i ζ)),
        affinePoint i ζ ∉ finitePointHyperplaneException p F →
        letI := nativeBertiniMemberChartedSpace p i ζ hsm
        letI := nativeBertiniMemberComplex p i ζ hsm
        letI := isCompact_iff_compactSpace.mp (isClosed_member p p.contMDiff.continuous (affinePoint i ζ)).isCompact
        Function.Injective (nativeBertiniPhysicalQuotientRestriction p i ζ hsm L hφ) := by
  obtain ⟨F,hF⟩ := exists_finite_nativeBertini_quotient_restriction_injective p L hφ
  classical
  let x₀ : Y := Classical.choice inferInstance
  let F' := insert x₀ F
  obtain ⟨ha,_hc,_hi,hp,ho,hd,hpl⟩ := finitePointHyperplaneException_properties p F'
  refine ⟨F',⟨x₀,Finset.mem_insert_self _ _⟩,ha,hp,ho,hd,hpl,?_⟩
  intro i ζ hsm hgood
  exact hF i ζ hsm (fun x hx hmem => hgood ⟨x,Finset.mem_insert_of_mem hx,hmem⟩)

end Native
end SGPT.Trace.Bertini
