import SGPT.PSH.OhsawaTakegoshiRestriction

/-! Full actual book restriction stalk inclusion for CLOSED REGULAR W,
without connectedness, nonempty W or finite restricted-weight point. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Trace.BertiniUniversal
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
open SGPT.Okounkov SGPT.PSH.IdealRestriction SGPT.PSH.OhsawaTakegoshi
variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}

theorem regular_multiplierIdeal_restrict_le_restStalk
    (hclosed : IsClosed W) (hk : m ≤ n)
    (hreg : ∀ x ∈ W, RegularAtDim (n := n) W x m)
    {φ : X → EReal} (hφ : ManifoldQuasiPlurisubharmonic (n := n) φ) (c : ℝ) :
    let hC : IsClosedSubmanifold n W := ⟨hclosed,fun x hx => ⟨m,hreg x hx⟩⟩
    letI := chartedSpace hk hreg
    ∀ p : W,
      Ideal.comap (structureStalkEquiv hk hreg hC p)
        (stalkIdeal (multiplierIdeal (n := m) c (fun q : W => φ q.val)) p) ≤
      restStalk (multiplierIdeal (n := n) c φ) (submanifoldSubspace hC) p.val := by
  intro hC
  let := chartedSpace hk hreg
  intro p
  let e := structureStalkEquiv hk hreg hC p
  rw [← Ideal.map_symm,Ideal.map_le_iff_le_comap]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨f,hf,hmem,rfl⟩
  obtain ⟨F,hF,hFf⟩ := SGPT.PSH.OhsawaTakegoshi.exists_extension_mem_multiplierIdeal hk hreg hφ p f hmem
  have hFhol : HolomorphicAt n F p.val := hF.1
  have he : e (Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol)) = NativeHolGerm.mk f hf := by
    rw [structureStalkEquiv_mk,restrictGerm_mk]
    exact NativeHolGerm.mk_eq_mk_iff.mpr hFf
  have hsymm : e.symm (NativeHolGerm.mk f hf) =
      Ideal.Quotient.mk _ (NativeHolGerm.mk F hFhol) := by
    rw [← he]
    exact e.symm_apply_apply _
  rw [SetLike.mem_coe,Ideal.mem_comap]
  change e.symm (NativeHolGerm.mk f hf) ∈ _
  rw [hsymm]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨F,hFhol,hF,rfl⟩)

end SGPT.Trace.BertiniUniversal
