import SGPT.Okounkov.AlgebraicValuationSections
import SGPT.Foundations.Schemes.LineSectionZeroSubscheme

/-! Genuine original local units and zero valuation from actual original zero-support avoidance.
Blueprint: okounkov-original-section-units.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalUnits
open Set CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open SGPT.Okounkov.AlgebraicValuation

variable {X : Scheme.{0}} {M : X.Modules}

/-- Actual original zero-support avoidance manufactures a local unit in EVERY genuine frame. -/
theorem isUnit_coefficientGerm_of_not_mem_zeroSupport (b : LineBundleAtlas M) (s : Γ(M,⊤))
    (c : X) (havoid : c ∉ (sectionZeroIdealSheaf b s).support)
    {U : X.Opens} (e : LocalBundleFrame M U) (hc : c ∈ U) :
    IsUnit (X.presheaf.germ U c hc
      (e.coefficients (𝟙 _) (M.val.map U.leTop.op s))) := by
  obtain ⟨V,hV,hcV,hVU⟩ := exists_isAffineOpen_mem_and_subset hc
  let a : Γ(X,V) := e.coefficients (homOfLE hVU) (M.val.map V.leTop.op s)
  have hsupp : c ∈ (sectionZeroIdealSheaf b s).support ↔ c ∉ X.basicOpen a := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U:=⟨V,hV⟩) hcV]
    change c ∈ X.zeroLocus (U:=V) (sectionZeroIdeal M s V : Set Γ(X,V)) ↔ _
    rw [sectionZeroIdeal_eq_span_frame s e (homOfLE hVU),Scheme.zeroLocus_span,Scheme.zeroLocus_singleton]
    rfl
  have hb : c ∈ X.basicOpen a := by
    by_contra hn
    exact havoid (hsupp.mpr hn)
  have hu := (X.mem_basicOpen a c hcV).mp hb
  change IsUnit (X.presheaf.germ V c hcV
    (e.coefficients (homOfLE hVU) (M.val.map V.leTop.op s))) at hu
  have hres := frame_global_coefficients_restrict e (homOfLE hVU) s
  have hgerm : X.presheaf.germ V c hcV
      (e.coefficients (homOfLE hVU) (M.val.map V.leTop.op s)) =
      X.presheaf.germ U c hc (e.coefficients (𝟙 _) (M.val.map U.leTop.op s)) :=
    (congrArg (fun r : Γ(X,V) => X.presheaf.germ V c hcV r) hres).trans
      (X.presheaf.germ_res_apply (homOfLE hVU) c hcV _)
  exact hgerm ▸ hu

variable [IsIntegral X] {n : ℕ}
  (v : AddValuation X.functionField (WithTop (Lex (Fin n → ℤ))))

/-- Actual ordinary section avoiding the original center has ZERO existing original valuation. -/
theorem plainSectionValue_eq_zero_of_not_mem_zeroSupport (b : LineBundleAtlas M) (s : Γ(M,⊤))
    (c : X) (hc : IsNonnegAt v c) (havoid : c ∉ (sectionZeroIdealSheaf b s).support) :
    plainSectionValue v c b s = 0 := by
  let U := b.opens (b.centerIndex c)
  let e := b.frame (b.centerIndex c)
  have hcU : c ∈ U := b.centerIndex_mem c
  let : Nonempty U := ⟨⟨c,hcU⟩⟩
  have hu := isUnit_coefficientGerm_of_not_mem_zeroSupport b s c havoid e hcU
  obtain ⟨u,hu⟩ := hu
  change v (X.germToFunctionField U (e.coefficients (𝟙 _) (M.val.map U.leTop.op s))) = 0
  rw [← X.algebraMap_germ_eq_germToFunctionField hcU,← hu]
  exact valuation_stalkUnit_eq_zero hc u

end SGPT.Okounkov.OriginalUnits
