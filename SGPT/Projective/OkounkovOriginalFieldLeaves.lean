import SGPT.Projective.OkounkovOriginalBookVolume

/-! Genuine one-dimensional leaves on the ENTIRE original function field.
Blueprint: okounkov-original-field-leaves.tex. No leaf/cone/ratio certificate is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OriginalFieldLeaves
open Set Filter CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov.ValGen SGPT.Okounkov.AlgebraicValuation SGPT.AlmostSemigroup
open SGPT.LineBundle
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology
variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
  {m : ℕ} [SmoothOfRelativeDimension (m+1) f] (E : ClosedProjectiveEmbedding f)
  [Nonempty (SchemeComplexPoint f)] {L : X.Modules} (a : LineBundleAtlas L)
  (hbig : SGPT.LineBundle.IsBig f L (m+1))
  (v : AddValuation X.functionField (WithTop (Lex (Fin (m+1) → ℤ)))) (hv : Function.Surjective v)
include f E a hbig hv

/-- Actual arbitrary full-rank original valuation cancellation on the ENTIRE original function field. -/
theorem exists_originalField_leaf_cancel (x y : X.functionField) (hy : y≠0) (hxy : v x=v y) :
    letI := schemeFunctionFieldAlgebra f
    ∃ c : ℂ, c≠0 ∧ v x < v (x + algebraMap ℂ X.functionField c * y) := by
  let := schemeFunctionFieldAlgebra f
  obtain ⟨Y,hY⟩ := OriginalBook.exists_original_smoothFlag_allDimensions f (m+1) E
  let c := genericPoint X
  obtain ⟨C,hS,hG⟩ := OriginalBook.exists_original_admissibleCone_allDimensions f a (m+1) E hbig v hv c
  obtain ⟨B,hB⟩ := exists_h0_le_pow f (m+1) E Y hY a
  obtain ⟨c₀,hc₀,hlow⟩ := exists_card_slice_ge f a c v hS hG
  have hfinS : ∀ j, FiniteDimensional ℂ (SectionSpace f L j) :=
    fun j => SectionSpace.finiteDimensional f E a j
  have hfin : ∀ j, FiniteDimensional ℂ (sectionRange f c a j) := by
    intro j
    have := hfinS j
    exact LinearMap.finiteDimensional_range _
  have hrank : ∀ j, Module.finrank ℂ (sectionRange f c a j) = SGPT.LineBundle.h0 f L j := by
    intro j
    have := hfinS j
    exact LinearMap.finrank_range_of_inj (sectionToField_injective f c a j)
  have hlow' : ∀ᶠ j : ℕ in atTop,
      c₀ * (j:ℝ)^(m+1) ≤ Nat.card (valueSet v (sectionRange f c a j).subtype) := by
    filter_upwards [hlow] with j hj
    have heq := card_valueSet_map_eq f c a v j ⊤
    rw [Submodule.map_top] at heq
    change c₀ * (j:ℝ)^(m+1) ≤ (Nat.card (valueSet v (sectionRange f c a j).subtype):ℝ)
    rw [show sectionRange f c a j = LinearMap.range (sectionToField f c a j) from rfl,heq]
    exact hj
  have hup : ∀ᶠ j : ℕ in atTop,
      (Module.finrank ℂ (sectionRange f c a j):ℝ) ≤ B*(j:ℝ)^(m+1) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    rw [hrank]
    exact hB j hj
  have hx : x≠0 := by
    intro h0
    apply (v.ne_top_iff.mpr hy)
    simpa only [v.map_zero] using ((congrArg v h0).symm.trans hxy).symm
  obtain ⟨k,-,s,t,hs,ht,hratio⟩ :=
    OriginalRationalPairs.exists_bigLine_equalDegree_sectionPair a f E Y hY hbig (x/y) (div_ne_zero hx hy)
  let p := sectionToField f c a k s
  let q := sectionToField f c a k t
  have hq : q≠0 := by
    intro h0
    exact ht (sectionToField_injective f c a k (h0.trans (map_zero _).symm))
  have hpq : p/q=x/y := hratio _ ⟨⟨c,a.centerIndex_mem c⟩⟩ ((a.frame (a.centerIndex c)).tensorPower k)
  let z := y/q
  have hz : z≠0 := div_ne_zero hy hq
  have hzp : z*p=x := by dsimp only [z]; field_simp [hq,hy] at hpq ⊢; linear_combination hpq
  have hzq : z*q=y := div_mul_cancel₀ y hq
  have hvz : v z≠⊤ := v.ne_top_iff.mpr hz
  have hvpq : v p=v q := WithTop.add_left_cancel hvz (by
    rw [←v.map_mul,←v.map_mul,hzp,hzq]
    exact hxy)
  obtain ⟨d,hd,hcancel⟩ := exists_leaf_cancel hfin (one_mem_sectionRange f c a)
    (fun hu hw => mul_mem_sectionRange f c a hu hw) hc₀ hlow' hup
    (show p∈sectionRange f c a k from ⟨s,rfl⟩) (show q∈sectionRange f c a k from ⟨t,rfl⟩) hq hvpq
  refine ⟨d,hd,?_⟩
  have hfactor : x + algebraMap ℂ X.functionField d * y = z*(p+algebraMap ℂ X.functionField d*q) := by
    calc
      _ = z*p + algebraMap ℂ X.functionField d*(z*q) := by rw [hzp,hzq]
      _ = _ := by ring
  rw [hfactor,←hzp,v.map_mul,v.map_mul]
  exact WithTop.add_lt_add_left hvz hcancel

/-- ANY actual finite-dimensional original field representation has the genuine dimension value count. -/
theorem card_originalFieldValueSet_eq_finrank {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W]
    (ι : letI := schemeFunctionFieldAlgebra f; W →ₗ[ℂ] X.functionField)
    (hι : Function.Injective ι) :
    letI := schemeFunctionFieldAlgebra f
    Nat.card (valueSet v ι)=Module.finrank ℂ W := by
  let := schemeFunctionFieldAlgebra f
  apply card_valueSet_eq_finrank v ι hι (fun d hd => valuation_algebraMap_complex v hd)
  intro s t _hs ht hst
  have ht0 : ι t≠0 := fun h => ht (hι (h.trans (map_zero _).symm))
  obtain ⟨d,hd,hcancel⟩ := exists_originalField_leaf_cancel f E a hbig v hv (ι s) (ι t) ht0 hst
  refine ⟨d,hd,?_⟩
  simpa only [map_add,map_smul,Algebra.smul_def] using hcancel

end SGPT.Okounkov.OriginalFieldLeaves
