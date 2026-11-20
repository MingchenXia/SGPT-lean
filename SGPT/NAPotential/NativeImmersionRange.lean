import SGPT.NAPotential.NativeSchemeImmersion

/-! # Actual native immersion point image is its genuine scheme image condition
Blueprint: `native-graph-local-image.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.NativeImmersionRange

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set

/-- **Actual native immersion complex-point image**, obtained from actual open lifting and actual closed lifting. -/
theorem pointMap_range {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of ℂ)) (fY : Y ⟶ Spec (.of ℂ))
    (j : X ⟶ Y) (hj : j ≫ fY = fX) [IsImmersion j] :
    Set.range (schemeComplexPointMap fX fY j hj) =
      {q | schemeComplexPointImage fY q ∈ Set.range j} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨schemeComplexPointImage fX p, (Scheme.Hom.comp_apply p.val j default).symm⟩
  · rintro ⟨y, hy⟩
    let O := j.coborderRange
    let c := j.liftCoborder
    let fO := O.ι ≫ fY
    have hcf : c ≫ fO = fX := by
      rw [← Category.assoc]
      exact (congrArg (fun h : X ⟶ Y => h ≫ fY) j.liftCoborder_ι).trans hj
    have hcy : O.ι (c y) = j y := by
      exact (Scheme.Hom.comp_apply c O.ι y).symm.trans (congrArg (fun k : X ⟶ Y => k y) j.liftCoborder_ι)
    have hqO : schemeComplexPointImage fY q ∈ Set.range O.ι := ⟨c y, hcy.trans hy⟩
    let qO : SchemeComplexPoint fO := schemeComplexPointLift fY O.ι q hqO
    have hqimage : O.ι (schemeComplexPointImage fO qO) = schemeComplexPointImage fY q := by
      exact (Scheme.Hom.comp_apply qO.val O.ι default).symm.trans
        (congrArg (fun k : Spec (.of ℂ) ⟶ Y => k default) (schemeComplexPointLift_fac fY O.ι q hqO))
    have hqc : schemeComplexPointImage fO qO ∈ Set.range c := by
      refine ⟨y, ?_⟩
      apply O.ι.isEmbedding.injective
      exact hcy.trans (hy.trans hqimage.symm)
    obtain ⟨p, hp⟩ := exists_closedImmersionComplexPoint fO c qO hqc
    let pX : SchemeComplexPoint fX := ⟨p.val, by rw [← hcf]; exact p.property⟩
    refine ⟨pX, ?_⟩
    apply Subtype.ext
    change p.val ≫ j = q.val
    have hpc : p.val ≫ c = qO.val := congrArg Subtype.val hp
    calc
      _ = (p.val ≫ c) ≫ O.ι := by rw [Category.assoc, j.liftCoborder_ι]
      _ = qO.val ≫ O.ι := by rw [hpc]
      _ = q.val := schemeComplexPointLift_fac fY O.ι q hqO

end SGPT.NAPotential.NativeImmersionRange
