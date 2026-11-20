import SGPT.Foundations.Schemes.SchemeComplexPointOpen
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.OkoNov16
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set

theorem original_restricted_complexPoint_bijective_of_good_inverse
    {X Y : Scheme} (f : X ⟶ Spec (.of ℂ)) (π : Y ⟶ X) (U : X.Opens)
    (s : SchemeComplexPoint f → SchemeComplexPoint (π ≫ f))
    (hr : ∀ x : SchemeComplexPoint f, schemeComplexPointImage f x ∈ U →
      schemeComplexPointMap (π ≫ f) f π rfl (s x) = x)
    (hl : ∀ y : SchemeComplexPoint (π ≫ f),
      schemeComplexPointImage f (schemeComplexPointMap (π ≫ f) f π rfl y) ∈ U →
      s (schemeComplexPointMap (π ≫ f) f π rfl y) = y) :
    Function.Bijective (schemeComplexPointMap ((π ⁻¹ᵁ U).ι ≫ (π ≫ f)) (U.ι ≫ f)
      (π ∣_ U) (by rw [← Category.assoc,morphismRestrict_ι,Category.assoc])) := by
  let W := π ⁻¹ᵁ U
  let N := schemeComplexPointMap (π ≫ f) f π rfl
  let A := schemeComplexPointMap (W.ι ≫ (π ≫ f)) (π ≫ f) W.ι rfl
  let B := schemeComplexPointMap (U.ι ≫ f) f U.ι rfl
  let M := schemeComplexPointMap (W.ι ≫ (π ≫ f)) (U.ι ≫ f) (π ∣_ U)
    (by rw [← Category.assoc,morphismRestrict_ι,Category.assoc])
  have hsq : ∀ q, B (M q) = N (A q) := by
    intro q
    apply Subtype.ext
    change (q.val ≫ (π ∣_ U)) ≫ U.ι = (q.val ≫ W.ι) ≫ π
    rw [Category.assoc,morphismRestrict_ι,Category.assoc]
  have hBU : ∀ x, schemeComplexPointImage f (B x) ∈ U := by
    intro x
    change (x.val default).1 ∈ U
    exact (x.val default).property
  have hAi : Function.Injective A := by
    intro p q h
    apply Subtype.ext
    exact (cancel_mono W.ι).mp (congrArg Subtype.val h)
  have hBi : Function.Injective B := by
    intro p q h
    apply Subtype.ext
    exact (cancel_mono U.ι).mp (congrArg Subtype.val h)
  change Function.Bijective M
  constructor
  · intro p q hpq
    apply hAi
    have hn : N (A p) = N (A q) := (hsq p).symm.trans ((congrArg B hpq).trans (hsq q))
    exact (hl (A p) (by change schemeComplexPointImage f (N (A p)) ∈ U; rw [← hsq];exact hBU _) ).symm.trans
      ((congrArg s hn).trans (hl (A q) (by change schemeComplexPointImage f (N (A q)) ∈ U; rw [← hsq];exact hBU _)))
  · intro x
    have hs : N (s (B x)) = B x := hr (B x) (hBU x)
    have hW : schemeComplexPointImage (π ≫ f) (s (B x)) ∈ range W.ι := by
      rw [Scheme.Opens.range_ι]
      change schemeComplexPointImage f (N (s (B x))) ∈ U
      rw [hs]
      exact hBU x
    let q := schemeComplexPointLift (π ≫ f) W.ι (s (B x)) hW
    refine ⟨q,hBi ?_⟩
    rw [hsq]
    have hq : A q = s (B x) := by
      apply Subtype.ext
      exact schemeComplexPointLift_fac (π ≫ f) W.ι _ hW
    rw [hq,hs]
end SGPT.Okounkov.OkoNov16
