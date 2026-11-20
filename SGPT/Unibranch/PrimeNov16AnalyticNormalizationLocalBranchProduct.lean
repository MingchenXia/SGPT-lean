import SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralExtensionTest
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Original local ring normality from the ENTIRE actual branch product.
Blueprint: prime-nov16-analytic-normalization-local-branch-product.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalBranchProduct

theorem local_of_bijective_normal_product {A ι : Type*} [CommRing A]
    [IsLocalRing A] (D : ι → Type*) [∀ i,CommRing (D i)] [∀ i,IsDomain (D i)]
    [∀ i,IsIntegrallyClosed (D i)] (f : A →+* ∀ i,D i)
    (hf : Function.Injective f) (hs : Function.Surjective f) : IsDomain A ∧ IsIntegrallyClosed A := by
  classical
  have hi : Nonempty ι := by
    by_contra hempty
    let : IsEmpty ι := not_nonempty_iff.mp hempty
    have he : f 0=f 1 := Subsingleton.elim _ _
    exact zero_ne_one (hf he)
  obtain ⟨i0⟩ := hi
  let : Nonempty ι := ⟨i0⟩
  let : Nontrivial (∀ i,D i) := ⟨⟨0,1,fun he => zero_ne_one (congrFun he i0)⟩⟩
  let : IsLocalRing (∀ i,D i) := IsLocalRing.of_surjective' f hs
  have hsub : Subsingleton ι := by
    constructor
    intro i j
    by_contra hij
    let e : ∀ k,D k := fun k => if k=i then 1 else 0
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with he | he
    · have hz := he.map (Pi.evalRingHom D j)
      have hji : j ≠ i := Ne.symm hij
      simp [e,hji] at hz
    · have hz := he.map (Pi.evalRingHom D i)
      simp [e] at hz
  let : Subsingleton ι := hsub
  have heval : Function.Bijective (Pi.evalRingHom D i0) := by
    constructor
    · intro a b he
      funext i
      obtain rfl : i=i0 := Subsingleton.elim _ _
      exact he
    · intro d
      refine ⟨fun i => if h : i=i0 then h.symm ▸ d else 0,?_⟩
      simp
  let e := (RingEquiv.ofBijective f ⟨hf,hs⟩).trans (RingEquiv.ofBijective (Pi.evalRingHom D i0) heval)
  exact ⟨Function.Injective.isDomain e e.injective,IsIntegrallyClosed.of_equiv e.symm⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalBranchProduct
