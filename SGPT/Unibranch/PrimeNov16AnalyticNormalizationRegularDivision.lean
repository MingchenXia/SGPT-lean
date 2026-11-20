import SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularOriginalStalk
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! Actual local division at genuine regular points, from primitive monic relations.
Blueprint: prime-nov16-analytic-normalization-regular-division.tex. -/
set_option autoImplicit false
noncomputable section
open Set Polynomial
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularDivision
open HironakaActualAnalyticSubspace
open PrimeNov16AnalyticNormalizationRegularOriginalStalk

theorem exists_divisor_of_scaled_monic {A : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (g h : A) (hh : h ≠ 0) (p : A[X]) (hp : p.Monic)
    (hrel : eval g (p.scaleRoots h) = 0) : ∃ q : A,g=h*q := by
  let f := algebraMap A (FractionRing A)
  have hfn : f h ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A (FractionRing A)).ne hh
  let u : FractionRing A := f g/f h
  have hu : f h*u=f g := by dsimp [u]; exact mul_div_cancel₀ _ hfn
  have hroot : aeval u p = 0 := by
    have he := Polynomial.scaleRoots_eval₂_mul (p := p) f u h
    rw [hu] at he
    have hz : eval₂ f (f g) (p.scaleRoots h) = 0 := by
      have hz := congrArg f hrel
      change f (eval₂ (RingHom.id A) g (p.scaleRoots h)) = f 0 at hz
      rw [Polynomial.hom_eval₂,map_zero] at hz
      exact hz
    rw [hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hfn)
  obtain ⟨q,hq⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance
    (show IsIntegral A u from ⟨p,hp,hroot⟩)
  refine ⟨q,IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul,hq]
  exact hu.symm

theorem actual_regular_original_stalk_division {d t : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (d+t)) M]
    [IsComplexManifold (d+t) M] (C : Set M) (x : M)
    (hreg : RegularAtDim (n := d+t) C x d)
    (g h : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier)
    (hh : h ≠ 0)
    (p : Polynomial ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier)
    (hp : p.Monic) (hrel : eval g (p.scaleRoots h)=0) :
    ∃ q : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier,g=h*q := by
  obtain ⟨hd,hn⟩ := actual_regular_original_stalk_normal C x hreg
  let := hd
  let := hn
  exact exists_divisor_of_scaled_monic g h hh p hp hrel

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularDivision
