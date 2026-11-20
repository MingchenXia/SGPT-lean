import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRange
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphProper

/-! Actual entire-graph monics manufacture genuine properfinite projection and whole-base cleared equations.
Blueprint: prime-nov16-analytic-normalization-original-integral-geometry.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
open PrimeNov16AnalyticNormalizationOriginalGraphRange
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphProper
open PrimeNov16AnalyticNormalizationGraphFinite

variable {n : ℕ} {Z : Set (ComplexModel n)}

theorem actual_graph_rational_monic (d : GraphPresentation n Z) (deg : Fin d.arity → ℕ)
    (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0) :
    ∀ x : d.base.obj.left,d.denominator x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (deg i) (a i) x.val.val
        (d.numerator i x.val.val/d.denominator x.val.val)=0 := by
  intro x hx i
  obtain ⟨p,hp⟩ := original_good_point_mem_range (ballDomain (n := n) d.radius)
    d.carrier_analytic d.denominator d.numerator d.denominator_holo d.numerator_holo x hx
  have hb : baseProjection n d.arity p.val.val=x.val.val :=
    congrArg (fun b : d.base.obj.left => b.val.val) hp
  have hd : d.denominator x.val.val*fibreProjection n d.arity p.val.val i=d.numerator i x.val.val := by
    simpa only [hb] using whole_denominator_identity d p i
  have ht : fibreProjection n d.arity p.val.val i=d.numerator i x.val.val/d.denominator x.val.val :=
    (eq_div_iff hx).mpr ((mul_comm _ _).trans hd)
  simpa only [hb,ht] using hm p i

theorem actual_graph_projection_proper (d : GraphPresentation n Z) (deg : Fin d.arity → ℕ)
    (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius))
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0) :
    IsProperMap d.projection.hom.left.base :=
  projection_isProperMap (ballDomain (n := n) d.radius) d.carrier_analytic d.denominator d.numerator
    d.denominator_holo d.numerator_holo deg a ha (actual_graph_rational_monic d deg a hm)

theorem actual_graph_projection_finite (d : GraphPresentation n Z) (deg : Fin d.arity → ℕ)
    (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius))
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0)
    (b : d.base.obj.left) : (d.projection.hom.left.base ⁻¹' {b}).Finite :=
  projection_fibres_finite (ballDomain (n := n) d.radius) d.carrier_analytic d.denominator d.numerator
    d.denominator_holo d.numerator_holo deg a ha (actual_graph_rational_monic d deg a hm) b

theorem cleared_monic_of_root {R : Type*} [CommRing R] (k : ℕ) (c : ℕ → R)
    (h t g : R) (hgt : h*t=g) (he : t^k+∑ j ∈ Finset.range k,c j*t^j=0) :
    g^k+∑ j ∈ Finset.range k,c j*h^(k-j)*g^j=0 := by
  subst g
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      c j*h^(k-j)*(h*t)^j=h^k*(c j*t^j) := by
    rw [mul_pow]
    calc
      c j*h^(k-j)*(h^j*t^j)=c j*(h^(k-j)*h^j)*t^j := by ring
      _=c j*h^k*t^j := by rw [← pow_add,Nat.sub_add_cancel (Finset.mem_range.mp hj).le]
      _=h^k*(c j*t^j) := by ring
  calc
    (h*t)^k+∑ j ∈ Finset.range k,c j*h^(k-j)*(h*t)^j=
        h^k*t^k+∑ j ∈ Finset.range k,h^k*(c j*t^j) := by
      rw [mul_pow]
      congr 1
      exact Finset.sum_congr rfl hterm
    _=h^k*(t^k+∑ j ∈ Finset.range k,c j*t^j) := by rw [mul_add,Finset.mul_sum]
    _=0 := by rw [he,mul_zero]

theorem actual_whole_base_cleared (d : GraphPresentation n Z) (deg : Fin d.arity → ℕ)
    (a : Fin d.arity → ℕ → ComplexModel n → ℂ)
    (hm : ∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
      (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0)
    (hs : Function.Surjective d.map.hom.left.base) (b : d.target.obj.left) (i : Fin d.arity) :
    (d.numerator i b.val.val.val)^(deg i)+∑ j ∈ Finset.range (deg i),
      a i j b.val.val.val*(d.denominator b.val.val.val)^(deg i-j)*(d.numerator i b.val.val.val)^j=0 := by
  obtain ⟨p,hp⟩ := hs b
  have hb : baseProjection n d.arity p.val.val.val=b.val.val.val :=
    (map_ambient d p).symm.trans (congrArg (fun x : d.target.obj.left => x.val.val.val) hp)
  have hroot := hm p.val i
  change (fibreProjection n d.arity p.val.val.val i)^(deg i)+∑ j ∈ Finset.range (deg i),
    a i j (baseProjection n d.arity p.val.val.val)*(fibreProjection n d.arity p.val.val.val i)^j=0 at hroot
  have he := cleared_monic_of_root (deg i) (fun j => a i j (baseProjection n d.arity p.val.val.val))
    (d.denominator (baseProjection n d.arity p.val.val.val)) (fibreProjection n d.arity p.val.val.val i)
    (d.numerator i (baseProjection n d.arity p.val.val.val)) (whole_denominator_identity d p.val i) hroot
  simpa only [hb] using he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
