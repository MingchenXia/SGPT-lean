import SGPT.Toric.Toric3PEquivalence

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ContDiff BigOperators Manifold

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric

/-- Actual trivial bundle metric, with zero curvature and zero frame weights. -/
def zeroMetric : BigToricMetric (0 : ToricDivisor γ hs) where
  form := 0
  weight _ _ := 0
  smooth _ := contDiff_const
  coeff _ z := by rw [smoothDDC_zero]; rfl
  invariant _ _ _ _ := rfl
  transition _ _ _ := by simp [toricCartierDatum, latticeFunctional_apply]

/-- Actual tensor-product metric, constructed from its smooth frame weights,
transition functions, literal sum curvature and compact-torus invariance. -/
def addMetric {D E : ToricDivisor γ hs} (h : BigToricMetric D) (g : BigToricMetric E) :
    BigToricMetric (D + E) where
  form := h.form + g.form
  weight v z := h.weight v z + g.weight v z
  smooth v := (h.smooth v).add (g.smooth v)
  coeff v z := by
    change h.form.val.coeff (polytopeToricVertexChart γ hs v) z +
      g.form.val.coeff (polytopeToricVertexChart γ hs v) z = _
    rw [h.coeff v z, g.coeff v z]
    exact (smoothDDC_add isOpen_univ (h.smooth v).contDiffOn
      (g.smooth v).contDiffOn (mem_univ z)).symm
  invariant v a ha z := by rw [h.invariant v a ha z, g.invariant v a ha z]
  transition v w a := by
    rw [toricCartierDatum_add, toricCartierDatum_add,
      latticeFunctional_add_apply, latticeFunctional_add_apply]
    linarith [h.transition v w a, g.transition v w a]

@[simp] theorem zeroMetric_potential (x : EuclideanSpace ℝ (Fin n)) :
    (zeroMetric (γ := γ) (hs := hs)).potential x = 0 := by
  simp [potential, zeroMetric, toricCartierDatum, latticeFunctional_apply]

@[simp] theorem addMetric_potential {D E : ToricDivisor γ hs}
    (h : BigToricMetric D) (g : BigToricMetric E) (x : EuclideanSpace ℝ (Fin n)) :
    (h.addMetric g).potential x = h.potential x + g.potential x := by
  simp only [potential, addMetric, toricCartierDatum_add, latticeFunctional_add_apply]
  ring

/-- Transport only the actual divisor index; the metric's geometry is retained. -/
def castMetric {D E : ToricDivisor γ hs} (hDE : D = E) (h : BigToricMetric D) :
    BigToricMetric E := hDE ▸ h

@[simp] theorem castMetric_form {D E : ToricDivisor γ hs}
    (hDE : D = E) (h : BigToricMetric D) : (castMetric hDE h).form = h.form := by
  subst E
  rfl

@[simp] theorem castMetric_potential {D E : ToricDivisor γ hs}
    (hDE : D = E) (h : BigToricMetric D) (x : EuclideanSpace ℝ (Fin n)) :
    (castMetric hDE h).potential x = h.potential x := by
  subst E
  rfl

/-- Every actual finite tensor-product family internally manufactures the
metric on the actual sum divisor, with the SAME sum curvature and profile
reference potential. The empty family is the actual trivial metric. -/
theorem exists_finite_sum_metric {ι : Type*} (D : ι → ToricDivisor γ hs)
    (h : ∀ i, BigToricMetric (D i)) (S : Finset ι) :
    ∃ H : BigToricMetric (∑ i ∈ S, D i),
      H.form = ∑ i ∈ S, (h i).form ∧
      ∀ x, H.potential x = ∑ i ∈ S, (h i).potential x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨zeroMetric, rfl, zeroMetric_potential⟩
  | @insert a S ha ih =>
    obtain ⟨H, hform, hpot⟩ := ih
    have hdiv : (∑ i ∈ insert a S, D i) = D a + ∑ i ∈ S, D i :=
      Finset.sum_insert ha
    refine ⟨castMetric hdiv.symm ((h a).addMetric H), ?_, ?_⟩
    · rw [castMetric_form]
      change (h a).form + H.form = ∑ i ∈ insert a S, (h i).form
      rw [hform, Finset.sum_insert ha]
    · intro x
      rw [castMetric_potential, addMetric_potential, hpot x, Finset.sum_insert ha]

private theorem ereal_coe_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ S, f i : ℝ) : EReal) = ∑ i ∈ S, (f i : EReal) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp only [Finset.sum_insert ha, EReal.coe_add, ih]

/-- Actual reference potentials identify the profile of the literal sum of
global potentials with the literal sum of the ORIGINAL individual profiles.
No Newton-body or mixed-volume equality is an input. -/
theorem profile_finite_sum {ι : Type*} (D : ι → ToricDivisor γ hs)
    (h : ∀ i, BigToricMetric (D i)) (S : Finset ι)
    (H : BigToricMetric (∑ i ∈ S, D i))
    (hpot : ∀ x, H.potential x = ∑ i ∈ S, (h i).potential x)
    (u : ι → PolytopeToricVariety γ hs → EReal) :
    H.profile (fun p => ∑ i ∈ S, u i p) =
      fun x => ∑ i ∈ S, (h i).profile (u i) x := by
  funext x
  simp only [profile, hpot, ereal_coe_finset_sum, Finset.sum_add_distrib]

end BigToricMetric
end SGPT.Toric
