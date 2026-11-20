import SGPT.Convex.FamilyOperations
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Pi

/-!
# The actual finite weighted rooftop

Admissible tuples use actual domain points and nonnegative real weights of
total one. Their costs are finite real values, with no convention for zero
times an infinite value. This is Appendix A `prop:concavhull`.
-/

namespace SGPT.Convex

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {I : Type*} [Fintype I]

/-- The actual tuples occurring in the source's finite rooftop formula. -/
structure RooftopData (f : I → V → EReal) where
  weight : I → ℝ
  point : I → V
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  point_mem_domain : ∀ i, point i ∈ effectiveDomain (f i)

namespace RooftopData

omit [AddCommGroup V] [Module ℝ V] in
/-- Every weight in an actual admissible tuple lies in the source interval. -/
theorem weight_le_one {f : I → V → EReal} (d : RooftopData f) (i : I) :
    d.weight i ≤ 1 := by
  rw [← d.weight_sum]
  exact Finset.single_le_sum (fun j _ ↦ d.weight_nonneg j) (Finset.mem_univ i)

/-- The actual weighted sum of the domain points. -/
noncomputable def barycenter {f : I → V → EReal} (d : RooftopData f) : V :=
  ∑ i, d.weight i • d.point i

/-- The actual finite real cost of an admissible tuple. -/
noncomputable def cost {f : I → V → EReal} (d : RooftopData f) : ℝ :=
  ∑ i, d.weight i * (f i (d.point i)).toReal

end RooftopData

/-- The actual displayed infimum in source `prop:concavhull`. -/
noncomputable def weightedRooftop (f : I → V → EReal) (x : V) : EReal :=
  ⨅ (d : RooftopData f) (_ : d.barycenter = x), (d.cost : EReal)

/-- An actual admissible tuple bounds the actual weighted rooftop at its barycenter. -/
theorem weightedRooftop_le_cost {f : I → V → EReal} (d : RooftopData f) :
    weightedRooftop f d.barycenter ≤ (d.cost : EReal) :=
  iInf_le_of_le d (iInf_le_of_le rfl le_rfl)

/-- A finite convex epigraph combination bounds every actual convex common minorant. -/
theorem le_weightedRooftop {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    {g : V → EReal} (hg : IsConvex g) (hgf : ∀ i, g ≤ f i) :
    g ≤ weightedRooftop f := by
  classical
  intro x
  apply le_iInf
  intro d
  apply le_iInf
  intro hx
  have hfinite (i : I) : f i (d.point i) = ((f i (d.point i)).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt (d.point_mem_domain i)) ((hf i).2.2 _)).symm
  have hmem (i : I) : (d.point i, (f i (d.point i)).toReal) ∈ epigraph g := by
    exact (hgf i _).trans (hfinite i).le
  have hcombo := hg.sum_mem (t := Finset.univ) (fun i _ ↦ d.weight_nonneg i)
    d.weight_sum (fun i _ ↦ hmem i)
  have hpair : (∑ i, d.weight i • (d.point i, (f i (d.point i)).toReal)) =
      (d.barycenter, d.cost) := by
    ext <;> simp [RooftopData.barycenter, RooftopData.cost, Prod.fst_sum, Prod.snd_sum]
  rw [hpair] at hcombo
  change g d.barycenter ≤ (d.cost : EReal) at hcombo
  simpa only [hx] using hcombo

/-- Each family member bounds the actual weighted rooftop, using unit weights. -/
theorem weightedRooftop_le {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    (i : I) : weightedRooftop f ≤ f i := by
  classical
  choose q hq using fun j ↦ (hf j).2.1
  intro x
  by_cases hx : f i x = ⊤
  · rw [hx]
    exact le_top
  let d : RooftopData f :=
    { weight := fun j ↦ if j = i then 1 else 0
      point := fun j ↦ if j = i then x else q j
      weight_nonneg := fun j ↦ by split_ifs <;> norm_num
      weight_sum := by simp
      point_mem_domain := fun j ↦ by
        split_ifs with h
        · subst j
          exact lt_top_iff_ne_top.mpr hx
        · exact hq j }
  have hb : d.barycenter = x := by
    change (∑ j, (if j = i then (1 : ℝ) else 0) • (if j = i then x else q j)) = x
    have hterm (j : I) : (if j = i then (1 : ℝ) else 0) • (if j = i then x else q j) =
        if j = i then x else 0 := by split_ifs <;> simp_all
    simp only [hterm]
    simp
  have hc : d.cost = (f i x).toReal := by simp [d, RooftopData.cost]
  have hbound := weightedRooftop_le_cost d
  rw [hb, hc, EReal.coe_toReal hx ((hf i).2.2 x)] at hbound
  exact hbound

namespace RooftopData

/-- Merge actual weighted tuples by normalizing each positive combined weight. -/
noncomputable def combine {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    (d e : RooftopData f) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    RooftopData f where
  weight i := a * d.weight i + b * e.weight i
  point i := if 0 < a * d.weight i + b * e.weight i then
    (a * d.weight i / (a * d.weight i + b * e.weight i)) • d.point i +
      (b * e.weight i / (a * d.weight i + b * e.weight i)) • e.point i
    else d.point i
  weight_nonneg i := add_nonneg (mul_nonneg ha (d.weight_nonneg i))
    (mul_nonneg hb (e.weight_nonneg i))
  weight_sum := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, d.weight_sum, e.weight_sum,
      mul_one, hab]
  point_mem_domain := by
    intro i
    split_ifs with hi
    · apply convex_effectiveDomain (hf i).1 (d.point_mem_domain i) (e.point_mem_domain i)
      · exact div_nonneg (mul_nonneg ha (d.weight_nonneg i)) hi.le
      · exact div_nonneg (mul_nonneg hb (e.weight_nonneg i)) hi.le
      · rw [← add_div, div_self (ne_of_gt hi)]
    · exact d.point_mem_domain i

/-- The actual barycenter of merged tuples is their convex combination. -/
theorem barycenter_combine {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    (d e : RooftopData f) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (combine hf d e a b ha hb hab).barycenter = a • d.barycenter + b • e.barycenter := by
  have hterm (i : I) : (combine hf d e a b ha hb hab).weight i •
        (combine hf d e a b ha hb hab).point i =
      a • (d.weight i • d.point i) + b • (e.weight i • e.point i) := by
    change (a * d.weight i + b * e.weight i) •
      (if 0 < a * d.weight i + b * e.weight i then
        (a * d.weight i / (a * d.weight i + b * e.weight i)) • d.point i +
          (b * e.weight i / (a * d.weight i + b * e.weight i)) • e.point i
        else d.point i) = _
    split_ifs with hi
    · have hα : (a * d.weight i + b * e.weight i) *
          (a * d.weight i / (a * d.weight i + b * e.weight i)) = a * d.weight i := by
        field_simp
      have hβ : (a * d.weight i + b * e.weight i) *
          (b * e.weight i / (a * d.weight i + b * e.weight i)) = b * e.weight i := by
        field_simp
      simp only [smul_add, smul_smul, hα, hβ]
    · have hd := mul_nonneg ha (d.weight_nonneg i)
      have he := mul_nonneg hb (e.weight_nonneg i)
      have hzero : a * d.weight i + b * e.weight i = 0 := by linarith
      have hα : a * d.weight i = 0 := by linarith
      have hβ : b * e.weight i = 0 := by linarith
      simp [smul_smul, hα, hβ]
  unfold barycenter
  rw [Finset.sum_congr rfl (fun i _ ↦ hterm i)]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum]

/-- Convexity of each actual obstacle bounds the cost of the merged tuple. -/
theorem cost_combine_le {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    (d e : RooftopData f) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (combine hf d e a b ha hb hab).cost ≤ a * d.cost + b * e.cost := by
  let c := combine hf d e a b ha hb hab
  have hterm (i : I) : c.weight i * (f i (c.point i)).toReal ≤
      a * (d.weight i * (f i (d.point i)).toReal) +
        b * (e.weight i * (f i (e.point i)).toReal) := by
    have hd := mul_nonneg ha (d.weight_nonneg i)
    have he := mul_nonneg hb (e.weight_nonneg i)
    by_cases hi : 0 < a * d.weight i + b * e.weight i
    · have hsum : a * d.weight i / (a * d.weight i + b * e.weight i) +
          b * e.weight i / (a * d.weight i + b * e.weight i) = 1 := by
        rw [← add_div, div_self (ne_of_gt hi)]
      have hdfinite : f i (d.point i) = ((f i (d.point i)).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt (d.point_mem_domain i)) ((hf i).2.2 _)).symm
      have hefinite : f i (e.point i) = ((f i (e.point i)).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt (e.point_mem_domain i)) ((hf i).2.2 _)).symm
      have hconv := (hf i).1 (x := (d.point i, (f i (d.point i)).toReal))
        (y := (e.point i, (f i (e.point i)).toReal)) hdfinite.le hefinite.le
        (div_nonneg hd hi.le) (div_nonneg he hi.le) hsum
      have hpoint : c.point i =
          (a * d.weight i / (a * d.weight i + b * e.weight i)) • d.point i +
            (b * e.weight i / (a * d.weight i + b * e.weight i)) • e.point i := by
        simp only [c, combine, if_pos hi]
      have hcfinite : f i (c.point i) = ((f i (c.point i)).toReal : EReal) :=
        (EReal.coe_toReal (ne_of_lt (c.point_mem_domain i)) ((hf i).2.2 _)).symm
      change f i ((a * d.weight i / (a * d.weight i + b * e.weight i)) • d.point i +
        (b * e.weight i / (a * d.weight i + b * e.weight i)) • e.point i) ≤
        ((a * d.weight i / (a * d.weight i + b * e.weight i) * (f i (d.point i)).toReal +
          b * e.weight i / (a * d.weight i + b * e.weight i) *
            (f i (e.point i)).toReal : ℝ) : EReal) at hconv
      rw [← hpoint, hcfinite, EReal.coe_le_coe_iff] at hconv
      have hbound := mul_le_mul_of_nonneg_left hconv hi.le
      have hα : (a * d.weight i + b * e.weight i) *
          (a * d.weight i / (a * d.weight i + b * e.weight i)) = a * d.weight i := by
        field_simp
      have hβ : (a * d.weight i + b * e.weight i) *
          (b * e.weight i / (a * d.weight i + b * e.weight i)) = b * e.weight i := by
        field_simp
      change (a * d.weight i + b * e.weight i) * (f i (c.point i)).toReal ≤ _
      simpa only [mul_add, ← mul_assoc, hα, hβ] using hbound
    · have hzero : a * d.weight i + b * e.weight i = 0 := by linarith
      have hα : a * d.weight i = 0 := by linarith
      have hβ : b * e.weight i = 0 := by linarith
      change (a * d.weight i + b * e.weight i) * (f i (c.point i)).toReal ≤ _
      simp [← mul_assoc, hα, hβ]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hterm i)
  simpa only [cost, c, Finset.sum_add_distrib, ← Finset.mul_sum] using h

end RooftopData

/-- The actual infimum of weighted tuples is convex, including bottom outputs. -/
theorem isConvex_weightedRooftop {f : I → V → EReal} (hf : ∀ i, IsProper (f i)) :
    IsConvex (weightedRooftop f) := by
  classical
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  obtain ⟨d, hd⟩ := iInf_lt_iff.mp hxr
  obtain ⟨hd, hdr⟩ := iInf_lt_iff.mp hd
  obtain ⟨e, he⟩ := iInf_lt_iff.mp hys
  obtain ⟨he, hes⟩ := iInf_lt_iff.mp he
  have hdr' : d.cost < r := EReal.coe_lt_coe_iff.mp hdr
  have hes' : e.cost < s := EReal.coe_lt_coe_iff.mp hes
  let c := RooftopData.combine hf d e a b ha.le hb.le hab
  have hbar : c.barycenter = a • x + b • y := by
    rw [RooftopData.barycenter_combine, hd, he]
  have hbound : weightedRooftop f (a • x + b • y) ≤ (c.cost : EReal) := by
    rw [← hbar]
    exact weightedRooftop_le_cost c
  have hcost : c.cost < a * r + b * s :=
    (RooftopData.cost_combine_le hf d e a b ha.le hb.le hab).trans_lt
      (add_lt_add (mul_lt_mul_of_pos_left hdr' ha) (mul_lt_mul_of_pos_left hes' hb))
  exact hbound.trans_lt (EReal.coe_lt_coe hcost)

/-- Full source `prop:concavhull`: the actual finite weighted formula is the rooftop. -/
theorem convexInf_eq_weightedRooftop {f : I → V → EReal} (hf : ∀ i, IsProper (f i)) :
    convexInf f = weightedRooftop f :=
  le_antisymm
    (le_weightedRooftop hf (isConvex_convexInf f) (convexInf_le f))
    (le_convexInf (isConvex_weightedRooftop hf) (weightedRooftop_le hf))

/-- The actual tuple infimum is exactly the unbundled source formula. -/
theorem weightedRooftop_eq_iInf (f : I → V → EReal) (x : V) :
    weightedRooftop f x =
      ⨅ (z : I → V) (_ : ∀ i, z i ∈ effectiveDomain (f i))
        (w : I → ℝ) (_ : ∀ i, w i ∈ Set.Icc 0 1)
        (_ : ∑ i, w i = 1) (_ : ∑ i, w i • z i = x),
        ((∑ i, w i * (f i (z i)).toReal : ℝ) : EReal) := by
  apply le_antisymm
  · apply le_iInf
    intro z
    apply le_iInf
    intro hz
    apply le_iInf
    intro w
    apply le_iInf
    intro hw
    apply le_iInf
    intro hsum
    apply le_iInf
    intro hx
    let d : RooftopData f := ⟨w, z, fun i ↦ (hw i).1, hsum, hz⟩
    have hb : d.barycenter = x := hx
    have h := weightedRooftop_le_cost d
    rw [hb] at h
    exact h
  · apply le_iInf
    intro d
    apply le_iInf
    intro hx
    exact iInf_le_of_le d.point (iInf_le_of_le d.point_mem_domain
      (iInf_le_of_le d.weight (iInf_le_of_le (fun i ↦
        ⟨d.weight_nonneg i, d.weight_le_one i⟩) (iInf_le_of_le d.weight_sum
          (iInf_le_of_le hx le_rfl)))))

/-- The exact displayed source formula, with interval weights and actual domain tuples. -/
theorem convexInf_eq_iInf_weighted {f : I → V → EReal} (hf : ∀ i, IsProper (f i))
    (x : V) : convexInf f x =
      ⨅ (z : I → V) (_ : ∀ i, z i ∈ effectiveDomain (f i))
        (w : I → ℝ) (_ : ∀ i, w i ∈ Set.Icc 0 1)
        (_ : ∑ i, w i = 1) (_ : ∑ i, w i • z i = x),
        ((∑ i, w i * (f i (z i)).toReal : ℝ) : EReal) := by
  rw [convexInf_eq_weightedRooftop hf, weightedRooftop_eq_iInf]

end SGPT.Convex
