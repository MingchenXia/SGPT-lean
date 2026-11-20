import SGPT.Convex.FamilyOperations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual finite infimal convolution

The defining infimum is over actual decompositions in the vector space,
with the source's sum of extended-real values. Properness is needed only
to prove convexity; no existence of a minimizing tuple is assumed.
-/

namespace SGPT.Convex

open Set
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  {I : Type*} [Fintype I]

omit [AddCommGroup V] [Module ℝ V] [Fintype I] in
/-- Extended-real addition preserves two independent actual suprema. -/
theorem iSup_add_iSup {A B : Sort*} (u : A → EReal) (v : B → EReal) :
    (⨆ a, u a) + (⨆ b, v b) = ⨆ a, ⨆ b, u a + v b := by
  apply le_antisymm
  · apply EReal.add_le_of_forall_lt
    intro p hp q hq
    obtain ⟨a, ha⟩ := lt_iSup_iff.mp hp
    obtain ⟨b, hb⟩ := lt_iSup_iff.mp hq
    exact (add_le_add ha.le hb.le).trans
      (le_iSup_of_le a (le_iSup (fun j ↦ u a + v j) b))
  · exact iSup_le fun a ↦ iSup_le fun b ↦
      add_le_add (le_iSup u a) (le_iSup v b)

omit [AddCommGroup V] [Module ℝ V] [Fintype I] in
/-- Finite independent actual choices exchange with a sum of extended-real suprema. -/
theorem sum_iSup_eq_iSup_sum {J : Type*} [Nonempty J]
    (s : Finset I) (a : I → J → EReal) :
    (∑ i ∈ s, ⨆ x, a i x) = ⨆ z : I → J, ∑ i ∈ s, a i (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, ih, iSup_add_iSup]
    apply le_antisymm
    · apply iSup_le
      intro x
      apply iSup_le
      intro z
      apply le_iSup_of_le (Function.update z i x)
      rw [Finset.sum_insert hi, Function.update_self]
      apply add_le_add le_rfl
      exact (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]).le
    · apply iSup_le
      intro z
      rw [Finset.sum_insert hi]
      exact le_iSup_of_le (z i) (le_iSup_of_le z le_rfl)

/-- The actual source infimal convolution, as an infimum over decompositions. -/
noncomputable def infimalConvolution (f : I → V → EReal) (x : V) : EReal :=
  ⨅ (z : I → V) (_ : ∑ i, z i = x), ∑ i, f i (z i)

omit [Module ℝ V] in
/-- Every actual decomposition supplies an upper bound on the infimal cost. -/
theorem infimalConvolution_le_sum (f : I → V → EReal) (z : I → V) :
    infimalConvolution f (∑ i, z i) ≤ ∑ i, f i (z i) :=
  iInf_le_of_le z (iInf_le_of_le rfl le_rfl)

omit [Fintype I] in
private theorem finite_sum_ne_bot (s : Finset I) (g : I → EReal)
    (hg : ∀ i ∈ s, g i ≠ ⊥) : ∑ i ∈ s, g i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
    exact ⟨hg i (Finset.mem_insert_self _ _),
      ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))⟩

private theorem finite_sum_ne_top (g : I → EReal) (hg : ∀ i, g i ≠ ⊥)
    (hsum : (∑ i, g i) ≠ ⊤) : ∀ i, g i ≠ ⊤ := by
  classical
  intro i hi
  have hnobot : ∑ j ∈ Finset.univ.erase i, g j ≠ ⊥ :=
    finite_sum_ne_bot _ g (fun j _ ↦ hg j)
  have hdecomp := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
  rw [hi, EReal.top_add_of_ne_bot hnobot] at hdecomp
  exact hsum hdecomp.symm

omit [AddCommGroup V] [Module ℝ V] [Fintype I] in
/-- A finite sum of actual non-bottom values remains non-bottom. -/
theorem sum_ne_bot_of_forall_ne_bot (s : Finset I) (g : I → EReal)
    (hg : ∀ i ∈ s, g i ≠ ⊥) : ∑ i ∈ s, g i ≠ ⊥ :=
  finite_sum_ne_bot s g hg

omit [AddCommGroup V] [Module ℝ V] in
/-- Genuine finite total cost excludes top in every non-bottom summand. -/
theorem forall_ne_top_of_sum_ne_top (g : I → EReal) (hg : ∀ i, g i ≠ ⊥)
    (hsum : (∑ i, g i) ≠ ⊤) : ∀ i, g i ≠ ⊤ :=
  finite_sum_ne_top g hg hsum

private theorem coe_finite_sum (g : I → ℝ) :
    ((∑ i, g i : ℝ) : EReal) = ∑ i, (g i : EReal) :=
  map_sum (⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g Finset.univ

omit [Fintype I] in
private theorem real_sub_finite_sum (s : Finset I) (r : I → ℝ) (g : I → EReal)
    (hg : ∀ i ∈ s, g i ≠ ⊥) :
    ((∑ i ∈ s, r i : ℝ) : EReal) - (∑ i ∈ s, g i) =
      ∑ i ∈ s, ((r i : EReal) - g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hgs : ∀ j ∈ s, g j ≠ ⊥ := fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi,
      EReal.coe_add, EReal.add_sub_add_comm
        (Or.inl (hg i (Finset.mem_insert_self _ _))) (Or.inr (finite_sum_ne_bot s g hgs)), ih hgs]

/-- Source convexity of the actual finite infimal convolution of proper functions. -/
theorem isConvex_infimalConvolution {f : I → V → EReal}
    (hf : ∀ i, IsProper (f i)) : IsConvex (infimalConvolution f) := by
  classical
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  obtain ⟨u, hu⟩ := iInf_lt_iff.mp hxr
  obtain ⟨hu, hur⟩ := iInf_lt_iff.mp hu
  obtain ⟨v, hv⟩ := iInf_lt_iff.mp hys
  obtain ⟨hv, hvs⟩ := iInf_lt_iff.mp hv
  have hutop : ∀ i, f i (u i) ≠ ⊤ :=
    finite_sum_ne_top _ (fun i ↦ (hf i).2.2 _) (ne_of_lt (hur.trans (EReal.coe_lt_top r)))
  have hvtop : ∀ i, f i (v i) ≠ ⊤ :=
    finite_sum_ne_top _ (fun i ↦ (hf i).2.2 _) (ne_of_lt (hvs.trans (EReal.coe_lt_top s)))
  have hufinite (i : I) : f i (u i) = ((f i (u i)).toReal : EReal) :=
    (EReal.coe_toReal (hutop i) ((hf i).2.2 _)).symm
  have hvfinite (i : I) : f i (v i) = ((f i (v i)).toReal : EReal) :=
    (EReal.coe_toReal (hvtop i) ((hf i).2.2 _)).symm
  have hucost : (∑ i, f i (u i)) = ((∑ i, (f i (u i)).toReal : ℝ) : EReal) := by
    rw [coe_finite_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ hufinite i)
  have hvcost : (∑ i, f i (v i)) = ((∑ i, (f i (v i)).toReal : ℝ) : EReal) := by
    rw [coe_finite_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ hvfinite i)
  have hur' : ∑ i, (f i (u i)).toReal < r := by
    simpa only [hucost, EReal.coe_lt_coe_iff] using hur
  have hvs' : ∑ i, (f i (v i)).toReal < s := by
    simpa only [hvcost, EReal.coe_lt_coe_iff] using hvs
  let z : I → V := fun i ↦ a • u i + b • v i
  have hz : ∑ i, z i = a • x + b • y := by
    simp only [z, Finset.sum_add_distrib, ← Finset.smul_sum, hu, hv]
  have hcost : ∑ i, f i (z i) ≤
      ((a * ∑ i, (f i (u i)).toReal + b * ∑ i, (f i (v i)).toReal : ℝ) : EReal) := by
    have hi (i : I) : f i (z i) ≤
        ((a * (f i (u i)).toReal + b * (f i (v i)).toReal : ℝ) : EReal) :=
      (hf i).1 (x := (u i, (f i (u i)).toReal))
        (y := (v i, (f i (v i)).toReal)) (hufinite i).le (hvfinite i).le ha.le hb.le hab
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
    simpa only [← coe_finite_sum, Finset.sum_add_distrib, ← Finset.mul_sum] using h
  have hstrict : a * ∑ i, (f i (u i)).toReal + b * ∑ i, (f i (v i)).toReal <
      a * r + b * s :=
    add_lt_add (mul_lt_mul_of_pos_left hur' ha) (mul_lt_mul_of_pos_left hvs' hb)
  have hbound : infimalConvolution f (a • x + b • y) ≤ ∑ i, f i (z i) := by
    rw [← hz]
    exact infimalConvolution_le_sum f z
  exact (hbound.trans hcost).trans_lt (EReal.coe_lt_coe hstrict)

/-- The actual effective domain is exactly the sum of the effective domains. -/
theorem effectiveDomain_infimalConvolution {f : I → V → EReal}
    (hf : ∀ i, IsProper (f i)) :
    effectiveDomain (infimalConvolution f) =
      {x | ∃ z : I → V, (∀ i, z i ∈ effectiveDomain (f i)) ∧ ∑ i, z i = x} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨r, hxr, _⟩ := EReal.exists_between_coe_real hx
    obtain ⟨z, hz⟩ := iInf_lt_iff.mp hxr
    obtain ⟨hz, hcost⟩ := iInf_lt_iff.mp hz
    have hnottop : ∀ i, f i (z i) ≠ ⊤ :=
      finite_sum_ne_top _ (fun i ↦ (hf i).2.2 _)
        (ne_of_lt (hcost.trans (EReal.coe_lt_top r)))
    exact ⟨z, fun i ↦ lt_top_iff_ne_top.mpr (hnottop i), hz⟩
  · rintro ⟨z, hzD, rfl⟩
    have hfinite : (∑ i, f i (z i)) = ((∑ i, (f i (z i)).toReal : ℝ) : EReal) := by
      rw [coe_finite_sum]
      exact Finset.sum_congr rfl (fun i _ ↦
        (EReal.coe_toReal (ne_of_lt (hzD i)) ((hf i).2.2 _)).symm)
    exact (infimalConvolution_le_sum f z).trans_lt (hfinite ▸ EReal.coe_lt_top _)

/-- A finite family of proper functions gives a genuinely nonempty infimal domain. -/
theorem nonempty_effectiveDomain_infimalConvolution {f : I → V → EReal}
    (hf : ∀ i, IsProper (f i)) : (effectiveDomain (infimalConvolution f)).Nonempty := by
  classical
  choose z hz using fun i ↦ (hf i).2.1
  rw [effectiveDomain_infimalConvolution hf]
  exact ⟨∑ i, z i, z, hz, rfl⟩

/-- The actual finite infimal convolution conjugates to the actual sum of conjugates. -/
theorem conjugate_infimalConvolution {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) {f : I → V → EReal} (hf : ∀ i, IsProper (f i)) :
    conjugate B (infimalConvolution f) = fun y ↦ ∑ i, conjugate B (f i) y := by
  classical
  funext y
  calc
    conjugate B (infimalConvolution f) y =
        ⨆ z : I → V, (B (∑ i, z i) y : EReal) - ∑ i, f i (z i) := by
      simp only [conjugate, infimalConvolution, real_sub_iInf]
      apply le_antisymm
      · apply iSup_le
        intro x
        apply iSup_le
        intro z
        apply iSup_le
        intro hz
        subst x
        exact le_iSup (fun z : I → V ↦
          (B (∑ i, z i) y : EReal) - ∑ i, f i (z i)) z
      · exact iSup_le fun z ↦ le_iSup_of_le (∑ i, z i)
          (le_iSup_of_le z (le_iSup_of_le rfl le_rfl))
    _ = ⨆ z : I → V, ∑ i, ((B (z i) y : EReal) - f i (z i)) := by
      apply iSup_congr
      intro z
      have hsum : B (∑ i, z i) y = ∑ i, B (z i) y := by
        rw [map_sum, LinearMap.sum_apply]
      rw [hsum]
      exact real_sub_finite_sum Finset.univ (fun i ↦ B (z i) y)
        (fun i ↦ f i (z i)) (fun i _ ↦ (hf i).2.2 _)
    _ = ∑ i, conjugate B (f i) y :=
      (sum_iSup_eq_iSup_sum Finset.univ (fun i x ↦ (B x y : EReal) - f i x)).symm

end SGPT.Convex
