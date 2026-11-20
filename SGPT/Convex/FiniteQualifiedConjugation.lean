import SGPT.Convex.QualifiedConjugation

/-!
# Actual finite qualified sum conjugation

Proper partial sums preserve an actual common intrinsic-interior domain point.
Nonempty finite induction then assembles genuine continuous covector splits.
-/

namespace SGPT.Convex

open Set
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Actual proper extended-real obstacles have a genuinely convex pointwise sum. -/
theorem isConvex_add_of_isProper {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) : IsConvex (fun x ↦ f x + g x) := by
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  have hxtop : f x ≠ ⊤ ∧ g x ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ (hf.2.2 _) (hg.2.2 _)).mp
      (ne_of_lt (hxr.trans (EReal.coe_lt_top r)))
  have hytop : f y ≠ ⊤ ∧ g y ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ (hf.2.2 _) (hg.2.2 _)).mp
      (ne_of_lt (hys.trans (EReal.coe_lt_top s)))
  have hfx : f x = ((f x).toReal : EReal) :=
    (EReal.coe_toReal hxtop.1 (hf.2.2 _)).symm
  have hgx : g x = ((g x).toReal : EReal) :=
    (EReal.coe_toReal hxtop.2 (hg.2.2 _)).symm
  have hfy : f y = ((f y).toReal : EReal) :=
    (EReal.coe_toReal hytop.1 (hf.2.2 _)).symm
  have hgy : g y = ((g y).toReal : EReal) :=
    (EReal.coe_toReal hytop.2 (hg.2.2 _)).symm
  have hcostx : f x + g x = (((f x).toReal + (g x).toReal : ℝ) : EReal) := by
    rw [hfx, hgx, ← EReal.coe_add]
    simp only [EReal.toReal_coe]
  have hcosty : f y + g y = (((f y).toReal + (g y).toReal : ℝ) : EReal) := by
    rw [hfy, hgy, ← EReal.coe_add]
    simp only [EReal.toReal_coe]
  have hxr' : (f x).toReal + (g x).toReal < r := by
    simpa only [hcostx, EReal.coe_lt_coe_iff] using hxr
  have hys' : (f y).toReal + (g y).toReal < s := by
    simpa only [hcosty, EReal.coe_lt_coe_iff] using hys
  have hfc := hf.1 (x := (x, (f x).toReal)) (y := (y, (f y).toReal))
    hfx.le hfy.le ha.le hb.le hab
  have hgc := hg.1 (x := (x, (g x).toReal)) (y := (y, (g y).toReal))
    hgx.le hgy.le ha.le hb.le hab
  have hbound : f (a • x + b • y) + g (a • x + b • y) ≤
      ((a * ((f x).toReal + (g x).toReal) +
        b * ((f y).toReal + (g y).toReal) : ℝ) : EReal) := by
    calc
      _ ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) +
          ((a * (g x).toReal + b * (g y).toReal : ℝ) : EReal) := add_le_add hfc hgc
      _ = _ := by rw [← EReal.coe_add]; congr 1; ring
  exact hbound.trans_lt (EReal.coe_lt_coe
    (add_lt_add (mul_lt_mul_of_pos_left hxr' ha) (mul_lt_mul_of_pos_left hys' hb)))

omit [FiniteDimensional ℝ E] in
/-- Actual proper-sum domain membership is exactly simultaneous original membership. -/
theorem effectiveDomain_add_of_isProper {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) :
    effectiveDomain (fun x ↦ f x + g x) = effectiveDomain f ∩ effectiveDomain g := by
  ext x
  simp only [effectiveDomain, mem_ofPred_eq, mem_inter_iff, lt_top_iff_ne_top]
  exact EReal.add_ne_top_iff_ne_top₂ (hf.2.2 _) (hg.2.2 _)

omit [FiniteDimensional ℝ E] in
/-- An actual common finite domain point makes the actual sum proper. -/
theorem isProper_add_of_common_domain {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) {x : E}
    (hx : x ∈ effectiveDomain f) (hx' : x ∈ effectiveDomain g) :
    IsProper (fun y ↦ f y + g y) := by
  refine ⟨isConvex_add_of_isProper hf hg, ?_, ?_⟩
  · rw [effectiveDomain_add_of_isProper hf hg]
    exact ⟨x, hx, hx'⟩
  · intro y
    exact EReal.add_ne_bot_iff.mpr ⟨hf.2.2 y, hg.2.2 y⟩

omit [FiniteDimensional ℝ E] in
/-- Actual common relative-interior qualification persists through the actual sum. -/
theorem mem_intrinsicInterior_effectiveDomain_add {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx' : x ∈ intrinsicInterior ℝ (effectiveDomain g)) :
    x ∈ intrinsicInterior ℝ (effectiveDomain (fun y ↦ f y + g y)) := by
  rw [effectiveDomain_add_of_isProper hf hg]
  exact mem_intrinsicInterior_inter hx hx'

omit [FiniteDimensional ℝ E] in
/-- Every actual finite partial sum is proper and retains the actual common qualification. -/
theorem isProper_sum_and_mem_intrinsicInterior {I : Type*} (f : I → E → EReal)
    (s : Finset I) {x₀ : E}
    (hf : ∀ i ∈ s, IsProper (f i))
    (hx₀ : ∀ i ∈ s, x₀ ∈ intrinsicInterior ℝ (effectiveDomain (f i))) :
    IsProper (fun x ↦ ∑ i ∈ s, f i x) ∧
      x₀ ∈ intrinsicInterior ℝ (effectiveDomain (fun x ↦ ∑ i ∈ s, f i x)) := by
  classical
  revert hf hx₀
  induction s using Finset.induction_on with
  | empty =>
    intro hf hx₀
    simp only [Finset.sum_empty]
    have hd : effectiveDomain (fun _ : E ↦ (0 : EReal)) = univ := by
      ext x
      simp [effectiveDomain]
    constructor
    · exact ⟨by simpa only [EReal.coe_zero] using (isConvex_const (V := E) 0),
        ⟨x₀, by simp [effectiveDomain]⟩, fun _ ↦ by simp⟩
    · rw [hd]
      exact interior_subset_intrinsicInterior (by simp)
  | @insert i s hi ih =>
    intro hf hx₀
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hxi := hx₀ i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, IsProper (f j) := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have hxs : ∀ j ∈ s, x₀ ∈ intrinsicInterior ℝ (effectiveDomain (f j)) :=
      fun j hj ↦ hx₀ j (Finset.mem_insert_of_mem hj)
    obtain ⟨hps, hrs⟩ := ih hfs hxs
    simp only [Finset.sum_insert hi]
    exact ⟨isProper_add_of_common_domain hfi hps
      (intrinsicInterior_subset hxi) (intrinsicInterior_subset hrs),
      mem_intrinsicInterior_effectiveDomain_add hfi hps hxi hrs⟩

/-- Finite weak duality reuses genuine infimal conjugation and biconjugation,
including the actual closure order, rather than reproving extended-real sum algebra. -/
theorem conjugate_sum_le_infimalConvolution {I : Type*} [Fintype I]
    {f : I → E → EReal} (hf : ∀ i, IsProper (f i)) :
    conjugate continuousDualPairing (fun x ↦ ∑ i, f i x) ≤
      infimalConvolution (fun i ↦ conjugate continuousDualPairing (f i)) := by
  have hp : ∀ i, IsProper (conjugate continuousDualPairing (f i)) :=
    fun i ↦ isProper_conjugate_of_isContPerfPair continuousDualPairing (hf i)
  let G := infimalConvolution (fun i ↦ conjugate continuousDualPairing (f i))
  have hdouble : conjugate continuousDualPairing.flip G =
      fun x ↦ ∑ i, convexClosure (f i) x := by
    rw [conjugate_infimalConvolution continuousDualPairing.flip hp]
    funext x
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (biconjugate_eq_convexClosure_of_isContPerfPair continuousDualPairing (hf i).1) x
  have horder : (fun x ↦ ∑ i, convexClosure (f i) x) ≤ (fun x ↦ ∑ i, f i x) :=
    fun x ↦ Finset.sum_le_sum (fun i _ ↦ convexClosure_le (f i) x)
  calc
    conjugate continuousDualPairing (fun x ↦ ∑ i, f i x) ≤
        conjugate continuousDualPairing (fun x ↦ ∑ i, convexClosure (f i) x) :=
      conjugate_antitone continuousDualPairing horder
    _ = convexClosure G := by
      rw [← hdouble]
      simpa only [LinearMap.flip_flip] using
        (biconjugate_eq_convexClosure_of_isContPerfPair continuousDualPairing.flip
          (isConvex_infimalConvolution hp))
    _ ≤ G := convexClosure_le G

/-- Nonempty finite induction assembles actual covectors attaining every
genuinely finite qualified sum conjugate. -/
theorem exists_split_finset_of_conjugate_ne_top {I : Type*}
    (f : I → E → EReal) (s : Finset I) (hs : s.Nonempty) {x₀ : E} :
    (∀ i ∈ s, IsProper (f i)) →
    (∀ i ∈ s, x₀ ∈ intrinsicInterior ℝ (effectiveDomain (f i))) →
    ∀ m : StrongDual ℝ E,
      conjugate continuousDualPairing (fun x ↦ ∑ i ∈ s, f i x) m ≠ ⊤ →
      ∃ z : I → StrongDual ℝ E,
        (∑ i ∈ s, z i) = m ∧
        (∑ i ∈ s, conjugate continuousDualPairing (f i) (z i)) =
          conjugate continuousDualPairing (fun x ↦ ∑ i ∈ s, f i x) m := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
    intro hf hx₀ m hfinite
    exact ⟨fun _ ↦ m, by simp, by simp⟩
  | @cons i s hi hs ih =>
    intro hf hx₀ m hfinite
    have hfi := hf i (by simp)
    have hxi := hx₀ i (by simp)
    have hfs : ∀ j ∈ s, IsProper (f j) := fun j hj ↦ hf j (by simp [hj])
    have hxs : ∀ j ∈ s, x₀ ∈ intrinsicInterior ℝ (effectiveDomain (f j)) :=
      fun j hj ↦ hx₀ j (by simp [hj])
    obtain ⟨hps, hrs⟩ := isProper_sum_and_mem_intrinsicInterior f s hfs hxs
    have hfinite' : conjugate continuousDualPairing
        (fun x ↦ f i x + ∑ j ∈ s, f j x) m ≠ ⊤ := by
      simpa only [Finset.sum_cons] using hfinite
    obtain ⟨ℓ, hℓ⟩ := exists_split_of_conjugate_ne_top hfi hps m hxi hrs hfinite'
    have hci := isProper_conjugate_of_isContPerfPair continuousDualPairing hfi
    have hcs := isProper_conjugate_of_isContPerfPair continuousDualPairing hps
    have hsplitTop : conjugate continuousDualPairing (f i) ℓ +
        conjugate continuousDualPairing (fun x ↦ ∑ j ∈ s, f j x) (m - ℓ) ≠ ⊤ := by
      rw [hℓ]
      exact hfinite'
    have hrestTop :=
      ((EReal.add_ne_top_iff_ne_top₂ (hci.2.2 _) (hcs.2.2 _)).mp hsplitTop).2
    obtain ⟨z, hzsum, hzcost⟩ := ih hfs hxs (m - ℓ) hrestTop
    have hupdate (j : I) (hj : j ∈ s) : Function.update z i ℓ j = z j :=
      Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
    have hupdateSum : (∑ j ∈ s, Function.update z i ℓ j) = ∑ j ∈ s, z j :=
      Finset.sum_congr rfl hupdate
    have hupdateCost :
        (∑ j ∈ s, conjugate continuousDualPairing (f j) (Function.update z i ℓ j)) =
          ∑ j ∈ s, conjugate continuousDualPairing (f j) (z j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hupdate j hj]
    refine ⟨Function.update z i ℓ, ?_, ?_⟩
    · rw [Finset.sum_cons, Function.update_self, hupdateSum, hzsum]
      abel
    · rw [Finset.sum_cons, Function.update_self, hupdateCost, hzcost]
      simpa only [Finset.sum_cons] using hℓ

/-- Exact source `prop:sumLegendre` for the actual nonempty finite family,
the actual common intrinsic-interior witness and actual tuple decompositions. -/
theorem conjugate_sum_eq_infimalConvolution_of_common_intrinsicInterior
    {I : Type*} [Fintype I] [Nonempty I] {f : I → E → EReal}
    (hf : ∀ i, IsProper (f i)) {x₀ : E}
    (hx₀ : ∀ i, x₀ ∈ intrinsicInterior ℝ (effectiveDomain (f i))) :
    conjugate continuousDualPairing (fun x ↦ ∑ i, f i x) =
      infimalConvolution (fun i ↦ conjugate continuousDualPairing (f i)) := by
  classical
  apply le_antisymm (conjugate_sum_le_infimalConvolution hf)
  intro m
  by_cases htop : conjugate continuousDualPairing (fun x ↦ ∑ i, f i x) m = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨z, hzsum, hzcost⟩ := exists_split_finset_of_conjugate_ne_top f Finset.univ
    Finset.univ_nonempty (fun i _ ↦ hf i) (fun i _ ↦ hx₀ i) m htop
  have hbound := infimalConvolution_le_sum (fun i ↦ conjugate continuousDualPairing (f i)) z
  rw [hzsum] at hbound
  exact hbound.trans hzcost.le

end SGPT.Convex
