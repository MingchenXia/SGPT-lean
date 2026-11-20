import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueUniqueness
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Module.NatInt

set_option autoImplicit false

/-! # Genuine local finite mixed expansion of scalar subset sums

The natural-number multilinear map is constructed internally on the
actual PSH additive cone. All measures are on the original open domain.
-/

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff BigOperators

namespace SGPT.Foundations.Analysis.Pending.LocalCanonicalMixedSubsetExpansion

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCalculus
  LocalBedfordTaylorLocality LocalBedfordTaylorSmoothTraceMeasure
  LocalBedfordTaylorCanonicalTraceMeasure

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {n : ℕ} {Ω : Opens (ComplexModel n)}

private def pshCone (Ω : Opens (ComplexModel n)) : AddSubmonoid (ComplexModel n → ℝ) where
  carrier := {u | IsLocallyBoundedPshOn Ω u}
  zero_mem' := isLocallyBoundedPshOn_of_continuousOn
    (fun z _ => plurisubharmonicAt_const 0 EReal.zero_ne_top z) continuousOn_const
  add_mem' := fun hu hv => isLocallyBoundedPshOn_add hu hv

private def product (m : Fin n → pshCone Ω) : LocalProductCurrent n Ω 0 :=
  btProduct n 0 (fun i => (m i : ComplexModel n → ℝ))
    (oneCurrentOf (U := Ω) (Nat.zero_add n))

private theorem product_update_add (m : Fin n → pshCone Ω) (i : Fin n)
    (x y : pshCone Ω) :
    product (Function.update m i (x + y)) =
      product (Function.update m i x) + product (Function.update m i y) := by
  have e (c : pshCone Ω) :
      (fun j => (Function.update m i c j : ComplexModel n → ℝ)) =
        Function.update (fun j => (m j : ComplexModel n → ℝ)) i (c : ComplexModel n → ℝ) := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  unfold product
  rw [e, e, e]
  change btProduct n 0
      (Function.update (fun j => (m j : ComplexModel n → ℝ)) i
        (fun z => (x : ComplexModel n → ℝ) z + (y : ComplexModel n → ℝ) z)) _ = _
  exact btProduct_update_add n 0 (oneCurrentOf (U := Ω) (Nat.zero_add n))
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
      (fun j => (m j : ComplexModel n → ℝ)) (fun j => (m j).property)
      i x.property y.property

private def productSlotHom (m : Fin n → pshCone Ω) (i : Fin n) :
    pshCone Ω →+ LocalProductCurrent n Ω 0 where
  toFun x := product (Function.update m i x)
  map_zero' := by
    have h := product_update_add m i (0 : pshCone Ω) 0
    simp only [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' := product_update_add m i

private def productMultilinear :
    MultilinearMap ℕ (fun _ : Fin n => pshCone Ω) (LocalProductCurrent n Ω 0) :=
  MultilinearMap.mk' product product_update_add
    (fun m i c x => (productSlotHom m i).map_nsmul c x)

private theorem positive_product (m : Fin n → pshCone Ω) : IsPositive (product m) :=
  (isPositive_btProduct n 0 _ _ (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (fun j => (m j).property)).1

private theorem positive_sum {ι : Type*} (s : Finset ι)
    (T : ι → LocalProductCurrent n Ω 0) (hT : ∀ i, IsPositive (T i)) :
    IsPositive (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (isPositive_zero (n := n) (U := Ω) (q := 0))
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (hT i).add ih

private theorem trace_zero (h : IsPositive (0 : LocalProductCurrent n Ω 0)) :
    h.traceMeasure = 0 := by
  apply eq_of_forall_testFunction_integral_eq (U := Ω) h.traceMeasure_compl
    (by simp) (fun K hK hKΩ => h.traceMeasure_lt_top hK hKΩ) (by simp)
  intro φ
  rw [h.integral_traceMeasure]
  simp

private theorem trace_sum {ι : Type*} (s : Finset ι)
    (T : ι → LocalProductCurrent n Ω 0) (hT : ∀ i, IsPositive (T i)) :
    (positive_sum s T hT).traceMeasure = ∑ i ∈ s, (hT i).traceMeasure := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact trace_zero _
  | insert i s his ih =>
    have e : (∑ j ∈ insert i s, T j) = T i + ∑ j ∈ s, T j := Finset.sum_insert his
    calc
      (positive_sum (insert i s) T hT).traceMeasure =
          ((hT i).add (positive_sum s T hT)).traceMeasure := by congr 1
      _ = (hT i).traceMeasure + (positive_sum s T hT).traceMeasure :=
        ActualPositiveCurrentLebesgueUniqueness.traceMeasure_add _ _
      _ = ∑ j ∈ insert i s, (hT j).traceMeasure := by rw [ih, Finset.sum_insert his]

/-- Natural original PSH data produce the literal finite selected-measure expansion. -/
theorem canonicalScalar_subsetSum_eq_sum_selected
    {u : Fin n → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) (J : Finset (Fin n)) :
    ∃ hJ : IsLocallyBoundedPshOn Ω (fun z => ∑ i ∈ J, u i z),
      MongeAmpere.canonicalBedfordTaylorMeasure Ω (fun z => ∑ i ∈ J, u i z) hJ =
        ∑ g : Fin n → Fin n with ∀ j, g j ∈ J,
          MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω (fun j => u (g j))
            (fun j => hu (g j)) := by
  classical
  let m : Fin n → pshCone Ω := fun i => ⟨u i, hu i⟩
  let w : pshCone Ω := ∑ i ∈ J, m i
  have hw : IsLocallyBoundedPshOn Ω (w : ComplexModel n → ℝ) := w.property
  have hwMix : IsLocallyBoundedMixedPshOn Ω (fun _ => (w : ComplexModel n → ℝ)) :=
    fun _ => hw
  have ew : (w : ComplexModel n → ℝ) = fun z => ∑ i ∈ J, u i z := by
    change (AddSubmonoidClass.subtype (pshCone Ω)) (∑ i ∈ J, m i) = _
    rw [map_sum]
    ext z
    change (∑ i ∈ J, u i) z = ∑ i ∈ J, u i z
    exact Finset.sum_apply z J u
  have hJ : IsLocallyBoundedPshOn Ω (fun z => ∑ i ∈ J, u i z) := ew ▸ hw
  refine ⟨hJ, ?_⟩
  let A : Finset (Fin n → Fin n) := Finset.univ.filter (fun g => ∀ j, g j ∈ J)
  have eA : Fintype.piFinset (fun _ : Fin n => J) = A := by
    ext g
    simp [A]
  have ep : product (fun _ : Fin n => w) = ∑ g ∈ A, product (fun j => m (g j)) := by
    have h := (productMultilinear (Ω := Ω)).map_sum_finset (fun _ j => m j)
      (fun _ => J)
    change product (fun _ : Fin n => w) = ∑ g ∈ Fintype.piFinset (fun _ => J),
      product (fun j => m (g j)) at h
    rwa [eA] at h
  have et : (positive_product (fun _ : Fin n => w)).traceMeasure =
      ∑ g ∈ A, (positive_product (fun j => m (g j))).traceMeasure := by
    calc
      (positive_product (fun _ : Fin n => w)).traceMeasure =
          (positive_sum A (fun g => product (fun j => m (g j)))
            (fun g => positive_product (fun j => m (g j)))).traceMeasure := by congr 1
      _ = _ := trace_sum _ _ _
  have ec : (positive_product (fun _ : Fin n => w)).traceMeasure =
      MongeAmpere.canonicalBedfordTaylorMeasure Ω (fun z => ∑ i ∈ J, u i z) hJ := by
    change recursiveMixedTraceMeasure Ω (fun _ => (w : ComplexModel n → ℝ))
      (fun _ => hw) = _
    calc
      _ = MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω
          (fun _ => (w : ComplexModel n → ℝ)) hwMix :=
        (canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
          hwMix).symm
      _ = _ := by
        simpa only [ew] using
          MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_diagonal Ω
            (w : ComplexModel n → ℝ) hw
  rw [← ec, et]
  apply Finset.sum_congr rfl
  intro g _
  exact (canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
    (fun j => hu (g j))).symm

end SGPT.Foundations.Analysis.Pending.LocalCanonicalMixedSubsetExpansion
