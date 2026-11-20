import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

/-! Actual real readback only after finite obstacle caps/floors.
Mathematical proof: global-weight-approximation.tex, gwa:finite-obstacle-readback. -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.GlobalWeightFiniteObstacles

open Set

universe u
variable {X : Type u} [TopologicalSpace X]

/-- Real and included-real strict superlevels agree, so original LSC is retained. -/
theorem lowerSemicontinuous_of_ereal_coe {g : X → ℝ}
    (hg : LowerSemicontinuous (fun x => (g x : EReal))) : LowerSemicontinuous g := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  have heq : g ⁻¹' Ioi t = (fun x => (g x : EReal)) ⁻¹' Ioi (t : EReal) := by
    ext x
    exact EReal.coe_lt_coe_iff.symm
  rw [heq]
  exact hg.isOpen_preimage (t : EReal)

/-- Real and included-real strict sublevels agree, so original USC is retained. -/
theorem upperSemicontinuous_of_ereal_coe {g : X → ℝ}
    (hg : UpperSemicontinuous (fun x => (g x : EReal))) : UpperSemicontinuous g := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro t
  have heq : g ⁻¹' Iio t = (fun x => (g x : EReal)) ⁻¹' Iio (t : EReal) := by
    ext x
    exact EReal.coe_lt_coe_iff.symm
  rw [heq]
  exact hg.isOpen_preimage (t : EReal)

/-- An actual finite lower bound and finite cap internally give a real LSC
obstacle with exact scalar reinclusion, before any approximation is chosen. -/
theorem exists_real_lowerSemicontinuous_cap {f : X → EReal}
    (hf : LowerSemicontinuous f) (L C : ℝ) (hLC : L ≤ C)
    (hL : ∀ x, (L : EReal) ≤ f x) :
    ∃ g : X → ℝ, LowerSemicontinuous g ∧
      (∀ x, (g x : EReal) = min (f x) (C : EReal)) ∧
      ∀ x, L ≤ g x ∧ g x ≤ C := by
  let g : X → ℝ := fun x => (min (f x) (C : EReal)).toReal
  have hcoe (x) : (g x : EReal) = min (f x) (C : EReal) := by
    apply EReal.coe_toReal
    · exact ne_of_lt ((min_le_right (f x) (C : EReal)).trans_lt (EReal.coe_lt_top C))
    · exact ne_of_gt (lt_min ((EReal.bot_lt_coe L).trans_le (hL x)) (EReal.bot_lt_coe C))
  have hg : LowerSemicontinuous g := by
    apply lowerSemicontinuous_of_ereal_coe
    have heq : (fun x => (g x : EReal)) = fun x => min (f x) (C : EReal) := funext hcoe
    rw [heq]
    apply lowerSemicontinuous_iff_isOpen_preimage.mpr
    intro t
    have he : (fun x => min (f x) (C : EReal)) ⁻¹' Ioi t =
        (f ⁻¹' Ioi t) ∩ ((fun _ : X => (C : EReal)) ⁻¹' Ioi t) := by
      ext x
      change t < min (f x) (C : EReal) ↔ t < f x ∧ t < (C : EReal)
      exact lt_min_iff
    rw [he]
    exact (hf.isOpen_preimage t).inter
      ((show LowerSemicontinuous (fun _ : X => (C : EReal)) from lowerSemicontinuous_const).isOpen_preimage t)
  refine ⟨g, hg, hcoe, fun x => ?_⟩
  constructor
  · apply EReal.coe_le_coe_iff.mp
    rw [hcoe x]
    exact le_min (hL x) (EReal.coe_le_coe_iff.mpr hLC)
  · apply EReal.coe_le_coe_iff.mp
    rw [hcoe x]
    exact min_le_right _ _

/-- An actual finite upper bound and finite floor internally give a real USC
obstacle, with no readback at an uncut negative-infinite pole. -/
theorem exists_real_upperSemicontinuous_floor {f : X → EReal}
    (hf : UpperSemicontinuous f) (L C : ℝ) (hLC : L ≤ C)
    (hC : ∀ x, f x ≤ (C : EReal)) :
    ∃ g : X → ℝ, UpperSemicontinuous g ∧
      (∀ x, (g x : EReal) = max (f x) (L : EReal)) ∧
      ∀ x, L ≤ g x ∧ g x ≤ C := by
  let g : X → ℝ := fun x => (max (f x) (L : EReal)).toReal
  have hcoe (x) : (g x : EReal) = max (f x) (L : EReal) := by
    apply EReal.coe_toReal
    · exact ne_of_lt ((max_le (hC x) (EReal.coe_le_coe_iff.mpr hLC)).trans_lt (EReal.coe_lt_top C))
    · exact ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right (f x) (L : EReal)))
  have hg : UpperSemicontinuous g := by
    apply upperSemicontinuous_of_ereal_coe
    have heq : (fun x => (g x : EReal)) = fun x => max (f x) (L : EReal) := funext hcoe
    rw [heq]
    apply upperSemicontinuous_iff_isOpen_preimage.mpr
    intro t
    have he : (fun x => max (f x) (L : EReal)) ⁻¹' Iio t =
        (f ⁻¹' Iio t) ∩ ((fun _ : X => (L : EReal)) ⁻¹' Iio t) := by
      ext x
      change max (f x) (L : EReal) < t ↔ f x < t ∧ (L : EReal) < t
      exact max_lt_iff
    rw [he]
    exact (hf.isOpen_preimage t).inter
      ((show UpperSemicontinuous (fun _ : X => (L : EReal)) from upperSemicontinuous_const).isOpen_preimage t)
  refine ⟨g, hg, hcoe, fun x => ?_⟩
  constructor
  · apply EReal.coe_le_coe_iff.mp
    rw [hcoe x]
    exact le_max_right _ _
  · apply EReal.coe_le_coe_iff.mp
    rw [hcoe x]
    exact max_le (hC x) (EReal.coe_le_coe_iff.mpr hLC)


end SGPT.Bergman.GlobalWeightFiniteObstacles
