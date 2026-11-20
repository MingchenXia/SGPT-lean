import SGPT.Convex.IntrinsicLinearImage
import SGPT.Convex.InfimalConvolution

/-!
# Actual qualified conjugation

The perturbation is an actual infimum of actual costs. Its genuine domain
qualification and the actual touching-minorant producer yield dual splitting.
-/

namespace SGPT.Convex

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual binary perturbation, including all actual infinite infima. -/
noncomputable def binaryPerturbation (f g : E → EReal) (m : StrongDual ℝ E)
    (z : E) : EReal := ⨅ x, f (x + z) + g x - (m x : EReal)

omit [FiniteDimensional ℝ E] in
private theorem binary_cost_finite {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    {x z : E} {m : StrongDual ℝ E} {r : ℝ}
    (h : f (x + z) + g x - (m x : EReal) < (r : EReal)) :
    f (x + z) = ((f (x + z)).toReal : EReal) ∧ g x = ((g x).toReal : EReal) := by
  have hsum : f (x + z) + g x ≠ ⊤ := by
    intro heq
    simp [heq] at h
  obtain ⟨hftop, hgtop⟩ :=
    (EReal.add_ne_top_iff_ne_top₂ (hf.2.2 _) (hg.2.2 _)).mp hsum
  exact ⟨(EReal.coe_toReal hftop (hf.2.2 _)).symm,
    (EReal.coe_toReal hgtop (hg.2.2 _)).symm⟩

omit [FiniteDimensional ℝ E] in
/-- Actual cost interpolation proves convexity of the actual perturbation. -/
theorem isConvex_binaryPerturbation {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : StrongDual ℝ E) :
    IsConvex (binaryPerturbation f g m) := by
  apply isConvex_iff_strict_combo.mpr
  intro x y r s a b hxr hys ha hb hab
  obtain ⟨u, hur⟩ := iInf_lt_iff.mp hxr
  obtain ⟨v, hvs⟩ := iInf_lt_iff.mp hys
  obtain ⟨huf, hug⟩ := binary_cost_finite hf hg hur
  obtain ⟨hvf, hvg⟩ := binary_cost_finite hf hg hvs
  have hcostu : f (u + x) + g u - (m u : EReal) =
      (((f (u + x)).toReal + (g u).toReal - m u : ℝ) : EReal) := by
    rw [huf, hug, ← EReal.coe_add, ← EReal.coe_sub]
    simp only [EReal.toReal_coe]
  have hcostv : f (v + y) + g v - (m v : EReal) =
      (((f (v + y)).toReal + (g v).toReal - m v : ℝ) : EReal) := by
    rw [hvf, hvg, ← EReal.coe_add, ← EReal.coe_sub]
    simp only [EReal.toReal_coe]
  have hur' : (f (u + x)).toReal + (g u).toReal - m u < r := by
    simpa only [hcostu, EReal.coe_lt_coe_iff] using hur
  have hvs' : (f (v + y)).toReal + (g v).toReal - m v < s := by
    simpa only [hcostv, EReal.coe_lt_coe_iff] using hvs
  let w : E := a • u + b • v
  have hw : w + (a • x + b • y) = a • (u + x) + b • (v + y) := by
    simp only [w, smul_add]
    abel
  have hfc : f (w + (a • x + b • y)) ≤
      ((a * (f (u + x)).toReal + b * (f (v + y)).toReal : ℝ) : EReal) := by
    rw [hw]
    exact hf.1 (x := (u + x, (f (u + x)).toReal))
      (y := (v + y, (f (v + y)).toReal)) huf.le hvf.le ha.le hb.le hab
  have hgc : g w ≤ ((a * (g u).toReal + b * (g v).toReal : ℝ) : EReal) :=
    hg.1 (x := (u, (g u).toReal)) (y := (v, (g v).toReal))
      hug.le hvg.le ha.le hb.le hab
  have hmc : m w = a * m u + b * m v := by simp [w]
  have hcost : f (w + (a • x + b • y)) + g w - (m w : EReal) ≤
      ((a * ((f (u + x)).toReal + (g u).toReal - m u) +
        b * ((f (v + y)).toReal + (g v).toReal - m v) : ℝ) : EReal) := by
    calc
      _ ≤ ((a * (f (u + x)).toReal + b * (f (v + y)).toReal : ℝ) : EReal) +
          ((a * (g u).toReal + b * (g v).toReal : ℝ) : EReal) - (m w : EReal) :=
        EReal.sub_le_sub (add_le_add hfc hgc) le_rfl
      _ = _ := by rw [hmc, ← EReal.coe_add, ← EReal.coe_sub]; congr 1; ring
  have hstrict : a * ((f (u + x)).toReal + (g u).toReal - m u) +
      b * ((f (v + y)).toReal + (g v).toReal - m v) < a * r + b * s :=
    add_lt_add (mul_lt_mul_of_pos_left hur' ha) (mul_lt_mul_of_pos_left hvs' hb)
  exact ((iInf_le (fun z ↦ f (z + (a • x + b • y)) + g z - (m z : EReal)) w).trans
    hcost).trans_lt (EReal.coe_lt_coe hstrict)

omit [FiniteDimensional ℝ E] in
/-- The actual perturbation domain is exactly the actual difference domain. -/
theorem effectiveDomain_binaryPerturbation {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : StrongDual ℝ E) :
    effectiveDomain (binaryPerturbation f g m) =
      {z | ∃ u ∈ effectiveDomain f, ∃ v ∈ effectiveDomain g, u - v = z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨r, hzr, _⟩ := EReal.exists_between_coe_real hz
    obtain ⟨x, hxr⟩ := iInf_lt_iff.mp hzr
    obtain ⟨hfx, hgx⟩ := binary_cost_finite hf hg hxr
    refine ⟨x + z, ?_, x, ?_, add_sub_cancel_left x z⟩
    · change f (x + z) < ⊤
      rw [hfx]
      exact EReal.coe_lt_top _
    · change g x < ⊤
      rw [hgx]
      exact EReal.coe_lt_top _
  · rintro ⟨u, hu, v, hv, rfl⟩
    have heq : v + (u - v) = u := by abel
    have hfu : f u = ((f u).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hu) (hf.2.2 _)).symm
    have hgv : g v = ((g v).toReal : EReal) :=
      (EReal.coe_toReal (ne_of_lt hv) (hg.2.2 _)).symm
    apply (iInf_le (fun x ↦ f (x + (u - v)) + g x - (m x : EReal)) v).trans_lt
    rw [heq, hfu, hgv, ← EReal.coe_add, ← EReal.coe_sub]
    exact EReal.coe_lt_top _

/-- Common actual relative-interior domain points qualify the perturbation at zero. -/
theorem zero_mem_intrinsicInterior_effectiveDomain_binaryPerturbation
    {f g : E → EReal} (hf : IsProper f) (hg : IsProper g)
    (m : StrongDual ℝ E) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx' : x ∈ intrinsicInterior ℝ (effectiveDomain g)) :
    (0 : E) ∈ intrinsicInterior ℝ (effectiveDomain (binaryPerturbation f g m)) := by
  rw [effectiveDomain_binaryPerturbation hf hg m]
  exact zero_mem_intrinsicInterior_difference hx hx'

omit [FiniteDimensional ℝ E] in
/-- The actual perturbation value at zero is the negative actual sum conjugate. -/
theorem binaryPerturbation_zero_eq_neg_conjugate (f g : E → EReal)
    (m : StrongDual ℝ E) :
    binaryPerturbation f g m 0 =
      -conjugate continuousDualPairing (fun x ↦ f x + g x) m := by
  have h := EReal.negOrderIso.map_iSup
    (fun x : E ↦ (m x : EReal) - (f x + g x))
  change -(⨆ x : E, (m x : EReal) - (f x + g x)) =
    ⨅ x : E, -((m x : EReal) - (f x + g x)) at h
  change (⨅ x : E, f (x + 0) + g x - (m x : EReal)) =
    -(⨆ x : E, (m x : EReal) - (f x + g x))
  rw [h]
  apply iInf_congr
  intro x
  rw [add_zero, EReal.neg_sub (Or.inl (EReal.coe_ne_bot _))
    (Or.inl (EReal.coe_ne_top _)), sub_eq_add_neg, add_comm]

/-- A genuine finite conjugate value makes the actually qualified perturbation proper. -/
theorem isProper_binaryPerturbation_of_conjugate_ne_top {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : StrongDual ℝ E) {x : E}
    (hx : x ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx' : x ∈ intrinsicInterior ℝ (effectiveDomain g))
    (hfinite : conjugate continuousDualPairing (fun x ↦ f x + g x) m ≠ ⊤) :
    IsProper (binaryPerturbation f g m) := by
  apply isProper_of_ne_bot_of_mem_intrinsicInterior (isConvex_binaryPerturbation hf hg m)
    (zero_mem_intrinsicInterior_effectiveDomain_binaryPerturbation hf hg m hx hx')
  rw [binaryPerturbation_zero_eq_neg_conjugate]
  exact fun h ↦ hfinite (EReal.neg_eq_bot_iff.mp h)

omit [FiniteDimensional ℝ E] in
/-- Every actual continuous covector split supplies the genuine weak-duality bound. -/
theorem conjugate_add_le_split {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m ℓ : StrongDual ℝ E) :
    conjugate continuousDualPairing (fun x ↦ f x + g x) m ≤
      conjugate continuousDualPairing f ℓ + conjugate continuousDualPairing g (m - ℓ) := by
  apply iSup_le
  intro x
  change (m x : EReal) - (f x + g x) ≤ _
  have hm : m x = ℓ x + (m - ℓ) x := by simp
  calc
    (m x : EReal) - (f x + g x) =
        ((ℓ x : EReal) - f x) + (((m - ℓ) x : EReal) - g x) := by
      rw [hm, EReal.coe_add, EReal.add_sub_add_comm
        (Or.inl (hf.2.2 x)) (Or.inr (hg.2.2 x))]
    _ ≤ _ := add_le_add (le_iSup (fun y ↦ (ℓ y : EReal) - f y) x)
      (le_iSup (fun y ↦ ((m - ℓ) y : EReal) - g y) x)

/-- At a genuinely finite qualified conjugate, an actual touching minorant
produces a genuine continuous-covector split attaining the dual cost. -/
theorem exists_split_of_conjugate_ne_top {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : StrongDual ℝ E) {x₀ : E}
    (hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx₀' : x₀ ∈ intrinsicInterior ℝ (effectiveDomain g))
    (hfinite : conjugate continuousDualPairing (fun x ↦ f x + g x) m ≠ ⊤) :
    ∃ ℓ : StrongDual ℝ E,
      conjugate continuousDualPairing f ℓ + conjugate continuousDualPairing g (m - ℓ) =
        conjugate continuousDualPairing (fun x ↦ f x + g x) m := by
  have hv := isProper_binaryPerturbation_of_conjugate_ne_top hf hg m hx₀ hx₀' hfinite
  have hzero := zero_mem_intrinsicInterior_effectiveDomain_binaryPerturbation hf hg m hx₀ hx₀'
  obtain ⟨ℓ, b, hminor, htouch⟩ := exists_touching_continuous_affine_minorant hv hzero
  have hb : (b : EReal) = -conjugate continuousDualPairing (fun x ↦ f x + g x) m := by
    simpa only [map_zero, zero_add, binaryPerturbation_zero_eq_neg_conjugate] using htouch
  have hc : conjugate continuousDualPairing (fun x ↦ f x + g x) m = ((-b : ℝ) : EReal) := by
    have h := congrArg Neg.neg hb
    simpa only [← EReal.coe_neg, neg_neg] using h.symm
  have hcost (y x : E) :
      ((ℓ y : EReal) - f y) + (((m - ℓ) x : EReal) - g x) ≤ ((-b : ℝ) : EReal) := by
    by_cases hytop : f y = ⊤
    · simp [hytop]
    by_cases hxtop : g x = ⊤
    · simp [hxtop]
    have hfy : f y = ((f y).toReal : EReal) :=
      (EReal.coe_toReal hytop (hf.2.2 _)).symm
    have hgx : g x = ((g x).toReal : EReal) :=
      (EReal.coe_toReal hxtop (hg.2.2 _)).symm
    have hp := (hminor (y - x)).trans
      (iInf_le (fun u ↦ f (u + (y - x)) + g u - (m u : EReal)) x)
    have heq : x + (y - x) = y := by abel
    rw [heq, hfy, hgx, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hp
    rw [hfy, hgx, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    simp only [map_sub, sub_apply] at hp ⊢
    linarith
  refine ⟨ℓ, le_antisymm ?_ (conjugate_add_le_split hf hg m ℓ)⟩
  rw [hc]
  change (⨆ y : E, (ℓ y : EReal) - f y) +
    (⨆ x : E, ((m - ℓ) x : EReal) - g x) ≤ ((-b : ℝ) : EReal)
  rw [iSup_add_iSup]
  exact iSup_le fun y ↦ iSup_le fun x ↦ hcost y x

/-- Genuine binary qualified conjugation as the actual infimum over actual splits. -/
theorem conjugate_add_eq_iInf_split_of_common_intrinsicInterior {f g : E → EReal}
    (hf : IsProper f) (hg : IsProper g) (m : StrongDual ℝ E) {x₀ : E}
    (hx₀ : x₀ ∈ intrinsicInterior ℝ (effectiveDomain f))
    (hx₀' : x₀ ∈ intrinsicInterior ℝ (effectiveDomain g)) :
    conjugate continuousDualPairing (fun x ↦ f x + g x) m =
      ⨅ ℓ : StrongDual ℝ E,
        conjugate continuousDualPairing f ℓ + conjugate continuousDualPairing g (m - ℓ) := by
  apply le_antisymm
  · exact le_iInf fun ℓ ↦ conjugate_add_le_split hf hg m ℓ
  · by_cases htop : conjugate continuousDualPairing (fun x ↦ f x + g x) m = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨ℓ, hℓ⟩ := exists_split_of_conjugate_ne_top hf hg m hx₀ hx₀' htop
    exact (iInf_le _ ℓ).trans hℓ.le

end SGPT.Convex
