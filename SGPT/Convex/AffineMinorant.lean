import SGPT.Convex.Closure

/-!
# Actual affine minorants of proper convex functions

Finite-dimensional intrinsic-interior separation constructs the actual
minorant even when the effective domain has smaller affine dimension.
No lower semicontinuity or ordinary epigraph interior is assumed.
-/

namespace SGPT.Convex

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every proper convex function in finite dimension admits an actual continuous
affine minorant, including functions on lower-dimensional effective domains. -/
theorem exists_continuous_affine_minorant_of_isProper {f : E → EReal}
    (hf : IsProper f) :
    ∃ (m : E →L[ℝ] ℝ) (b : ℝ), ∀ z, ((m z + b : ℝ) : EReal) ≤ f z := by
  obtain ⟨x₀, hx₀⟩ := hf.2.1
  have hfinite : f x₀ = ((f x₀).toReal : EReal) :=
    (EReal.coe_toReal (ne_of_lt hx₀) (hf.2.2 x₀)).symm
  have hnonempty : (epigraph f).Nonempty := ⟨(x₀, (f x₀).toReal), hfinite.le⟩
  obtain ⟨⟨x, s⟩, hp⟩ := hnonempty.intrinsicInterior hf.1
  have hpmem : (x, s) ∈ epigraph f := intrinsicInterior_subset hp
  have hps : f x ≤ (s : EReal) := hpmem
  let u : ℝ := (f x).toReal
  have hfx : f x = (u : EReal) :=
    (EReal.coe_toReal (ne_of_lt (hps.trans_lt (EReal.coe_lt_top s))) (hf.2.2 x)).symm
  have hus : u ≤ s := EReal.coe_le_coe_iff.mp (by simpa only [hfx] using hps)
  let A := affineSpan ℝ (epigraph f)
  have hpA : (x, s) ∈ A := subset_affineSpan ℝ (epigraph f) (intrinsicInterior_subset hp)
  have hp1A : (x, s + 1) ∈ A := by
    apply subset_affineSpan ℝ (epigraph f)
    exact hps.trans (EReal.coe_le_coe (by linarith : s ≤ s + 1))
  have hvertical : ((0 : E), (1 : ℝ)) ∈ A.direction := by
    have h := A.vsub_mem_direction hp1A hpA
    simpa [vsub_eq_sub] using h
  have hqA : (x, u - 1) ∈ A := by
    have h := A.vadd_mem_of_mem_direction
      (A.direction.smul_mem (u - 1 - s) hvertical) hpA
    convert h using 1
    ext <;> simp [vadd_eq_add]
  have hqnot : (x, u - 1) ∉ epigraph f := by
    change ¬ f x ≤ ((u - 1 : ℝ) : EReal)
    rw [hfx, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨L, hstrict, hsep⟩ := exists_functional_of_mem_intrinsicInterior hf.1 hp hqA hqnot
  let a : ℝ := L (0, 1)
  have hsplit (z : E) (t : ℝ) : L (z, t) = L (z, 0) + t * a := by
    have heq : (z, t) = (z, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [heq, map_add, map_smul]
    rfl
  have ha : 0 < a := by
    rw [hsplit x (u - 1), hsplit x s] at hstrict
    nlinarith
  let ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let m : E →L[ℝ] ℝ := (-a⁻¹) • ℓ
  let b : ℝ := L (x, u - 1) / a
  have hvalue (z : E) : m z + b = (L (x, u - 1) - L (z, 0)) / a := by
    simp only [m, b, ℓ, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  refine ⟨m, b, ?_⟩
  intro z
  cases hz : f z using EReal.rec with
  | bot => exact False.elim (hf.2.2 z hz)
  | top => exact le_top
  | coe c =>
    have hzc : (z, c) ∈ epigraph f := hz.le
    have h := hsep (z, c) hzc
    rw [hsplit z c] at h
    rw [hvalue, EReal.coe_le_coe_iff, div_le_iff₀ ha]
    linarith

end SGPT.Convex
