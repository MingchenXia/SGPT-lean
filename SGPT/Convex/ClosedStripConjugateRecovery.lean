import SGPT.Convex.TimeConjugateBounds
import SGPT.Convex.ClosedConvexSegmentContinuity

/-! The original dual inequalities manufacture the actual finite closed-strip
profile and both endpoint limits. Every intermediate domain/finite-value fact
is produced internally from those inequalities. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Convex
open Set Filter Topology
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The actual finite reading, used only on the internally proved closed strip. -/
def timeConjugateRealProfile (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (Ψ : F × ℝ → EReal)
    (p : E × ℝ) : ℝ := (conjugate (timeProductPairing B).flip Ψ p).toReal

/-- The true source dual bounds supply the whole finite convex strip profile,
finite convex endpoints below the original ones, and actual one-sided limits. -/
theorem timeConjugateRealProfile_spec
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair]
    (f₀ f₁ : E → ℝ) (Ψ : F × ℝ → EReal) (G : F → EReal)
    (hΨ : IsProper Ψ) (hG : IsProper G)
    (hlower : ∀ (m : F) (s : ℝ), max (conjugate B (fun x => (f₀ x : EReal)) m)
      (conjugate B (fun x => (f₁ x : EReal)) m + (s : EReal)) ≤ Ψ (m, s))
    (hupper : ∀ m s, Ψ (m, s) ≤ G m + ((max s 0 : ℝ) : EReal)) :
    ConvexOn ℝ (univ ×ˢ Icc (0 : ℝ) 1) (timeConjugateRealProfile B Ψ) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        ConvexOn ℝ univ (fun x => timeConjugateRealProfile B Ψ (x, t))) ∧
      (∀ x, timeConjugateRealProfile B Ψ (x, 0) ≤ f₀ x) ∧
      (∀ x, timeConjugateRealProfile B Ψ (x, 1) ≤ f₁ x) ∧
      (∀ x, Tendsto (fun t => timeConjugateRealProfile B Ψ (x, t))
        (𝓝[>] 0) (𝓝 (timeConjugateRealProfile B Ψ (x, 0)))) ∧
      (∀ x, Tendsto (fun t => timeConjugateRealProfile B Ψ (x, t))
        (𝓝[<] 1) (𝓝 (timeConjugateRealProfile B Ψ (x, 1)))) ∧
      (∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1,
        (timeConjugateRealProfile B Ψ p : EReal) =
          conjugate (timeProductPairing B).flip Ψ p) := by
  let H := conjugate (timeProductPairing B).flip Ψ
  have hHP : IsProper H := isProper_conjugate_of_isContPerfPair _ hΨ
  have hHL : LowerSemicontinuous H := lowerSemicontinuous_conjugate _ _
  have hD : effectiveDomain H = univ ×ˢ Icc (0 : ℝ) 1 :=
    effectiveDomain_timeConjugate_eq_closedStrip B f₀ f₁ Ψ G hG hlower hupper
  have hfinite (p : E × ℝ) (hp : p ∈ univ ×ˢ Icc (0 : ℝ) 1) :
      (timeConjugateRealProfile B Ψ p : EReal) = H p :=
    EReal.coe_toReal (ne_of_lt (show p ∈ effectiveDomain H from hD.symm ▸ hp)) (hHP.2.2 p)
  have hc : ConvexOn ℝ (univ ×ˢ Icc (0 : ℝ) 1) (timeConjugateRealProfile B Ψ) := by
    have hh := convexOn_toReal_effectiveDomain hHP
    rw [hD] at hh
    refine ⟨convex_univ.prod (convex_Icc 0 1), ?_⟩
    intro p hp q hq a b ha hb hab
    exact hh.2 hp hq ha hb hab
  have hslice (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ConvexOn ℝ univ (fun x => timeConjugateRealProfile B Ψ (x, t)) := by
    let A : E →ᵃ[ℝ] E × ℝ := (AffineMap.id ℝ E).prod (AffineMap.const ℝ E t)
    have hpre : A ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) = univ := by
      ext x
      simp [A, ht]
    have hh := hc.comp_affineMap A
    rw [hpre] at hh
    simpa only [A, Function.comp_def, AffineMap.prod_apply, AffineMap.id_apply,
      AffineMap.const_apply] using hh
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  refine ⟨hc, hslice, ?_, ?_, ?_, ?_, hfinite⟩
  · intro x
    have hh := timeConjugate_le_chord B f₀ f₁ Ψ hlower x hzero
    change H (x, 0) ≤ _ at hh
    rw [← hfinite (x, 0) ⟨mem_univ _, hzero⟩] at hh
    simpa only [sub_zero, one_mul, zero_mul, add_zero, EReal.coe_le_coe_iff] using hh
  · intro x
    have hh := timeConjugate_le_chord B f₀ f₁ Ψ hlower x hone
    change H (x, 1) ≤ _ at hh
    rw [← hfinite (x, 1) ⟨mem_univ _, hone⟩] at hh
    simpa only [sub_self, zero_mul, one_mul, zero_add, EReal.coe_le_coe_iff] using hh
  · intro x
    have hleft := tendsto_closedConvex_segment_left hHP hHL
      (show (x, 0) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hzero⟩)
      (show (x, 1) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hone⟩)
    have heq (t : ℝ) : (1 - t) • (x, 0) + t • (x, 1) = (x, t) := by
      apply Prod.ext
      · simp only [Prod.smul_fst, Prod.fst_add, ← add_smul, sub_add_cancel, one_smul]
      · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul, mul_zero, mul_one, zero_add]
    simp_rw [heq] at hleft
    exact (EReal.tendsto_toReal
      (ne_of_lt (show (x, 0) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hzero⟩))
      (hHP.2.2 (x, 0))).comp hleft
  · intro x
    have hright := tendsto_closedConvex_segment_left hHP hHL
      (show (x, 1) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hone⟩)
      (show (x, 0) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hzero⟩)
    have heq (t : ℝ) : (1 - t) • (x, 1) + t • (x, 0) = (x, 1 - t) := by
      apply Prod.ext
      · simp only [Prod.smul_fst, Prod.fst_add, ← add_smul, sub_add_cancel, one_smul]
      · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul, mul_zero, mul_one, add_zero]
    simp_rw [heq] at hright
    have hm : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun t : ℝ => 1 - t)
      · have hh : Continuous (fun t : ℝ => 1 - t) := by fun_prop
        simpa using (hh.tendsto 1).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change 0 < 1 - t
        linarith [show t < 1 from ht]
    have hh := hright.comp hm
    simp only [Function.comp_def, sub_sub_cancel] at hh
    exact (EReal.tendsto_toReal
      (ne_of_lt (show (x, 1) ∈ effectiveDomain H from hD.symm ▸ ⟨mem_univ _, hone⟩))
      (hHP.2.2 (x, 1))).comp hh

end SGPT.Convex
