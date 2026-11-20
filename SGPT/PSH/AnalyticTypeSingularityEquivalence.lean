import SGPT.PSH.IntrinsicRationalAnalytic
import SGPT.PSH.SingularityOrder
import SGPT.Foundations.Analysis.FirstPass.ExtendedDifference

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X] {A : VariableComplexAtlas X}

/-- Keep each original connected neighborhood, positive rational coefficient,
and actual holomorphic generators, changing only its bounded real remainder. -/
theorem HasRationalAnalyticType.of_singularityEquiv {u v : X → EReal}
    (hA : A.HasRationalAnalyticType u)
    (hu : ∀ x, u x ≠ ⊤) (hv : ∀ x, v x ≠ ⊤)
    (h : SGPT.PSH.SingularityEquiv u v) : A.HasRationalAnalyticType v := by
  let d : X → ℝ := fun x => canonicalERealDiffToReal (v x) (u x)
  obtain ⟨C, D, hCD⟩ := sameSingularityTypeOn_canonicalDiff_bounded h.symm
  have hd (x : X) : |d x| ≤ |C| + |D| := by
    by_cases hp : v x = ⊥
    · have hup : u x = ⊥ := h.1.eq_bot_of_eq_bot (mem_univ x) hp
      simp only [d, hp, hup, canonicalERealDiffToReal_bot_bot, abs_zero]
      positivity
    · have hb := hCD x (mem_univ x) (hv x) (hu x) hp
      exact abs_le.mpr ⟨by linarith [le_abs_self D, abs_nonneg C],
        by linarith [le_abs_self C, abs_nonneg D]⟩
  have heq (x : X) : v x = u x + (d x : EReal) := by
    by_cases hp : v x = ⊥
    · have hup : u x = ⊥ := h.1.eq_bot_of_eq_bot (mem_univ x) hp
      simp [d, hp, hup]
    · have hup : u x ≠ ⊥ := fun hb => hp (h.2.eq_bot_of_eq_bot (mem_univ x) hb)
      change v x = u x + (canonicalERealDiffToReal (v x) (u x) : EReal)
      have hucoe := EReal.coe_toReal (hu x) hup
      have hvcoe := EReal.coe_toReal (hv x) hp
      conv_rhs => rw [← hvcoe, ← hucoe, canonicalERealDiffToReal_coe_coe]
      rw [← EReal.coe_add]
      convert hvcoe.symm using 1
      congr 1
      ring
  intro x
  obtain ⟨c, N, f, b, B, U, hc, hB, hU, hconn, hxU, hf, hb, hrep⟩ := hA x
  refine ⟨c, N, f, fun y => b y + d y, B + (|C| + |D|), U,
    hc, by positivity, hU, hconn, hxU, hf, ?_, ?_⟩
  · intro y hy
    exact (abs_add_le _ _).trans (add_le_add (hb y hy) (hd y))
  · intro y hy
    rw [heq y, hrep hy]
    simp only [EReal.coe_add, add_assoc]

end SGPT.PSH.VariableComplexAtlas
