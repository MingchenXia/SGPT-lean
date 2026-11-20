import SGPT.Checks.Comparison.BJModel2GaussPoint

/-!
# `σ(v)(𝔞 · 𝒪_𝒳) = b - φ_𝔞(v)` on the blow-up model (lane BJ-MODEL2, step R1(e))

Source: [BJ22] (`references/bj22-trivval`), §2.1: `σ(v)(𝔞) = min_λ (v(𝔞_λ) - λ)` and
`φ_𝔞 = -σ(·)(𝔞)` (`equ:gaussflag`); on the test configuration `𝒳` of `𝔞`, `𝔞 · 𝒪_𝒳 = 𝒪_𝒳(D)`
and `φ_𝔞(v) = σ(v)(D)` ([BJ22, proof of `thm:VCarPL`]). Here `t^b 𝔞` is an honest ideal sheaf and
the statement reads `σ(v)(t^b 𝔞 · 𝒪_𝒳) = b - φ_𝔞(v)`. Blueprint: `claude-bj-model2.tex`.

* `iInf_idealVal_add_eq_ofReal`: `inf_j (v(𝔞_{b-j}) + j) = b - φ_𝔞(v)` for a weight bound `b`;
* `idealVal_gaussPoint_flagSheaf_eq`, `idealVal_gaussModelPoint_flagSheaf`: the value of `t^b 𝔞`
  at the Gauss point of `X × ℙ¹`, and of `(t^b 𝔞) · 𝒪_𝒳` at the Gauss point of the model, is
  `b - φ_𝔞(v)`, given that the Gauss point has value `1` on the ideal of the central fibre
  (`σ(v)(t) = 1`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.BJ

open AlgebraicGeometry CategoryTheory
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJModel FlagIdealBound
open scoped ENNReal

section algebra

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} [IsProper f]

/-- **`inf_j (v(𝔞_{b-j}) + j) = b - φ_𝔞(v)`** for a weight bound `b` of `𝔞`: the formula
`σ(v)(t^b 𝔞) = min_j (v(𝔞_{b-j}) + j) = b - φ_𝔞(v)` of [BJ22, §2.1]. -/
theorem iInf_idealVal_add_eq_ofReal (v : BerkovichPoint f) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) :
    ⨅ j : ℕ, (v.idealVal (𝔞.ideal (b - j)) + (j : ℝ≥0∞)) = ENNReal.ofReal (b - 𝔞.phi v) := by
  have hφ : 𝔞.phi v ≤ b := 𝔞.phi_le v hb
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨l, hl⟩ := (𝔞.lt_phi_iff v (𝔞.phi v - ε)).mp (by
      have : (0 : ℝ) < ε := hε
      linarith)
    have hpos : 0 < (l : ℝ) - (𝔞.phi v - ε) :=
      ENNReal.ofReal_pos.mp (lt_of_le_of_lt (zero_le) hl)
    have hlb : l ≤ b := by
      by_contra h
      rw [hb l (by omega), idealVal_bot] at hl
      exact not_top_lt hl
    obtain ⟨j, hj⟩ : ∃ j : ℕ, l = b - j := ⟨(b - l).toNat, by omega⟩
    have hjr : ((j : ℕ) : ℝ) = (b : ℝ) - l := by
      have : ((j : ℤ) : ℝ) = ((b - l : ℤ) : ℝ) := by rw [hj]; ring_nf
      push_cast at this
      linarith
    calc ⨅ j : ℕ, (v.idealVal (𝔞.ideal (b - j)) + (j : ℝ≥0∞))
        ≤ v.idealVal (𝔞.ideal (b - j)) + (j : ℝ≥0∞) := iInf_le _ j
      _ ≤ ENNReal.ofReal ((l : ℝ) - (𝔞.phi v - ε)) + ENNReal.ofReal (j : ℝ) := by
          rw [← hj, ENNReal.ofReal_natCast]
          exact add_le_add hl.le le_rfl
      _ = ENNReal.ofReal ((b : ℝ) - 𝔞.phi v + ε) := by
          rw [← ENNReal.ofReal_add hpos.le (Nat.cast_nonneg j)]
          congr 1
          rw [hjr]
          ring
      _ = ENNReal.ofReal ((b : ℝ) - 𝔞.phi v) + (ε : ℝ≥0∞) := by
          rw [ENNReal.ofReal_add (p := (b : ℝ) - 𝔞.phi v) (q := (ε : ℝ)) (by linarith)
            ε.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · refine le_iInf fun j => ?_
    have h1 := 𝔞.ofReal_sub_phi_le v (b - j)
    push_cast at h1
    calc ENNReal.ofReal ((b : ℝ) - 𝔞.phi v)
        = ENNReal.ofReal (((b : ℝ) - j - 𝔞.phi v) + j) := by ring_nf
      _ ≤ ENNReal.ofReal ((b : ℝ) - j - 𝔞.phi v) + ENNReal.ofReal (j : ℝ) := ENNReal.ofReal_add_le
      _ ≤ v.idealVal (𝔞.ideal (b - j)) + (j : ℝ≥0∞) := by
          rw [ENNReal.ofReal_natCast]
          exact add_le_add h1 le_rfl

end algebra

variable {X : Scheme.{0}} {p : X ⟶ Spec (.of ℂ)} [IsProjective p]

local instance : IsProper p := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective p).isProper

/-- **`σ(v)(t^b 𝔞) = b - φ_𝔞(v)`** at the Gauss point of `X × ℙ¹`, for a weight bound `b`, given
`σ(v)(t) = 1` on the ideal of the central fibre. -/
theorem idealVal_gaussPoint_flagSheaf_eq (v : BerkovichPoint p) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) (hc : (gaussPoint v).idealVal (centralIdeal p) = 1) :
    (gaussPoint v).idealVal (flagSheaf p 𝔞 b) = ENNReal.ofReal (b - 𝔞.phi v) := by
  rw [idealVal_gaussPoint_flagSheaf, hc, ← iInf_idealVal_add_eq_ofReal v 𝔞 hb]
  simp only [mul_one]

/-- **The Gauss point of the model computes `φ_𝔞`** ([BJ22, §2.1]): on the blow-up model `𝒳` of
`t^b 𝔞`, `σ(v)((t^b 𝔞) · 𝒪_𝒳) = b - φ_𝔞(v)`, given `σ(v)(t) = 1`. -/
theorem idealVal_gaussModelPoint_flagSheaf (v : BerkovichPoint p) (𝔞 : FlagIdeal X) {b : ℤ}
    (hb : IsWeightBound 𝔞 b) (hc : (gaussPoint v).idealVal (centralIdeal p) = 1) :
    (gaussModelPoint v 𝔞 b).idealVal ((flagSheaf p 𝔞 b).comap (flagModelπ p 𝔞 b)) =
      ENNReal.ofReal (b - 𝔞.phi v) := by
  rw [idealVal_gaussModelPoint_comap, idealVal_gaussPoint_flagSheaf_eq v 𝔞 hb hc]

end SGPT.NAPotential.BJ
