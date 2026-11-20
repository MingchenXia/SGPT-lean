import SGPT.Trace.TwistedL2MDefectForm
import SGPT.Trace.TwistedL2MainConclusion

/-!
# The functional bound on `ℂⁿ` from the density lemma in its textbook form

Blueprint `claude-tl2-main.tex` (`claude-tl2-main:defect`, `claude-tl2-main:sigma-density`).
`FrameFamily.defect_le`: the `∂̄`-defect of a family is at most `sup_U a` times its `S`-energy
`‖∂̄(σ^♭ W_τ)‖²` (`FrameFamily.senergy`).  Hence graph density follows from
`TwistedDatum.SigmaGraphDensity` (approximation in the data pairing and the `T*`-energy by families
of small `S`-energy: density of test forms in `Dom T* ∩ ker S` for the graph norm), and
`TwistedFunctionalBoundStatement n (ComplexModel n)` follows from `SigmaGraphDensity` for all data.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Set Filter MeasureTheory Matrix Bundle
open scoped Topology ContDiff ComplexConjugate ComplexOrder Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.Hormander
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ}

namespace TwistedDatum

variable {T : TwistedDatum n (ComplexModel n)} {ρ : ComplexModel n → ℝ}

namespace FrameFamily

/-- The `S`-energy `‖∂̄(σ^♭ W_τ)‖²` of a family (weight `e^{-φ}`, metric `σ`). -/
def senergy (F : T.FrameFamily) (ρ : ComplexModel n → ℝ) : ℝ :=
  ∫ z, (T.Φ (T.FS ρ) F.s F.e F.h z).re

variable (hρ : IsChartDensity T.μ chart0 ρ) (F : T.FrameFamily)
include hρ

theorem neg_FT_le {Ma : ℝ} (hMa : ∀ x ∈ T.U, T.a x ≤ Ma) (z : ComplexModel n) :
    -(T.Φ (T.FT ρ) F.s F.e F.h z).re ≤ Ma * (T.Φ (T.FS ρ) F.s F.e F.h z).re := by
  by_cases hz : z ∈ T.U
  · set e₀ := atlasFrameAt T.L z
    have hz₀ : z ∈ T.dom e₀ := frameAt_mem_dom hz
    rw [Φ_eq_diag F.spec (isGaugeForm_tr hρ) hz, Φ_eq_diag F.spec (isGaugeForm_S hρ) hz]
    simp only [FT, FS, cweight]
    have hT : (trS (T.tot F.s F.e F.h e₀) (T.tot F.s F.e F.h e₀) z *
        ((Real.exp (-T.pT ρ e₀ z) : ℝ) : ℂ)).re =
        (trS (T.tot F.s F.e F.h e₀) (T.tot F.s F.e F.h e₀) z).re * Real.exp (-T.pT ρ e₀ z) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hS : (zeroTwoPair (sigmaInv T.omega T.r z) (sigmaDbar T.omega T.r (T.tot F.s F.e F.h e₀) z)
        (sigmaDbar T.omega T.r (T.tot F.s F.e F.h e₀) z) * ((Real.exp (-T.pW ρ e₀ z) : ℝ) : ℂ)).re =
        zeroTwoNormSq (sigmaInv T.omega T.r z) (sigmaDbar T.omega T.r (T.tot F.s F.e F.h e₀) z) *
          Real.exp (-T.pW ρ e₀ z) := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        zeroTwoPair_re]
    rw [hT, hS, exp_neg_pT hz₀]
    have hdef := neg_re_trS_le T.isOpen_U T.kahler (T.isOpen_dom e₀) (dom_subset_U e₀)
      ((T.contDiffOn_tot (s := F.s) F.spec e₀).mono fun y hy => ((T.mem_dom).mp hy).1) hz₀
    have hZ : 0 ≤ zeroTwoNormSq (sigmaInv T.omega T.r z)
        (sigmaDbar T.omega T.r (T.tot F.s F.e F.h e₀) z) :=
      zeroTwoNormSq_nonneg (posDef_sigmaMat_transpose T.isOpen_U T.kahler hz) _
    have ha := T.a_pos hz
    have haM := hMa z hz
    have hE := Real.exp_pos (-T.pW ρ e₀ z)
    have k1 := mul_le_mul_of_nonneg_right hdef (mul_nonneg ha.le hE.le)
    have k2 := mul_le_mul_of_nonneg_right haM (mul_nonneg hZ hE.le)
    nlinarith [k1, k2]
  · simp [Φ_eq_zero F.spec (isGaugeForm_tr hρ) hz, Φ_eq_zero F.spec (isGaugeForm_S hρ) hz]

/-- **The `∂̄`-defect is controlled by the `S`-energy** (`claude-tl2-main:defect`). -/
theorem defect_le {Ma : ℝ} (hMa : ∀ x ∈ T.U, T.a x ≤ Ma) : F.defect ρ ≤ Ma * F.senergy ρ := by
  have iT : Integrable (fun z => T.Φ (T.FT ρ) F.s F.e F.h z) :=
    T.integrable_sum_pieces (s := F.s) F.spec (isGaugeForm_tr hρ)
  have iS : Integrable (fun z => (T.Φ (T.FS ρ) F.s F.e F.h z).re) :=
    (T.integrable_sum_pieces (s := F.s) F.spec (isGaugeForm_S hρ)).re
  have hre : (∫ z, T.Φ (T.FT ρ) F.s F.e F.h z).re = ∫ z, (T.Φ (T.FT ρ) F.s F.e F.h z).re :=
    (integral_re iT).symm
  unfold defect senergy
  rw [hre, ← integral_neg, ← integral_const_mul]
  exact integral_mono iT.re.neg (iS.const_mul Ma) (neg_FT_le hρ F hMa)

end FrameFamily

variable (T) in
/-- **Density of test families in `Dom T* ∩ ker S` for the graph norm** (FPT
`lem:cutoff-mollifier-density`, read on test families): every family can be approximated in the
data pairing and in the `T*`-energy by families of arbitrarily small `S`-energy. -/
def SigmaGraphDensity : Prop :=
  ∀ ρ : ComplexModel n → ℝ, IsChartDensity T.μ chart0 ρ →
  ∀ F : T.FrameFamily, ∀ ε : ℝ, 0 < ε → ∃ F' : T.FrameFamily,
    ‖F'.data ρ - F.data ρ‖ ≤ ε ∧ F'.energy ρ ≤ F.energy ρ + ε ∧ F'.senergy ρ ≤ ε

theorem graphDensity_of_sigmaGraphDensity (h : T.SigmaGraphDensity) : T.GraphDensity := by
  intro ρ hρ F ε hε
  obtain ⟨m, Ma, hm, hb⟩ := T.bounds
  have hMa : ∀ x ∈ T.U, T.a x ≤ Ma := fun x hx => (hb x hx).2.1
  -- `Ma` may be taken positive
  set M' := max Ma 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hMa' : ∀ x ∈ T.U, T.a x ≤ M' := fun x hx => (hMa x hx).trans (le_max_left _ _)
  obtain ⟨F', h1, h2, h3⟩ := h ρ hρ F (min ε (ε / M')) (lt_min hε (div_pos hε hM'pos))
  refine ⟨F', h1.trans (min_le_left _ _), h2.trans (by linarith [min_le_left ε (ε / M')]), ?_⟩
  have hd := F'.defect_le hρ hMa'
  have h3' : F'.senergy ρ ≤ ε / M' := h3.trans (min_le_right _ _)
  calc F'.defect ρ ≤ M' * F'.senergy ρ := hd
    _ ≤ M' * (ε / M') := mul_le_mul_of_nonneg_left h3' hM'pos.le
    _ = ε := by field_simp

end TwistedDatum

variable (n)

/-- **`TwistedFunctionalBoundStatement` on `ℂⁿ` from the density lemma**
(`claude-tl2-main:sigma-density`). -/
theorem twistedFunctionalBoundStatement_of_sigmaGraphDensity
    (hdens : ∀ T : TwistedDatum n (ComplexModel n), T.SigmaGraphDensity) :
    TwistedFunctionalBoundStatement n (ComplexModel n) :=
  twistedFunctionalBoundStatement_of_graphDensity n fun T =>
    TwistedDatum.graphDensity_of_sigmaGraphDensity (hdens T)

/-- **The main twisted estimate on open sets of `ℂⁿ`** (`TwistedL2CorrectionStatement n ℂⁿ`, the
input of `thm:OT_ext` for `dim Y > 0`), from the density lemma for all data. -/
theorem twistedL2CorrectionStatement_complexModel_of_sigmaGraphDensity
    (hdens : ∀ T : TwistedDatum n (ComplexModel n), T.SigmaGraphDensity) :
    TwistedL2CorrectionStatement n (ComplexModel n) :=
  twistedL2CorrectionStatement_of_functional
    (twistedFunctionalBoundStatement_of_sigmaGraphDensity n hdens)

end SGPT.Trace.TwistedL2
