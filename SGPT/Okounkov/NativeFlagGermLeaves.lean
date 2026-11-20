import SGPT.Okounkov.NativeFlagGermScalars

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

private theorem vector_const_mul {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (c : ℂ) (hc : c ≠ 0)
    (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) :
    originalFlagGermVector F x (NativeHolGerm.constHom c * f)
      (mul_ne_zero (NativeHolGerm.const_ne_zero c hc) hf) = originalFlagGermVector F x f hf := by
  rw [originalFlagGermVector_mul F x _ f (NativeHolGerm.const_ne_zero c hc) hf,
    originalFlagGermVector_const F x c hc, zero_add]

private theorem valuation_lt_top {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    (x : OriginalFlagGermPoint F) (f : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) :
    originalFlagGermValuation F x f < ⊤ := by
  rw [originalFlagGermValuation_apply_of_ne_zero F x f hf]
  exact WithTop.coe_lt_top _

private theorem lexVector_lt_of_head_lt {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0)
    (h : originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) f <
      originalFirstFlagGermOrderNat F (OriginalFlagGermPoint.first F x) g) :
    originalFlagGermLexVector F x f hf < originalFlagGermLexVector F x g hg := by
  rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
  change Pi.Lex (· < ·) (· < ·) _ _
  apply (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr
  exact Or.inl (by exact_mod_cast h)

/-- For SAME actual original values, a scalar manufactured from genuine
original tail cancellation increases the entire original value strictly.
In dimension zero it is the actual scalar ratio under original evaluation. -/
theorem exists_originalFlagGerm_scalar_cancel {n : ℕ}
    (F : OriginalFlagGeometry.{u} n) (x : OriginalFlagGermPoint F)
    (f g : NativeHolGerm n F.carrier x.1) (hf : f ≠ 0) (hg : g ≠ 0)
    (hν : originalFlagGermVector F x f hf = originalFlagGermVector F x g hg) :
    ∃ c : ℂ, c ≠ 0 ∧ originalFlagGermValuation F x f <
      originalFlagGermValuation F x (f + NativeHolGerm.constHom c * g) := by
  induction n with
  | zero =>
      have hfscalar : NativeHolGerm.eval f ≠ 0 := by
        intro hz
        apply hf
        apply NativeHolGerm.zeroDimensionEval_injective
        exact hz.trans (map_zero _).symm
      have hgscalar : NativeHolGerm.eval g ≠ 0 := by
        intro hz
        apply hg
        apply NativeHolGerm.zeroDimensionEval_injective
        exact hz.trans (map_zero _).symm
      refine ⟨-NativeHolGerm.eval f / NativeHolGerm.eval g,
        div_ne_zero (neg_ne_zero.mpr hfscalar) hgscalar, ?_⟩
      have hz : f + NativeHolGerm.constHom (-NativeHolGerm.eval f / NativeHolGerm.eval g) * g = 0 := by
        apply NativeHolGerm.zeroDimensionEval_injective
        rw [map_add, map_mul, map_zero]
        change NativeHolGerm.eval f +
          (-NativeHolGerm.eval f / NativeHolGerm.eval g) * NativeHolGerm.eval g = 0
        rw [div_mul_cancel₀ _ hgscalar, add_neg_cancel]
      rw [hz, (originalFlagGermValuation F x).map_zero]
      exact valuation_lt_top F x f hf
  | succ m ih =>
      let y := OriginalFlagGermPoint.first F x
      let z := OriginalFlagGermPoint.tail F x
      have heq : originalFirstFlagGermOrderNat F y f = originalFirstFlagGermOrderNat F y g :=
        congrFun hν 0
      have htailEq : originalFlagGermVector F.tail z
          (originalFirstFlagGermResidual F y f hf) (originalFirstFlagGermResidual_ne_zero F y f hf) =
          originalFlagGermVector F.tail z
            (originalFirstFlagGermResidual F y g hg) (originalFirstFlagGermResidual_ne_zero F y g hg) := by
        funext j
        exact congrFun hν j.succ
      obtain ⟨c, hc, hcancel⟩ := ih F.tail z
        (originalFirstFlagGermResidual F y f hf) (originalFirstFlagGermResidual F y g hg)
        (originalFirstFlagGermResidual_ne_zero F y f hf)
        (originalFirstFlagGermResidual_ne_zero F y g hg) htailEq
      let h : NativeHolGerm (m + 1) F.carrier x.1 := NativeHolGerm.constHom c * g
      have hh : h ≠ 0 := mul_ne_zero (NativeHolGerm.const_ne_zero c hc) hg
      have hvh := vector_const_mul F x c hc g hg
      have heqh : originalFirstFlagGermOrderNat F y f = originalFirstFlagGermOrderNat F y h :=
        heq.trans (congrFun hvh 0).symm
      refine ⟨c, hc, ?_⟩
      change originalFlagGermValuation F x f < originalFlagGermValuation F x (f + h)
      by_cases hs : f + h = 0
      · rw [hs, (originalFlagGermValuation F x).map_zero]
        exact valuation_lt_top F x f hf
      have hhead := originalFirstFlagGermOrderNat_le_add_of_eq F y f h hf hh hs heqh
      rw [originalFlagGermValuation_apply_of_ne_zero F x f hf,
        originalFlagGermValuation_apply_of_ne_zero F x (f + h) hs]
      apply WithTop.coe_lt_coe.mpr
      rcases hhead.lt_or_eq with hstrict | hsame
      · exact lexVector_lt_of_head_lt F x f (f + h) hf hs hstrict
      · have hres := originalFirstFlagGermResidual_add_of_eq F y f h hf hh hs heqh hsame.symm
        have hscaled := originalFirstFlagGermResidual_const_mul F y c hc g hg
        have hr : originalFirstFlagGermResidual F y (f + h) hs =
            originalFirstFlagGermResidual F y f hf +
              NativeHolGerm.constHom c * originalFirstFlagGermResidual F y g hg :=
          hres.trans (congrArg (fun q => originalFirstFlagGermResidual F y f hf + q) hscaled)
        have htail : originalFlagGermValuation F.tail z
            (originalFirstFlagGermResidual F y f hf) <
            originalFlagGermValuation F.tail z (originalFirstFlagGermResidual F y (f + h) hs) :=
          lt_of_lt_of_eq hcancel (congrArg (originalFlagGermValuation F.tail z) hr.symm)
        rw [originalFlagGermValuation_apply_of_ne_zero F.tail z _
            (originalFirstFlagGermResidual_ne_zero F y f hf),
          originalFlagGermValuation_apply_of_ne_zero F.tail z _
            (originalFirstFlagGermResidual_ne_zero F y (f + h) hs)] at htail
        rw [originalFlagGermLexVector_cons, originalFlagGermLexVector_cons]
        change Pi.Lex (· < ·) (· < ·) _ _
        exact (Fin.pi_lex_lt_cons_cons (s := (· < ·))).mpr
          (Or.inr ⟨congrArg Int.ofNat hsame, WithTop.coe_lt_coe.mp htail⟩)

end SGPT.Okounkov
